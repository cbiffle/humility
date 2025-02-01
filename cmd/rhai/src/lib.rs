// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! ## `humility rhai`
//!

use anyhow::{bail, Context as _, Result};
use clap::{CommandFactory, Parser};
use humility::core::Core;
use humility::reflect::Format as _;
use humility::{hubris::*, reflect};
use humility_cli::{ExecutionContext, Subcommand};
use humility_cmd::{Archive, Attach, Command, CommandKind, Dumper, Validate};
use rhai::{Dynamic, Engine, EvalAltResult, Map, ModuleResolver, Scope};
use std::collections::BTreeMap;
use std::convert::TryInto;
use std::io::Write;
use std::cell::RefCell;
use std::rc::Rc;
use std::path::PathBuf;
use std::time::Duration;

#[derive(Parser, Debug)]
#[clap(name = "rhai", about = env!("CARGO_PKG_DESCRIPTION"))]
struct RhaiArgs {
    script: PathBuf,
}

pub fn run(mut context: ExecutionContext) -> Result<()> {
    let Subcommand::Other(subargs) = context.cli.cmd.as_ref().unwrap();
    let subargs = RhaiArgs::try_parse_from(subargs)?;

    let mut hubris = HubrisArchive::new().context("failed to initialize")?;
    let doneness = HubrisArchiveDoneness::Cook;
    if let Some(archive) = &context.cli.archive {
        hubris.load(archive, doneness).with_context(|| {
            format!("failed to load archive \"{}\"", archive)
        })?;
    } else if let Some(dump) = &context.cli.dump {
        hubris
            .load_dump(dump, doneness)
            .with_context(|| format!("failed to load dump \"{}\"", dump))?;
    }
    context.archive = Some(hubris);

    let context = Rc::new(RefCell::new(context));

    //let core = &mut **context.core.as_mut().unwrap();
    let mut engine = Engine::new();
    engine.set_module_resolver(BundleResolver::new(context.clone()));

    engine.register_type::<reflect::Struct>();
    {
        let context = context.clone();
        engine.register_fn("to_string", move |p: &mut reflect::Enum| -> Result<String, Box<EvalAltResult>> {
            let ctx = context.borrow();
            let fmt = HubrisPrintFormat::default();
            let mut s = vec![];
            p.format(ctx.archive.as_ref().unwrap(), fmt, &mut s)
                .map_err(|e| e.to_string())?;
            Ok(String::from_utf8(s).unwrap())
        });
        engine.register_get("variant", move |e: &mut reflect::Enum| -> String {
            e.disc().into()
        });
        engine.register_get("contents", move |e: &mut reflect::Enum| -> Dynamic {
            if let Some(c) = e.contents() {
                rhaiify(c)
            } else {
                Dynamic::UNIT
            }
        });
        engine.register_fn("to_debug", move |p: &mut reflect::Enum| -> String {
            format!("{p:?}")
        });
    }
    {
        let context = context.clone();
        engine.register_fn("to_string", move |p: &mut reflect::Ptr| -> Result<String, Box<EvalAltResult>> {
            let ctx = context.borrow();
            let fmt = HubrisPrintFormat::default();
            let mut s = vec![];
            p.format(ctx.archive.as_ref().unwrap(), fmt, &mut s)
                .map_err(|e| e.to_string())?;
            Ok(String::from_utf8(s).unwrap())
        });
    }
    {
        let context = context.clone();
        engine.register_fn("deref", move |p: &mut reflect::Ptr| -> Result<Dynamic, Box<EvalAltResult>> {
            let mut ctx = context.borrow_mut();
            let ctx = &mut *ctx;
            let v = p.load_from(ctx.archive.as_ref().unwrap(), ctx.core.as_deref_mut().unwrap())
                .map_err(|e| e.to_string())?;
            Ok(rhaiify(&v))
        });
        engine.register_fn("to_debug", move |p: &mut reflect::Ptr| -> String {
            format!("{p:?}")
        });
    }

    {
        let context = context.clone();
        engine.register_fn("attach", move || -> Result<_, Box<EvalAltResult>> {
            humility_cmd::attach(&mut context.borrow_mut(), Attach::Any, Validate::None, |_| Ok(()))
                .map_err(|e| e.to_string().into())
        });
    }
    {
        let context = context.clone();
        engine.register_fn("task_module", move |i: i64| -> Result<_, Box<EvalAltResult>> {
            let ctx = context.borrow();
            let m = ctx.archive.as_ref().unwrap()
                .lookup_module(HubrisTask::Task(i as u32))
                .map_err(|e| format!("{e}"))?;
            Ok(m.clone())
        });
    }
    {
        let context = context.clone();
        engine.register_fn("poke32", move |a: Dynamic, v: Dynamic| -> Result<_, Box<EvalAltResult>> {
            let v = v.as_int()?;
            let v = u32::try_from(v)
                .map_err(|e| format!("{e}"))?;
            let a = u32::try_from(a.as_int()?)
                .map_err(|e| format!("{e}"))?;
            let mut ctx = context.borrow_mut();
            ctx.core.as_mut()
                .unwrap()
                .write_word_32(a, v)
                .map_err(|e| format!("{e}"))?;
            Ok(())
        });
    }
    {
        let context = context.clone();
        engine.register_fn("peek32", move |a: Dynamic| -> Result<_, Box<EvalAltResult>> {
            let a = u32::try_from(a.as_int()?)
                .map_err(|e| format!("{e}"))?;
            let mut ctx = context.borrow_mut();
            let v = ctx.core.as_mut()
                .unwrap()
                .read_word_32(a)
                .map_err(|e| format!("{e}"))?;
            Ok(v as i64)
        });
    }
    {
        let context = context.clone();
        engine.register_fn("halt", move || -> Result<_, Box<EvalAltResult>> {
            let mut ctx = context.borrow_mut();
            ctx.core.as_mut()
                .unwrap()
                .halt()
                .map_err(|e| format!("{e}"))?;
            Ok(())
        });
    }
    {
        let context = context.clone();
        engine.register_fn("resume", move || -> Result<_, Box<EvalAltResult>> {
            let mut ctx = context.borrow_mut();
            ctx.core.as_mut()
                .unwrap()
                .run()
                .map_err(|e| format!("{e}"))?;
            Ok(())
        });
    }
    {
        let context = context.clone();
        engine.register_fn("readvar", move |name: &str| -> Result<_, Box<EvalAltResult>> {
            let mut ctx = context.borrow_mut();
            let ctx = &mut *ctx;
            let hubris = ctx.archive.as_ref().unwrap();
            fn match_exact(n: &str, v: &str) -> bool {
                n == v
            }

            fn match_suffix(n: &str, v: &str) -> bool {
                let mut suffix = "::".to_string();
                suffix.push_str(v);

                n == v || n.ends_with(&suffix)
            }

            let m =
                if name.contains("::") { match_exact } else { match_suffix };

            let s = if let Some((_n, v)) = hubris.qualified_variables().find(|&(n, _)| m(n, name)) {
                let core = &mut **ctx.core.as_mut().unwrap();
                readvar_dump(hubris, core, v)
                    .map_err(|e| e.to_string())?
            } else {
                Dynamic::UNIT
            };
            Ok(s)
        });
    }
    {
        let context = context.clone();
        engine.register_fn("varinfo", move |name: &str| -> Result<_, Box<EvalAltResult>> {
            let mut ctx = context.borrow_mut();
            let ctx = &mut *ctx;
            let hubris = ctx.archive.as_ref().unwrap();

            let s = if let Some((_n, v)) = hubris.qualified_variables().find(|&(n, _)| n == name) {
                let t = hubris.lookup_type(v.goff)
                    .map_err(|e| e.to_string())?;
                let t = rhaiify_type(t);
                Dynamic::from_map([
                    ("address".into(), Dynamic::from(v.addr as i64)),
                    ("goff".into(), Dynamic::from(v.goff)),
                    ("typeinfo".into(), t),
                ].into_iter().collect())
            } else {
                Dynamic::UNIT
            };
            Ok(s)
        });
    }
    {
        let context = context.clone();
        engine.register_fn("typeinfo", move |goff: &mut HubrisGoff| -> Result<_, Box<EvalAltResult>> {
            let mut ctx = context.borrow_mut();
            let ctx = &mut *ctx;
            let hubris = ctx.archive.as_ref().unwrap();

            let t = hubris.lookup_type(*goff)
                .map_err(|e| e.to_string())?;

            Ok(rhaiify_type(t))
        });
    }
    engine.register_fn("delay_millis", move |n: i64| {
        std::thread::sleep(Duration::from_millis(n as u64));
    });
    engine.register_type::<HubrisModule>()
        .register_get("name", |m: &mut HubrisModule| m.name.clone());
    engine.register_type::<comfy_table::Table>()
        .register_fn("new_bare_table", || {
            let mut t = comfy_table::Table::new();
            t.load_preset(comfy_table::presets::NOTHING);
            t
        })
        .register_fn("new_bare_table", |h: rhai::Array| {
            let mut t = comfy_table::Table::new();
            t.load_preset(comfy_table::presets::NOTHING);
            t.set_header(h.into_iter().map(|d| d.to_string()).collect::<Vec<_>>());
            t
        })
        .register_fn("new_table", || {
            let mut t = comfy_table::Table::new();
            t.load_preset(comfy_table::presets::UTF8_FULL);
            t
        })
        .register_fn("new_table", |h: rhai::Array| {
            let mut t = comfy_table::Table::new();
            t.load_preset(comfy_table::presets::UTF8_FULL);
            t.set_header(h.into_iter().map(|d| d.to_string()).collect::<Vec<_>>());
            t
        })
        .register_fn("add_row", |t: &mut comfy_table::Table, row: rhai::Array| {
            let v = row.into_iter().map(|v| v.to_string()).collect::<Vec<String>>();
            t.add_row(v);
        })
        .register_fn("to_string", |t: &mut comfy_table::Table| {
            format!("{t}")
        })
        .register_fn("make_big_int", || u64::MAX)
    ;

    let r = engine.run_file(subargs.script.clone());
    if let Err(e) = r {
        bail!("{e}");
    }

    Ok(())
}

pub fn init() -> Command {
    Command {
        app: RhaiArgs::command(),
        name: "rhai",
        run: |_| Ok(()),
        kind: CommandKind::Unattached {
            archive: Archive::Optional,
        },
    }
}


fn readvar_dump(
    hubris: &HubrisArchive,
    core: &mut dyn Core,
    variable: &HubrisVariable,
) -> Result<rhai::Dynamic> {
    let mut buf: Vec<u8> = vec![];
    buf.resize_with(variable.size, Default::default);

    core.halt()?;
    core.read_8(variable.addr, buf.as_mut_slice())?;

    let v = humility::reflect::load_value(
        hubris,
        &buf,
        hubris.lookup_type(variable.goff).unwrap(),
        0,
    )?;

    let v = rhaiify(&v);

    let mut result = Map::new();
    result.insert("address".into(), Dynamic::from(variable.addr));
    result.insert("value".into(), v);
    Ok(result.into())
}

fn rhaiify(value: &reflect::Value) -> Dynamic {
    match value {
        reflect::Value::Base(b) => match b {
            reflect::Base::I8(i) => Dynamic::from(*i),
            reflect::Base::I16(i) => Dynamic::from(*i),
            reflect::Base::I32(i) => Dynamic::from(*i),
            reflect::Base::I64(i) => Dynamic::from(*i),
            reflect::Base::I128(i) => Dynamic::from(*i),
            reflect::Base::U0 => Dynamic::UNIT,
            reflect::Base::U8(i) => Dynamic::from(*i),
            reflect::Base::U16(i) => Dynamic::from(*i),
            reflect::Base::U32(i) => Dynamic::from(*i),
            reflect::Base::U64(i) => Dynamic::from(*i),
            reflect::Base::U128(i) => Dynamic::from(*i),
            reflect::Base::Bool(f) => Dynamic::from(*f),
            reflect::Base::F32(n) => Dynamic::from(*n),
            reflect::Base::F64(n) => Dynamic::from(*n),
        },
        reflect::Value::Enum(e) => Dynamic::from(e.clone()),
        reflect::Value::Struct(s) => {
            Dynamic::from_map(s.iter().map(|(n, v)| (n.into(), rhaiify(v))).collect())
        }
        reflect::Value::Tuple(t) => if t.len() == 1 {
            rhaiify(&t[0])
        } else {
            Dynamic::from_array(t.iter().map(rhaiify).collect())
        },
        reflect::Value::Array(a) => Dynamic::from_array(a.iter().map(rhaiify).collect()),
        reflect::Value::Ptr(p) => Dynamic::from(*p),
    }
}

fn rhaiify_type(t: HubrisType) -> Dynamic {
    match t {
        HubrisType::Base(b) => {
            Dynamic::from_map([
                ("kind".into(), "base".into()),
                ("encoding".into(), format!("{:?}", b.encoding).into()),
                ("size".into(), Dynamic::from(b.size as i64)),
            ].into_iter().collect())
        }
        HubrisType::Struct(s) => {
            let members = s.members.iter()
                .map(|field| {
                    Dynamic::from_map([
                        ("name".into(), field.name.as_str().into()),
                        ("offset".into(), Dynamic::from(field.offset)),
                        ("goff".into(), Dynamic::from(field.goff)),
                    ].into_iter().collect())
                })
                .collect();
            Dynamic::from_map([
                ("kind".into(), "struct".into()),
                ("name".into(), s.name.as_str().into()),
                ("goff".into(), Dynamic::from(s.goff)),
                ("members".into(), Dynamic::from_array(members)),
            ].into_iter().collect())
        }
        HubrisType::Enum(_) => todo!(),
        HubrisType::Array(_) => todo!(),
        HubrisType::Union(_) => todo!(),
        HubrisType::Ptr(_) => todo!(),
    }
}

struct BundleResolver {
    shared: Rc<RefCell<ExecutionContext>>,
    cache: RefCell<BTreeMap<String, rhai::Shared<rhai::Module>>>,
}

impl BundleResolver {
    fn new(shared: Rc<RefCell<ExecutionContext>>) -> Self {
        Self {
            shared,
            cache: RefCell::new(BTreeMap::new()),
        }
    }
}

impl ModuleResolver for BundleResolver {
    fn resolve(
        &self,
        engine: &Engine,
        _source: Option<&str>,
        path: &str,
        pos: rhai::Position,
    ) -> Result<rhai::Shared<rhai::Module>, Box<EvalAltResult>> {
        {
            let cache = self.cache.borrow();
            if let Some(m) = cache.get(path) {
                return Ok(m.clone());
            }
        }

        let file = {
            let ctx = self.shared.borrow();
            let archive = ctx.archive.as_ref().unwrap();
            archive.read_file(&format!("rhai/{path}.rhai"))
                .map_err(|e| e.to_string())?
        };
        let Some(data) = file else {
            return Err(EvalAltResult::ErrorModuleNotFound(path.to_string(), pos).into());
        };
        let data = String::from_utf8(data).map_err(|e| {
            EvalAltResult::ErrorInModule(path.to_string(), EvalAltResult::ErrorSystem("invalid UTF-8".to_string(), e.into()).into(), pos)
        })?;
        let mut ast = engine.compile(data).map_err(|e| {
            EvalAltResult::ErrorInModule(path.to_string(), e.into(), pos)
        })?;
        ast.set_source(path);
        let m = rhai::Module::eval_ast_as_new(Scope::new(), &ast, engine).map_err(|e| {
            EvalAltResult::ErrorInModule(path.to_string(), e, pos)
        })?;
        let m = rhai::Shared::from(m);

        {
            let mut cache = self.cache.borrow_mut();
            cache.insert(path.to_string(), m.clone());
        }
        Ok(m)
    }
}
