// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! ## `humility lpc55gpio`
//!
//! The LPC55-equivalent of `humility gpio`, allowing for GPIO pins to
//! be set, reset, queried or configured on LPC55 targets.  Commands:
//!
//! - `--set` (`-s`): Sets a pin (sets it high)
//! - `--reset` (`-r`): Resets a pin (sets it low)
//! - `--toggle` (`-t`): Toggles a pin (sets it high if low, low if high)
//! - `--input` (`-i`): Queries the state of a pin (or all pins if no pin
//!   is specified)
//! - `--configure` (`-c`): Configures a pin
//! - `--direction` (`-d`): Configure the direction of a pin
//!
//! ### Set, reset, toggle
//!
//! To change the state of a pin (or pins), specify the pin (or pins) and
//! the desired command.  For example, to toggle the state on pin PIO0_17:
//!
//! ```console
//! $ humility lpc55gpio --toggle --pins PIO0_17
//! humility: attached via CMSIS-DAP
//! [Ok([])]
//! ```
//!
//! To set pins PIO0_15, PIO0_16 and PIO0_17:
//!
//! ```console
//! $ humility lpc55gpio --set --pins PIO0_15,PIO0_16,PIO0_17
//! humility: attached via CMSIS-DAP
//! [Ok([]), Ok([]), Ok([])]
//! ```
//!
//! To reset pin PIO0_17:
//!
//! ```console
//! $ humility lpc55gpio --reset --pins PIO0_17
//! humility: attached via CMSIS-DAP
//! [Ok([])]
//! ```
//!
//! ### Input
//!
//! To get input values for a particular pin:
//!
//! ```console
//! $ humility lpc55gpio --input --pins PIO0_10,PIO0_11,PIO1_0
//! humility: attached via CMSIS-DAP
//! PIO0_10 = 0
//! PIO0_11 = 1
//! PIO1_0 = 0
//! ```
//!
//! To get input values for all pins, leave the pin unspecified:
//!
//! ```console
//! $ humility lpc55gpio --input
//! humility: attached via ST-Link V3
//! humility: attached to 1fc9:0143:12UNOSLDXOK51 via CMSIS-DAP
//! PIO0_0 = 0
//! PIO0_1 = 0
//! PIO0_2 = 0
//! PIO0_3 = 0
//! PIO0_4 = 0
//! PIO0_5 = 1
//! PIO0_6 = 0
//! PIO0_7 = 0
//! PIO0_8 = 0
//! PIO0_9 = 1
//! PIO0_10 = 0
//! PIO0_11 = 1
//! PIO0_13 = 0
//! ...
//! ```
//!
//! ### Configure, direction
//!
//! To configure a pin, the configuration should be specified as a
//! colon-delimited 6-tuple consisting of:
//!
//! - Alternate function: one of `Alt0` through `Alt9`
//! - Mode:  `NoPull`, `PullDown`, `PullUp`, or `Repeater`
//! - Slew: `Standard` or `Fast`
//! - Invert: `Disable`, or `Enabled`
//! - Digital mode: `Analog` or `Digital`
//! - Open drain: `Normal` or `OpenDrain`
//!
//! Note that the direction of the pin should also likely be configured;
//! this is done via the `--direction` option, specifying either `Input` or
//! `Output`.  For example, to configure pin PIO0_17 to be an output:
//!
//! ```console
//! $ humility lpc55gpio -c Alt0:NoPull:Standard:Disable:Digital:Normal -p PIO0_17
//! humility: attached via CMSIS-DAP
//! [Ok([])]
//! $ humility lpc55gpio -p PIO0_17 --direction Output
//! humility: attached via CMSIS-DAP
//! [Ok([])]
//! ```
//!

use humility_cli::{ExecutionContext, Subcommand};
use humility_cmd::{Archive, Attach, Command, CommandKind, Validate};
use humility_hiffy::*;
use std::str;

use anyhow::{bail, Result};
use clap::{CommandFactory, Parser};
use hif::*;

use std::convert::TryInto;

#[derive(Parser, Debug)]
#[clap(name = "lpc55gpio", about = "GPIO pin manipulation (lpc55 variant)")]
struct GpioArgs {
    /// sets timeout
    #[clap(
        long, short = 'T', default_value_t = 5000, value_name = "timeout_ms",
        parse(try_from_str = parse_int::parse)
    )]
    timeout: u32,

    /// toggle specified pins
    #[clap(
        long, short,
        conflicts_with_all = &["toggle", "set", "reset", "configure"]
    )]
    input: bool,

    /// toggle specified pins
    #[clap(
        long, short, requires = "pins",
        conflicts_with_all = &["set", "reset", "configure"]
    )]
    toggle: bool,

    /// sets specified pins
    #[clap(
        long, short, requires = "pins",
        conflicts_with_all = &["reset", "configure"]
    )]
    set: bool,

    /// resets specified pins
    #[clap(
        long, short, requires = "pins",
         conflicts_with_all = &["configure"])]
    reset: bool,

    /// configures specified pins
    #[clap(long, short, requires = "pins")]
    configure: Option<String>,

    /// configures specified pins
    #[clap(long, short, requires = "pins")]
    direction: Option<String>,

    /// specifies GPIO pins on which to operate
    #[clap(long, short, value_name = "pins", use_value_delimiter = true)]
    pins: Option<Vec<String>>,
}

fn gpio(context: &mut ExecutionContext) -> Result<()> {
    let core = &mut **context.core.as_mut().unwrap();
    let Subcommand::Other(subargs) = context.cli.cmd.as_ref().unwrap();
    let hubris = context.archive.as_ref().unwrap();

    let subargs = GpioArgs::try_parse_from(subargs)?;
    let mut context = HiffyContext::new(hubris, core, subargs.timeout)?;

    let gpio_toggle = context.get_function("GpioToggle", 1)?;
    let gpio_set = context.get_function("GpioSet", 1)?;
    let gpio_reset = context.get_function("GpioReset", 1)?;
    let gpio_input = context.get_function("GpioInput", 1)?;
    let gpio_configure = context.get_function("GpioConfigure", 7)?;
    let gpio_direction = context.get_function("GpioDirection", 2)?;
    let mut configure_args = vec![];
    let mut direction_args = vec![];

    let target = if subargs.toggle {
        gpio_toggle.id
    } else if subargs.set {
        gpio_set.id
    } else if subargs.reset {
        gpio_reset.id
    } else if let Some(ref configure) = subargs.configure {
        let params: Vec<&str> = configure.split(':').collect();
        let args = ["AltFn", "Mode", "Slew", "Invert", "Digimode", "Opendrain"];

        if params.len() != args.len() {
            bail!("expected {}", args.join(":"));
        }

        for i in 0..args.len() {
            configure_args.push(gpio_configure.lookup_argument(
                hubris,
                args[i],
                1 + i,
                params[i],
            )?);
        }

        gpio_configure.id
    } else if let Some(ref dir) = subargs.direction {
        let params: Vec<&str> = dir.split(':').collect();
        let args = ["Direction"];

        if params.len() != args.len() {
            bail!("expected {}", args.join(":"));
        }

        for i in 0..args.len() {
            direction_args.push(gpio_direction.lookup_argument(
                hubris,
                args[i],
                1 + i,
                params[i],
            )?);
        }

        gpio_direction.id
    } else if subargs.input {
        gpio_input.id
    } else {
        bail!("expected one of input, toggle, set, or reset to be specified");
    };

    let mut args: Vec<(u16, String)> = vec![];

    if let Some(ref pins) = subargs.pins {
        for pin in pins {
            let p = gpio_toggle.lookup_argument(hubris, "pin", 0, pin)?;

            args.push((p, pin.to_string()));
        }
    }

    let mut ops = vec![];

    if subargs.input {
        if args.is_empty() {
            let pins = gpio_input.argument_variants(hubris, 0)?;

            for pin in &pins {
                args.push((pin.1, pin.0.clone()));
            }
        }

        for arg in &args {
            ops.push(Op::Push16(arg.0));
            ops.push(Op::Call(target));
            ops.push(Op::DropN(1));
        }
    } else if subargs.configure.is_some() {
        for arg in &args {
            ops.push(Op::Push16(arg.0));

            for configure_arg in &configure_args {
                ops.push(Op::Push16(*configure_arg));
            }

            ops.push(Op::Call(target));
            ops.push(Op::DropN(7));
        }
    } else if subargs.direction.is_some() {
        for arg in &args {
            ops.push(Op::Push16(arg.0));

            for direction_arg in &direction_args {
                ops.push(Op::Push16(*direction_arg));
            }

            ops.push(Op::Call(target));
            ops.push(Op::DropN(2));
        }
    } else {
        for arg in &args {
            ops.push(Op::Push16(arg.0));
            ops.push(Op::Call(target));
            ops.push(Op::DropN(1));
        }
    }

    ops.push(Op::Done);

    let results = context.run(core, ops.as_slice(), None)?;

    if subargs.input {
        for (ndx, arg) in args.iter().enumerate() {
            println!(
                "{} = {}",
                arg.1,
                match results[ndx] {
                    Err(code) => {
                        gpio_input.strerror(code)
                    }
                    Ok(ref val) => {
                        let arr: &[u8; 2] = val[0..2].try_into()?;
                        let v = u16::from_le_bytes(*arr);
                        format!("{}", v)
                    }
                }
            );
        }
    } else {
        println!("{:?}", results);
    }

    Ok(())
}

pub fn init() -> Command {
    Command {
        app: GpioArgs::command(),
        name: "lpc55gpio",
        run: gpio,
        kind: CommandKind::Attached {
            archive: Archive::Required,
            attach: Attach::LiveOnly,
            validate: Validate::Booted,
        },
    }
}
