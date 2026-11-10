//! `goat-canvas SCRIPT.goat [EVENTS.txt] [-o OUT.svg]` runs a canvas script
//! headlessly through a file of events (see `Event::parse_script`) and writes
//! the final picture as an SVG, to stdout unless `-o` names a file.

use goat_canvas::{Event, render};
use std::process::ExitCode;
use std::{env, fs};

fn main() -> ExitCode {
    match run(env::args().skip(1).collect()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("goat-canvas: {message}");
            ExitCode::FAILURE
        }
    }
}

fn run(mut args: Vec<String>) -> Result<(), String> {
    let usage = "usage: goat-canvas SCRIPT.goat [EVENTS.txt] [-o OUT.svg]";
    let out = match args.iter().position(|a| a == "-o") {
        Some(at) if at + 1 < args.len() => {
            let out = args.remove(at + 1);
            args.remove(at);
            Some(out)
        }
        Some(_) => return Err(usage.to_string()),
        None => None,
    };
    let [script, rest @ ..] = &args[..] else {
        return Err(usage.to_string());
    };
    let read =
        |file: &str| fs::read_to_string(file).map_err(|e| format!("cannot read {file}: {e}"));
    let events = match rest {
        [] => Vec::new(),
        [events] => Event::parse_script(&read(events)?)?,
        _ => return Err(usage.to_string()),
    };
    let svg = render(&read(script)?, &events).map_err(|e| format!("{script}: {e}"))?;
    match out {
        Some(path) => fs::write(&path, svg).map_err(|e| format!("cannot write {path}: {e}")),
        None => {
            print!("{svg}");
            Ok(())
        }
    }
}
