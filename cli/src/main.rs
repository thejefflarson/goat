//! `goat` — the command-line driver.
//!
//! - `goat check FILE`   parse and type-check, printing the program's type.
//! - `goat build FILE [-o OUT]`  compile to a WebAssembly module.
//! - `goat run FILE [-o OUT.svg]`  compile and run under wasmtime; `-o` saves
//!   the turtle's drawing as an SVG.

use goat_cli::turtle::TurtleHost;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::{env, fs};

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    match run(&args) {
        Ok(code) => code,
        Err(message) => {
            eprintln!("goat: {message}");
            ExitCode::FAILURE
        }
    }
}

fn run(args: &[String]) -> Result<ExitCode, String> {
    let command = args.get(1).map(String::as_str);
    match command {
        Some("check") => {
            let file = args.get(2).ok_or("usage: goat check FILE")?;
            let source = read(file)?;
            let checked = goat_checker::check(&source)
                .map_err(|errors| render_errors(file, &source, &errors))?;
            println!("{}", checked.typed.root_ty);
            Ok(ExitCode::SUCCESS)
        }
        Some("build") => {
            let file = args.get(2).ok_or("usage: goat build FILE [-o OUT]")?;
            let out = parse_out_flag(&args[3..]).unwrap_or_else(|| default_output(file));
            let wasm = build(file)?;
            fs::write(&out, wasm).map_err(|e| format!("cannot write {}: {e}", out.display()))?;
            eprintln!("goat: wrote {}", out.display());
            Ok(ExitCode::SUCCESS)
        }
        Some("run") => {
            let file = args.get(2).ok_or("usage: goat run FILE [-o OUT.svg]")?;
            run_program(&build(file)?, parse_out_flag(&args[3..]))
        }
        _ => {
            eprintln!("usage: goat <check|build|run> FILE [-o OUT]");
            Ok(ExitCode::FAILURE)
        }
    }
}

/// Run `wasm` under wasmtime with the turtle as its host and print what it
/// emitted. A trap becomes an error, so the process exits non-zero. With `out`,
/// the turtle's drawing is written there as an SVG.
fn run_program(wasm: &[u8], out: Option<PathBuf>) -> Result<ExitCode, String> {
    let (run, turtle) = goat_cli::run_with_host(wasm, TurtleHost::default())?;
    for line in run.printed {
        println!("{line}");
    }
    match out {
        Some(_) if turtle.commands.is_empty() => {
            eprintln!("goat: the program used no turtle commands, so no SVG was written");
            Ok(ExitCode::FAILURE)
        }
        Some(path) => {
            fs::write(&path, turtle.to_svg())
                .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
            eprintln!("goat: wrote {}", path.display());
            Ok(ExitCode::SUCCESS)
        }
        None => {
            if !turtle.commands.is_empty() {
                eprintln!("goat: the turtle drew something; pass -o FILE.svg to save it");
            }
            Ok(ExitCode::SUCCESS)
        }
    }
}

fn read(file: &str) -> Result<String, String> {
    fs::read_to_string(file).map_err(|e| format!("cannot read {file}: {e}"))
}

fn render_errors(file: &str, source: &str, errors: &[goat_checker::GoatError]) -> String {
    let rendered: Vec<String> = errors.iter().map(|e| e.render(source)).collect();
    format!(
        "{} error(s) in {file}:\n{}",
        errors.len(),
        rendered.join("\n")
    )
}

fn build(file: &str) -> Result<Vec<u8>, String> {
    let source = read(file)?;
    goat::compile(&source).map_err(|errors| render_errors(file, &source, &errors))
}

fn parse_out_flag(args: &[String]) -> Option<PathBuf> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "-o" {
            return it.next().map(PathBuf::from);
        }
    }
    None
}

fn default_output(file: &str) -> PathBuf {
    Path::new(file).with_extension("wasm")
}
