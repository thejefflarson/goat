//! `goat` — the command-line driver.
//!
//! - `goat check FILE`   parse and type-check, printing the program's type.
//! - `goat build FILE [-o OUT]`  compile to a native executable.
//! - `goat run FILE`     compile to a temporary executable and run it.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::{env, fs};

/// The C runtime: it provides `main`, which calls the compiled program's
/// `goat_entry`, plus the print builtins the generated code calls. Cranelift's
/// object backend already applies each platform's C symbol convention (the
/// leading underscore on macOS), so plain C names match it on macOS and Linux
/// alike.
const RUNTIME_C: &str = r#"
#include <stdio.h>
extern void goat_entry(void);
void goat_print_number(double x) { printf("%g\n", x); }
void goat_print_bool(long b) { printf("%s\n", b ? "true" : "false"); }
int main(void) { goat_entry(); return 0; }
"#;

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
            let (source, checked) = check(file)?;
            let _ = source;
            println!("{}", checked.typed.root_ty);
            Ok(ExitCode::SUCCESS)
        }
        Some("build") => {
            let file = args.get(2).ok_or("usage: goat build FILE [-o OUT]")?;
            let out = parse_out_flag(&args[3..]).unwrap_or_else(|| default_output(file));
            build(file, &out)?;
            eprintln!("goat: wrote {}", out.display());
            Ok(ExitCode::SUCCESS)
        }
        Some("run") => {
            let file = args.get(2).ok_or("usage: goat run FILE")?;
            let dir = temp_dir()?;
            let exe = dir.join("program");
            build(file, &exe)?;
            let status = Command::new(&exe)
                .status()
                .map_err(|e| format!("could not run compiled program: {e}"))?;
            let _ = fs::remove_dir_all(&dir);
            Ok(match status.code() {
                Some(0) | None => ExitCode::SUCCESS,
                Some(code) => ExitCode::from(code as u8),
            })
        }
        _ => {
            eprintln!("usage: goat <check|build|run> FILE [-o OUT]");
            Ok(ExitCode::FAILURE)
        }
    }
}

/// Read and type-check a file, rendering any diagnostics against the source.
fn check(file: &str) -> Result<(String, goat_checker::Checked), String> {
    let source = fs::read_to_string(file).map_err(|e| format!("cannot read {file}: {e}"))?;
    match goat_checker::check(&source) {
        Ok(checked) => Ok((source, checked)),
        Err(errors) => {
            let rendered: Vec<String> = errors.iter().map(|e| e.render(&source)).collect();
            Err(format!(
                "{} error(s) in {file}:\n{}",
                errors.len(),
                rendered.join("\n")
            ))
        }
    }
}

/// Compile `file` to a native executable at `out`.
fn build(file: &str, out: &Path) -> Result<(), String> {
    let (_source, checked) = check(file)?;
    let object = goat_compiler::compile(&checked).map_err(|e| format!("codegen: {e}"))?;

    let dir = temp_dir()?;
    let obj_path = dir.join("program.o");
    let rt_path = dir.join("runtime.c");
    fs::write(&obj_path, &object).map_err(|e| format!("writing object: {e}"))?;
    fs::write(&rt_path, RUNTIME_C).map_err(|e| format!("writing runtime: {e}"))?;

    let status = Command::new(cc())
        .arg(&obj_path)
        .arg(&rt_path)
        .arg("-o")
        .arg(out)
        .status()
        .map_err(|e| format!("could not invoke the C linker ({}): {e}", cc()))?;
    let _ = fs::remove_dir_all(&dir);
    if !status.success() {
        return Err("linking failed".to_string());
    }
    Ok(())
}

fn cc() -> String {
    env::var("CC").unwrap_or_else(|_| "cc".to_string())
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
    PathBuf::from(Path::new(file).file_stem().unwrap_or_default())
}

/// A fresh temporary directory unique to this process and call.
fn temp_dir() -> Result<PathBuf, String> {
    use std::sync::atomic::{AtomicU32, Ordering};
    static COUNTER: AtomicU32 = AtomicU32::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = env::temp_dir().join(format!("goat-{}-{}", std::process::id(), n));
    fs::create_dir_all(&dir).map_err(|e| format!("creating temp dir: {e}"))?;
    Ok(dir)
}
