//! `goat` — the command-line driver.
//!
//! - `goat check FILE`   parse and type-check, printing the program's type.
//! - `goat build FILE [-o OUT]`  compile to a WebAssembly module.
//! - `goat build --native [--turtle|--canvas] FILE [-o OUT]`  compile to a native
//!   executable: LLVM IR linked by clang with `libgoat_native.a`, which this
//!   executable carries; `$GOAT_NATIVE_LIB` or a copy beside it takes
//!   precedence. `$GOAT_CLANG` names the clang to use. The
//!   executable takes `-o OUT.svg`. With `-o NAME.app` an interactive program
//!   becomes a signed macOS app bundle (ADR 0043). An interactive program (`init`, `update`,
//!   `draw`) opens a window on macOS, where `swiftc` (`$GOAT_SWIFTC`) builds
//!   its AppKit host. The vocabulary is the canvas's (`Frame`, `Dot`, ...) or
//!   the turtle's, read from the names the program uses; a program that names
//!   neither is the turtle's, and one that names both is an error. `--turtle`
//!   and `--canvas` choose instead, for `run` as well.
//! - `goat run FILE [-o OUT.svg] [--timeout MS]`  compile and run under
//!   wasmtime; `-o` saves the turtle's drawing as an SVG. A program runs as
//!   long as it likes unless `--timeout` bounds it; `Ctrl-C` stops it either way.
//!   A canvas program is sent 60 `Frame` events and drawn once; it prints the
//!   frame count, and `-o` saves that last picture as an SVG.
//!
//! - `goat fmt [--check] FILE...`  lay each file out in the one house style
//!   (ADR 0041), rewriting it in place; with `--check`, change nothing and
//!   fail if a file is not already formatted.
//!
//! `build` and `run` take `--target desktop|embedded` (default `desktop`):
//! `embedded` makes an `Int` an `i32` and a `Float` an `f32`; with it,
//! `--board c6|c3|rp2040` sizes the heap arena and call depth for that board
//! (ADR 0029).

use goat::{EmbeddedLimits, Profile};
use goat_cli::native_build::Vocabulary;
use goat_cli::turtle::TurtleHost;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;
use std::{env, fs};

fn main() -> ExitCode {
    goat_cli::native_build::embed_static_lib(include_bytes!(concat!(
        env!("OUT_DIR"),
        "/libgoat_native.a"
    )));
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
            let (ty, warnings) = goat::check(&source, &goat::HostInterface::turtle())
                .map_err(|errors| render_errors(file, &source, &errors))?;
            print_warnings(file, &source, &warnings);
            println!("{ty}");
            Ok(ExitCode::SUCCESS)
        }
        Some("build") if args.get(2).map(String::as_str) == Some("--native") => {
            let rest: Vec<String> = args[3..]
                .iter()
                .filter(|a| *a != "--canvas" && *a != "--turtle")
                .cloned()
                .collect();
            let file = rest
                .first()
                .ok_or("usage: goat build --native [--turtle|--canvas] FILE [-o OUT]")?;
            let source = read(file)?;
            let vocabulary = choose_vocabulary(file, &source, &args[3..])?;
            build_native(file, &source, parse_out_flag(&rest[1..]), vocabulary)
        }
        Some("build") => {
            let file = args.get(2).ok_or("usage: goat build FILE [-o OUT]")?;
            let out = parse_out_flag(&args[3..]).unwrap_or_else(|| default_output(file));
            let wasm = build(
                file,
                parse_target_flag(&args[3..])?,
                parse_board_flag(&args[3..])?,
            )?;
            fs::write(&out, wasm).map_err(|e| format!("cannot write {}: {e}", out.display()))?;
            eprintln!("goat: wrote {}", out.display());
            Ok(ExitCode::SUCCESS)
        }
        Some("run") => {
            let file = args
                .get(2)
                .ok_or("usage: goat run FILE [-o OUT.svg] [--timeout MS]")?;
            let source = read(file)?;
            if choose_vocabulary(file, &source, &args[3..])? == Vocabulary::Canvas {
                return run_canvas(file, &source, parse_out_flag(&args[3..]));
            }
            let wasm = build(
                file,
                parse_target_flag(&args[3..])?,
                parse_board_flag(&args[3..])?,
            )?;
            let timeout = parse_timeout_flag(&args[3..])?;
            run_program(&wasm, &source, parse_out_flag(&args[3..]), timeout)
        }
        Some("fmt") => format_files(&args[2..]),
        _ => {
            eprintln!(
                "usage: goat <check|build|run|fmt> [--native] FILE [-o OUT] [--target desktop|embedded] [--board c6|c3|rp2040] [--timeout MS]"
            );
            Ok(ExitCode::FAILURE)
        }
    }
}

/// `goat build --native`: link the program into an executable that prints to
/// stdout, reports a trap as `goat run` does, and takes `-o FILE.svg` for the
/// turtle's drawing. The executable is `OUT`, or the file's name without its
/// extension.
fn build_native(
    file: &str,
    source: &str,
    out: Option<PathBuf>,
    vocabulary: Vocabulary,
) -> Result<ExitCode, String> {
    let ll = goat_cli::native_build::emit_ir(source, vocabulary)
        .map_err(|errors| render_errors(file, source, &errors))?;
    let out = out.unwrap_or_else(|| Path::new(file).with_extension(""));
    if goat_cli::native_build::is_app_path(&out) {
        goat_cli::native_build::bundle(&ll, source, &out)?;
    } else {
        goat_cli::native_build::link(&ll, source, &out)?;
    }
    eprintln!("goat: wrote {}", out.display());
    Ok(ExitCode::SUCCESS)
}

/// The vocabulary `source` is written in: `--turtle` or `--canvas` in `flags`
/// if given, else what its names say.
fn choose_vocabulary(file: &str, source: &str, flags: &[String]) -> Result<Vocabulary, String> {
    let has = |flag: &str| flags.iter().any(|a| a == flag);
    match (has("--turtle"), has("--canvas")) {
        (true, true) => Err("--turtle and --canvas conflict: pick one".to_string()),
        (true, false) => Ok(Vocabulary::Turtle),
        (false, true) => Ok(Vocabulary::Canvas),
        (false, false) => {
            goat_cli::detect::detect(source).map_err(|error| render_errors(file, source, &[error]))
        }
    }
}

/// Run a canvas program headlessly: `FRAMES` `Frame` events, then one `draw`.
/// It prints the frame count; with `out`, the last picture is written there as
/// an SVG.
fn run_canvas(file: &str, source: &str, out: Option<PathBuf>) -> Result<ExitCode, String> {
    const FRAMES: u32 = 60;
    const FRAME_MS: f64 = 16.0;
    let wasm = goat::compile(source, &Vocabulary::Canvas.interface())
        .map_err(|errors| render_errors(file, source, &errors))?;
    let mut canvas = goat_canvas::Canvas::new(&wasm)?;
    for _ in 0..FRAMES {
        canvas.send(&goat_canvas::Event::Frame(FRAME_MS))?;
    }
    let picture = canvas.draw()?;
    let leaked = canvas.finish()?;
    if leaked != 0 {
        return Err(format!("the program leaked {leaked} heap blocks"));
    }
    println!("ran {FRAMES} frames");
    if let Some(path) = out {
        fs::write(&path, goat_canvas::to_svg(&picture))
            .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    }
    Ok(ExitCode::SUCCESS)
}

/// `goat fmt`: format each file, or with `--check` only report the ones that
/// are not formatted. A file that does not lex has no edits and is left alone.
fn format_files(args: &[String]) -> Result<ExitCode, String> {
    let check = args.iter().any(|a| a == "--check");
    let files: Vec<&String> = args.iter().filter(|a| *a != "--check").collect();
    if files.is_empty() {
        return Err("usage: goat fmt [--check] FILE...".to_string());
    }
    let mut formatter = goat::format::Formatter::new()?;
    let mut unformatted = 0;
    for file in files {
        let source = read(file)?;
        let formatted = formatter.format(&source)?;
        if formatted == source {
            continue;
        }
        unformatted += 1;
        if check {
            eprintln!("goat: {file} is not formatted");
        } else {
            fs::write(file, formatted).map_err(|e| format!("cannot write {file}: {e}"))?;
            eprintln!("goat: formatted {file}");
        }
    }
    Ok(if check && unformatted > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
}

/// Run `wasm` under wasmtime with the turtle as its host and print what it
/// emitted. A trap becomes an error, so the process exits non-zero. With `out`,
/// the turtle's drawing is written there as an SVG. With `timeout`, a program
/// still running when it passes is stopped and reported as a trap.
fn run_program(
    wasm: &[u8],
    source: &str,
    out: Option<PathBuf>,
    timeout: Option<Duration>,
) -> Result<ExitCode, String> {
    let finished = goat::native::run_to_end_within(wasm, TurtleHost::default(), timeout)?;
    for line in &finished.printed {
        println!("{line}");
    }
    let turtle = finished.host;
    if let Err(stopped) = finished.result {
        return Err(goat::render_trap(source, &stopped.message, stopped.site));
    }
    Ok(if turtle.finish(out.as_deref()) {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    })
}

fn read(file: &str) -> Result<String, String> {
    fs::read_to_string(file).map_err(|e| format!("cannot read {file}: {e}"))
}

fn render_errors(file: &str, source: &str, errors: &[goat::GoatError]) -> String {
    let rendered: Vec<String> = errors.iter().map(|e| e.render(source)).collect();
    format!(
        "{} error(s) in {file}:\n{}",
        errors.len(),
        rendered.join("\n")
    )
}

fn print_warnings(file: &str, source: &str, warnings: &[goat::GoatError]) {
    for warning in warnings {
        eprintln!("warning in {file}: {}", warning.render(source));
    }
}

fn build(file: &str, profile: Profile, board: Option<EmbeddedLimits>) -> Result<Vec<u8>, String> {
    if board.is_some() && profile != Profile::Embedded {
        return Err("--board needs --target embedded".to_string());
    }
    let source = read(file)?;
    let host = goat::HostInterface::turtle();
    let compiled = match board {
        Some(limits) => goat::compile_embedded(&source, &host, limits),
        None => goat::compile_for(profile, &source, &host),
    };
    let (wasm, warnings) = compiled.map_err(|errors| render_errors(file, &source, &errors))?;
    print_warnings(file, &source, &warnings);
    Ok(wasm)
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

fn parse_target_flag(args: &[String]) -> Result<Profile, String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--target" {
            return match it.next().map(String::as_str) {
                Some("desktop") => Ok(Profile::Desktop),
                Some("embedded") => Ok(Profile::Embedded),
                _ => Err("--target takes desktop or embedded".to_string()),
            };
        }
    }
    Ok(Profile::Desktop)
}

fn parse_board_flag(args: &[String]) -> Result<Option<EmbeddedLimits>, String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--board" {
            return match it.next().map(String::as_str) {
                Some("c6") => Ok(Some(EmbeddedLimits::C6)),
                Some("c3") => Ok(Some(EmbeddedLimits::C3)),
                Some("rp2040") => Ok(Some(EmbeddedLimits::RP2040)),
                _ => Err("--board takes c6, c3 or rp2040".to_string()),
            };
        }
    }
    Ok(None)
}

fn parse_timeout_flag(args: &[String]) -> Result<Option<Duration>, String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--timeout" {
            return match it.next().map(|ms| ms.parse::<u64>()) {
                Some(Ok(ms)) if ms > 0 => Ok(Some(Duration::from_millis(ms))),
                _ => Err("--timeout takes a positive number of milliseconds".to_string()),
            };
        }
    }
    Ok(None)
}

fn default_output(file: &str) -> PathBuf {
    Path::new(file).with_extension("wasm")
}
