//! The `main` of a standalone binary (ADR 0042). `goat build --native` links
//! the program's IR with a C `main` that calls [`goat_standalone_main`] from
//! this crate's staticlib, handing it `goat_main` and the program's source.
//! Printing goes to stdout, a trap prints what `goat run` prints and exits
//! non-zero, and the turtle's drawing is saved as an SVG with `-o`.

use crate::abi::{Ctx, GoatHost, GoatInstance, Instance};
use crate::adapter::Adapter;
use crate::driver::DEFAULT_HEAP_BYTES;
use crate::turtle::TurtleHost;
use std::ffi::{CStr, c_char, c_int};
use std::path::PathBuf;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicPtr, Ordering};

type GoatMain = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance) -> i32;

/// Stack for the thread goat runs on: address space, not memory, so a deep
/// recursion reaches goat's stack-overflow trap instead of the main thread's
/// 8 MiB guard page.
const STACK_BYTES: usize = 256 << 20;

static SOURCE: OnceLock<String> = OnceLock::new();
static INSTANCE: AtomicPtr<GoatInstance> = AtomicPtr::new(std::ptr::null_mut());

/// # Safety
///
/// `argv` holds `argc` C strings, and `source` points at `source_len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goat_standalone_main(
    argc: c_int,
    argv: *const *const c_char,
    goat_main: GoatMain,
    source: *const u8,
    source_len: u64,
) -> c_int {
    // SAFETY: the caller's contract.
    let (args, source) = unsafe {
        (
            std::slice::from_raw_parts(argv, argc.max(0) as usize),
            std::slice::from_raw_parts(source, source_len as usize),
        )
    };
    let args: Vec<String> = args
        .iter()
        .map(|arg| {
            unsafe { CStr::from_ptr(*arg) }
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    let _ = SOURCE.set(String::from_utf8_lossy(source).into_owned());
    let out = match parse_args(&args) {
        Ok(out) => out,
        Err(usage) => {
            eprintln!("{usage}");
            return 2;
        }
    };
    let worker = std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(move || run(goat_main, out));
    match worker.map(|worker| worker.join()) {
        Ok(Ok(true)) => 0,
        _ => 1,
    }
}

/// The `-o FILE.svg` of the command line, if any.
fn parse_args(args: &[String]) -> Result<Option<PathBuf>, String> {
    let program = args.first().map_or("program", String::as_str);
    match args.get(1..).unwrap_or_default() {
        [] => Ok(None),
        [flag, path] if flag == "-o" => Ok(Some(PathBuf::from(path))),
        _ => Err(format!("usage: {program} [-o OUT.svg]")),
    }
}

/// Runs the program; true when the process should exit zero.
fn run(goat_main: GoatMain, out: Option<PathBuf>) -> bool {
    let mut instance = Instance::new(DEFAULT_HEAP_BYTES);
    instance.set_stack_limit(crate::stack::limit());
    let raw = instance.as_ptr();
    INSTANCE.store(raw, Ordering::Release);
    let mut adapter = Adapter::new(TurtleHost::default(), trap).echoing();
    let table = adapter.table();
    let ctx = adapter.ctx();
    // SAFETY: the table, the context and the instance outlive the call, and a
    // trap exits the process instead of returning into the program.
    let status = unsafe { goat_main(&table, ctx, raw) };
    if status != 0 {
        eprintln!("goat: the program's runtime is out of step with its code (status {status})");
        return false;
    }
    adapter.host.finish(out.as_deref())
}

unsafe extern "C" fn trap(_: Ctx, message: *const u8, len: u64) -> ! {
    let message = match len {
        0 => std::borrow::Cow::Borrowed(""),
        // SAFETY: the table's contract: `len` bytes at `message`.
        _ => String::from_utf8_lossy(unsafe { std::slice::from_raw_parts(message, len as usize) }),
    };
    // SAFETY: the instance `run` stored lives until the process exits.
    let site = unsafe { INSTANCE.load(Ordering::Acquire).as_ref() }.and_then(GoatInstance::site);
    let source = SOURCE.get().map_or("", String::as_str);
    eprintln!("goat: {}", goat::render_trap(source, &message, site));
    std::process::exit(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn the_command_line_is_nothing_or_an_svg_path() {
        assert_eq!(parse_args(&args(&["spiral"])), Ok(None));
        assert_eq!(
            parse_args(&args(&["spiral", "-o", "a.svg"])),
            Ok(Some(PathBuf::from("a.svg")))
        );
        assert!(parse_args(&args(&["spiral", "-x"])).is_err());
        assert!(parse_args(&args(&["spiral", "-o"])).is_err());
    }
}
