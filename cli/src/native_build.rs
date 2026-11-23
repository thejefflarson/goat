//! `goat build --native`: compile a program to LLVM IR, then have clang link it
//! with the standalone runtime in `libgoat_native.a` (ADR 0042).

use goat::{HostInterface, Profile};
use std::path::{Path, PathBuf};
use std::process::Command;

const STATIC_LIB: &str = "libgoat_native.a";
const CLANG_CANDIDATES: [&str; 3] = ["clang-23", "clang-17", "clang"];

#[cfg(target_os = "macos")]
const SYSTEM_LIBS: &[&str] = &["-liconv", "-Wl,-dead_strip"];
#[cfg(not(target_os = "macos"))]
const SYSTEM_LIBS: &[&str] = &["-lpthread", "-ldl", "-lm", "-Wl,--gc-sections"];

#[cfg(target_os = "macos")]
const MISSING_CLANG: &str = "run `xcode-select --install` to get Apple's clang";
#[cfg(not(target_os = "macos"))]
const MISSING_CLANG: &str =
    "install clang with your package manager (for example `apt install clang`)";

/// The program's LLVM IR, or why the backend has none.
pub fn emit_ir(source: &str) -> Result<String, Vec<goat::GoatError>> {
    goat::compile_ll(Profile::Desktop, source, &HostInterface::turtle())
}

/// Whether `ll` is an interactive program, which has no `goat_main` for a
/// standalone binary to run.
pub fn is_interactive(ll: &str) -> bool {
    ll.contains("@goat_attach(")
}

/// The clang to run: `$GOAT_CLANG`, else the first of `clang-23`, `clang-17`
/// and `clang` that runs.
pub fn find_clang() -> Result<String, String> {
    if let Ok(named) = std::env::var("GOAT_CLANG") {
        return if runs(&named) {
            Ok(named)
        } else {
            Err(format!("GOAT_CLANG is {named}, which does not run"))
        };
    }
    CLANG_CANDIDATES
        .iter()
        .find(|name| runs(name))
        .map(|name| name.to_string())
        .ok_or_else(|| {
            format!("goat build --native needs clang, which is not installed: {MISSING_CLANG}")
        })
}

fn runs(clang: &str) -> bool {
    Command::new(clang)
        .arg("--version")
        .output()
        .is_ok_and(|out| out.status.success())
}

/// The runtime library: `$GOAT_NATIVE_LIB`, else the one beside this executable.
pub fn find_static_lib() -> Result<PathBuf, String> {
    let path = match std::env::var_os("GOAT_NATIVE_LIB") {
        Some(path) => PathBuf::from(path),
        None => std::env::current_exe()
            .map_err(|e| format!("cannot find the goat executable: {e}"))?
            .with_file_name(STATIC_LIB),
    };
    if path.is_file() {
        Ok(path)
    } else {
        Err(format!(
            "{} not found; build it with `cargo build -p goat_native`, or point GOAT_NATIVE_LIB at it",
            path.display()
        ))
    }
}

/// The C file that holds the program's source for trap reports and starts the
/// runtime.
fn entry_c(source: &str) -> String {
    let bytes: Vec<String> = source
        .bytes()
        .chain([0])
        .map(|byte| byte.to_string())
        .collect();
    format!(
        "#include <stdint.h>\n\
         int32_t goat_main(const void *, void *, void *);\n\
         int goat_standalone_main(int, char **, int32_t (*)(const void *, void *, void *), const uint8_t *, uint64_t);\n\
         static const uint8_t source[] = {{{}}};\n\
         int main(int argc, char **argv) {{\n    \
         return goat_standalone_main(argc, argv, goat_main, source, sizeof source - 1);\n}}\n",
        bytes.join(",")
    )
}

/// Links `ll`, the IR of `source`, into the executable `out`.
pub fn link(ll: &str, source: &str, out: &Path) -> Result<(), String> {
    let (clang, lib) = (find_clang()?, find_static_lib()?);
    let dir = tempfile::tempdir().map_err(|e| format!("cannot make a temporary directory: {e}"))?;
    let (ll_path, c_path) = (dir.path().join("program.ll"), dir.path().join("entry.c"));
    for (path, text) in [(&ll_path, ll), (&c_path, &entry_c(source))] {
        std::fs::write(path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    }
    let output = Command::new(&clang)
        .args(["-O2", "-x", "ir"])
        .arg(&ll_path)
        .args(["-x", "c"])
        .arg(&c_path)
        .args(["-x", "none"])
        .arg(&lib)
        .args(SYSTEM_LIBS)
        .arg("-o")
        .arg(out)
        .output()
        .map_err(|e| format!("cannot run {clang}: {e}"))?;
    if output.status.success() {
        Ok(())
    } else {
        Err(format!(
            "{clang} failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        ))
    }
}
