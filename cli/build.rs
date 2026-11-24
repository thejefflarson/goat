//! Builds `libgoat_native.a` for the `goat` binary to embed, so `goat build
//! --native` works from a plain `cargo build` or `cargo install` (ADR 0042).
//! Cargo writes a dependency's `staticlib` only when its own package is built,
//! so this runs that build into a private target directory.

use std::path::Path;
use std::process::Command;

const SOURCES: [&str; 6] = ["native", "llvm", "mir", "goat", "checker", "parser"];

fn main() {
    for dir in SOURCES {
        println!("cargo:rerun-if-changed=../{dir}");
    }
    println!("cargo:rerun-if-changed=../Cargo.toml");

    let out_dir = std::env::var_os("OUT_DIR").expect("OUT_DIR");
    let out_dir = Path::new(&out_dir);
    let embedded = out_dir.join("libgoat_native.a");
    if clippy_run() {
        std::fs::write(&embedded, []).expect("write the empty library");
    } else if let Err(reason) = build(out_dir, &embedded) {
        println!("cargo:warning=goat build --native will not work from this binary: {reason}");
        std::fs::write(&embedded, []).expect("write the empty library");
    }
}

/// Clippy type-checks without linking, so the archive would go unused; skipping
/// the nested build also keeps it from waiting on cargo locks the outer run holds.
fn clippy_run() -> bool {
    std::env::var_os("RUSTC_WORKSPACE_WRAPPER")
        .is_some_and(|wrapper| wrapper.to_string_lossy().contains("clippy"))
}

fn build(out_dir: &Path, embedded: &Path) -> Result<(), String> {
    let release = std::env::var("PROFILE").is_ok_and(|profile| profile == "release");
    let target_dir = out_dir.join("native-target");
    let mut cargo = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()));
    cargo
        .args([
            "build",
            "--package",
            "goat_native",
            "--manifest-path",
            "../Cargo.toml",
        ])
        .arg("--target-dir")
        .arg(&target_dir)
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("CARGO_BUILD_TARGET_DIR")
        .env("CARGO_BUILD_BUILD_DIR", &target_dir);
    if release {
        cargo.arg("--release");
    }
    let status = cargo
        .status()
        .map_err(|e| format!("cannot run cargo: {e}"))?;
    if !status.success() {
        return Err(format!("cargo build -p goat_native failed ({status})"));
    }
    let built = target_dir
        .join(if release { "release" } else { "debug" })
        .join("libgoat_native.a");
    std::fs::copy(&built, embedded)
        .map(|_| ())
        .map_err(|e| format!("cannot copy {}: {e}", built.display()))
}
