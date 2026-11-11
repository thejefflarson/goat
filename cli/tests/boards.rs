//! Per-board embedded builds (ADR 0029): every example compiled for each board
//! validates host-side, and its memory is a fixed arena of whole 64 KiB pages
//! that fits the board's budget. No board is involved.

use goat::{EmbeddedLimits, HostInterface, compile_embedded, compile_for};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use wasmtime::{Engine, ExternType, Module};

const PAGE: u64 = 65536;

const BOARDS: [(&str, EmbeddedLimits); 3] = [
    ("c6", EmbeddedLimits::C6),
    ("c3", EmbeddedLimits::C3),
    ("rp2040", EmbeddedLimits::RP2040),
];

fn examples() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples");
    let mut files: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "goat"))
        .collect();
    files.sort();
    files
}

/// The module's (minimum, maximum) memory pages, after validating it.
fn memory_pages(wasm: &[u8]) -> (u64, Option<u64>) {
    let module = Module::new(&Engine::default(), wasm).expect("module validates");
    let export = module.exports().find(|e| e.name() == "memory").unwrap();
    let ExternType::Memory(ty) = export.ty() else {
        panic!("memory is a memory");
    };
    (ty.minimum(), ty.maximum())
}

fn budget_pages(limits: EmbeddedLimits) -> u64 {
    u64::from(limits.heap_bytes).div_ceil(PAGE)
}

#[test]
fn presets_are_whole_pages_of_arena() {
    for (name, limits) in BOARDS {
        let total = u64::from(limits.heap_bytes) + (8 << 10);
        assert_eq!(total % PAGE, 0, "{name}");
    }
    assert_eq!(budget_pages(EmbeddedLimits::C6), 4);
    assert_eq!(budget_pages(EmbeddedLimits::C3), 4);
    assert_eq!(budget_pages(EmbeddedLimits::RP2040), 1);
}

#[test]
fn every_example_builds_for_every_board_within_its_budget() {
    let mut built = 0;
    for path in examples() {
        let source = fs::read_to_string(&path).unwrap();
        let host = HostInterface::turtle();
        if compile_for(goat::Profile::Embedded, &source, &host).is_err() {
            continue;
        }
        for (name, limits) in BOARDS {
            let (wasm, _) = compile_embedded(&source, &host, limits)
                .unwrap_or_else(|e| panic!("{} for {name}: {e:?}", path.display()));
            let (min, max) = memory_pages(&wasm);
            assert_eq!(max, Some(min), "{} for {name}", path.display());
            assert!(
                min <= budget_pages(limits),
                "{} for {name}: {min} pages",
                path.display()
            );
        }
        built += 1;
    }
    assert!(built >= 10, "only {built} examples build for embedded");
}

#[test]
fn the_board_flag_sizes_the_module() {
    let dir = tempfile::tempdir().unwrap();
    let src = dir.path().join("p.goat");
    fs::write(&src, "print(1 + 2)").unwrap();
    for (name, limits) in BOARDS {
        let out = dir.path().join(format!("{name}.wasm"));
        let status = Command::new(env!("CARGO_BIN_EXE_goat"))
            .args(["build", src.to_str().unwrap(), "--target", "embedded"])
            .args(["--board", name, "-o", out.to_str().unwrap()])
            .output()
            .unwrap();
        assert!(status.status.success(), "{name}");
        let (min, max) = memory_pages(&fs::read(out).unwrap());
        assert_eq!(max, Some(min), "{name}");
        assert_eq!(min, budget_pages(limits), "{name}");
    }
}

#[test]
fn a_board_needs_the_embedded_target() {
    let dir = tempfile::tempdir().unwrap();
    let src = dir.path().join("p.goat");
    fs::write(&src, "1").unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_goat"))
        .args(["build", src.to_str().unwrap(), "--board", "c6"])
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("--board needs --target embedded"));

    let out = Command::new(env!("CARGO_BIN_EXE_goat"))
        .args(["build", src.to_str().unwrap(), "--target", "embedded"])
        .args(["--board", "esp8266"])
        .output()
        .unwrap();
    assert!(String::from_utf8_lossy(&out.stderr).contains("--board takes c6, c3 or rp2040"));
}
