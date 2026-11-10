//! Builds the vendored WAMR with `cc`, so the only tool it needs is the C
//! compiler cargo already requires to link. The source list and defines mirror
//! what WAMR's own CMake build produces for `WAMR_BUILD_FAST_INTERP=1`,
//! `WAMR_BUILD_AOT=0`, and every JIT off.
//!
//! WAMR fixes its interpreter at compile time, so the classic interpreter that
//! ADR 0025 falls back to is a second copy of the runtime. Its global symbols
//! get a `goat_classic_` prefix, found by running `nm` over its object files,
//! so both copies link into one binary.

use std::{env, path::Path, path::PathBuf, process::Command};

const WAMR: &str = "vendor/wasm-micro-runtime/core";

const CLASSIC_PREFIX: &str = "goat_classic_";

const SOURCES: &[&str] = &[
    "iwasm/common/wasm_application.c",
    "iwasm/common/wasm_blocking_op.c",
    "iwasm/common/wasm_c_api.c",
    "iwasm/common/wasm_exec_env.c",
    "iwasm/common/wasm_loader_common.c",
    "iwasm/common/wasm_memory.c",
    "iwasm/common/wasm_native.c",
    "iwasm/common/wasm_runtime_common.c",
    "iwasm/common/wasm_shared_memory.c",
    "iwasm/common/arch/invokeNative_general.c",
    "iwasm/interpreter/wasm_loader.c",
    "iwasm/interpreter/wasm_runtime.c",
    "shared/mem-alloc/ems/ems_alloc.c",
    "shared/mem-alloc/ems/ems_gc.c",
    "shared/mem-alloc/ems/ems_hmu.c",
    "shared/mem-alloc/ems/ems_kfc.c",
    "shared/mem-alloc/mem_alloc.c",
    "shared/platform/common/memory/mremap.c",
    "shared/platform/common/posix/posix_blocking_op.c",
    "shared/platform/common/posix/posix_memmap.c",
    "shared/platform/common/posix/posix_malloc.c",
    "shared/platform/common/posix/posix_sleep.c",
    "shared/platform/common/posix/posix_thread.c",
    "shared/platform/common/posix/posix_time.c",
    "shared/utils/bh_assert.c",
    "shared/utils/bh_bitmap.c",
    "shared/utils/bh_common.c",
    "shared/utils/bh_hashmap.c",
    "shared/utils/bh_leb128.c",
    "shared/utils/bh_list.c",
    "shared/utils/bh_log.c",
    "shared/utils/bh_queue.c",
    "shared/utils/bh_vector.c",
    "shared/utils/runtime_timer.c",
];

const INCLUDES: &[&str] = &[
    "iwasm/include",
    "iwasm/common",
    "iwasm/interpreter",
    "shared/utils",
    "shared/mem-alloc",
    "shared/platform/include",
];

#[derive(Clone, Copy, PartialEq)]
enum Interp {
    Fast,
    Classic,
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    configure(Interp::Fast, None).compile("iwasm");
    let renames = classic_renames();
    configure(Interp::Classic, Some(&renames)).compile("iwasm_classic");
}

/// A header renaming every global symbol the classic build defines.
fn classic_renames() -> PathBuf {
    let mut header = String::new();
    for object in configure(Interp::Classic, None).compile_intermediates() {
        let listing = Command::new("nm")
            .args(["-g", "--defined-only", "-P"])
            .arg(&object)
            .output()
            .expect("nm lists the symbols of the classic runtime");
        assert!(
            listing.status.success(),
            "nm failed on {}",
            object.display()
        );
        for line in String::from_utf8_lossy(&listing.stdout).lines() {
            let mut fields = line.split_whitespace();
            let (Some(name), Some(kind)) = (fields.next(), fields.next()) else {
                continue;
            };
            if !matches!(kind, "T" | "D" | "B" | "S" | "R" | "C") {
                continue;
            }
            let name = if cfg!(target_vendor = "apple") {
                name.strip_prefix('_').unwrap_or(name)
            } else {
                name
            };
            header.push_str(&format!("#define {name} {CLASSIC_PREFIX}{name}\n"));
        }
    }
    // wasm_runtime_common.c insists BH_MALLOC and BH_FREE spell the runtime's
    // allocator, which the renaming changes; this makes the renamed spelling pass.
    for name in ["malloc", "free"] {
        header.push_str(&format!(
            "#define SHOULD_BE_{CLASSIC_PREFIX}wasm_runtime_{name} 1\n"
        ));
    }
    let path = Path::new(&env::var("OUT_DIR").unwrap()).join("classic_rename.h");
    std::fs::write(&path, header).unwrap();
    path
}

fn configure(interp: Interp, renames: Option<&Path>) -> cc::Build {
    let fast = interp == Interp::Fast;
    let platform = match env::var("CARGO_CFG_TARGET_OS").as_deref() {
        Ok("macos") => "darwin",
        Ok("linux") => "linux",
        Ok(os) => panic!("goat_wamr builds WAMR for macOS and Linux hosts, not {os}"),
        Err(e) => panic!("CARGO_CFG_TARGET_OS: {e}"),
    };
    let arch = match env::var("CARGO_CFG_TARGET_ARCH").as_deref() {
        Ok("x86_64") => ("BUILD_TARGET_X86_64", "X86_64"),
        Ok("aarch64") => ("BUILD_TARGET_AARCH64", "AARCH64"),
        Ok(arch) => panic!("goat_wamr builds WAMR for x86_64 and aarch64 hosts, not {arch}"),
        Err(e) => panic!("CARGO_CFG_TARGET_ARCH: {e}"),
    };

    let mut build = cc::Build::new();
    build
        // Third-party code, and an interpreter loop that is unusably slow
        // unoptimized, so the profile's opt level does not apply.
        .warnings(false)
        .opt_level(2)
        .debug(false)
        .define(arch.0, None)
        .define("BUILD_TARGET", format!("\"{}\"", arch.1).as_str())
        .define(
            if platform == "darwin" {
                "BH_PLATFORM_DARWIN"
            } else {
                "BH_PLATFORM_LINUX"
            },
            None,
        )
        .define("BH_MALLOC", "wasm_runtime_malloc")
        .define("BH_FREE", "wasm_runtime_free")
        // One interpreter per copy of the runtime: the fast one, or the classic
        // one that has no per-function cell limit (ADR 0025).
        .define("WASM_ENABLE_INTERP", "1")
        .define("WASM_ENABLE_FAST_INTERP", if fast { "1" } else { "0" })
        .define("WASM_ENABLE_MINI_LOADER", "0")
        .define("WASM_ENABLE_AOT", "0")
        .define("WASM_ENABLE_JIT", "0")
        .define("WASM_ENABLE_FAST_JIT", "0")
        // The feature floor of docs/adr/0019-on-device-wasm-runtime.md: the
        // MVP plus tail calls and bulk memory. `csrc/floor.c` fails the build
        // if either does not take effect.
        .define("WASM_ENABLE_TAIL_CALL", "1")
        .define("WASM_ENABLE_BULK_MEMORY", "1")
        .define("WASM_ENABLE_REF_TYPES", "1")
        .define("WASM_ENABLE_SIMD", "0")
        .define("WASM_ENABLE_SHARED_MEMORY", "0")
        .define("WASM_ENABLE_MULTI_MODULE", "0")
        .define("WASM_ENABLE_LIBC_BUILTIN", "0")
        .define("WASM_ENABLE_LIBC_WASI", "0")
        // Software bounds checks: no signal handlers, so the runtime is safe on
        // any host thread.
        .define("WASM_DISABLE_HW_BOUND_CHECK", "1")
        .define("WASM_DISABLE_STACK_HW_BOUND_CHECK", "1")
        // Used on every platform, so one build covers macOS and Linux alike.
        .define("WASM_HAVE_MREMAP", "0");

    for include in INCLUDES {
        build.include(Path::new(WAMR).join(include));
    }
    build.include(Path::new(WAMR).join(format!("shared/platform/{platform}")));
    build.include(WAMR);
    if let Some(renames) = renames {
        build.flag("-include").flag(renames.to_str().unwrap());
    }

    let interp_source = format!(
        "iwasm/interpreter/wasm_interp_{}.c",
        if fast { "fast" } else { "classic" }
    );
    for source in SOURCES.iter().copied().chain([interp_source.as_str()]) {
        let path = Path::new(WAMR).join(source);
        println!("cargo:rerun-if-changed={}", path.display());
        build.file(path);
    }
    println!("cargo:rerun-if-changed=csrc/floor.c");
    build.file("csrc/floor.c");
    let platform_init = format!("{WAMR}/shared/platform/{platform}/platform_init.c");
    println!("cargo:rerun-if-changed={platform_init}");
    build.file(platform_init);
    build
}
