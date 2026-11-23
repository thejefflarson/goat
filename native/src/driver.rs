//! Compiles emitted `.ll` into a shared library with clang, loads it, and runs
//! its `goat_main` against a Rust [`Host`]. Every library is its own `dlopen`
//! scope, so any number can be loaded and run side by side in one process, each
//! call with its own instance and host.
//!
//! A trap must leave generated code without returning into it. This driver
//! links a small C shim whose `goat_shim_trap` is the table's trap entry: it
//! `longjmp`s back to `goat_shim_run`, which reports the message.

use crate::abi::{Ctx, GoatHost, GoatInstance, HOST_VERSION, INSTANCE_VERSION, Instance};
use crate::adapter::Adapter;
use goat::Host;
use libloading::Library as Dylib;
use std::fmt;
use std::path::Path;
use std::process::Command;
use tempfile::TempDir;

const SHIM: &str = r#"
#include <setjmp.h>
#include <stdint.h>

typedef struct {
    jmp_buf env;
    const uint8_t *message;
    uint64_t len;
} frame;

static _Thread_local frame *current;

void goat_shim_trap(void *ctx, const uint8_t *message, uint64_t len) {
    (void)ctx;
    current->message = message;
    current->len = len;
    longjmp(current->env, 1);
}

typedef int32_t (*entry)(const void *, void *, void *);

int32_t goat_shim_run(entry main, const void *host, void *ctx, void *inst,
                      const uint8_t **message, uint64_t *len) {
    frame mine = {.message = 0, .len = 0};
    frame *outer = current;
    current = &mine;
    int32_t status = setjmp(mine.env) == 0 ? main(host, ctx, inst) : -1;
    current = outer;
    *message = mine.message;
    *len = mine.len;
    return status;
}
"#;

/// The heap a run gets when its caller does not bring an instance: address
/// space, not memory, since its pages are zeroed on demand.
pub const DEFAULT_HEAP_BYTES: usize = 1 << 28;

#[derive(Debug)]
pub enum NativeError {
    /// `clang` is not installed (or `$CLANG` names nothing runnable).
    NoClang(String),
    Clang(String),
    Load(String),
    /// The generated code refused the table or the instance as too old.
    Version {
        what: &'static str,
        found: u32,
        wanted: u32,
    },
    /// The instance trapped on an earlier run and was not reset.
    DeadInstance,
}

impl fmt::Display for NativeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeError::NoClang(why) => write!(f, "clang is not available: {why}"),
            NativeError::Clang(stderr) => write!(f, "clang failed:\n{stderr}"),
            NativeError::Load(why) => write!(f, "cannot load the compiled program: {why}"),
            NativeError::Version {
                what,
                found,
                wanted,
            } => write!(
                f,
                "the program needs {what} version {wanted} or later, but was given {found}"
            ),
            NativeError::DeadInstance => write!(
                f,
                "the instance trapped, so it cannot run again until it is reset"
            ),
        }
    }
}

impl std::error::Error for NativeError {}

/// Why a program halted, and the source range to blame when it came from code
/// the user wrote.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stopped {
    pub message: String,
    pub site: Option<(usize, usize)>,
}

/// What one run left behind.
pub struct Run<H> {
    pub printed: Vec<String>,
    pub host: H,
    /// The heap blocks still allocated after a clean finish.
    pub live_allocs: u32,
    /// The allocations the program made, freed or not.
    pub allocations: u64,
    pub result: Result<(), Stopped>,
}

/// The table and instance versions a run presents; the defaults are the
/// emitter's own.
#[derive(Clone, Copy)]
pub struct Versions {
    pub host: u32,
    pub instance: u32,
}

impl Default for Versions {
    fn default() -> Versions {
        Versions {
            host: HOST_VERSION,
            instance: INSTANCE_VERSION,
        }
    }
}

type Main = unsafe extern "C" fn(*const GoatHost, Ctx, *mut GoatInstance) -> i32;
type Shim = unsafe extern "C" fn(
    Main,
    *const GoatHost,
    Ctx,
    *mut GoatInstance,
    *mut *const u8,
    *mut u64,
) -> i32;
type Trap = unsafe extern "C" fn(Ctx, *const u8, u64) -> !;

/// A compiled program, loaded.
pub struct Library {
    dylib: Dylib,
}

/// The clang to run: `$CLANG`, or the one on `PATH`.
pub fn clang() -> String {
    std::env::var("CLANG").unwrap_or_else(|_| "clang".to_string())
}

/// Whether [`Library::build`] can work here.
pub fn clang_available() -> bool {
    Command::new(clang())
        .arg("--version")
        .output()
        .is_ok_and(|out| out.status.success())
}

impl Library {
    /// Compiles `ll`, textual LLVM IR from `goat_llvm`, and loads the result.
    pub fn build(ll: &str) -> Result<Library, NativeError> {
        let dir = TempDir::new().map_err(|e| NativeError::Clang(e.to_string()))?;
        let (ll_path, shim_path) = (dir.path().join("program.ll"), dir.path().join("shim.c"));
        let output = dir.path().join(if cfg!(target_os = "macos") {
            "program.dylib"
        } else {
            "program.so"
        });
        for (path, text) in [(&ll_path, ll), (&shim_path, SHIM)] {
            std::fs::write(path, text).map_err(|e| NativeError::Clang(e.to_string()))?;
        }
        let out = Command::new(clang())
            .args(["-shared", "-fPIC", "-x", "ir"])
            .arg(&ll_path)
            .args(["-x", "c"])
            .arg(&shim_path)
            .arg("-lm")
            .arg("-o")
            .arg(&output)
            .output()
            .map_err(|e| NativeError::NoClang(e.to_string()))?;
        if !out.status.success() {
            return Err(NativeError::Clang(
                String::from_utf8_lossy(&out.stderr).into_owned(),
            ));
        }
        Self::load(&output)
    }

    fn load(path: &Path) -> Result<Library, NativeError> {
        // SAFETY: the library is the code this crate just built: it runs no
        // constructor beyond the C runtime's.
        let dylib = unsafe { Dylib::new(path) }.map_err(|e| NativeError::Load(e.to_string()))?;
        Ok(Library { dylib })
    }

    /// Runs `goat_main` against `host`.
    pub fn run<H: Host>(&self, host: H) -> Result<Run<H>, NativeError> {
        self.run_versioned(host, Versions::default())
    }

    /// Like [`run`](Self::run), presenting the versions in `versions`.
    pub fn run_versioned<H: Host>(
        &self,
        host: H,
        versions: Versions,
    ) -> Result<Run<H>, NativeError> {
        let mut instance = Instance::new(DEFAULT_HEAP_BYTES);
        instance.set_version(versions.instance);
        self.run_in(&mut instance, host, versions.host)
    }

    /// Runs `goat_main` in `instance`, which a host may reuse across runs while
    /// it stays alive. A trap kills it ([`Instance::is_dead`]); running a dead
    /// instance is refused with [`NativeError::DeadInstance`] until
    /// [`Instance::reset`].
    pub fn run_in<H: Host>(
        &self,
        instance: &mut Instance,
        host: H,
        host_version: u32,
    ) -> Result<Run<H>, NativeError> {
        if instance.is_dead() {
            return Err(NativeError::DeadInstance);
        }
        let versions = Versions {
            host: host_version,
            instance: instance.version(),
        };
        let load = |e: libloading::Error| NativeError::Load(e.to_string());
        // SAFETY: these symbols have the signatures the emitter and the shim
        // define, and the library outlives the copies.
        let (main, shim, trap) = unsafe {
            (
                *self.dylib.get::<Main>(b"goat_main\0").map_err(load)?,
                *self.dylib.get::<Shim>(b"goat_shim_run\0").map_err(load)?,
                *self.dylib.get::<Trap>(b"goat_shim_trap\0").map_err(load)?,
            )
        };
        let mut adapter = Adapter::new(host, trap);
        let mut table = adapter.table();
        table.version = versions.host;
        let (mut message, mut len) = (std::ptr::null(), 0u64);
        let ctx = adapter.ctx();
        // SAFETY: the table, the context and the instance outlive the call, and
        // the shim returns here whether the program finishes or traps.
        let status = unsafe { shim(main, &table, ctx, instance.as_ptr(), &mut message, &mut len) };
        match status {
            0 => {}
            1 => {
                return Err(NativeError::Version {
                    what: "goat_host",
                    found: versions.host,
                    wanted: HOST_VERSION,
                });
            }
            2 => {
                return Err(NativeError::Version {
                    what: "goat_instance",
                    found: versions.instance,
                    wanted: INSTANCE_VERSION,
                });
            }
            _ => {}
        }
        let result = if status == -1 {
            instance.mark_dead();
            // SAFETY: the shim stored the trap's message, which the library's
            // constants or the adapter keep alive until here.
            let bytes = unsafe { std::slice::from_raw_parts(message, len as usize) };
            Err(Stopped {
                message: String::from_utf8_lossy(bytes).into_owned(),
                site: instance.site(),
            })
        } else {
            Ok(())
        };
        Ok(Run {
            printed: std::mem::take(&mut adapter.lines),
            live_allocs: instance.live(),
            allocations: instance.allocations(),
            host: adapter.host,
            result,
        })
    }

    /// The layout of the emitter's structs as clang computes it: see
    /// [`crate::abi::expected_layout`].
    pub fn probe_layout(&self) -> Result<Vec<u64>, NativeError> {
        let count = crate::abi::expected_layout().len();
        let mut out = vec![0u64; count];
        // SAFETY: the probe writes `count` words, as `goat_llvm` documents.
        unsafe {
            let probe = self
                .dylib
                .get::<unsafe extern "C" fn(*mut u64)>(b"goat_layout_probe\0")
                .map_err(|e| NativeError::Load(e.to_string()))?;
            probe(out.as_mut_ptr());
        }
        Ok(out)
    }
}
