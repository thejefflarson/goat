//! Run compiled goat modules under wasmtime. Native only: the `native` cargo
//! feature keeps wasmtime out of the compiler's wasm32 build.
//!
//! - [`run_to_end`] runs a run-once program (`goat_entry`) against a [`Host`].
//! - [`Interactive`] drives the ADR 0015 export contract, streaming each frame
//!   to a [`SceneSink`].
//!   [`Interactive::reload`] swaps in a recompiled program over the same heap.
//! - [`Guest`] is the raw instance both are built on.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use wasmtime::{Caller, Config, Engine, ExternType, Instance, Linker, Module, Store, Trap, Val};

mod interactive;

pub use goat_checker::hir::Boundary;
pub use goat_mir::{Host, HostValue, NoHost, SceneSink};
pub use interactive::{Event, Interactive, Reloaded};

/// What a finished program left behind.
pub struct Run {
    pub printed: Vec<String>,
    /// Heap blocks still allocated after `goat_entry`; a correct program leaves none.
    pub live_allocs: u32,
}

/// The lines the program has printed, and the one it is still writing: `write_*`
/// extends `line`, `write_end` (and every `print_*`) finishes it.
#[derive(Default)]
struct Output {
    lines: Vec<String>,
    line: String,
}

impl Output {
    fn finish(&mut self) {
        self.lines.push(std::mem::take(&mut self.line));
    }

    fn write_line(&mut self, text: &str) {
        self.line.push_str(text);
        self.finish();
    }
}

/// Why a program halted: the message it gave, and the user's source range
/// (byte offsets) to blame when the trap came from code the user wrote.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stopped {
    pub message: String,
    pub site: Option<(usize, usize)>,
}

/// A program that has run to its end or halted, with everything it printed
/// either way.
pub struct Finished<H> {
    pub printed: Vec<String>,
    pub host: H,
    /// The heap blocks still allocated after a clean finish, or why it halted.
    pub result: Result<u32, Stopped>,
}

struct State<H> {
    output: Output,
    host: H,
    /// The source range of each site number, from the module's `goat.sites`.
    sites: Vec<(usize, usize)>,
    stopped: Option<Stopped>,
}

/// The ranges in a module's `goat.sites` custom section, in site-number order.
fn site_table(wasm: &[u8]) -> Vec<(usize, usize)> {
    fn leb(bytes: &mut &[u8]) -> Option<usize> {
        let (mut value, mut shift) = (0usize, 0);
        loop {
            let (&byte, rest) = bytes.split_first()?;
            *bytes = rest;
            value |= usize::from(byte & 0x7f).checked_shl(shift)?;
            if byte & 0x80 == 0 {
                return Some(value);
            }
            shift += 7;
        }
    }
    let mut rest = wasm.get(8..).unwrap_or_default();
    while let Some((&id, tail)) = rest.split_first() {
        rest = tail;
        let Some(size) = leb(&mut rest) else { break };
        let Some((mut section, tail)) = rest.split_at_checked(size) else {
            break;
        };
        rest = tail;
        if id != 0 {
            continue;
        }
        let Some(name_len) = leb(&mut section) else {
            continue;
        };
        let Some((name, table)) = section.split_at_checked(name_len) else {
            continue;
        };
        if name == b"goat.sites" {
            let word = |w: &[u8]| u32::from_le_bytes(w.try_into().unwrap()) as usize;
            return table
                .as_chunks::<8>()
                .0
                .iter()
                .map(|pair| (word(&pair[..4]), word(&pair[4..])))
                .collect();
        }
    }
    Vec::new()
}

/// Instantiate `wasm` under wasmtime, run its entry export, and return the
/// lines the program printed. A trap becomes an error.
pub fn execute(wasm: &[u8]) -> Result<Vec<String>, String> {
    run(wasm).map(|run| run.printed)
}

/// Where a string object keeps its length and its bytes (`docs/mir.md`).
const STR_LEN: usize = 8;
const STR_BYTES: usize = 12;

fn memory<T>(caller: &mut Caller<'_, T>) -> wasmtime::Result<wasmtime::Memory> {
    caller
        .get_export("memory")
        .and_then(|e| e.into_memory())
        .ok_or_else(|| wasmtime::Error::msg("module exports no memory"))
}

/// The text of the goat string at `ptr` in the module's memory.
fn read_string<T>(caller: &mut Caller<'_, T>, ptr: i32) -> wasmtime::Result<String> {
    let memory = memory(caller)?;
    let data = memory.data(&*caller);
    let ptr = ptr as u32 as usize;
    let oob = || wasmtime::Error::msg("string out of bounds");
    let len_bytes = data.get(ptr + STR_LEN..ptr + STR_LEN + 4).ok_or_else(oob)?;
    let len = u32::from_le_bytes(len_bytes.try_into().unwrap()) as usize;
    let bytes = data
        .get(ptr + STR_BYTES..ptr + STR_BYTES + len)
        .ok_or_else(oob)?;
    Ok(String::from_utf8_lossy(bytes).into_owned())
}

/// A string object holding `text`, made in the module's own heap through its
/// exported `goat_alloc`, which hands it over with count 1: goat owns it.
fn alloc_string<T>(caller: &mut Caller<'_, T>, text: &str) -> wasmtime::Result<i32> {
    let too_long = || wasmtime::Error::msg("string too long");
    let len = u32::try_from(text.len()).map_err(|_| too_long())?;
    let size = u32::try_from(STR_BYTES + text.len()).map_err(|_| too_long())?;
    let alloc = caller
        .get_export("goat_alloc")
        .and_then(|e| e.into_func())
        .ok_or_else(|| wasmtime::Error::msg("module exports no goat_alloc"))?
        .typed::<u32, u32>(&*caller)?;
    let ptr = alloc.call(&mut *caller, size)?;
    let memory = memory(caller)?;
    memory.write(&mut *caller, ptr as usize + STR_LEN, &len.to_le_bytes())?;
    memory.write(&mut *caller, ptr as usize + STR_BYTES, text.as_bytes())?;
    Ok(ptr as i32)
}

/// Make `module.name` callable from the program as the host function `host`
/// describes: wasm values in, `HostValue`s to the host, its result back out.
fn link_foreign<H: Host + 'static>(
    linker: &mut Linker<State<H>>,
    host: &H,
    module: &str,
    name: &str,
    ty: wasmtime::FuncType,
) -> Result<(), String> {
    let (params, ret) = host
        .signature(module, name)
        .ok_or_else(|| format!("the host provides no function {module}.{name}"))?;
    let (module_name, fn_name) = (module.to_string(), name.to_string());
    linker
        .func_new(
            module,
            name,
            ty,
            move |mut caller: Caller<'_, State<H>>, args, results| {
                let mut raw = args.iter();
                let mut values = Vec::with_capacity(params.len());
                for param in &params {
                    values.push(match param {
                        Boundary::Number => HostValue::Number(next(&mut raw)?.unwrap_f64()),
                        Boundary::Int => HostValue::Int(next(&mut raw)?.unwrap_i64()),
                        Boundary::Bool => HostValue::Bool(next(&mut raw)?.unwrap_i32() != 0),
                        Boundary::Unit => HostValue::Unit,
                        Boundary::Str => {
                            let ptr = next(&mut raw)?.unwrap_i32();
                            HostValue::Str(read_string(&mut caller, ptr)?)
                        }
                    });
                }
                let returned = caller
                    .data_mut()
                    .host
                    .call(&module_name, &fn_name, &values)
                    .map_err(wasmtime::Error::msg)?;
                match (ret, returned) {
                    (Boundary::Number, HostValue::Number(x)) => results[0] = Val::F64(x.to_bits()),
                    (Boundary::Int, HostValue::Int(n)) => results[0] = Val::I64(n),
                    (Boundary::Bool, HostValue::Bool(b)) => results[0] = Val::I32(b as i32),
                    (Boundary::Unit, HostValue::Unit) => {}
                    (Boundary::Str, HostValue::Str(text)) => {
                        results[0] = Val::I32(alloc_string(&mut caller, &text)?);
                    }
                    _ => {
                        return Err(wasmtime::Error::msg(format!(
                            "{module_name}.{fn_name} returned a value of the wrong type"
                        )));
                    }
                }
                Ok(())
            },
        )
        .map_err(|e| e.to_string())?;
    Ok(())
}

fn next<'a>(args: &mut impl Iterator<Item = &'a Val>) -> wasmtime::Result<&'a Val> {
    args.next()
        .ok_or_else(|| wasmtime::Error::msg("host call with too few arguments"))
}

/// Like `execute`, but also reads the allocator's live-allocation count.
pub fn run(wasm: &[u8]) -> Result<Run, String> {
    run_with_host(wasm, NoHost).map(|(run, _)| run)
}

/// How often a timeout's ticker advances the epoch.
const EPOCH_TICK: Duration = Duration::from_millis(10);

/// A wall-clock bound on each call into a guest, enforced by wasmtime's epoch
/// interruption: a thread advances the engine's epoch every [`EPOCH_TICK`] and
/// a call that outlives its ticks traps at the next function entry or loop
/// back-edge. The host owns this bound (ADR 0021); the module carries none.
struct Deadline {
    timeout: Duration,
    ticks: u64,
    stop: Arc<AtomicBool>,
}

impl Deadline {
    fn start(engine: &Engine, timeout: Duration) -> Deadline {
        let stop = Arc::new(AtomicBool::new(false));
        let (ticker, halt) = (engine.clone(), Arc::clone(&stop));
        std::thread::spawn(move || {
            while !halt.load(Ordering::Relaxed) {
                std::thread::sleep(EPOCH_TICK);
                ticker.increment_epoch();
            }
        });
        // One extra tick, because the first falls anywhere in the first interval.
        let ticks = u64::try_from(timeout.as_nanos().div_ceil(EPOCH_TICK.as_nanos()))
            .unwrap_or(u64::MAX)
            .saturating_add(1);
        Deadline {
            timeout,
            ticks,
            stop,
        }
    }

    fn stuck(&self) -> String {
        format!(
            "the program ran for more than {} ms, so it looks stuck",
            self.timeout.as_millis()
        )
    }
}

impl Drop for Deadline {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Relaxed);
    }
}

/// Start a call's clock: `deadline` from now, or never without one. A store
/// with epochs enabled traps at once until this is set.
fn arm<T>(store: &mut Store<T>, deadline: Option<&Deadline>) {
    store.set_epoch_deadline(deadline.map_or(u64::MAX, |deadline| deadline.ticks));
}

fn interrupted(error: &wasmtime::Error) -> bool {
    error.downcast_ref::<Trap>() == Some(&Trap::Interrupt)
}

fn engine() -> Result<Engine, String> {
    let mut config = Config::new();
    config.wasm_tail_call(true);
    config.epoch_interruption(true);
    Engine::new(&config).map_err(|e| format!("engine: {e}"))
}

/// What `module` imports from the host, answered from `host`.
fn link<H: Host + 'static>(
    engine: &Engine,
    module: &Module,
    host: &H,
) -> Result<Linker<State<H>>, String> {
    let mut linker: Linker<State<H>> = Linker::new(engine);
    linker
        .func_wrap(
            "goat",
            "print_number",
            |mut caller: Caller<'_, State<H>>, x: f64| {
                caller
                    .data_mut()
                    .output
                    .write_line(&crate::format_number(x));
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "print_bool",
            |mut caller: Caller<'_, State<H>>, b: i32| {
                caller
                    .data_mut()
                    .output
                    .write_line(crate::format_bool(b != 0));
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "print_int",
            |mut caller: Caller<'_, State<H>>, n: i64| {
                caller.data_mut().output.write_line(&n.to_string());
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "print_string",
            |mut caller: Caller<'_, State<H>>, ptr: i32| -> wasmtime::Result<()> {
                let text = read_string(&mut caller, ptr)?;
                caller.data_mut().output.write_line(&text);
                Ok(())
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "write_number",
            |mut caller: Caller<'_, State<H>>, x: f64| {
                caller
                    .data_mut()
                    .output
                    .line
                    .push_str(&crate::format_number(x));
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "write_int",
            |mut caller: Caller<'_, State<H>>, n: i64| {
                caller.data_mut().output.line.push_str(&n.to_string());
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "write_string",
            |mut caller: Caller<'_, State<H>>, ptr: i32| -> wasmtime::Result<()> {
                let text = read_string(&mut caller, ptr)?;
                caller.data_mut().output.line.push_str(&text);
                Ok(())
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap("goat", "write_end", |mut caller: Caller<'_, State<H>>| {
            caller.data_mut().output.finish();
        })
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "trap",
            |mut caller: Caller<'_, State<H>>, ptr: i32| -> wasmtime::Result<()> {
                let message = read_string(&mut caller, ptr)?;
                let site = caller
                    .get_export("goat_site")
                    .and_then(|e| e.into_global())
                    .and_then(|g| g.get(&mut caller).i32())
                    .and_then(|n| usize::try_from(n).ok()?.checked_sub(1))
                    .and_then(|n| caller.data().sites.get(n).copied());
                caller.data_mut().stopped = Some(Stopped {
                    message: message.clone(),
                    site,
                });
                Err(wasmtime::Error::msg(message))
            },
        )
        .map_err(|e| e.to_string())?;

    for import in module.imports() {
        if let (false, ExternType::Func(ty)) = (import.module() == "goat", import.ty()) {
            link_foreign(&mut linker, host, import.module(), import.name(), ty)?;
        }
    }

    Ok(linker)
}

/// The memory and allocator state a reloadable module imports. Every module
/// run over the same `Hosted` shares one heap, so objects one allocated are
/// valid in the next.
#[derive(Clone, Copy)]
struct Hosted {
    memory: wasmtime::Memory,
    heap: wasmtime::Global,
    live: wasmtime::Global,
}

impl Hosted {
    fn new<T>(store: &mut Store<T>) -> Result<Hosted, String> {
        let memory = wasmtime::Memory::new(&mut *store, wasmtime::MemoryType::new(1, None))
            .map_err(|e| e.to_string())?;
        let mut cell = |init: u32| {
            let ty = wasmtime::GlobalType::new(wasmtime::ValType::I32, wasmtime::Mutability::Var);
            wasmtime::Global::new(&mut *store, ty, Val::I32(init as i32)).map_err(|e| e.to_string())
        };
        Ok(Hosted {
            heap: cell(goat_wasm::HOSTED_HEAP_START)?,
            live: cell(0)?,
            memory,
        })
    }

    fn define<T>(&self, linker: &mut Linker<T>, store: &Store<T>) -> Result<(), String> {
        let mut define = |name: &str, item: wasmtime::Extern| {
            linker
                .define(store, "goat", name, item)
                .map(|_| ())
                .map_err(|e| e.to_string())
        };
        define("memory", self.memory.into())?;
        define("heap", self.heap.into())?;
        define("live", self.live.into())
    }
}

fn imports_memory(module: &Module) -> bool {
    module
        .imports()
        .any(|i| i.module() == "goat" && i.name() == "memory")
}

fn load(engine: &Engine, wasm: &[u8]) -> Result<Module, String> {
    Module::new(engine, wasm).map_err(|e| format!("invalid module: {e}"))
}

/// Instantiate `module` in `store`, over the shared heap in `hosted` if it
/// imports one, which is made on first need.
fn instantiate_in<H: Host + 'static>(
    store: &mut Store<State<H>>,
    module: &Module,
    hosted: &mut Option<Hosted>,
) -> Result<Instance, String> {
    let mut linker = link(store.engine(), module, &store.data().host)?;
    if imports_memory(module) {
        let shared = match *hosted {
            Some(shared) => shared,
            None => *hosted.insert(Hosted::new(store)?),
        };
        shared.define(&mut linker, store)?;
    }
    linker
        .instantiate(&mut *store, module)
        .map_err(|e| format!("instantiate: {e}"))
}

/// A module instantiated with its imports answered from `host`.
fn instantiate<H: Host + 'static>(
    wasm: &[u8],
    host: H,
    timeout: Option<Duration>,
) -> Result<Guest<H>, String> {
    let engine = engine()?;
    let module = load(&engine, wasm)?;
    let mut store = Store::new(
        &engine,
        State {
            output: Output::default(),
            host,
            sites: site_table(wasm),
            stopped: None,
        },
    );
    let deadline = timeout.map(|timeout| Deadline::start(&engine, timeout));
    arm(&mut store, deadline.as_ref());
    let mut hosted = None;
    let instance = instantiate_in(&mut store, &module, &mut hosted)?;
    Ok(Guest {
        store,
        instance,
        hosted,
        deadline,
    })
}

/// Like `run`, answering the program's `foreign` calls from `host`, which
/// comes back so a test can read what it recorded.
pub fn run_with_host<H: Host + 'static>(wasm: &[u8], host: H) -> Result<(Run, H), String> {
    let finished = run_to_end(wasm, host)?;
    match finished.result {
        Ok(live_allocs) => Ok((
            Run {
                printed: finished.printed,
                live_allocs,
            },
            finished.host,
        )),
        Err(stopped) => Err(format!("trap: {}", stopped.message)),
    }
}

/// Like `run_with_host`, but a halt keeps what the program printed before it,
/// including a line it had started, and says where the user's code was.
pub fn run_to_end<H: Host + 'static>(wasm: &[u8], host: H) -> Result<Finished<H>, String> {
    run_to_end_within(wasm, host, None)
}

/// Like `run_to_end`, but a program still running after `timeout` is stopped
/// with a trap. `None` lets it run as long as it likes.
pub fn run_to_end_within<H: Host + 'static>(
    wasm: &[u8],
    host: H,
    timeout: Option<Duration>,
) -> Result<Finished<H>, String> {
    let Guest {
        mut store,
        instance,
        deadline,
        ..
    } = instantiate(wasm, host, timeout)?;
    let entry = instance
        .get_typed_func::<(), ()>(&mut store, "goat_entry")
        .map_err(|e| format!("missing entry point: {e}"))?;
    let result = match entry.call(&mut store, ()) {
        Ok(()) => {
            arm(&mut store, deadline.as_ref());
            Ok(instance
                .get_typed_func::<(), u32>(&mut store, "goat_live_allocs")
                .and_then(|live| live.call(&mut store, ()))
                .map_err(|e| format!("goat_live_allocs: {e}"))?)
        }
        Err(error) => Err(store.data_mut().stopped.take().unwrap_or_else(|| Stopped {
            message: match &deadline {
                Some(deadline) if interrupted(&error) => deadline.stuck(),
                _ => format!("{error:#}"),
            },
            site: None,
        })),
    };
    let State {
        mut output, host, ..
    } = store.into_data();
    if result.is_err() && !output.line.is_empty() {
        output.finish();
    }
    Ok(Finished {
        printed: output.lines,
        host,
        result,
    })
}

/// An interactive module as its host holds it: instantiated once, then driven
/// through its exports.
pub struct Guest<H: Host + 'static> {
    store: Store<State<H>>,
    instance: Instance,
    /// Set when the module imports its heap, which a later module can then
    /// share.
    hosted: Option<Hosted>,
    deadline: Option<Deadline>,
}

impl<H: Host + 'static> Guest<H> {
    pub fn new(wasm: &[u8], host: H) -> Result<Guest<H>, String> {
        instantiate(wasm, host, None)
    }

    /// Like `new`, but each call into the guest is stopped with a trap once it
    /// has run longer than `timeout`.
    pub fn with_timeout(wasm: &[u8], host: H, timeout: Duration) -> Result<Guest<H>, String> {
        instantiate(wasm, host, Some(timeout))
    }

    /// Instantiate a recompiled `wasm` over this guest's heap without making
    /// it the current instance. Both it and the running module must import
    /// their heap, as `compile_reloadable` makes them.
    fn spawn(&mut self, wasm: &[u8]) -> Result<Instance, String> {
        let module = load(self.store.engine(), wasm)?;
        if self.hosted.is_none() || !imports_memory(&module) {
            return Err("only modules from compile_reloadable can be reloaded".into());
        }
        arm(&mut self.store, self.deadline.as_ref());
        instantiate_in(&mut self.store, &module, &mut self.hosted)
    }

    /// Run `f` with `instance` as the current one, then put the current one
    /// back.
    fn on<R>(&mut self, instance: Instance, f: impl FnOnce(&mut Self) -> R) -> R {
        let current = std::mem::replace(&mut self.instance, instance);
        let result = f(self);
        self.instance = current;
        result
    }

    /// `instance`'s model fingerprint, or why it has none.
    fn fingerprint(&mut self, instance: Instance) -> Result<u64, String> {
        instance
            .get_global(&mut self.store, goat_wasm::FINGERPRINT_EXPORT)
            .and_then(|global| global.get(&mut self.store).i64())
            .map(|bits| bits as u64)
            .ok_or_else(|| format!("module exports no {}", goat_wasm::FINGERPRINT_EXPORT))
    }

    /// Call the export `name`; a trap is an error, and so is outrunning the
    /// timeout.
    pub fn call<P: wasmtime::WasmParams, R: wasmtime::WasmResults>(
        &mut self,
        name: &str,
        args: P,
    ) -> Result<R, String> {
        let func = self
            .instance
            .get_typed_func::<P, R>(&mut self.store, name)
            .map_err(|e| format!("{name}: {e}"))?;
        arm(&mut self.store, self.deadline.as_ref());
        func.call(&mut self.store, args)
            .map_err(|error| match &self.deadline {
                Some(deadline) if interrupted(&error) => {
                    format!("{name} stopped: {}", deadline.stuck())
                }
                _ => format!("{name} trapped: {error:#}"),
            })
    }

    pub fn exports(&mut self) -> Vec<String> {
        self.instance
            .exports(&mut self.store)
            .map(|e| e.name().to_string())
            .collect()
    }

    /// A goat string holding `text`, owned by the caller (count 1), as the
    /// host hands one to an event constructor.
    pub fn string(&mut self, text: &str) -> Result<i32, String> {
        let len = u32::try_from(text.len()).map_err(|_| "string too long".to_string())?;
        let ptr: u32 = self.call("goat_alloc", STR_BYTES as u32 + len)?;
        let memory = self
            .instance
            .get_memory(&mut self.store, "memory")
            .ok_or("module exports no memory")?;
        let at = ptr as usize;
        memory
            .write(&mut self.store, at + STR_LEN, &len.to_le_bytes())
            .and_then(|()| memory.write(&mut self.store, at + STR_BYTES, text.as_bytes()))
            .map_err(|e| e.to_string())?;
        Ok(ptr as i32)
    }

    /// `len` bytes of the module's memory at `at`.
    pub fn read(&mut self, at: usize, len: usize) -> Result<Vec<u8>, String> {
        let memory = self
            .instance
            .get_memory(&mut self.store, "memory")
            .ok_or("module exports no memory")?;
        let mut bytes = vec![0; len];
        memory
            .read(&self.store, at, &mut bytes)
            .map_err(|e| e.to_string())?;
        Ok(bytes)
    }

    pub fn live_allocs(&mut self) -> Result<u32, String> {
        self.call("goat_live_allocs", ())
    }

    pub fn into_host(self) -> H {
        self.store.into_data().host
    }
}
