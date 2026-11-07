//! The wasmtime host that runs compiled goat modules, shared by the `goat`
//! binary and the differential tests.

use goat_checker::hir::Boundary;
use goat_mir::{Host, HostValue, NoHost};
use wasmtime::{Caller, Config, Engine, ExternType, Instance, Linker, Module, Store, Val};

pub mod turtle;

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

/// A module instantiated with its imports answered from `host`.
fn instantiate<H: Host + 'static>(
    wasm: &[u8],
    host: H,
) -> Result<(Store<State<H>>, Instance), String> {
    let mut config = Config::new();
    config.wasm_tail_call(true);
    let engine = Engine::new(&config).map_err(|e| format!("engine: {e}"))?;
    let module = Module::new(&engine, wasm).map_err(|e| format!("invalid module: {e}"))?;

    let mut linker: Linker<State<H>> = Linker::new(&engine);
    linker
        .func_wrap(
            "goat",
            "print_number",
            |mut caller: Caller<'_, State<H>>, x: f64| {
                caller.data_mut().output.write_line(&goat::format_number(x));
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
                    .write_line(goat::format_bool(b != 0));
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
                    .push_str(&goat::format_number(x));
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
            link_foreign(&mut linker, &host, import.module(), import.name(), ty)?;
        }
    }

    let mut store = Store::new(
        &engine,
        State {
            output: Output::default(),
            host,
            sites: site_table(wasm),
            stopped: None,
        },
    );
    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| format!("instantiate: {e}"))?;
    Ok((store, instance))
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
    let (mut store, instance) = instantiate(wasm, host)?;
    let entry = instance
        .get_typed_func::<(), ()>(&mut store, "goat_entry")
        .map_err(|e| format!("missing entry point: {e}"))?;
    let result = match entry.call(&mut store, ()) {
        Ok(()) => Ok(instance
            .get_typed_func::<(), u32>(&mut store, "goat_live_allocs")
            .and_then(|live| live.call(&mut store, ()))
            .map_err(|e| format!("goat_live_allocs: {e}"))?),
        Err(error) => Err(store.data_mut().stopped.take().unwrap_or_else(|| Stopped {
            message: format!("{error:#}"),
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
}

impl<H: Host + 'static> Guest<H> {
    pub fn new(wasm: &[u8], host: H) -> Result<Guest<H>, String> {
        let (store, instance) = instantiate(wasm, host)?;
        Ok(Guest { store, instance })
    }

    /// Call the export `name`; a trap is an error.
    pub fn call<P: wasmtime::WasmParams, R: wasmtime::WasmResults>(
        &mut self,
        name: &str,
        args: P,
    ) -> Result<R, String> {
        let func = self
            .instance
            .get_typed_func::<P, R>(&mut self.store, name)
            .map_err(|e| format!("{name}: {e}"))?;
        func.call(&mut self.store, args)
            .map_err(|e| format!("{name} trapped: {e:#}"))
    }

    /// Refill the module's fuel, as a host does before each update.
    pub fn set_fuel(&mut self, fuel: i32) -> Result<(), String> {
        let global = self
            .instance
            .get_global(&mut self.store, "goat_fuel")
            .ok_or("module exports no goat_fuel")?;
        global
            .set(&mut self.store, Val::I32(fuel))
            .map_err(|e| e.to_string())
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
