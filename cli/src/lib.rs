//! The wasmtime host that runs compiled goat modules, shared by the `goat`
//! binary and the differential tests.

use wasmtime::{Caller, Config, Engine, Linker, Module, Store};

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

/// Instantiate `wasm` under wasmtime, run its entry export, and return the
/// lines the program printed. A trap becomes an error.
pub fn execute(wasm: &[u8]) -> Result<Vec<String>, String> {
    run(wasm).map(|run| run.printed)
}

/// The text of the goat string at `ptr` in the module's memory.
fn read_string(caller: &mut Caller<'_, Output>, ptr: i32) -> wasmtime::Result<String> {
    let memory = caller
        .get_export("memory")
        .and_then(|e| e.into_memory())
        .ok_or_else(|| wasmtime::Error::msg("module exports no memory"))?;
    let data = memory.data(&*caller);
    let ptr = ptr as u32 as usize;
    let oob = || wasmtime::Error::msg("string out of bounds");
    let len_bytes = data.get(ptr + 8..ptr + 12).ok_or_else(oob)?;
    let len = u32::from_le_bytes(len_bytes.try_into().unwrap()) as usize;
    let bytes = data.get(ptr + 12..ptr + 12 + len).ok_or_else(oob)?;
    Ok(String::from_utf8_lossy(bytes).into_owned())
}

/// Like `execute`, but also reads the allocator's live-allocation count.
pub fn run(wasm: &[u8]) -> Result<Run, String> {
    let mut config = Config::new();
    config.wasm_tail_call(true);
    let engine = Engine::new(&config).map_err(|e| format!("engine: {e}"))?;
    let module = Module::new(&engine, wasm).map_err(|e| format!("invalid module: {e}"))?;

    let mut linker: Linker<Output> = Linker::new(&engine);
    linker
        .func_wrap(
            "goat",
            "print_number",
            |mut caller: Caller<'_, Output>, x: f64| {
                caller.data_mut().write_line(&goat::format_number(x));
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "print_bool",
            |mut caller: Caller<'_, Output>, b: i32| {
                caller.data_mut().write_line(goat::format_bool(b != 0));
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "print_string",
            |mut caller: Caller<'_, Output>, ptr: i32| -> wasmtime::Result<()> {
                let text = read_string(&mut caller, ptr)?;
                caller.data_mut().write_line(&text);
                Ok(())
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "write_number",
            |mut caller: Caller<'_, Output>, x: f64| {
                caller.data_mut().line.push_str(&goat::format_number(x));
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "write_string",
            |mut caller: Caller<'_, Output>, ptr: i32| -> wasmtime::Result<()> {
                let text = read_string(&mut caller, ptr)?;
                caller.data_mut().line.push_str(&text);
                Ok(())
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap("goat", "write_end", |mut caller: Caller<'_, Output>| {
            caller.data_mut().finish();
        })
        .map_err(|e| e.to_string())?;

    let mut store = Store::new(&engine, Output::default());
    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| format!("instantiate: {e}"))?;
    let entry = instance
        .get_typed_func::<(), ()>(&mut store, "goat_entry")
        .map_err(|e| format!("missing entry point: {e}"))?;
    entry
        .call(&mut store, ())
        .map_err(|e| format!("trap: {e}"))?;
    let live_allocs = instance
        .get_typed_func::<(), u32>(&mut store, "goat_live_allocs")
        .and_then(|live| live.call(&mut store, ()))
        .map_err(|e| format!("goat_live_allocs: {e}"))?;
    Ok(Run {
        printed: store.into_data().lines,
        live_allocs,
    })
}
