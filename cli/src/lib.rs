//! The wasmtime host that runs compiled goat modules, shared by the `goat`
//! binary and the differential tests.

use wasmtime::{Caller, Config, Engine, Linker, Module, Store};

/// Instantiate `wasm` under wasmtime, run its entry export, and return the
/// lines the program printed. A trap becomes an error.
pub fn execute(wasm: &[u8]) -> Result<Vec<String>, String> {
    let mut config = Config::new();
    config.wasm_tail_call(true);
    let engine = Engine::new(&config).map_err(|e| format!("engine: {e}"))?;
    let module = Module::new(&engine, wasm).map_err(|e| format!("invalid module: {e}"))?;

    let mut linker: Linker<Vec<String>> = Linker::new(&engine);
    linker
        .func_wrap(
            "goat",
            "print_number",
            |mut caller: Caller<'_, Vec<String>>, x: f64| {
                caller.data_mut().push(goat::format_number(x));
            },
        )
        .map_err(|e| e.to_string())?;
    linker
        .func_wrap(
            "goat",
            "print_bool",
            |mut caller: Caller<'_, Vec<String>>, b: i32| {
                caller
                    .data_mut()
                    .push(goat::format_bool(b != 0).to_string());
            },
        )
        .map_err(|e| e.to_string())?;

    let mut store = Store::new(&engine, Vec::new());
    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| format!("instantiate: {e}"))?;
    let entry = instance
        .get_typed_func::<(), ()>(&mut store, "goat_entry")
        .map_err(|e| format!("missing entry point: {e}"))?;
    entry
        .call(&mut store, ())
        .map_err(|e| format!("trap: {e}"))?;
    Ok(store.into_data())
}
