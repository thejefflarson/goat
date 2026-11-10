//! Run compiled goat modules under WAMR, the runtime goat targets on boards
//! (ADR 0019): the fast interpreter, or the classic one for a module the fast
//! one cannot load (ADR 0025). This is a conformance driver (ADR 0018): it
//! takes the same [`Host`] and returns the same [`Finished`] as the wasmtime
//! driver in `goat::native`, so one suite checks both. Native only; the C
//! build keeps it out of the compiler's wasm32 crates.

use std::ffi::{CStr, CString, c_char, c_void};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Mutex;

use goat::{Boundary, Host, HostValue};
use wasmparser::ValType;

mod ffi;
mod imports;
mod limits;

use ffi::Api;
pub use limits::{FAST_INTERP_CELL_LIMIT, interp_for};

pub use goat::NoHost;
pub use goat::native::{Finished, Run, Stopped};

/// Where a string object keeps its length and its bytes (`docs/mir.md`).
const STR_LEN: u64 = 8;
const STR_BYTES: u64 = 12;

/// WAMR's operand stack for the program, in bytes.
const STACK_SIZE: u32 = 8 << 20;

const ERROR_LEN: usize = 256;

/// Slots WAMR always provides to a host function: one per parameter, 16 at
/// least.
const MIN_SLOTS: usize = 16;

/// Every host function registered with WAMR so far. WAMR links imports by
/// `(module, name)` from one process-wide list, so each pair registers once
/// and its index here is its attachment. The lock also serializes loading,
/// because registering edits that list.
static FAST_REGISTRY: Mutex<Registry> = Mutex::new(Registry::new(Interp::Fast));
static CLASSIC_REGISTRY: Mutex<Registry> = Mutex::new(Registry::new(Interp::Classic));

/// Which copy of the WAMR runtime runs a module (ADR 0025).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Interp {
    Fast,
    Classic,
}

impl Interp {
    fn api(self) -> &'static Api {
        match self {
            Interp::Fast => &ffi::FAST,
            Interp::Classic => &ffi::CLASSIC,
        }
    }

    fn registry(self) -> &'static Mutex<Registry> {
        match self {
            Interp::Fast => &FAST_REGISTRY,
            Interp::Classic => &CLASSIC_REGISTRY,
        }
    }
}

struct Registry {
    interp: Interp,
    started: bool,
    natives: Vec<(String, String)>,
}

impl Registry {
    const fn new(interp: Interp) -> Self {
        Registry {
            interp,
            started: false,
            natives: Vec::new(),
        }
    }

    fn start(&mut self) -> Result<(), String> {
        if !self.started {
            // SAFETY: the first WAMR call in the process, under the lock.
            if !unsafe { (self.interp.api().init)() } {
                return Err("wamr: runtime init failed".into());
            }
            self.started = true;
        }
        Ok(())
    }

    /// The id `module.name` is registered under, registering it if new.
    fn id(&mut self, module: &str, name: &str) -> Result<usize, String> {
        if let Some(id) = self
            .natives
            .iter()
            .position(|(m, n)| m == module && n == name)
        {
            return Ok(id);
        }
        let id = self.natives.len();
        let c_module = CString::new(module).map_err(|e| e.to_string())?;
        let c_name = CString::new(name).map_err(|e| e.to_string())?;
        let symbol = Box::new(ffi::NativeSymbol {
            symbol: c_name.into_raw(),
            func_ptr: match self.interp {
                Interp::Fast => trampoline::<false> as ffi::RawNative,
                Interp::Classic => trampoline::<true> as ffi::RawNative,
            } as *mut c_void,
            // Empty: WAMR neither checks nor rewrites the arguments, and one
            // registration serves whatever type a module gives the import.
            signature: c"".as_ptr(),
            attachment: id as *mut c_void,
        });
        // SAFETY: WAMR keeps these pointers for the life of the process, so
        // none of them is ever freed.
        let registered = unsafe {
            (self.interp.api().register_natives_raw)(c_module.into_raw(), Box::into_raw(symbol), 1)
        };
        if !registered {
            return Err(format!("wamr: cannot register {module}.{name}"));
        }
        self.natives.push((module.to_string(), name.to_string()));
        Ok(id)
    }
}

/// One import of the module being run: its wasm type, and for a `foreign`
/// function the goat types the host declared for it.
struct Signature {
    module: String,
    name: String,
    params: Vec<ValType>,
    result: Option<ValType>,
    foreign: Option<(Vec<Boundary>, Boundary)>,
}

/// The lines the program has printed, and the one it is still writing.
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

struct Session<H> {
    api: &'static Api,
    output: Output,
    host: H,
    /// The module's imports, indexed by registry id.
    signatures: Vec<Option<Signature>>,
    stopped: Option<Stopped>,
}

/// A `Session` without its host type, which is all WAMR's user data can hold.
trait Dispatch {
    fn call(&mut self, env: ffi::ExecEnv, id: usize, slots: &mut [u64]) -> Result<(), String>;
}

impl<H: Host> Dispatch for Session<H> {
    fn call(&mut self, env: ffi::ExecEnv, id: usize, slots: &mut [u64]) -> Result<(), String> {
        let Session {
            api,
            output,
            host,
            signatures,
            stopped,
        } = self;
        let Some(Some(sig)) = signatures.get(id) else {
            return Err("host call to an import this module does not have".into());
        };
        let result = if sig.module == "goat" {
            runtime_call(api, output, sig, env, slots)
        } else {
            foreign_call(api, host, sig, env, slots)
        };
        if let Err(message) = &result {
            stopped.get_or_insert_with(|| Stopped {
                message: message.clone(),
                site: None,
            });
        }
        result
    }
}

/// The one host function WAMR calls, for every import of every module.
unsafe extern "C" fn trampoline<const CLASSIC: bool>(env: ffi::ExecEnv, slots: *mut u64) {
    let api = if CLASSIC { &ffi::CLASSIC } else { &ffi::FAST };
    // SAFETY: `run_to_end` keeps a live `&mut dyn Dispatch` as the user data
    // for as long as the module can call out.
    let (dispatch, id) = unsafe {
        let user = (api.get_user_data)(env).cast::<&mut dyn Dispatch>();
        (&mut **user, (api.get_function_attachment)(env) as usize)
    };
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: WAMR passes a buffer of at least `MIN_SLOTS`.
        let slots = unsafe { std::slice::from_raw_parts_mut(slots, MIN_SLOTS) };
        dispatch.call(env, id, slots)
    }));
    let failure = match outcome {
        Ok(Ok(())) => return,
        Ok(Err(message)) => message,
        Err(_) => "host function panicked".to_string(),
    };
    let message = CString::new(failure).unwrap_or_else(|_| c"host error".into());
    // SAFETY: `env` is the live environment WAMR called us with.
    unsafe {
        let instance = (api.get_module_inst)(env);
        (api.set_exception)(instance, message.as_ptr());
    }
}

fn as_i64(ty: ValType, slot: u64) -> i64 {
    match ty {
        ValType::I32 => i64::from(slot as u32 as i32),
        _ => slot as i64,
    }
}

fn as_f64(ty: ValType, slot: u64) -> f64 {
    match ty {
        ValType::F32 => f64::from(f32::from_bits(slot as u32)),
        _ => f64::from_bits(slot),
    }
}

fn from_i64(ty: ValType, n: i64) -> u64 {
    match ty {
        ValType::I32 => u64::from(n as i32 as u32),
        _ => n as u64,
    }
}

fn from_f64(ty: ValType, x: f64) -> u64 {
    match ty {
        ValType::F32 => u64::from((x as f32).to_bits()),
        _ => x.to_bits(),
    }
}

/// A call to one of the `goat.*` imports every module may have.
fn runtime_call(
    api: &Api,
    output: &mut Output,
    sig: &Signature,
    env: ffi::ExecEnv,
    slots: &[u64],
) -> Result<(), String> {
    let arg = || {
        sig.params
            .first()
            .map(|&ty| (ty, slots[0]))
            .ok_or_else(|| format!("goat.{} takes an argument", sig.name))
    };
    let int = || arg().map(|(ty, slot)| as_i64(ty, slot));
    let number = || arg().map(|(ty, slot)| as_f64(ty, slot));
    let string = || arg().and_then(|(_, slot)| read_string(api, env, slot as u32));
    match sig.name.as_str() {
        "print_number" => output.write_line(&goat::format_number(number()?)),
        "print_bool" => output.write_line(goat::format_bool(int()? != 0)),
        "print_int" => output.write_line(&int()?.to_string()),
        "print_string" => output.write_line(&string()?),
        "write_number" => output.line.push_str(&goat::format_number(number()?)),
        "write_int" => output.line.push_str(&int()?.to_string()),
        "write_string" => output.line.push_str(&string()?),
        "write_end" => output.finish(),
        "trap" => return Err(string()?),
        other => return Err(format!("unknown runtime import goat.{other}")),
    }
    Ok(())
}

/// A call to a `foreign` function the program imports: wasm values in,
/// `HostValue`s to the host, its result back out through `slots[0]`.
fn foreign_call<H: Host>(
    api: &Api,
    host: &mut H,
    sig: &Signature,
    env: ffi::ExecEnv,
    slots: &mut [u64],
) -> Result<(), String> {
    let (module, name) = (&sig.module, &sig.name);
    let (kinds, ret) = sig.foreign.as_ref().ok_or("not a host function")?;
    let mut values = Vec::with_capacity(kinds.len());
    for (kind, (&ty, &slot)) in kinds.iter().zip(sig.params.iter().zip(slots.iter())) {
        values.push(match kind {
            Boundary::Number => HostValue::Number(as_f64(ty, slot)),
            Boundary::Int => HostValue::Int(as_i64(ty, slot)),
            Boundary::Bool => HostValue::Bool(slot as u32 != 0),
            Boundary::Unit => HostValue::Unit,
            Boundary::Str => HostValue::Str(read_string(api, env, slot as u32)?),
        });
    }
    let returned = host.call(module, name, &values)?;
    slots[0] = match (ret, returned, sig.result) {
        (Boundary::Number, HostValue::Number(x), Some(ty)) => from_f64(ty, x),
        (Boundary::Int, HostValue::Int(n), Some(ty)) => from_i64(ty, n),
        (Boundary::Bool, HostValue::Bool(b), Some(_)) => u64::from(b),
        (Boundary::Unit, HostValue::Unit, None) => return Ok(()),
        (Boundary::Str, HostValue::Str(text), Some(_)) => u64::from(alloc_string(api, env, &text)?),
        _ => {
            return Err(format!(
                "{module}.{name} returned a value of the wrong type"
            ));
        }
    };
    Ok(())
}

/// The guest memory range `[offset, offset + len)`, which must lie inside it.
fn guest_range(api: &Api, env: ffi::ExecEnv, offset: u64, len: u64) -> Result<*mut u8, String> {
    // SAFETY: `env` is live; the range is validated before it is converted.
    unsafe {
        let instance = (api.get_module_inst)(env);
        if !(api.validate_app_addr)(instance, offset, len) {
            return Err("string out of bounds".into());
        }
        Ok((api.addr_app_to_native)(instance, offset).cast())
    }
}

fn read_string(api: &Api, env: ffi::ExecEnv, ptr: u32) -> Result<String, String> {
    let at = u64::from(ptr);
    let len_at = guest_range(api, env, at + STR_LEN, 4)?;
    // SAFETY: the range was validated just above, and nothing runs between.
    let len = u64::from(u32::from_le_bytes(unsafe {
        len_at.cast::<[u8; 4]>().read()
    }));
    let bytes = guest_range(api, env, at + STR_BYTES, len)?;
    // SAFETY: as above.
    let bytes = unsafe { std::slice::from_raw_parts(bytes, len as usize) };
    Ok(String::from_utf8_lossy(bytes).into_owned())
}

fn write_guest(api: &Api, env: ffi::ExecEnv, offset: u64, bytes: &[u8]) -> Result<(), String> {
    let to = guest_range(api, env, offset, bytes.len() as u64)?;
    // SAFETY: the range was validated just above, and `bytes` is host memory.
    unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), to, bytes.len()) };
    Ok(())
}

/// A string object holding `text`, made in the module's own heap through its
/// exported `goat_alloc`, which hands it over with count 1: goat owns it.
fn alloc_string(api: &Api, env: ffi::ExecEnv, text: &str) -> Result<u32, String> {
    let too_long = |_| "string too long".to_string();
    let len = u32::try_from(text.len()).map_err(too_long)?;
    let size = u32::try_from(STR_BYTES as usize + text.len()).map_err(too_long)?;
    let mut argv = [size];
    call_export(api, env, c"goat_alloc", 1, &mut argv)?;
    let at = u64::from(argv[0]);
    write_guest(api, env, at + STR_LEN, &len.to_le_bytes())?;
    write_guest(api, env, at + STR_BYTES, text.as_bytes())?;
    Ok(argv[0])
}

/// Call the module's export `name` in the running environment. `argv` holds
/// the `argc` arguments going in and the results coming out.
fn call_export(
    api: &Api,
    env: ffi::ExecEnv,
    name: &CStr,
    argc: u32,
    argv: &mut [u32],
) -> Result<(), String> {
    // SAFETY: `env` is live and `argv` outlasts the call.
    unsafe {
        let instance = (api.get_module_inst)(env);
        let function = (api.lookup_function)(instance, name.as_ptr());
        if function.is_null() {
            return Err(format!("module exports no {}", name.to_string_lossy()));
        }
        if (api.call_wasm)(env, function, argc, argv.as_mut_ptr()) {
            return Ok(());
        }
        let message = (api.get_exception)(instance);
        Err(if message.is_null() {
            "unknown trap".into()
        } else {
            CStr::from_ptr(message).to_string_lossy().into_owned()
        })
    }
}

/// A loaded, instantiated module and the environment that runs it.
struct Loaded {
    api: &'static Api,
    module: ffi::Module,
    instance: ffi::Instance,
    env: ffi::ExecEnv,
    /// WAMR reads the module's bytes for as long as the module lives.
    _wasm: Vec<u8>,
}

impl Drop for Loaded {
    fn drop(&mut self) {
        let api = self.api;
        // SAFETY: each handle came from its create call and is released once,
        // in reverse order.
        unsafe {
            (api.destroy_exec_env)(self.env);
            (api.deinstantiate)(self.instance);
            (api.unload)(self.module);
        }
    }
}

fn error_text(buf: &[c_char; ERROR_LEN]) -> String {
    // SAFETY: WAMR NUL-terminates what it writes, and the buffer starts zeroed.
    unsafe { CStr::from_ptr(buf.as_ptr()) }
        .to_string_lossy()
        .into_owned()
}

/// Register the host functions `wasm` imports, then load and instantiate it.
fn load<H: Host>(
    interp: Interp,
    wasm: &[u8],
    host: &H,
) -> Result<(Loaded, Vec<Option<Signature>>), String> {
    let api = interp.api();
    let imports = imports::function_imports(wasm)?;
    let mut registry = interp.registry().lock().unwrap_or_else(|e| e.into_inner());
    registry.start()?;
    let mut ids = Vec::with_capacity(imports.len());
    for import in &imports {
        ids.push(registry.id(&import.module, &import.name)?);
    }
    let mut signatures: Vec<Option<Signature>> =
        (0..registry.natives.len()).map(|_| None).collect();
    for (import, id) in imports.into_iter().zip(ids) {
        let foreign = match import.module.as_str() {
            "goat" => None,
            module => Some(host.signature(module, &import.name).ok_or_else(|| {
                format!("the host provides no function {module}.{}", import.name)
            })?),
        };
        signatures[id] = Some(Signature {
            module: import.module,
            name: import.name,
            params: import.params,
            result: import.result,
            foreign,
        });
    }

    let mut wasm = wasm.to_vec();
    let size = u32::try_from(wasm.len()).map_err(|_| "module too large".to_string())?;
    let mut error = [0 as c_char; ERROR_LEN];
    let error_len = ERROR_LEN as u32;
    // SAFETY: `wasm` moves into the returned `Loaded`, which outlives the module.
    let module = unsafe { (api.load)(wasm.as_mut_ptr(), size, error.as_mut_ptr(), error_len) };
    if module.is_null() {
        return Err(format!("invalid module: {}", error_text(&error)));
    }
    // SAFETY: `module` is live; each failure path below unloads what it made.
    let instance =
        unsafe { (api.instantiate)(module, STACK_SIZE, 0, error.as_mut_ptr(), error_len) };
    if instance.is_null() {
        unsafe { (api.unload)(module) };
        return Err(format!("instantiate: {}", error_text(&error)));
    }
    let env = unsafe { (api.create_exec_env)(instance, STACK_SIZE) };
    if env.is_null() {
        unsafe {
            (api.deinstantiate)(instance);
            (api.unload)(module);
        }
        return Err("wamr: cannot create an execution environment".into());
    }
    let loaded = Loaded {
        api,
        module,
        instance,
        env,
        _wasm: wasm,
    };
    Ok((loaded, signatures))
}

/// Instantiate `wasm` under WAMR, run its entry export against `host`, and
/// return everything it printed. A halt keeps what the program printed before
/// it, including a line it had started. The interpreter is the fast one unless
/// the module has a function past its cell limit ([`interp_for`]).
pub fn run_to_end<H: Host>(wasm: &[u8], host: H) -> Result<Finished<H>, String> {
    run_to_end_on(interp_for(wasm)?, wasm, host)
}

/// Like [`run_to_end`], on the interpreter the caller names.
pub fn run_to_end_on<H: Host>(interp: Interp, wasm: &[u8], host: H) -> Result<Finished<H>, String> {
    let api = interp.api();
    let (loaded, signatures) = load(interp, wasm, &host)?;
    let mut session = Session {
        api,
        output: Output::default(),
        host,
        signatures,
        stopped: None,
    };

    // SAFETY: paired with the destroy below.
    if !unsafe { (api.init_thread_env)() } {
        return Err("wamr: cannot initialize the thread".into());
    }
    let outcome = {
        let mut dispatch: &mut dyn Dispatch = &mut session;
        // SAFETY: `dispatch` outlives every call into the module below.
        unsafe {
            (api.set_user_data)(loaded.env, (&raw mut dispatch).cast::<c_void>());
        }
        call_export(api, loaded.env, c"goat_entry", 0, &mut []).and_then(|()| {
            let mut live = [0u32];
            call_export(api, loaded.env, c"goat_live_allocs", 0, &mut live)
                .map(|()| live[0])
                .map_err(|e| format!("goat_live_allocs: {e}"))
        })
    };
    // SAFETY: pairs the init above.
    unsafe { (api.destroy_thread_env)() };
    drop(loaded);

    let Session {
        mut output,
        host,
        stopped,
        ..
    } = session;
    let result = outcome.map_err(|message| {
        stopped.unwrap_or(Stopped {
            message,
            site: None,
        })
    });
    if result.is_err() && !output.line.is_empty() {
        output.finish();
    }
    Ok(Finished {
        printed: output.lines,
        host,
        result,
    })
}

/// Like [`run_to_end`], with a halt turned into an error, as the wasmtime
/// driver's `run_with_host` does.
pub fn run_with_host<H: Host>(wasm: &[u8], host: H) -> Result<(Run, H), String> {
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

/// Like [`run_with_host`], for a program that calls nothing foreign.
pub fn run(wasm: &[u8]) -> Result<Run, String> {
    run_with_host(wasm, NoHost).map(|(run, _)| run)
}
