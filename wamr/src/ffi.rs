//! The slice of WAMR's embedding API (`wasm_export.h`) that the driver calls.
//! Handles are opaque; the build compiles the C these declarations bind to.

use std::ffi::{c_char, c_void};

pub type Module = *mut c_void;
pub type Instance = *mut c_void;
pub type ExecEnv = *mut c_void;
pub type Function = *mut c_void;

/// `NativeSymbol`: a host function registered under a module name.
#[repr(C)]
pub struct NativeSymbol {
    pub symbol: *const c_char,
    pub func_ptr: *mut c_void,
    pub signature: *const c_char,
    pub attachment: *mut c_void,
}

/// A `wasm_runtime_register_natives_raw` host function: every argument is one
/// `u64` slot, and a result goes back in slot 0.
pub type RawNative = unsafe extern "C" fn(ExecEnv, *mut u64);

unsafe extern "C" {
    pub fn wasm_runtime_init() -> bool;
    pub fn wasm_runtime_init_thread_env() -> bool;
    pub fn wasm_runtime_destroy_thread_env();
    pub fn wasm_runtime_register_natives_raw(
        module_name: *const c_char,
        symbols: *mut NativeSymbol,
        count: u32,
    ) -> bool;
    pub fn wasm_runtime_load(
        buf: *mut u8,
        size: u32,
        error_buf: *mut c_char,
        error_buf_size: u32,
    ) -> Module;
    pub fn wasm_runtime_unload(module: Module);
    pub fn wasm_runtime_instantiate(
        module: Module,
        stack_size: u32,
        heap_size: u32,
        error_buf: *mut c_char,
        error_buf_size: u32,
    ) -> Instance;
    pub fn wasm_runtime_deinstantiate(instance: Instance);
    pub fn wasm_runtime_lookup_function(instance: Instance, name: *const c_char) -> Function;
    pub fn wasm_runtime_create_exec_env(instance: Instance, stack_size: u32) -> ExecEnv;
    pub fn wasm_runtime_destroy_exec_env(env: ExecEnv);
    pub fn wasm_runtime_get_module_inst(env: ExecEnv) -> Instance;
    pub fn wasm_runtime_call_wasm(
        env: ExecEnv,
        function: Function,
        argc: u32,
        argv: *mut u32,
    ) -> bool;
    pub fn wasm_runtime_set_exception(instance: Instance, message: *const c_char);
    pub fn wasm_runtime_get_exception(instance: Instance) -> *const c_char;
    pub fn wasm_runtime_validate_app_addr(instance: Instance, offset: u64, size: u64) -> bool;
    pub fn wasm_runtime_addr_app_to_native(instance: Instance, offset: u64) -> *mut c_void;
    pub fn wasm_runtime_get_function_attachment(env: ExecEnv) -> *mut c_void;
    pub fn wasm_runtime_set_user_data(env: ExecEnv, data: *mut c_void);
    pub fn wasm_runtime_get_user_data(env: ExecEnv) -> *mut c_void;
}
