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

/// A runtime's entry points. WAMR fixes its interpreter when it is compiled, so
/// goat links two copies and picks one per module (ADR 0025): the fast
/// interpreter, and the classic one, whose symbols the build renames.
pub struct Api {
    pub init: unsafe extern "C" fn() -> bool,
    pub init_thread_env: unsafe extern "C" fn() -> bool,
    pub destroy_thread_env: unsafe extern "C" fn(),
    pub register_natives_raw: unsafe extern "C" fn(*const c_char, *mut NativeSymbol, u32) -> bool,
    pub load: unsafe extern "C" fn(*mut u8, u32, *mut c_char, u32) -> Module,
    pub unload: unsafe extern "C" fn(Module),
    pub instantiate: unsafe extern "C" fn(Module, u32, u32, *mut c_char, u32) -> Instance,
    pub deinstantiate: unsafe extern "C" fn(Instance),
    pub lookup_function: unsafe extern "C" fn(Instance, *const c_char) -> Function,
    pub create_exec_env: unsafe extern "C" fn(Instance, u32) -> ExecEnv,
    pub destroy_exec_env: unsafe extern "C" fn(ExecEnv),
    pub get_module_inst: unsafe extern "C" fn(ExecEnv) -> Instance,
    pub call_wasm: unsafe extern "C" fn(ExecEnv, Function, u32, *mut u32) -> bool,
    pub set_exception: unsafe extern "C" fn(Instance, *const c_char),
    pub get_exception: unsafe extern "C" fn(Instance) -> *const c_char,
    pub validate_app_addr: unsafe extern "C" fn(Instance, u64, u64) -> bool,
    pub addr_app_to_native: unsafe extern "C" fn(Instance, u64) -> *mut c_void,
    pub get_function_attachment: unsafe extern "C" fn(ExecEnv) -> *mut c_void,
    pub set_user_data: unsafe extern "C" fn(ExecEnv, *mut c_void),
    pub get_user_data: unsafe extern "C" fn(ExecEnv) -> *mut c_void,
}

mod fast {
    use super::*;

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
}

mod classic {
    use super::*;

    unsafe extern "C" {
        #[link_name = "goat_classic_wasm_runtime_init"]
        pub fn wasm_runtime_init() -> bool;
        #[link_name = "goat_classic_wasm_runtime_init_thread_env"]
        pub fn wasm_runtime_init_thread_env() -> bool;
        #[link_name = "goat_classic_wasm_runtime_destroy_thread_env"]
        pub fn wasm_runtime_destroy_thread_env();
        #[link_name = "goat_classic_wasm_runtime_register_natives_raw"]
        pub fn wasm_runtime_register_natives_raw(
            module_name: *const c_char,
            symbols: *mut NativeSymbol,
            count: u32,
        ) -> bool;
        #[link_name = "goat_classic_wasm_runtime_load"]
        pub fn wasm_runtime_load(
            buf: *mut u8,
            size: u32,
            error_buf: *mut c_char,
            error_buf_size: u32,
        ) -> Module;
        #[link_name = "goat_classic_wasm_runtime_unload"]
        pub fn wasm_runtime_unload(module: Module);
        #[link_name = "goat_classic_wasm_runtime_instantiate"]
        pub fn wasm_runtime_instantiate(
            module: Module,
            stack_size: u32,
            heap_size: u32,
            error_buf: *mut c_char,
            error_buf_size: u32,
        ) -> Instance;
        #[link_name = "goat_classic_wasm_runtime_deinstantiate"]
        pub fn wasm_runtime_deinstantiate(instance: Instance);
        #[link_name = "goat_classic_wasm_runtime_lookup_function"]
        pub fn wasm_runtime_lookup_function(instance: Instance, name: *const c_char) -> Function;
        #[link_name = "goat_classic_wasm_runtime_create_exec_env"]
        pub fn wasm_runtime_create_exec_env(instance: Instance, stack_size: u32) -> ExecEnv;
        #[link_name = "goat_classic_wasm_runtime_destroy_exec_env"]
        pub fn wasm_runtime_destroy_exec_env(env: ExecEnv);
        #[link_name = "goat_classic_wasm_runtime_get_module_inst"]
        pub fn wasm_runtime_get_module_inst(env: ExecEnv) -> Instance;
        #[link_name = "goat_classic_wasm_runtime_call_wasm"]
        pub fn wasm_runtime_call_wasm(
            env: ExecEnv,
            function: Function,
            argc: u32,
            argv: *mut u32,
        ) -> bool;
        #[link_name = "goat_classic_wasm_runtime_set_exception"]
        pub fn wasm_runtime_set_exception(instance: Instance, message: *const c_char);
        #[link_name = "goat_classic_wasm_runtime_get_exception"]
        pub fn wasm_runtime_get_exception(instance: Instance) -> *const c_char;
        #[link_name = "goat_classic_wasm_runtime_validate_app_addr"]
        pub fn wasm_runtime_validate_app_addr(instance: Instance, offset: u64, size: u64) -> bool;
        #[link_name = "goat_classic_wasm_runtime_addr_app_to_native"]
        pub fn wasm_runtime_addr_app_to_native(instance: Instance, offset: u64) -> *mut c_void;
        #[link_name = "goat_classic_wasm_runtime_get_function_attachment"]
        pub fn wasm_runtime_get_function_attachment(env: ExecEnv) -> *mut c_void;
        #[link_name = "goat_classic_wasm_runtime_set_user_data"]
        pub fn wasm_runtime_set_user_data(env: ExecEnv, data: *mut c_void);
        #[link_name = "goat_classic_wasm_runtime_get_user_data"]
        pub fn wasm_runtime_get_user_data(env: ExecEnv) -> *mut c_void;
    }
}

pub static FAST: Api = Api {
    init: fast::wasm_runtime_init,
    init_thread_env: fast::wasm_runtime_init_thread_env,
    destroy_thread_env: fast::wasm_runtime_destroy_thread_env,
    register_natives_raw: fast::wasm_runtime_register_natives_raw,
    load: fast::wasm_runtime_load,
    unload: fast::wasm_runtime_unload,
    instantiate: fast::wasm_runtime_instantiate,
    deinstantiate: fast::wasm_runtime_deinstantiate,
    lookup_function: fast::wasm_runtime_lookup_function,
    create_exec_env: fast::wasm_runtime_create_exec_env,
    destroy_exec_env: fast::wasm_runtime_destroy_exec_env,
    get_module_inst: fast::wasm_runtime_get_module_inst,
    call_wasm: fast::wasm_runtime_call_wasm,
    set_exception: fast::wasm_runtime_set_exception,
    get_exception: fast::wasm_runtime_get_exception,
    validate_app_addr: fast::wasm_runtime_validate_app_addr,
    addr_app_to_native: fast::wasm_runtime_addr_app_to_native,
    get_function_attachment: fast::wasm_runtime_get_function_attachment,
    set_user_data: fast::wasm_runtime_set_user_data,
    get_user_data: fast::wasm_runtime_get_user_data,
};

pub static CLASSIC: Api = Api {
    init: classic::wasm_runtime_init,
    init_thread_env: classic::wasm_runtime_init_thread_env,
    destroy_thread_env: classic::wasm_runtime_destroy_thread_env,
    register_natives_raw: classic::wasm_runtime_register_natives_raw,
    load: classic::wasm_runtime_load,
    unload: classic::wasm_runtime_unload,
    instantiate: classic::wasm_runtime_instantiate,
    deinstantiate: classic::wasm_runtime_deinstantiate,
    lookup_function: classic::wasm_runtime_lookup_function,
    create_exec_env: classic::wasm_runtime_create_exec_env,
    destroy_exec_env: classic::wasm_runtime_destroy_exec_env,
    get_module_inst: classic::wasm_runtime_get_module_inst,
    call_wasm: classic::wasm_runtime_call_wasm,
    set_exception: classic::wasm_runtime_set_exception,
    get_exception: classic::wasm_runtime_get_exception,
    validate_app_addr: classic::wasm_runtime_validate_app_addr,
    addr_app_to_native: classic::wasm_runtime_addr_app_to_native,
    get_function_attachment: classic::wasm_runtime_get_function_attachment,
    set_user_data: classic::wasm_runtime_set_user_data,
    get_user_data: classic::wasm_runtime_get_user_data,
};
