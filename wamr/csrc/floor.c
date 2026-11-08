/* Fails the build unless the runtime is configured with the feature floor goat's
   modules need (docs/adr/0019-on-device-wasm-runtime.md): `return_call` /
   `return_call_indirect` carry every loop, and `memory.fill` zeroes memory. A
   module using either does not load without its flag. config.h supplies the
   defaults for anything build.rs leaves out, so this sees the effective value. */
#include "config.h"

#if WASM_ENABLE_TAIL_CALL != 1
#error "goat_wamr needs WASM_ENABLE_TAIL_CALL=1 (WAMR_BUILD_TAIL_CALL)"
#endif

#if WASM_ENABLE_BULK_MEMORY != 1
#error "goat_wamr needs WASM_ENABLE_BULK_MEMORY=1 (WAMR_BUILD_BULK_MEMORY)"
#endif

#if WASM_ENABLE_FAST_INTERP != 1
#error "goat_wamr runs the WAMR fast interpreter"
#endif
