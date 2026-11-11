/* Calls the runtime entry points a board's firmware uses, so linking this
   proves the whole interpreter resolves against the board's C library. */
#include "wasm_export.h"

static char pool[64 * 1024];

int
main(void)
{
    RuntimeInitArgs args = { 0 };
    char error[128];
    args.mem_alloc_type = Alloc_With_Pool;
    args.mem_alloc_option.pool.heap_buf = pool;
    args.mem_alloc_option.pool.heap_size = sizeof(pool);
    if (!wasm_runtime_full_init(&args))
        return 1;
    wasm_module_t module = wasm_runtime_load((uint8_t *)pool, 0, error, sizeof(error));
    if (module)
        wasm_runtime_unload(module);
    wasm_runtime_destroy();
    return 0;
}
