#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// Writes the timing report as UTF-8 into out[0..cap] and returns the bytes
// written. Call it once, from the main thread, with pulley true or false.
size_t goat_pulley_bench(bool pulley, uint8_t *out, size_t cap);
