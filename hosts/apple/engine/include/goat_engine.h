/*
 * goat_engine.h: the seam between the Apple apps and the goat engine
 * (ADR 0043). One engine runs one program at a time, on a worker thread of its
 * own, so no function here waits for the program.
 *
 * Messages come back through three callbacks. All of them run on one thread
 * belonging to the engine, one at a time. Messages arrive in the order they
 * were sent, except that a frame that has not been
 * delivered yet is dropped when a newer one arrives.
 *
 * Control messages are the JSON that GoatKit's EngineMessage decodes:
 *
 *   {"type":"ready"}
 *   {"type":"diagnostics","diagnostics":[{"line":1,"column":1,"length":3,"message":"..."}]}
 *   {"type":"output","lines":["..."]}
 *   {"type":"state","state":"running"|"finished"|"failed","message":"..."}
 *
 * and one more, sent when a program is run while an interactive program is
 * live and the new one replaces it in place (ADR 0035):
 *
 *   {"type":"reloaded","outcome":"kept"}
 *   {"type":"reloaded","outcome":"reset","reason":{"kind":"field_added","args":["z"]}}
 *
 * A frame is the bytes of one scene.frame (mir/src/frame.rs), the whole
 * picture, drawn over a 400 by 300 canvas. A run-once turtle program is
 * delivered as frames too: its drawing, a few segments at a time.
 *
 * Pointer positions are in the canvas's own 400 by 300 coordinates.
 */
#ifndef GOAT_ENGINE_H
#define GOAT_ENGINE_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct goat_engine goat_engine;

enum {
    GOAT_POINTER_MOVE = 0,
    GOAT_POINTER_DOWN = 1,
    GOAT_POINTER_UP = 2,
};

typedef struct {
    /* Handed back to every callback. It must stay valid until `closed` returns. */
    void *context;
    /* One control message, as UTF-8 JSON with no terminator. `json` is valid only during the call. */
    void (*control)(void *context, const uint8_t *json, size_t len);
    /* One frame. `bytes` is valid only during the call. */
    void (*frame)(void *context, const uint8_t *bytes, size_t len);
    /* The engine has been freed; this is the last callback. */
    void (*closed)(void *context);
} goat_engine_callbacks;

/* Starts an engine. It sends "ready" once it can run programs. */
goat_engine *goat_engine_new(goat_engine_callbacks callbacks);

/*
 * Compiles and runs UTF-8 `source`. While an interactive program is live, an
 * interactive `source` reloads it instead, and a program with errors leaves it
 * running and sends only diagnostics. A program that traps, or runs longer
 * than its budget (1 second for a frame, 10 seconds for setup, a reload or a
 * run-once program), is stopped with a failed state; the next run starts clean.
 */
void goat_engine_run(const goat_engine *engine, const uint8_t *source, size_t len);

/* Stops the program. */
void goat_engine_stop(const goat_engine *engine);

/* A key press or release; `key` is UTF-8 named as KeyboardEvent.key names it. */
void goat_engine_key(const goat_engine *engine, const uint8_t *key, size_t len, bool down);

/* `kind` is one of GOAT_POINTER_*; any other value is ignored. */
void goat_engine_pointer(const goat_engine *engine, uint32_t kind, double x, double y);

/*
 * Stops the program and frees the engine. `closed` is called once before this
 * returns, and no callback runs after it. It waits for a callback already in
 * flight, so never call it from inside a callback.
 */
void goat_engine_free(goat_engine *engine);

#ifdef __cplusplus
}
#endif

#endif
