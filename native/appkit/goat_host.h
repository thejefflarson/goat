#ifndef GOAT_HOST_H
#define GOAT_HOST_H

#include <stdint.h>

/* What a window host sees of goat: the exports of a compiled interactive
   program, and the session that runs them (native/src/session.rs). */

typedef struct GoatSession GoatSession;

typedef struct {
    const char *label;
    const void *constructor;
} GoatEvent;

typedef struct {
    int32_t (*attach)(const void *, void *, void *);
    void *(*setup)(const void *, void *, void *);
    void *(*update)(const void *, void *, void *, void *, void *);
    void (*draw)(const void *, void *, void *, void *);
    void *(*alloc)(const void *, void *, void *, uint32_t);
    const GoatEvent *events;
    uint64_t event_count;
} GoatProgram;

enum { GOAT_STOP_TRAP = 0, GOAT_STOP_STUCK = 1 };

typedef struct {
    void *user;
    void (*frame)(void *user, const uint8_t *bytes, uint64_t len);
    void (*stopped)(void *user, int32_t reason, const uint8_t *message, uint64_t len);
} GoatCallbacks;

/* The program and its source, defined by the entry code that goat build writes. */
typedef struct {
    const uint8_t *bytes;
    uint64_t len;
} GoatSource;

extern const GoatProgram goat_program;
extern const GoatSource goat_source;

GoatSession *goat_session_start(const GoatProgram *program, const uint8_t *source,
                                uint64_t source_len, const GoatCallbacks *callbacks);
void goat_session_key(const GoatSession *session, int32_t down, const uint8_t *key, uint64_t len);
void goat_session_pointer(const GoatSession *session, int32_t kind, double x, double y);
void goat_session_free(GoatSession *session);

#endif
