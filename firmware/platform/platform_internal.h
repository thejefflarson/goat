#ifndef _PLATFORM_INTERNAL_H
#define _PLATFORM_INTERNAL_H

#include <inttypes.h>
#include <stdbool.h>
#include <assert.h>
#include <time.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdarg.h>
#include <ctype.h>
#include <limits.h>
#include <errno.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifndef BH_PLATFORM_GOAT_FIRMWARE
#define BH_PLATFORM_GOAT_FIRMWARE
#endif

#define BH_APPLET_PRESERVED_STACK_SIZE (2 * 1024)
#define BH_THREAD_DEFAULT_PRIORITY 0

/* One thread, so every lock is a no-op and these types only have to exist. */
typedef int korp_tid;
typedef int korp_mutex;
typedef int korp_cond;
typedef int korp_thread;
typedef int korp_rwlock;
typedef int korp_sem;

#define OS_THREAD_MUTEX_INITIALIZER 0

#define os_thread_local_attribute

#define bh_socket_t int

#define os_getpagesize() 4096

typedef int os_file_handle;
typedef void *os_dir_stream;
typedef int os_raw_file_handle;

static inline os_file_handle
os_get_invalid_handle(void)
{
    return -1;
}

#ifdef __cplusplus
}
#endif

#endif
