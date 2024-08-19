// This file is a part of Julia. License is MIT: https://julialang.org/license

#ifndef THREADING_H
#define THREADING_H

#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

#include "julia.h"

#define PROFILE_JL_THREADING            0

extern uv_barrier_t thread_init_done;

extern _Atomic(jl_ptls_t*) jl_all_tls_states JL_GLOBALLY_ROOTED; /* thread local storage */

typedef struct _jl_threadarg_t {
    int16_t tid;
    uv_barrier_t *barrier;
    void *arg;
} jl_threadarg_t;

// each thread must initialize its TLS
jl_ptls_t jl_init_threadtls(int16_t tid) JL_NOTSAFEPOINT;

// provided by a threading infrastructure
void jl_init_threadinginfra(void);
void jl_parallel_gc_threadfun(void *arg);
void jl_concurrent_gc_threadfun(void *arg);
void jl_threadfun(void *arg);

extern JL_DLLIMPORT _Atomic(jl_task_t*) jl_interrupt_handler JL_GLOBALLY_ROOTED;
extern JL_DLLIMPORT uintptr_t jl_interrupt_handler_condition;
extern JL_DLLIMPORT _Atomic(int) jl_global_defer_signal;

#ifdef __cplusplus
}
#endif

#endif  /* THREADING_H */
