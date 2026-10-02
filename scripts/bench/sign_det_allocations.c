/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Operation-scoped allocation requests for a pure sign-determination callback.
Use Valgrind DHAT ad-hoc mode, not its ordinary heap mode: Lean's small-object
fast path bypasses malloc. Wrap the Lean allocation entry points and direct
mimalloc/GMP client requests; exclude nested wrapped calls with a thread-local
counter. Units are requested bytes (rounded sizes at the small-object boundary),
not live memory, allocator arena traffic or instrumented running times.

Define SIGN_DET_CALLBACK to the exact generated C symbol for the measured
single-threaded callback. Verify that symbol and its one-object argument/result
ABI against generated C before building. The default is Joint.runComparison.
The stderr JSON record reports callback invocations and per-allocator totals;
DHAT also retains weighted events with stacks, even when those stacks truncate.
Counters are enabled by entry/exit wrapping, so preparation outside the callback
is excluded without relying on stack matching.

Build with -DSIGN_DET_CHECK as an executable and run under DHAT ad-hoc mode.
The controlled fixture must report 280 units in six events and one callback;
its out-of-operation allocation and nested wrapped calls must not add events.
This is a coverage probe, not a claim that every possible allocator is wrapped.
Audit direct and inlined allocation paths in the actual measured executable.
*/
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <valgrind/valgrind.h>
#include <valgrind/dhat.h>

#ifndef SIGN_DET_CALLBACK
#define SIGN_DET_CALLBACK lp_Hex_Hex_SignDetBench_Joint_runComparison
#endif
#ifndef SIGN_DET_RESULT
#define SIGN_DET_RESULT void *
#endif
#define CALLBACK_WRAPPER(name) I_WRAP_SONAME_FNNAME_ZU(NONE, name)
static __thread unsigned depth;
static __thread unsigned active;
static unsigned long long requests[3], bytes[3], callbacks;
static int overflow;

static __attribute__((always_inline)) inline void record(unsigned kind, size_t n) {
    if (!active) return;
    if (bytes[kind] > UINT64_MAX - n || requests[kind] == UINT64_MAX) overflow = 1;
    else { bytes[kind] += n; ++requests[kind]; }
    DHAT_AD_HOC_EVENT(n);
}
#define WRAP1(name, type, kind) \
void *I_WRAP_SONAME_FNNAME_ZU(NONE, name)(type n) { \
    OrigFn fn; void *p; unsigned outer = depth++ == 0; \
    VALGRIND_GET_ORIG_FN(fn); CALL_FN_W_W(p, fn, n); \
    --depth; if (outer && p) record(kind, n); return p; \
}
WRAP1(lean_alloc_small_object_core, unsigned, 0)
WRAP1(lean_alloc_object, size_t, 0)
WRAP1(mi_malloc, size_t, 1)
WRAP1(mi_malloc_small, size_t, 1)
WRAP1(__gmp_default_allocate, size_t, 2)

void *I_WRAP_SONAME_FNNAME_ZU(NONE, mi_new_n)(size_t n, size_t size) {
    OrigFn fn; void *p; unsigned outer = depth++ == 0;
    VALGRIND_GET_ORIG_FN(fn); CALL_FN_W_WW(p, fn, n, size);
    --depth;
    if (outer && p) {
        if (n && size > SIZE_MAX / n) overflow = 1;
        else record(1, n * size);
    }
    return p;
}
void *I_WRAP_SONAME_FNNAME_ZU(NONE, __gmp_default_reallocate)(void *old, size_t old_size, size_t n) {
    OrigFn fn; void *p; unsigned outer = depth++ == 0;
    VALGRIND_GET_ORIG_FN(fn); CALL_FN_W_WWW(p, fn, old, old_size, n);
    --depth; if (outer && p) record(2, n); return p;
}
SIGN_DET_RESULT CALLBACK_WRAPPER(SIGN_DET_CALLBACK)(void *input) {
    OrigFn fn; uintptr_t result;
    VALGRIND_GET_ORIG_FN(fn);
    ++active; ++callbacks;
    CALL_FN_W_W(result, fn, input);
    --active;
    if (!active) fprintf(stderr,
        "SIGN_DET_ALLOCATIONS {\"callbacks\":%llu,\"overflow\":%d,"
        "\"lean_requests\":%llu,\"lean_bytes\":%llu,"
        "\"mimalloc_requests\":%llu,\"mimalloc_bytes\":%llu,"
        "\"gmp_requests\":%llu,\"gmp_bytes\":%llu}\n",
        callbacks, overflow, requests[0], bytes[0], requests[1], bytes[1], requests[2], bytes[2]);
    return (SIGN_DET_RESULT)result;
}

#ifdef SIGN_DET_CHECK
#include <stdlib.h>
#ifndef SIGN_DET_CHECK_VALUE
#define SIGN_DET_CHECK_VALUE 0xabu
#endif
#if defined(__clang__)
#define FIXTURE_FN __attribute__((noinline, optnone))
#else
#define FIXTURE_FN __attribute__((noipa))
#endif
FIXTURE_FN void *mi_malloc(size_t n) { return malloc(n); }
FIXTURE_FN void *lean_alloc_object(size_t n) { return mi_malloc(n); }
FIXTURE_FN void *lean_alloc_small_object_core(unsigned n) { return mi_malloc(n); }
FIXTURE_FN void *mi_malloc_small(size_t n) { return mi_malloc(n); }
FIXTURE_FN void *mi_new_n(size_t n, size_t size) { return mi_malloc(n * size); }
FIXTURE_FN void *__gmp_default_allocate(size_t n) { return mi_malloc(n); }
FIXTURE_FN void *__gmp_default_reallocate(void *p, size_t old_n, size_t n) {
    (void)old_n; return realloc(p, n);
}
static void *volatile sink;
FIXTURE_FN SIGN_DET_RESULT SIGN_DET_CALLBACK(void *input) {
    (void)input;
    void *p = lean_alloc_small_object_core(16); sink = p; free(p);
    p = lean_alloc_object(48); sink = p; free(p);
    p = mi_malloc_small(24); sink = p; free(p);
    p = mi_new_n(2, 16); sink = p; free(p);
    p = __gmp_default_allocate(64); sink = p;
    p = __gmp_default_reallocate(p, 64, 96); sink = p; free(p);
    return (SIGN_DET_RESULT)SIGN_DET_CHECK_VALUE;
}
int main(void) {
    void *p = mi_malloc(256); sink = p; free(p);
    uintptr_t result = (uintptr_t)SIGN_DET_CALLBACK(NULL);
    return result != SIGN_DET_CHECK_VALUE;
}
#endif
