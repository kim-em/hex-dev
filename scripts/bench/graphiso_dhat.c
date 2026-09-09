/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Count mimalloc allocation requests with DHAT's ad-hoc event mode. The
ordinary heap mode intercepts libc/GMP allocations but misses the statically
linked mimalloc used by the Lean toolchain. These are the three allocation
entry points called by the profiler outside mimalloc itself. A thread-local
depth counter excludes nested calls between entry points.

Build as a shared library and pass its path in LD_PRELOAD to Valgrind:
  cc -shared -fPIC -O2 $(pkg-config --cflags valgrind) graphiso_dhat.c -o wrapper.so
  LD_PRELOAD=./wrapper.so valgrind --tool=dhat --mode=ad-hoc \
    .lake/build/bin/hexgraphiso_profile run
Events count successful allocation requests, not bytes or live blocks. Use ordinary DHAT separately for libc/GMP allocations.

With -DGRAPHISO_DHAT_CHECK, compile an executable instead of a shared library.
Running that executable under DHAT ad-hoc mode must report exactly three
events, including two allocations that call another wrapped entry point.

Audit direct callers with:
  python3 scripts/bench/graphiso_alloc_calls.py .lake/build/bin/hexgraphiso_profile
Lean 4.34.0-rc2 output:
  direct mi_* targets called from outside mimalloc:
  mi_free
  mi_free_size
  mi_malloc
  mi_malloc_small
  mi_new_n
  mi_option_init(mi_option_desc_s*)
The last target initializes options; it does not allocate a client object.
This audit does not establish the absence of inlined or indirect allocators.
*/

#include <stddef.h>
#include <valgrind/valgrind.h>
#include <valgrind/dhat.h>
/* Each thread counts only its outermost wrapped allocation. */
static __thread unsigned depth;
#define WRAP1(name) \
void *I_WRAP_SONAME_FNNAME_ZU(NONE, name)(size_t n) { \
    OrigFn fn; void *p; unsigned outer = depth++ == 0; \
    VALGRIND_GET_ORIG_FN(fn); CALL_FN_W_W(p, fn, n); \
    --depth; if (outer && p) DHAT_AD_HOC_EVENT(1); return p; \
}
#define WRAP2(name) \
void *I_WRAP_SONAME_FNNAME_ZU(NONE, name)(size_t n, size_t size) { \
    OrigFn fn; void *p; unsigned outer = depth++ == 0; \
    VALGRIND_GET_ORIG_FN(fn); CALL_FN_W_WW(p, fn, n, size); \
    --depth; if (outer && p) DHAT_AD_HOC_EVENT(1); return p; \
}
WRAP1(mi_malloc)
WRAP1(mi_malloc_small)
WRAP2(mi_new_n)

#ifdef GRAPHISO_DHAT_CHECK
#include <stdlib.h>
__attribute__((noinline)) void *mi_malloc(size_t n) { return malloc(n); }
__attribute__((noinline)) void *mi_malloc_small(size_t n) { return mi_malloc(n); }
__attribute__((noinline)) void *mi_new_n(size_t n, size_t size) { return mi_malloc(n * size); }
static void *volatile sink;
int main(void) {
    void *p = mi_malloc(16); sink = p; free(p);
    p = mi_malloc_small(16); sink = p; free(p);
    p = mi_new_n(2, 16); sink = p; free(p);
    return 0;
}
#endif
