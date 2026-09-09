/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Count code-1 admission branches without changing the search. This Valgrind
wrapper targets the Lean 4.34.0-rc2 C ABI of Nauty.classify in the fixture
and campaign emitters. Its five arguments are n, ctx, level, numcells, st.
Search.firstcode, gcaFirst and noncheaplevel are fields 7, 17 and 20.
The returned pair's first component is Leaf.autoFirst exactly when it is
scalar 1. Recheck those indices and the generated C signature if the state
layout or compiler changes. The small-Nat checks fail closed.

Build with the Lean and Valgrind include directories, then run:
  LD_PRELOAD=./admissions.so valgrind --tool=none \
    .lake/build/bin/hexgraphiso_emit_fixtures > /dev/null
Repeat with hexgraphiso_emit_campaign. Each emitter calls the search once
per case. A run with no wrapped calls exits with status 2.
*/
#include <lean/lean.h>
#include <valgrind/valgrind.h>
#include <stdio.h>
#include <stdlib.h>

static unsigned long long calls, admitted, cheap, without_sentinel;

static size_t small_nat(lean_object *v) {
    if (!lean_is_scalar(v)) abort();
    return lean_unbox(v);
}

lean_object *I_WRAP_SONAME_FNNAME_ZU(NONE, lp_Hex_Hex_GraphIso_Nauty_classify)(
        lean_object *n, lean_object *ctx, lean_object *level,
        lean_object *numcells, lean_object *st) {
    size_t next = small_nat(level) + 1;
    lean_object *codes = lean_ctor_get(st, 7);
    if (next >= lean_array_size(codes)) abort();
    int missing = small_nat(lean_array_cptr(codes)[next]) != 077777;
    int ischeap = small_nat(lean_ctor_get(st, 17)) >= small_nat(lean_ctor_get(st, 20));
    OrigFn fn;
    lean_object *result;
    VALGRIND_GET_ORIG_FN(fn);
    CALL_FN_W_5W(result, fn, n, ctx, level, numcells, st);
    __atomic_fetch_add(&calls, 1, __ATOMIC_RELAXED);
    lean_object *leaf = lean_ctor_get(result, 0);
    if (lean_is_scalar(leaf) && lean_unbox(leaf) == 1) {
        __atomic_fetch_add(&admitted, 1, __ATOMIC_RELAXED);
        if (ischeap) __atomic_fetch_add(&cheap, 1, __ATOMIC_RELAXED);
        if (missing) __atomic_fetch_add(&without_sentinel, 1, __ATOMIC_RELAXED);
    }
    return result;
}

__attribute__((destructor)) static void report(void) {
    if (!RUNNING_ON_VALGRIND) return;
    fprintf(stderr, "admissions: classify=%llu autoFirst=%llu cheap=%llu without_sentinel=%llu\n",
            calls, admitted, cheap, without_sentinel);
    if (!calls) _Exit(2);
}
