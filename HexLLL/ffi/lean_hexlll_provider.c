#include <dlfcn.h>
#include <stdint.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <lean/lean.h>

typedef lean_obj_res (*lean_fplll_lll_reduce_fn)(
    size_t rows,
    size_t cols,
    b_lean_obj_arg entries,
    double delta,
    double eta,
    uint8_t method,
    uint8_t with_inverse);

static atomic_int lean_hexlll_provider_state = 0;
static atomic_uintptr_t lean_hexlll_provider_ptr = 0;
static atomic_int lean_hexlll_provider_dlopen_done = 0;

/* If `HEX_FPLLL_FFI_LIB` is set, `dlopen` the named shared library with
   `RTLD_GLOBAL` so its symbols (in particular `lean_fplll_lll_reduce`) become
   visible to `dlsym(RTLD_DEFAULT, ...)` below. Tried at most once per process.
   When the env var is unset the call is a no-op. When the env var is set but
   `dlopen` fails, the error is written to stderr so CI surfaces the actual
   loader diagnostic (typically an unresolved transitive dep like
   `libLake_shared`) instead of silently falling through to "provider
   absent". */
static void lean_hexlll_dlopen_provider_lib(void) {
    int done = atomic_load_explicit(&lean_hexlll_provider_dlopen_done, memory_order_acquire);
    if (done) {
        return;
    }
    int expected = 0;
    if (!atomic_compare_exchange_strong_explicit(
            &lean_hexlll_provider_dlopen_done, &expected, 1,
            memory_order_acq_rel, memory_order_acquire)) {
        return;
    }
    const char *path = getenv("HEX_FPLLL_FFI_LIB");
    if (path == NULL || path[0] == '\0') {
        return;
    }
    if (dlopen(path, RTLD_NOW | RTLD_GLOBAL) == NULL) {
        const char *err = dlerror();
        fprintf(stderr, "hexlll: dlopen(\"%s\") failed: %s\n",
                path, err != NULL ? err : "(no dlerror)");
    }
}

static lean_fplll_lll_reduce_fn lean_hexlll_resolve_provider(void) {
    int state = atomic_load_explicit(&lean_hexlll_provider_state, memory_order_acquire);
    if (state == 1) {
        return NULL;
    }
    if (state == 2) {
        return (lean_fplll_lll_reduce_fn)
            atomic_load_explicit(&lean_hexlll_provider_ptr, memory_order_acquire);
    }

    lean_hexlll_dlopen_provider_lib();

    void *sym = dlsym(RTLD_DEFAULT, "lean_fplll_lll_reduce");
    if (sym == NULL) {
        int expected = 0;
        atomic_compare_exchange_strong_explicit(
            &lean_hexlll_provider_state, &expected, 1,
            memory_order_release, memory_order_acquire);
        return NULL;
    }

    atomic_store_explicit(&lean_hexlll_provider_ptr, (uintptr_t)sym, memory_order_release);
    atomic_store_explicit(&lean_hexlll_provider_state, 2, memory_order_release);
    return (lean_fplll_lll_reduce_fn)sym;
}

static lean_obj_res lean_hexlll_except_error(const char *msg) {
    lean_object *err = lean_mk_string(msg);
    lean_object *res = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(res, 0, err);
    return res;
}

LEAN_EXPORT uint8_t lean_hexlll_provider_available(uint8_t unit) {
    (void)unit;
    return lean_hexlll_resolve_provider() != NULL;
}

LEAN_EXPORT lean_obj_res lean_hexlll_provider_reduce(
    size_t rows,
    size_t cols,
    b_lean_obj_arg entries,
    double delta,
    double eta,
    uint8_t method,
    uint8_t with_inverse) {
    lean_fplll_lll_reduce_fn provider = lean_hexlll_resolve_provider();
    if (provider == NULL) {
        return lean_hexlll_except_error("hexlll provider absent");
    }
    return provider(rows, cols, entries, delta, eta, method, with_inverse);
}
