#include <stdint.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <lean/lean.h>

/* Dynamic-loading primitives. Windows has no <dlfcn.h>; its probe for an
   already-linked provider searches the executable image only, so there a
   provider must be loaded explicitly unless it is linked into the program. */
#ifdef _WIN32
#include <windows.h>
typedef HMODULE hexlll_handle;
static void *hexlll_default_sym(const char *name) {
    return (void *)GetProcAddress(GetModuleHandleA(NULL), name);
}
static hexlll_handle hexlll_open(const char *path) { return LoadLibraryA(path); }
static void *hexlll_sym(hexlll_handle handle, const char *name) {
    return (void *)GetProcAddress(handle, name);
}
static void hexlll_close(hexlll_handle handle) { FreeLibrary(handle); }
static const char *hexlll_error(void) {
    static char buf[48];
    snprintf(buf, sizeof buf, "Windows error %lu", (unsigned long)GetLastError());
    return buf;
}
#else
#include <dlfcn.h>
typedef void *hexlll_handle;
static void *hexlll_default_sym(const char *name) { return dlsym(RTLD_DEFAULT, name); }
static hexlll_handle hexlll_open(const char *path) {
    return dlopen(path, RTLD_NOW | RTLD_GLOBAL);
}
static void *hexlll_sym(hexlll_handle handle, const char *name) {
    return dlsym(handle, name);
}
static void hexlll_close(hexlll_handle handle) { dlclose(handle); }
static const char *hexlll_error(void) { return dlerror(); }
#endif

typedef lean_obj_res (*lean_fplll_lll_reduce_fn)(
    size_t rows,
    size_t cols,
    b_lean_obj_arg entries,
    double delta,
    double eta,
    uint8_t method,
    uint8_t with_inverse);

/* Provider slot state:
     0 — not yet probed for a statically-linked provider symbol,
     1 — probed, none linked and none installed by the loader,
     2 — a provider is installed (`lean_hexlll_provider_ptr` is valid).
   The slot is set either by `lean_hexlll_load_provider` (the explicit Lean
   loader `Hex.lll.loadExternalReducer`) or, for a statically-linked provider, by the
   one-shot `RTLD_DEFAULT` probe in `lean_hexlll_resolve_provider`. There is no
   environment-variable read and no implicit `dlopen`: activation is always an
   explicit Lean action or a link-time fact. */
static atomic_int lean_hexlll_provider_state = 0;
static atomic_uintptr_t lean_hexlll_provider_ptr = 0;

/* Resolve the active provider, if any. State 2 returns the installed pointer;
   state 1 returns NULL. From the initial state 0 we probe *once* for a
   statically-linked `lean_fplll_lll_reduce` via `dlsym(RTLD_DEFAULT, ...)` so a
   provider linked into the process (a future in-tree adapter) self-activates
   with no loader call; a miss latches state 1. The probe never `dlopen`s and
   never reads the environment. */
static lean_fplll_lll_reduce_fn lean_hexlll_resolve_provider(void) {
    int state = atomic_load_explicit(&lean_hexlll_provider_state, memory_order_acquire);
    if (state == 2) {
        return (lean_fplll_lll_reduce_fn)
            atomic_load_explicit(&lean_hexlll_provider_ptr, memory_order_acquire);
    }
    if (state == 1) {
        return NULL;
    }

    void *sym = hexlll_default_sym("lean_fplll_lll_reduce");
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

/* `Hex.lll.loadExternalReducer`: explicitly `dlopen` the shared library at `path`
   (with `RTLD_GLOBAL` so its symbols satisfy the provider's transitive deps),
   resolve `lean_fplll_lll_reduce` from that handle, and install it as the
   active provider. Returns `true` on success and `false` on failure; on failure
   the `dlopen`/`dlsym` diagnostic is written to stderr so a caller sees why the
   library did not load (typically an unresolved transitive dep or a wrong
   path). Installing overrides a prior "absent" latch (state 1), so a load may
   follow an earlier availability probe; a later successful load replaces the
   current provider, and a failed load leaves the current state unchanged.
   Bound to `IO Bool`: the world token is erased in the generated call (a single
   object argument), and the return is an IO result carrying the boxed flag. */
LEAN_EXPORT lean_obj_res lean_hexlll_load_provider(b_lean_obj_arg path) {
    const char *cpath = lean_string_cstr(path);
    hexlll_handle handle = hexlll_open(cpath);
    if (handle == NULL) {
        const char *err = hexlll_error();
        fprintf(stderr, "hexlll: dlopen(\"%s\") failed: %s\n",
                cpath, err != NULL ? err : "(no dlerror)");
        return lean_io_result_mk_ok(lean_box(0));
    }
    void *sym = hexlll_sym(handle, "lean_fplll_lll_reduce");
    if (sym == NULL) {
        const char *err = hexlll_error();
        fprintf(stderr, "hexlll: dlsym(\"%s\", \"lean_fplll_lll_reduce\") failed: %s\n",
                cpath, err != NULL ? err : "(no dlerror)");
        hexlll_close(handle);
        return lean_io_result_mk_ok(lean_box(0));
    }
    atomic_store_explicit(&lean_hexlll_provider_ptr, (uintptr_t)sym, memory_order_release);
    atomic_store_explicit(&lean_hexlll_provider_state, 2, memory_order_release);
    return lean_io_result_mk_ok(lean_box(1));
}

LEAN_EXPORT uint8_t lean_hexlll_provider_available(lean_obj_arg unit) {
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
