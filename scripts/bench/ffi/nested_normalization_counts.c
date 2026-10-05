/* Diagnostic counters only. Never link this observer into a timed binary. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int active;
static uint64_t counts[7];
static uint64_t callbacks[32][12];
static int callback_overflow;
static const char *operations[12] = {
    "add", "sub", "neg", "mul", "inv", "div", "sign", "zero", "eq",
    "split", "inverse_gcd", "inverse_xgcd"
};

/* The pinned runtime/object.cpp consumes the string via io_eprintln and
   calls lean_apply_1(fn, lean_box(0)). For our diagnostic strings, replace
   that printing with a counter, consume the string and run the same thunk
   once. Other debug traces retain the ordinary runtime behavior. */
extern lean_object *__real_lean_dbg_trace(lean_object *, lean_object *);
lean_object *__wrap_lean_dbg_trace(lean_object *string, lean_object *fn) {
    const char *s = lean_string_cstr(string);
    if (strncmp(s, "NESTED ", 7) != 0) return __real_lean_dbg_trace(string, fn);
    if (active) {
        unsigned depth;
        char operation[32], extra;
        int known = 0;
        if (sscanf(s, "NESTED %u %31s %c", &depth, operation, &extra) == 2 && depth < 32) {
            for (unsigned i = 0; i < 12; i++) {
                if (strcmp(operation, operations[i]) == 0) {
                    callbacks[depth][i]++;
                    known = 1;
                    break;
                }
            }
        }
        if (!known) callback_overflow = 1;
    }
    lean_dec(string);
    return lean_apply_1(fn, lean_box(0));
}

void hex_nested_poly_count(unsigned kind) {
    if (active && kind < 4) counts[kind]++;
}

extern lean_object *__real_lean_nat_gcd(lean_object *, lean_object *);
lean_object *__wrap_lean_nat_gcd(lean_object *a, lean_object *b) {
    if (active) counts[4]++;
    return __real_lean_nat_gcd(a, b);
}

/* GMP's mpz pointer arguments are forwarded unchanged; no mpz is inspected. */
extern void __real___gmpz_gcd(void *, const void *, const void *);
void __wrap___gmpz_gcd(void *g, const void *a, const void *b) {
    if (active) counts[5]++;
    __real___gmpz_gcd(g, a, b);
}
extern void __real___gmpz_gcdext(void *, void *, void *, const void *, const void *);
void __wrap___gmpz_gcdext(void *g, void *s, void *t, const void *a, const void *b) {
    if (active) counts[6]++;
    __real___gmpz_gcdext(g, s, t, a, b);
}

/* Pinned Lean 4.35.0-rc3 runtime/io.cpp: the borrowed handle and string
   arguments are forwarded once. Markers are emitted by the ordinary driver. */
extern lean_object *__real_lean_io_prim_handle_put_str(lean_object *, lean_object *);
lean_object *__wrap_lean_io_prim_handle_put_str(lean_object *handle, lean_object *string) {
    const char *s = lean_string_cstr(string);
    int end = strcmp(s, "NESTED END\n") == 0;
    if (strcmp(s, "NESTED BEGIN\n") == 0) {
        memset(counts, 0, sizeof(counts));
        memset(callbacks, 0, sizeof(callbacks));
        callback_overflow = 0;
        active = 1;
    }
    if (end) active = 0;
    lean_object *result = __real_lean_io_prim_handle_put_str(handle, string);
    if (end) {
        fprintf(stderr, "NESTED COUNTERS {\"poly_gcd\":%llu,\"poly_xgcd\":%llu,"
            "\"poly_xgcd_left\":%llu,\"poly_pseudo_gcd\":%llu,"
            "\"lean_nat_gcd\":%llu,\"gmp_gcd\":%llu,\"gmp_gcdext\":%llu}\n",
            (unsigned long long)counts[0], (unsigned long long)counts[1],
            (unsigned long long)counts[2], (unsigned long long)counts[3],
            (unsigned long long)counts[4], (unsigned long long)counts[5],
            (unsigned long long)counts[6]);
        fprintf(stderr, "NESTED CALLBACKS {\"overflow\":%s,\"counts\":{",
            callback_overflow ? "true" : "false");
        int first = 1;
        for (unsigned depth = 0; depth < 32; depth++) {
            for (unsigned i = 0; i < 12; i++) {
                if (callbacks[depth][i]) {
                    fprintf(stderr, "%s\"%u:%s\":%llu", first ? "" : ",", depth,
                        operations[i], (unsigned long long)callbacks[depth][i]);
                    first = 0;
                }
            }
        }
        fprintf(stderr, "}}\n");
    }
    return result;
}
