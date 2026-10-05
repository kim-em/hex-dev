/* Diagnostic counters only. Never link this observer into a timed binary. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int active;
static uint64_t counts[7];

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
    }
    return result;
}
