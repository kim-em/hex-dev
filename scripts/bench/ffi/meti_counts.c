/* Diagnostic counts only; never link this observer into a timed executable. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* The builder supplies labels from the same table that selects workers. */
#ifndef HEX_METI_KINDS
#error "missing generated counter labels"
#endif
static const char *names[] = {HEX_METI_KINDS};
static uint64_t counts[sizeof(names) / sizeof(names[0])];
static uint64_t integer_counts[3];
static unsigned begins, ends;
static int active, invalid, overflow;

static void increment(uint64_t *value) {
    if (*value == UINT64_MAX) overflow = 1;
    else (*value)++;
}

void hex_meti_count(unsigned kind) {
    if (!active) return;
    if (kind >= sizeof(counts) / sizeof(counts[0])) invalid = 1;
    else increment(&counts[kind]);
}

extern lean_object *__real_lean_nat_gcd(lean_object *, lean_object *);
lean_object *__wrap_lean_nat_gcd(lean_object *a, lean_object *b) {
    if (active) increment(&integer_counts[0]);
    return __real_lean_nat_gcd(a, b);
}

/* These counters describe two different layers of the same arithmetic.
   Forward every original argument once and never add the layers together. */
extern void __real___gmpz_gcd(void *, const void *, const void *);
void __wrap___gmpz_gcd(void *g, const void *a, const void *b) {
    if (active) increment(&integer_counts[1]);
    __real___gmpz_gcd(g, a, b);
}
extern void __real___gmpz_gcdext(void *, void *, void *, const void *, const void *);
void __wrap___gmpz_gcdext(void *g, void *s, void *t, const void *a, const void *b) {
    if (active) increment(&integer_counts[2]);
    __real___gmpz_gcdext(g, s, t, a, b);
}

/* Pinned Lean 4.35.0-rc3 ABI: both arguments are borrowed and forwarded once. */
extern lean_object *__real_lean_io_prim_handle_put_str(lean_object *, lean_object *);
lean_object *__wrap_lean_io_prim_handle_put_str(lean_object *handle, lean_object *string) {
    const char *s = lean_string_cstr(string);
    int end = strcmp(s, "METI END\n") == 0;
    if (strcmp(s, "METI BEGIN\n") == 0) {
        if (active || begins != 0 || ends != 0) invalid = 1;
        begins++;
        active = 1;
    }
    if (end) {
        if (!active || begins != 1 || ends != 0) invalid = 1;
        ends++;
        active = 0;
    }
    lean_object *result = __real_lean_io_prim_handle_put_str(handle, string);
    if (end) {
        fprintf(stderr, "METI COUNTERS {\"schema\":1,\"valid\":%s,\"counts\":{",
                !invalid && !overflow && begins == 1 && ends == 1 ? "true" : "false");
        for (unsigned i = 0; i < sizeof(names) / sizeof(names[0]); i++)
            fprintf(stderr, "%s\"%s\":%llu", i ? "," : "", names[i],
                    (unsigned long long)counts[i]);
        fprintf(stderr, "},\"lean_nat_gcd\":%llu,\"gmp_gcd\":%llu,\"gmp_gcdext\":%llu}\n",
                (unsigned long long)integer_counts[0],
                (unsigned long long)integer_counts[1],
                (unsigned long long)integer_counts[2]);
        fflush(stderr);
    }
    return result;
}
