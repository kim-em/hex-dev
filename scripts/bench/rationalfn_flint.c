/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Persistent, test-only FLINT comparator. Protocol: operation, repeat count,
exponent, evaluation numerator and denominator, then four fmpz_poly_fread
polynomials (two fractions). Input conversion and canonicalisation for arithmetic
are outside the clock. Normalization copies the raw pair before every measured
canonicalise, with copying outside the measured interval.
*/
#define _POSIX_C_SOURCE 200809L
#include <flint/fmpz_poly_q.h>
#include <flint/fmpq.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}
int main(void) {
    fmpz_poly_q_t a, b, r;
    fmpq_t x, y;
    fmpz_poly_q_init(a); fmpz_poly_q_init(b); fmpz_poly_q_init(r);
    fmpq_init(x); fmpq_init(y);
    char op[32];
    unsigned long repeat, exponent;
    while (scanf("%31s %lu %lu", op, &repeat, &exponent) == 3) {
        if (!repeat || repeat > 1000000 ||
            !fmpz_fread(stdin, fmpq_numref(x)) ||
            !fmpz_fread(stdin, fmpq_denref(x)) ||
            !fmpz_poly_fread(stdin, a->num) || !fmpz_poly_fread(stdin, a->den) ||
            !fmpz_poly_fread(stdin, b->num) || !fmpz_poly_fread(stdin, b->den))
            return 2;
        if (fmpz_is_zero(fmpq_denref(x))) return 2;
        fmpq_canonicalise(x);
        if (fmpz_poly_is_zero(a->den) || fmpz_poly_is_zero(b->den)) {
            puts("rejected 0"); fflush(stdout); continue;
        }
        if (strcmp(op, "normalize")) fmpz_poly_q_canonicalise(a);
        fmpz_poly_q_canonicalise(b);
        double elapsed = 0;
        int boolean = 0, pole = 0;
        for (unsigned long i = 0; i < repeat; i++) {
            if (!strcmp(op, "normalize")) fmpz_poly_q_set(r, a);
            double start = now();
            if (!strcmp(op, "normalize")) fmpz_poly_q_canonicalise(r);
            else if (!strcmp(op, "add")) fmpz_poly_q_add(r, a, b);
            else if (!strcmp(op, "sub")) fmpz_poly_q_sub(r, a, b);
            else if (!strcmp(op, "mul")) fmpz_poly_q_mul(r, a, b);
            else if (!strcmp(op, "div")) {
                /* Hex field division is total. Do not call FLINT on zero. */
                if (fmpz_poly_q_is_zero(b)) fmpz_poly_q_zero(r);
                else fmpz_poly_q_div(r, a, b);
            } else if (!strcmp(op, "inv")) {
                if (fmpz_poly_q_is_zero(a)) fmpz_poly_q_zero(r);
                else fmpz_poly_q_inv(r, a);
            } else if (!strcmp(op, "neg")) fmpz_poly_q_neg(r, a);
            else if (!strcmp(op, "pow")) fmpz_poly_q_pow(r, a, exponent);
            else if (!strcmp(op, "derivative")) fmpz_poly_q_derivative(r, a);
            else if (!strcmp(op, "equal")) boolean = fmpz_poly_q_equal(a, b);
            else if (!strcmp(op, "eval")) pole = fmpz_poly_q_evaluate_fmpq(y, a, x);
            else return 2;
            elapsed += now() - start;
        }
        if (!strcmp(op, "equal")) printf("bool %.17g %d\n", elapsed / repeat, boolean);
        else if (!strcmp(op, "eval")) {
            if (pole) printf("none %.17g\n", elapsed / repeat);
            else {
                printf("value %.17g ", elapsed / repeat);
                fmpz_fprint(stdout, fmpq_numref(y)); putchar(' ');
                fmpz_fprint(stdout, fmpq_denref(y)); putchar('\n');
            }
        } else {
            printf("pair %.17g ", elapsed / repeat);
            fmpz_poly_fprint(stdout, r->num); putchar(' ');
            fmpz_poly_fprint(stdout, r->den); putchar('\n');
        }
        fflush(stdout);
    }
    fmpz_poly_q_clear(a); fmpz_poly_q_clear(b); fmpz_poly_q_clear(r);
    fmpq_clear(x); fmpq_clear(y); flint_cleanup();
    return 0;
}
