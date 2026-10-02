/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Kim Morrison
 *
 * Value-only diagnostic, never used by Lean proofs or production dispatch.
 * Same scalar elimination as Owned.lean, but contiguous unboxed words and C loops.
 * Input residues are below a prime p < 2^31; every product fits in 62 bits.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static uint64_t inverse(uint64_t a, uint64_t p) {
    int64_t old_s = 0, s = 1;
    uint64_t old_r = p, r = a;
    while (r) {
        uint64_t q = old_r / r;
        uint64_t next_r = old_r - q * r;
        int64_t next_s = old_s - (int64_t)q * s;
        old_r = r; r = next_r;
        old_s = s; s = next_s;
    }
    return old_s < 0 ? (uint64_t)(old_s + (int64_t)p) : (uint64_t)old_s;
}

/* Copies input inside the measured call, so the caller's matrix stays reusable. */
uint64_t determinant(const uint64_t *input, size_t n, uint64_t p) {
    if (n == 0) return 1;
    uint64_t *a = malloc(n * n * sizeof(uint64_t));
    if (!a) abort();
    memcpy(a, input, n * n * sizeof(uint64_t));
    uint64_t det = 1;
    for (size_t k = 0; k < n; ++k) {
        size_t pivot = k;
        while (pivot < n && a[pivot*n+k] == 0) ++pivot;
        if (pivot == n) { free(a); return 0; }
        if (pivot != k) {
            for (size_t j = k; j < n; ++j) {
                uint64_t t = a[k*n+j];
                a[k*n+j] = a[pivot*n+j];
                a[pivot*n+j] = t;
            }
            det = det ? p-det : 0;
        }
        uint64_t inv = inverse(a[k*n+k], p);
        det = det * a[k*n+k] % p;
        for (size_t i = k+1; i < n; ++i) {
            uint64_t c = (p-a[i*n+k]) * inv % p;
            a[i*n+k] = 0;
            if (!c) continue;
            for (size_t j = k+1; j < n; ++j) {
                uint64_t t = a[i*n+j] + c*a[k*n+j] % p;
                a[i*n+j] = t < p ? t : t-p;
            }
        }
    }
    free(a);
    return det;
}
