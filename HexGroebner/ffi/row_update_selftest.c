/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */

#define HEX_GROEBNER_NO_LEAN
#include "row_update.c"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint32_t seed = 4147;
static uint32_t random_word(void) {
    seed ^= seed << 13;
    seed ^= seed >> 17;
    seed ^= seed << 5;
    return seed;
}

static void fail(const char *message) {
    fprintf(stderr, "row_update_selftest: %s\n", message);
    exit(1);
}

static void check_monomials(void) {
    unsigned cases = 0;
    for (unsigned width = 1; width <= 4; width *= 2) {
        for (unsigned trial = 0; trial < 500; ++trial) {
            size_t n = trial % 129 + 1, bytes = 2 * n * width, output_bytes = 4 * n + 28;
            uint8_t *source = malloc(bytes), *output = malloc(output_bytes);
            uint64_t *left = malloc(n * sizeof(uint64_t)), *right = malloc(n * sizeof(uint64_t));
            if (!source || !output || !left || !right) fail("monomial allocation");
            uint64_t bound = width == 1 ? 256 : width == 2 ? 65536 : UINT64_C(4294967296);
            for (size_t i = 0; i < n; ++i) {
                left[i] = random_word() % bound;
                right[i] = trial % 2 ? random_word() % (left[i] + 1) : random_word() % bound;
                write_le(source + i * width, width, left[i]);
                write_le(source + (n + i) * width, width, right[i]);
            }
            for (unsigned operation = 0; operation < 3; ++operation) {
                int valid = 1, equal_left = 1, equal_right = 1;
                uint64_t degree = 0, mask = 0, hash = UINT64_C(14695981039346656037), largest = 0;
                int actual = prepare_monomial(operation, width, n, 2, 0, 1,
                    source, bytes, output, output_bytes);
                for (size_t i = 0; i < n; ++i) {
                    uint64_t x = left[i], y = right[i];
                    if ((operation == 1 && x + y >= UINT64_C(4294967296)) ||
                        (operation == 2 && y > x)) { valid = 0; break; }
                    uint64_t z = operation == 0 ? (x >= y ? x : y) : operation == 1 ? x + y : x - y;
                    if (actual && read_le(output + i * 4, 4) != z) fail("monomial coordinate");
                    equal_left &= z == x; equal_right &= z == y;
                    degree += z; if (z) mask |= UINT64_C(1) << (i % 64);
                    hash = (hash ^ z) * UINT64_C(1099511628211);
                    if (z > largest) largest = z;
                }
                if (actual != valid) fail("monomial overflow or quotient rejection");
                if (valid) {
                    uint64_t metadata[] = {degree, mask, hash};
                    for (size_t i = 0; i < 3; ++i) {
                        size_t offset = 4 * n + 8 * i;
                        uint64_t value = read_le(output + offset, 4) |
                            (read_le(output + offset + 4, 4) << 32);
                        if (value != metadata[i]) fail("monomial metadata");
                    }
                    if (read_le(output + 4 * n + 24, 4) != largest) fail("monomial maximum");
                    if (equal_monomial(width, n, 0, source, bytes, output, output_bytes) != equal_left ||
                        equal_monomial(width, n, 1, source, bytes, output, output_bytes) != equal_right)
                        fail("monomial exact equality");
                    if (equal_monomial(width, n, 2, source, bytes, output, output_bytes) ||
                        equal_monomial(width, n, 0, source, bytes, output, output_bytes - 1))
                        fail("monomial equality geometry");
                }
                ++cases;
            }
            free(source); free(output); free(left); free(right);
        }
    }
    if (monomial_shape(0, 4, 4096, UINT64_MAX, 0, 0, SIZE_MAX, 16412) ||
        monomial_shape(0, 4, 4097, 1, 0, 0, 16388, 16416) ||
        monomial_shape(0, 4, 0, 1, 0, 0, 0, 28) ||
        monomial_shape(3, 1, 1, 1, 0, 0, 1, 32) ||
        monomial_shape(0, 3, 1, 1, 0, 0, 3, 32)) fail("monomial malformed geometry");
    printf("monomial_selftest: %u cases and malformed boundaries OK\n", cases);
}

int main(void) {
    check_monomials();
    const uint64_t moduli[] = {2, 3, 251, 256, 257, 65521, 65536, 65537, 2147483647};
    unsigned cases = 0;
    for (unsigned field = 0; field < sizeof(moduli) / sizeof(moduli[0]); ++field) {
        uint64_t p = moduli[field];
        unsigned width = p <= 256 ? 1 : p <= 65536 ? 2 : 4;
        size_t bytes = 37 * width;
        uint8_t *dense = malloc(bytes), *expected = malloc(bytes);
        uint8_t *columns = malloc(64 * 4), *coefficients = malloc(64 * width);
        if (!dense || !expected || !columns || !coefficients) fail("allocation");
        for (unsigned trial = 0; trial < 500; ++trial) {
            for (size_t i = 0; i < 37; ++i) write_le(dense + i * width, width, random_word() % p);
            memcpy(expected, dense, bytes);
            for (size_t i = 0; i < 64; ++i) {
                write_le(columns + 4 * i, 4, random_word() % 37);
                write_le(coefficients + width * i, width, random_word() % p);
            }
            size_t start = random_word() % 65;
            size_t count = random_word() % (65 - start);
            uint64_t factor = trial % 2 ? p - 1 : random_word() % p;
            unsigned checked = row_shape(p, bytes, 64 * 4, 64 * width, start, count, factor);
            if (checked != width) fail("geometry rejected");
            for (size_t i = start; i < start + count; ++i) {
                size_t column = (size_t)read_le(columns + 4 * i, 4);
                uint64_t a = read_le(expected + column * width, width);
                uint64_t b = read_le(coefficients + i * width, width);
                uint64_t value = (a + p - factor * b % p) % p;
                write_le(expected + column * width, width, value);
            }
            if (!update_bytes(p, width, dense, bytes, columns, coefficients, start, count, factor))
                fail("valid update rejected");
            if (memcmp(expected, dense, bytes)) fail("different modular result");
            ++cases;
        }
        free(dense); free(expected); free(columns); free(coefficients);
    }
    if (row_shape(7, 1, 4, 1, SIZE_MAX, 1, 1)) fail("start overflow accepted");
    if (row_shape(7, 1, 4, 1, 0, SIZE_MAX, 1)) fail("count overflow accepted");
    if (row_shape(7, 1, 5, 1, 0, 1, 1)) fail("misaligned columns accepted");
    if (row_shape(257, 1, 4, 2, 0, 1, 1)) fail("misaligned dense accepted");
    if (row_shape(7, 1, 4, 2, 0, 1, 1)) fail("coefficient length accepted");
    if (row_shape(0, 1, 4, 1, 0, 1, 1)) fail("zero modulus accepted");
    if (row_shape(2147483648, 4, 4, 4, 0, 1, 1)) fail("wide modulus accepted");
    if (row_shape(7, 1, 4, 1, 0, 1, 7)) fail("noncanonical factor accepted");
    uint8_t dense[] = {1}, bad_columns[] = {255,255,255,255}, coefficients[] = {1};
    if (update_bytes(7, 1, dense, 1, bad_columns, coefficients, 0, 1, 1)) fail("bad column accepted");
    uint8_t columns[] = {0,0,0,0};
    coefficients[0] = 7;
    if (update_bytes(7, 1, dense, 1, columns, coefficients, 0, 1, 1)) fail("bad coefficient accepted");
    coefficients[0] = 1; dense[0] = 7;
    if (update_bytes(7, 1, dense, 1, columns, coefficients, 0, 1, 1)) fail("bad dense value accepted");
#if defined(__SIZEOF_INT128__) && !defined(HEX_GROEBNER_NO_UINT128)
    printf("row_update_selftest: uint128 Barrett, %u cases and malformed boundaries OK\n", cases);
#else
    printf("row_update_selftest: exact remainder, %u cases and malformed boundaries OK\n", cases);
#endif
    return 0;
}
