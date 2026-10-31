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

int main(void) {
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
