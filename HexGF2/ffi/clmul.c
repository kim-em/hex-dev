/* `HEX_CLMUL_NO_LEAN` compiles only the arithmetic, without the Lean export
   wrapper and so without the Lean runtime. The self-test uses it: it wants to
   compare the two implementations, not to link a Lean binary. */
#ifndef HEX_CLMUL_NO_LEAN
#include <lean/lean.h>
#endif
#include <stdint.h>

/* Which implementation this translation unit selects is a compile-time
   decision made by the guards below, not runtime CPU detection.
   `HEX_CLMUL_HAVE_INTRINSIC` records that decision so the self-test can report
   which path a given build exercised, and so a build that expected an
   intrinsic can tell that it did not get one. */
#if defined(__PCLMUL__) && (defined(__x86_64__) || defined(_M_X64))
#define HEX_CLMUL_HAVE_INTRINSIC 1
#define HEX_CLMUL_INTRINSIC_X86 1
#include <immintrin.h>
#elif defined(__ARM_FEATURE_CRYPTO) && (defined(__aarch64__) || defined(_M_ARM64))
#define HEX_CLMUL_HAVE_INTRINSIC 1
#define HEX_CLMUL_INTRINSIC_ARM 1
#include <arm_neon.h>
#else
#define HEX_CLMUL_HAVE_INTRINSIC 0
#endif

/* The portable reference, mirroring `Hex.pureClmul`, which is the logical
   definition every proof reasons about. Exported rather than `static` so the
   self-test can compare it against an intrinsic path inside one binary. */
void hex_clmul_portable(uint64_t a, uint64_t b, uint64_t* hi, uint64_t* lo) {
    uint64_t out_hi = 0;
    uint64_t out_lo = 0;
    for (unsigned bit = 0; bit < 64; ++bit) {
        if (((b >> bit) & 1ULL) == 0) {
            continue;
        }
        if (bit == 0) {
            out_lo ^= a;
        } else {
            out_lo ^= a << bit;
            out_hi ^= a >> (64 - bit);
        }
    }
    *hi = out_hi;
    *lo = out_lo;
}

#if HEX_CLMUL_HAVE_INTRINSIC
#ifdef HEX_CLMUL_INTRINSIC_X86
void hex_clmul_intrinsic(uint64_t a, uint64_t b, uint64_t* hi, uint64_t* lo) {
    __m128i lhs = _mm_set_epi64x(0, (long long)a);
    __m128i rhs = _mm_set_epi64x(0, (long long)b);
    __m128i prod = _mm_clmulepi64_si128(lhs, rhs, 0x00);
    *lo = (uint64_t)_mm_cvtsi128_si64(prod);
    *hi = (uint64_t)_mm_extract_epi64(prod, 1);
}
#else
void hex_clmul_intrinsic(uint64_t a, uint64_t b, uint64_t* hi, uint64_t* lo) {
    poly64_t lhs = (poly64_t)a;
    poly64_t rhs = (poly64_t)b;
    poly128_t prod = vmull_p64(lhs, rhs);
    *lo = (uint64_t)prod;
    *hi = (uint64_t)(prod >> 64);
}
#endif
#endif

/* Whether this build compiled an intrinsic path at all. */
int hex_clmul_uses_intrinsic(void) {
    return HEX_CLMUL_HAVE_INTRINSIC;
}

#ifndef HEX_CLMUL_NO_LEAN
LEAN_EXPORT lean_obj_res lean_hex_clmul_u64(uint64_t a, uint64_t b) {
    uint64_t hi;
    uint64_t lo;
#if HEX_CLMUL_HAVE_INTRINSIC
    hex_clmul_intrinsic(a, b, &hi, &lo);
#else
    hex_clmul_portable(a, b, &hi, &lo);
#endif
    lean_object* pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint64(hi));
    lean_ctor_set(pair, 1, lean_box_uint64(lo));
    return pair;
}
#endif
