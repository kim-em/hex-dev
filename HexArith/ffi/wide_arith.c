#include <lean/lean.h>
#include <stdint.h>

LEAN_EXPORT uint64_t lean_hex_uint64_mul_hi(uint64_t a, uint64_t b) {
    return (uint64_t)(((__uint128_t)a * (__uint128_t)b) >> 64);
}

LEAN_EXPORT lean_obj_res lean_hex_uint64_mul_full(uint64_t a, uint64_t b) {
    __uint128_t p = (__uint128_t)a * (__uint128_t)b;
    lean_object* pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint64((uint64_t)(p >> 64)));
    lean_ctor_set(pair, 1, lean_box_uint64((uint64_t)p));
    return pair;
}

LEAN_EXPORT lean_obj_res lean_hex_uint64_add_carry(uint64_t a, uint64_t b, uint8_t cin) {
    uint64_t sum;
    uint64_t total;
    uint8_t carry1 = __builtin_add_overflow(a, b, &sum);
    uint8_t carry2 = __builtin_add_overflow(sum, (uint64_t)cin, &total);
    lean_object* pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint64(total));
    lean_ctor_set(pair, 1, lean_box(carry1 | carry2));
    return pair;
}

LEAN_EXPORT lean_obj_res lean_hex_uint64_sub_borrow(uint64_t a, uint64_t b, uint8_t bin) {
    uint64_t diff;
    uint64_t total;
    uint8_t borrow1 = __builtin_sub_overflow(a, b, &diff);
    uint8_t borrow2 = __builtin_sub_overflow(diff, (uint64_t)bin, &total);
    lean_object* pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint64(total));
    lean_ctor_set(pair, 1, lean_box(borrow1 | borrow2));
    return pair;
}

/* Allocation-free executable counterpart of `Hex.montgomeryReduce`.
 *
 * The logical Lean definition uses `UInt64.mulFull` and two `addCarry`
 * results, which is convenient for proofs but allocates three product values
 * in generated code.  This primitive performs the identical word operations
 * directly.  `p_prime` is the first runtime field of `MontCtx`; proof fields
 * and the type index are erased by Lean.
 */
static inline uint64_t hex_montgomery_reduce(
        uint64_t p, uint64_t p_prime, uint64_t hi, uint64_t lo) {
    uint64_t m = lo * p_prime;
    __uint128_t mp = (__uint128_t)m * (__uint128_t)p;
    uint64_t mlo = (uint64_t)mp;
    uint64_t mhi = (uint64_t)(mp >> 64);

    uint64_t ignored_low;
    uint64_t add_hi;
    uint8_t carry1 = __builtin_add_overflow(lo, mlo, &ignored_low);
    uint8_t carry2a = __builtin_add_overflow(hi, mhi, &add_hi);
    uint8_t carry2b = __builtin_add_overflow(add_hi, (uint64_t)carry1, &add_hi);
    uint8_t carry2 = carry2a | carry2b;

    return (carry2 || add_hi >= p) ? add_hi - p : add_hi;
}

LEAN_EXPORT uint64_t lean_hex_montgomery_reduce(
        uint64_t p, b_lean_obj_arg ctx, uint64_t hi, uint64_t lo) {
    uint64_t p_prime = lean_ctor_get_uint64(ctx, 0);
    return hex_montgomery_reduce(p, p_prime, hi, lo);
}

LEAN_EXPORT uint64_t lean_hex_mont_to(
        uint64_t p, b_lean_obj_arg ctx, uint64_t a) {
    uint64_t p_prime = lean_ctor_get_uint64(ctx, 0);
    uint64_t r2 = lean_ctor_get_uint64(ctx, 8);
    __uint128_t product = (__uint128_t)a * (__uint128_t)r2;
    return hex_montgomery_reduce(
        p, p_prime, (uint64_t)(product >> 64), (uint64_t)product);
}

LEAN_EXPORT uint64_t lean_hex_mont_from(
        uint64_t p, b_lean_obj_arg ctx, uint64_t a) {
    uint64_t p_prime = lean_ctor_get_uint64(ctx, 0);
    return hex_montgomery_reduce(p, p_prime, 0, a);
}

LEAN_EXPORT uint64_t lean_hex_mont_mul(
        uint64_t p, b_lean_obj_arg ctx, uint64_t a, uint64_t b) {
    uint64_t p_prime = lean_ctor_get_uint64(ctx, 0);
    __uint128_t product = (__uint128_t)a * (__uint128_t)b;
    return hex_montgomery_reduce(
        p, p_prime, (uint64_t)(product >> 64), (uint64_t)product);
}

/* Allocation-free counterparts of `Hex.addModWord` and `Hex.subModWord`.
 * Their Lean definitions use pair-returning carry/borrow primitives so the
 * full-word overflow argument is easy to verify.  The runtime contracts are
 * the same: both inputs are reduced below the nonzero modulus.
 */
LEAN_EXPORT uint64_t lean_hex_word_mod_add(uint64_t m, uint64_t a, uint64_t b) {
    uint64_t sum = a + b;
    uint8_t carry = sum < a;
    return (carry || sum >= m) ? sum - m : sum;
}

LEAN_EXPORT uint64_t lean_hex_word_mod_sub(uint64_t m, uint64_t a, uint64_t b) {
    uint64_t diff = a - b;
    return a < b ? diff + m : diff;
}

static lean_obj_res hex_word_poly_add_sub(
        uint64_t modulus, b_lean_obj_arg a_arr,
        b_lean_obj_arg b_arr, uint8_t subtract) {
    size_t na = lean_array_size(a_arr);
    size_t nb = lean_array_size(b_arr);
    size_t nk = na > nb ? na : nb;
    lean_object* out = lean_alloc_array(nk, nk);
    for (size_t k = 0; k < nk; ++k) {
        uint64_t a = k < na
            ? lean_unbox_uint64(lean_array_get_core(a_arr, k)) : 0;
        uint64_t b = k < nb
            ? lean_unbox_uint64(lean_array_get_core(b_arr, k)) : 0;
        uint64_t result;
        if (subtract) {
            uint64_t diff = a - b;
            result = a < b ? diff + modulus : diff;
        } else {
            uint64_t sum = a + b;
            uint8_t carry = sum < a;
            result = (carry || sum >= modulus) ? sum - modulus : sum;
        }
        lean_array_set_core(out, k, lean_box_uint64(result));
    }
    while (nk > 0) {
        uint64_t last = lean_unbox_uint64(lean_array_get_core(out, nk - 1));
        if (last != 0) break;
        out = lean_array_pop(out);
        --nk;
    }
    return out;
}

LEAN_EXPORT lean_obj_res lean_hex_word_poly_add(
        uint64_t modulus, b_lean_obj_arg ctx,
        b_lean_obj_arg a_arr, b_lean_obj_arg b_arr) {
    (void)ctx;
    return hex_word_poly_add_sub(modulus, a_arr, b_arr, 0);
}

LEAN_EXPORT lean_obj_res lean_hex_word_poly_sub(
        uint64_t modulus, b_lean_obj_arg ctx,
        b_lean_obj_arg a_arr, b_lean_obj_arg b_arr) {
    (void)ctx;
    return hex_word_poly_add_sub(modulus, a_arr, b_arr, 1);
}

/* Dense polynomial convolution over Montgomery representatives modulo an odd
 * machine word.  `DensePoly (WordMod ctx)` erases to its coefficient array and
 * `WordMod` erases to its UInt64 field, so the FFI surface can operate directly
 * on the two arrays.  Each coefficient follows the verified Lean kernel's
 * increasing-i accumulation order.  Unlike the small-prime FpPoly kernel, a
 * full-word modulus cannot safely accumulate products lazily: reduce every
 * product and addition before continuing.
 */
LEAN_EXPORT lean_obj_res lean_hex_word_poly_mul(
        uint64_t modulus, b_lean_obj_arg ctx,
        b_lean_obj_arg a_arr, b_lean_obj_arg b_arr) {
    size_t na = lean_array_size(a_arr);
    size_t nb = lean_array_size(b_arr);
    if (na == 0 || nb == 0) {
        return lean_alloc_array(0, 0);
    }

    uint64_t p_prime = lean_ctor_get_uint64(ctx, 0);
    size_t nk = na + nb - 1;
    lean_object* out = lean_alloc_array(nk, nk);
    for (size_t k = 0; k < nk; ++k) {
        uint64_t acc = 0;
        size_t i_lo = (k + 1 > nb) ? (k + 1 - nb) : 0;
        size_t i_hi = (k < na) ? k : (na - 1);
        for (size_t i = i_lo; i <= i_hi; ++i) {
            uint64_t ai = lean_unbox_uint64(lean_array_get_core(a_arr, i));
            uint64_t bj = lean_unbox_uint64(lean_array_get_core(b_arr, k - i));
            __uint128_t product = (__uint128_t)ai * (__uint128_t)bj;
            uint64_t term = hex_montgomery_reduce(
                modulus, p_prime,
                (uint64_t)(product >> 64), (uint64_t)product);
            uint64_t sum = acc + term;
            uint8_t carry = sum < acc;
            acc = (carry || sum >= modulus) ? sum - modulus : sum;
        }
        lean_array_set_core(out, k, lean_box_uint64(acc));
    }

    /* `DensePoly.ofCoeffs` normalizes trailing zeros.  Products over a prime
     * power can acquire one, so mirror that normalization at the boundary. */
    while (nk > 0) {
        uint64_t last = lean_unbox_uint64(lean_array_get_core(out, nk - 1));
        if (last != 0) break;
        out = lean_array_pop(out);
        --nk;
    }
    return out;
}

/* Fused `(a * b) + (c * d)` over Montgomery coefficient arrays.  Computing
 * both convolutions into one accumulator removes the two temporary product
 * arrays and the subsequent addition array used by the generic expression.
 */
LEAN_EXPORT lean_obj_res lean_hex_word_poly_mul_add(
        uint64_t modulus, b_lean_obj_arg ctx,
        b_lean_obj_arg a_arr, b_lean_obj_arg b_arr,
        b_lean_obj_arg c_arr, b_lean_obj_arg d_arr) {
    size_t na = lean_array_size(a_arr);
    size_t nb = lean_array_size(b_arr);
    size_t nc = lean_array_size(c_arr);
    size_t nd = lean_array_size(d_arr);
    size_t nab = (na == 0 || nb == 0) ? 0 : na + nb - 1;
    size_t ncd = (nc == 0 || nd == 0) ? 0 : nc + nd - 1;
    size_t nk = nab > ncd ? nab : ncd;
    if (nk == 0) {
        return lean_alloc_array(0, 0);
    }

    uint64_t p_prime = lean_ctor_get_uint64(ctx, 0);
    lean_object* out = lean_alloc_array(nk, nk);
    for (size_t k = 0; k < nk; ++k) {
        uint64_t acc = 0;
        if (k < nab) {
            size_t i_lo = (k + 1 > nb) ? (k + 1 - nb) : 0;
            size_t i_hi = (k < na) ? k : (na - 1);
            for (size_t i = i_lo; i <= i_hi; ++i) {
                uint64_t ai = lean_unbox_uint64(
                    lean_array_get_core(a_arr, i));
                uint64_t bj = lean_unbox_uint64(
                    lean_array_get_core(b_arr, k - i));
                __uint128_t product = (__uint128_t)ai * (__uint128_t)bj;
                uint64_t term = hex_montgomery_reduce(
                    modulus, p_prime,
                    (uint64_t)(product >> 64), (uint64_t)product);
                uint64_t sum = acc + term;
                uint8_t carry = sum < acc;
                acc = (carry || sum >= modulus) ? sum - modulus : sum;
            }
        }
        if (k < ncd) {
            size_t i_lo = (k + 1 > nd) ? (k + 1 - nd) : 0;
            size_t i_hi = (k < nc) ? k : (nc - 1);
            for (size_t i = i_lo; i <= i_hi; ++i) {
                uint64_t ci = lean_unbox_uint64(
                    lean_array_get_core(c_arr, i));
                uint64_t dj = lean_unbox_uint64(
                    lean_array_get_core(d_arr, k - i));
                __uint128_t product = (__uint128_t)ci * (__uint128_t)dj;
                uint64_t term = hex_montgomery_reduce(
                    modulus, p_prime,
                    (uint64_t)(product >> 64), (uint64_t)product);
                uint64_t sum = acc + term;
                uint8_t carry = sum < acc;
                acc = (carry || sum >= modulus) ? sum - modulus : sum;
            }
        }
        lean_array_set_core(out, k, lean_box_uint64(acc));
    }

    while (nk > 0) {
        uint64_t last = lean_unbox_uint64(lean_array_get_core(out, nk - 1));
        if (last != 0) break;
        out = lean_array_pop(out);
        --nk;
    }
    return out;
}
