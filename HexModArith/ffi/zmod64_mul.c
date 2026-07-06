#include <lean/lean.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdint.h>

typedef unsigned long mp_limb_t;
typedef struct {
    int _mp_alloc;
    int _mp_size;
    mp_limb_t* _mp_d;
} __mpz_struct;
typedef __mpz_struct mpz_t[1];

extern void __gmpz_init(mpz_t);
extern void __gmpz_clear(mpz_t);
extern void* __gmpz_export(void*, size_t*, int, size_t, int, size_t, const mpz_t);
extern void lean_extract_mpz_value(lean_object*, mpz_t);

/* `ZMod64.Bounds p` guarantees `0 < p < 2^31` (`Bounds.pLtR`), so the modulus
   fits in a `uint64_t` and reading it needs no width check. Because both inputs
   are reduced residues `< p < 2^31`, their product is `< 2^62` and fits in a
   single `uint64_t`: no `__uint128_t` is needed, and the reduction is a plain
   64/64 division rather than a 128/64 one. The result is byte-identical to the
   pure Lean fallback `ofNat p (a * b)`. */

LEAN_EXPORT uint64_t lean_hex_zmod64_mul(b_lean_obj_arg p, uint64_t a, uint64_t b) {
    uint64_t modulus = lean_uint64_of_nat(p);
    uint64_t product = a * b;
    return product % modulus;
}

static uint64_t lean_hex_mul_mod_word(uint64_t a, uint64_t b, uint64_t modulus) {
    __uint128_t product = (__uint128_t)a * (__uint128_t)b;
    return (uint64_t)(product % modulus);
}

static uint64_t lean_hex_pow_mod_u64(uint64_t base, uint64_t exponent, uint64_t modulus) {
    uint64_t acc = 1 % modulus;

    while (exponent != 0) {
        if ((exponent & 1) != 0) {
            acc = lean_hex_mul_mod_word(acc, base, modulus);
        }
        exponent >>= 1;
        if (exponent != 0) {
            base = lean_hex_mul_mod_word(base, base, modulus);
        }
    }

    return acc;
}

static size_t lean_hex_bit_length_u64(uint64_t word) {
    size_t bits = 0;
    while (word != 0) {
        ++bits;
        word >>= 1;
    }
    return bits;
}

static uint64_t* lean_hex_nat_to_u64_limbs(b_lean_obj_arg exponent, size_t* limb_count) {
    mpz_t exponent_z;
    __gmpz_init(exponent_z);
    lean_extract_mpz_value(exponent, exponent_z);

    uint64_t* limbs =
        (uint64_t*)__gmpz_export(NULL, limb_count, -1, sizeof(uint64_t), 0, 0, exponent_z);
    __gmpz_clear(exponent_z);
    return limbs;
}

static uint64_t lean_hex_pow_mod_big_nat(uint64_t base, b_lean_obj_arg exponent,
        uint64_t modulus) {
    size_t limb_count = 0;
    uint64_t* limbs = lean_hex_nat_to_u64_limbs(exponent, &limb_count);
    uint64_t acc = 1 % modulus;

    if (limb_count != 0) {
        size_t top_bits = lean_hex_bit_length_u64(limbs[limb_count - 1]);
        for (size_t limb_index = limb_count; limb_index > 0; --limb_index) {
            uint64_t limb = limbs[limb_index - 1];
            size_t bit_limit = (limb_index == limb_count) ? top_bits : 64;
            for (size_t bit = bit_limit; bit > 0; --bit) {
                acc = lean_hex_mul_mod_word(acc, acc, modulus);
                if (((limb >> (bit - 1)) & 1) != 0) {
                    acc = lean_hex_mul_mod_word(acc, base, modulus);
                }
            }
        }
    }

    free(limbs);
    return acc;
}

LEAN_EXPORT uint64_t lean_hex_zmod64_pow(b_lean_obj_arg p, uint64_t a, b_lean_obj_arg n) {
    uint64_t modulus = lean_uint64_of_nat(p);

    if (modulus == 1) {
        return 0;
    }

    uint64_t base = a % modulus;

    if (lean_is_scalar(n)) {
        return lean_hex_pow_mod_u64(base, (uint64_t)lean_unbox(n), modulus);
    }

    return lean_hex_pow_mod_big_nat(base, n, modulus);
}

/* Lazy-reduction schoolbook convolution over F_p, backing `FpPoly.fpConvolve`.
   Inputs are two `Array UInt64` of reduced residues (< p < 2^31); the whole
   inner accumulation runs natively in `__uint128_t`, so each output coefficient
   pays exactly one 64-bit reduction instead of one per product term, with no
   per-term FFI boundary or boxed-residue traffic. Value-identical to the Lean
   fallback body (`FpPoly.mulPacked_eq` proves the packed multiply equals `*`). */
LEAN_EXPORT lean_obj_res lean_hex_fp_convolve(b_lean_obj_arg a_arr,
        b_lean_obj_arg b_arr, uint64_t modulus) {
    size_t na = lean_array_size(a_arr);
    size_t nb = lean_array_size(b_arr);
    if (na == 0 || nb == 0) {
        return lean_alloc_array(0, 0);
    }
    size_t nk = na + nb - 1;
    lean_object* out = lean_alloc_array(nk, nk);
    for (size_t k = 0; k < nk; ++k) {
        __uint128_t acc = 0;
        size_t i_lo = (k + 1 > nb) ? (k + 1 - nb) : 0;
        size_t i_hi = (k < na) ? k : (na - 1);
        for (size_t i = i_lo; i <= i_hi; ++i) {
            uint64_t ai = lean_unbox_uint64(lean_array_get_core(a_arr, i));
            uint64_t bj = lean_unbox_uint64(lean_array_get_core(b_arr, k - i));
            acc += (__uint128_t)ai * (__uint128_t)bj;
        }
        /* modulus == 0 would be division-by-zero UB; the pure-Lean fallback
           computes `sum % 0 = sum` reduced into a `UInt64`, i.e. the low 64 bits
           of the (128-bit-truncated) accumulator, so match it here. The real
           callers (`FpPoly.mulPacked`) always pass `0 < modulus < 2^31` with
           reduced word inputs, under which no truncation occurs. */
        uint64_t r = modulus ? (uint64_t)(acc % modulus) : (uint64_t)acc;
        lean_array_set_core(out, k, lean_box_uint64(r));
    }
    return out;
}
