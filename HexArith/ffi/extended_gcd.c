/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Temporary backport of leanprover/lean4#15160 at
3c93b48cf60f7053b0a5b3f2ce646a5196c4fc2f.
The runtime algorithm is adapted to Lean's installed C API instead of its
private C++ mpz class. The mathematical definition and fallback are copied
in HexArith/Nat/ExtendedGcd.lean.

TODO(lean4#15160): once the PR lands and Hex's toolchain provides
Nat.extendedGcd, delete this file, the Lean backport and fallback export,
this object's build rule, and HexArith's explicit -lgmp link flag. Use the toolchain implementation.
*/
#include <lean/lean.h>
/* Lean's GMP runtime exports these functions but its binary distribution does
   not ship gmp.h. Use the same public GMP ABI declarations as zmod64_mul.c;
   the limb pointer is opaque and never dereferenced. */
typedef struct {
    int _mp_alloc;
    int _mp_size;
    void * _mp_d;
} hex_mpz_struct;
typedef hex_mpz_struct mpz_t[1];
extern void __gmpz_init(mpz_t);
extern void __gmpz_clear(mpz_t);
extern void __gmpz_import(mpz_t, size_t, int, size_t, int, size_t, const void *);
extern void * __gmpz_export(void *, size_t *, int, size_t, int, size_t, const mpz_t);
extern size_t __gmpz_sizeinbase(const mpz_t, int);
extern void __gmpz_gcdext(mpz_t, mpz_t, mpz_t, const mpz_t, const mpz_t);
extern lean_obj_res lean_alloc_mpz(mpz_t);
extern void lean_extract_mpz_value(b_lean_obj_arg, mpz_t);

extern lean_obj_res lean_hex_nat_extended_gcd_fallback(lean_obj_arg a, lean_obj_arg b);

/* Inputs are borrowed; GMP receives independent initialized values. Import a
   full machine word, avoiding unsigned-long truncation on LLP64 platforms. */
static void nat_to_mpz(b_lean_obj_arg n, mpz_t out) {
    __gmpz_init(out);
    if (lean_is_scalar(n)) {
        size_t value = lean_unbox(n);
        __gmpz_import(out, 1, -1, sizeof(value), 0, 0, &value);
    } else {
        lean_extract_mpz_value(n, out);
    }
}

/* Only export into the fixed-size word once the bit length guarantees it fits.
   Normalization must cover the entire Lean scalar range, even on LLP64. */
static uint64_t small_magnitude(mpz_t n) {
    uint64_t magnitude = 0;
    size_t count = 0;
    __gmpz_export(&magnitude, &count, -1, sizeof(magnitude), 0, 0, n);
    return magnitude;
}

static lean_obj_res nat_from_mpz(mpz_t n) {
    if (__gmpz_sizeinbase(n, 2) <= 63) {
        uint64_t value = small_magnitude(n);
        if (value <= LEAN_MAX_SMALL_NAT)
            return lean_box((size_t)value);
    }
    return lean_alloc_mpz(n);
}

static lean_obj_res int_from_mpz(mpz_t n) {
    if (__gmpz_sizeinbase(n, 2) <= 63) {
        int64_t value = (int64_t)small_magnitude(n);
        if (n[0]._mp_size < 0) value = -value;
        if (LEAN_MIN_SMALL_INT <= value && value <= LEAN_MAX_SMALL_INT)
            return lean_int64_to_int(value);
    }
    return lean_alloc_mpz(n);
}

LEAN_EXPORT lean_obj_res lean_hex_nat_extended_gcd(b_lean_obj_arg a, b_lean_obj_arg b) {
    if (a != lean_box(0) && b != lean_box(0) && !lean_nat_dec_eq(a, b) &&
        !(lean_is_scalar(a) && lean_is_scalar(b) &&
          lean_unbox(a) <= UINT16_MAX && lean_unbox(b) <= UINT16_MAX)) {
        mpz_t aa, bb, g, s, t;
        nat_to_mpz(a, aa);
        nat_to_mpz(b, bb);
        __gmpz_init(g);
        __gmpz_init(s);
        __gmpz_init(t);
        /* Upstream uses the Lean reference for zero/equal inputs. Elsewhere
           the final Euclidean quotient is at least two, giving GMP's
           coefficient convention, including the half-size ties. */
        __gmpz_gcdext(g, s, t, aa, bb);
        lean_object * result = lean_alloc_ctor(0, 3, 0);
        lean_ctor_set(result, 0, nat_from_mpz(g));
        lean_ctor_set(result, 1, int_from_mpz(s));
        lean_ctor_set(result, 2, int_from_mpz(t));
        __gmpz_clear(aa);
        __gmpz_clear(bb);
        __gmpz_clear(g);
        __gmpz_clear(s);
        __gmpz_clear(t);
        return result;
    }
    lean_inc(a);
    lean_inc(b);
    return lean_hex_nat_extended_gcd_fallback(a, b);
}
