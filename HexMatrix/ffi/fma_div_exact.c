#include <lean/lean.h>

#ifdef LEAN_USE_GMP
#include <lean/lean_gmp.h>

static void lean_int_to_mpz(b_lean_obj_arg n, mpz_t out) {
    if (lean_is_scalar(n)) {
        mpz_init_set_si(out, lean_scalar_to_int64(n));
    } else {
        mpz_init(out);
        lean_extract_mpz_value(n, out);
    }
}
#endif

/* Compute `(a * b - c * d) / e` as a single Lean `Int`.

   Matches the Lean definition
       Hex.Matrix.fmaDivExact a b c d e := Hex.Matrix.exactDiv (a * b - c * d) e
   and is invoked via `@[extern "lean_hex_int_fma_div_exact"]`.

   Divisibility of `(a * b - c * d)` by `e` is an algorithmic precondition
   at every call site (the Bareiss recurrence); when it fails, behaviour
   matches the Lean fallback (`(a * b - c * d) / e` via `Int.divExact`).

   The GMP path performs at most one heap mpz allocation for the result,
   replacing the four-step Lean expression (which allocates one mpz per
   intermediate product, the subtraction, and the quotient). */
LEAN_EXPORT lean_obj_res lean_hex_int_fma_div_exact(
        b_lean_obj_arg a, b_lean_obj_arg b,
        b_lean_obj_arg c, b_lean_obj_arg d,
        b_lean_obj_arg e) {
#ifdef LEAN_USE_GMP
    mpz_t a_z, b_z, c_z, d_z, e_z;
    mpz_t lhs, rhs, q;
    lean_int_to_mpz(a, a_z);
    lean_int_to_mpz(b, b_z);
    lean_int_to_mpz(c, c_z);
    lean_int_to_mpz(d, d_z);
    lean_int_to_mpz(e, e_z);
    mpz_init(lhs);
    mpz_init(rhs);
    mpz_init(q);

    mpz_mul(lhs, a_z, b_z);
    mpz_mul(rhs, c_z, d_z);
    mpz_sub(lhs, lhs, rhs);
    mpz_divexact(q, lhs, e_z);

    lean_object * result = lean_alloc_mpz(q);

    mpz_clears(a_z, b_z, c_z, d_z, e_z, lhs, rhs, q, NULL);
    return result;
#else
    lean_object * ab = lean_int_mul(a, b);
    lean_object * cd = lean_int_mul(c, d);
    lean_object * diff = lean_int_sub(ab, cd);
    lean_object * result = lean_int_div_exact(diff, e);
    lean_dec(ab);
    lean_dec(cd);
    lean_dec(diff);
    return result;
#endif
}
