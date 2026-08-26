#include <lean/lean.h>
#include <stdbool.h>

#ifdef LEAN_USE_GMP
#include <lean/lean_gmp.h>
#endif

static lean_obj_res mk_pair(lean_obj_arg fst, lean_obj_arg snd) {
    lean_object * pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, fst);
    lean_ctor_set(pair, 1, snd);
    return pair;
}

static lean_obj_res mk_extgcd_result(lean_obj_arg g, lean_obj_arg s, lean_obj_arg t) {
    return mk_pair(g, mk_pair(s, t));
}

#ifdef LEAN_USE_GMP
static void lean_int_to_mpz(b_lean_obj_arg n, mpz_t out) {
    if (lean_is_scalar(n)) {
        mpz_init_set_si(out, lean_scalar_to_int64(n));
    } else {
        mpz_init(out);
        lean_extract_mpz_value(n, out);
    }
}

/* `lean_alloc_mpz` constructs the heap representation used only outside
   Lean's tagged-scalar range.  Normalize small GMP results before returning
   them across the FFI boundary. */
static lean_obj_res lean_nat_from_mpz(mpz_t n) {
    if (mpz_fits_ulong_p(n)) {
        unsigned long value = mpz_get_ui(n);
        if (value <= LEAN_MAX_SMALL_NAT) {
            return lean_box(value);
        }
    }
    return lean_alloc_mpz(n);
}

static lean_obj_res lean_int_from_mpz(mpz_t n) {
    if (mpz_fits_slong_p(n)) {
        long value = mpz_get_si(n);
        if (LEAN_MIN_SMALL_INT <= value && value <= LEAN_MAX_SMALL_INT) {
            return lean_int64_to_int((int64_t)value);
        }
    }
    return lean_alloc_mpz(n);
}
#else
static lean_obj_res lean_int_extgcd_fallback(b_lean_obj_arg a, b_lean_obj_arg b) {
    lean_object * zero = lean_box(0);
    lean_object * old_r = a;
    lean_object * r = b;
    lean_object * old_s = lean_int_to_int(1);
    lean_object * s = lean_box(0);
    lean_object * old_t = lean_box(0);
    lean_object * t = lean_int_to_int(1);

    lean_inc(old_r);
    lean_inc(r);

    while (!lean_int_eq(r, zero)) {
        lean_object * q = lean_int_ediv(old_r, r);
        lean_object * next_r = lean_int_emod(old_r, r);
        lean_object * qs = lean_int_mul(q, s);
        lean_object * next_s = lean_int_sub(old_s, qs);
        lean_object * qt = lean_int_mul(q, t);
        lean_object * next_t = lean_int_sub(old_t, qt);

        lean_dec(q);
        lean_dec(qs);
        lean_dec(qt);
        lean_dec(old_r);
        lean_dec(old_s);
        lean_dec(old_t);

        old_r = r;
        r = next_r;
        old_s = s;
        s = next_s;
        old_t = t;
        t = next_t;
    }

    lean_dec(r);
    lean_dec(s);
    lean_dec(t);

    if (lean_int_lt(old_r, zero)) {
        lean_object * normalized_s = lean_int_neg(old_s);
        lean_object * normalized_t = lean_int_neg(old_t);
        lean_dec(old_s);
        lean_dec(old_t);
        old_s = normalized_s;
        old_t = normalized_t;
    }

    lean_object * g = lean_nat_abs(old_r);
    lean_object * result = mk_extgcd_result(g, old_s, old_t);
    lean_dec(old_r);
    return result;
}
#endif

LEAN_EXPORT lean_obj_res lean_hex_mpz_gcdext(b_lean_obj_arg a, b_lean_obj_arg b) {
#ifdef LEAN_USE_GMP
    mpz_t a_z;
    mpz_t b_z;
    mpz_t g_z;
    mpz_t s_z;
    mpz_t t_z;

    lean_int_to_mpz(a, a_z);
    lean_int_to_mpz(b, b_z);
    mpz_inits(g_z, s_z, t_z, NULL);

    mpz_gcdext(g_z, s_z, t_z, a_z, b_z);

    lean_object * g = lean_nat_from_mpz(g_z);
    lean_object * s = lean_int_from_mpz(s_z);
    lean_object * t = lean_int_from_mpz(t_z);
    lean_object * result = mk_extgcd_result(g, s, t);

    mpz_clears(a_z, b_z, g_z, s_z, t_z, NULL);
    return result;
#else
    return lean_int_extgcd_fallback(a, b);
#endif
}
