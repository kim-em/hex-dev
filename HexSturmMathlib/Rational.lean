/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Domain
public import HexRealRootsMathlib.QueryDomain

public section

namespace HexSturmMathlib

open Hex HexPolyMathlib.Interpret HexRealRootsMathlib

/-- Positive denominator clearing has the same real interpretation as the
existing integer and rational polynomial correspondence. -/
theorem clear_real (p : DensePoly Rat) :
    toPolyℝ (ZPoly.clearDenominators p).2 =
      Polynomial.C ((ZPoly.clearDenominators p).1 : ℝ) *
        interpret (fun x : Rat => (x : ℝ)) (fun _ => Rat.cast_eq_zero) p := by
  ext i
  have h := congrArg (fun q : DensePoly Rat => q.coeff i) (ZPoly.toRatPoly_clearDenominators p)
  simp only [ZPoly.coeff_toRatPoly, DensePoly.coeff_scale _ _ _ (mul_zero _)] at h
  simp only [coeff_toPolyℝ, Polynomial.coeff_C_mul, coeff_interpret]
  exact_mod_cast h

/-- The rational and integer/dyadic frontends reject exactly the same domains
after positive denominator clearing. This establishes the invalid `none` cases;
it does not assert equality of successful query values. -/
theorem query_rat_domain (p g : DensePoly Rat) (I : DyadicInterval) :
    (Sturm.query Sturm.orderSign p g (.finite I.lower.toRat) (.finite I.upper.toRat)).isSome =
      (ZPoly.tarskiQuery (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2 I).isSome := by
  have hfield := query_isSome (fun x : Rat => (x : ℝ)) (fun _ => Rat.cast_eq_zero)
    (fun a b => Rat.cast_add a b) (fun a b => Rat.cast_sub a b) (fun a b => Rat.cast_mul a b)
    Sturm.orderSign
    (fun x => (orderSign_spec x).2.1.trans Rat.cast_lt_zero.symm)
    (fun x => (orderSign_spec x).2.2.1.trans Rat.cast_eq_zero.symm)
    Rat.cast_one (fun a => Rat.cast_neg a) (fun a => Rat.cast_inv a)
    (fun n => by simp) (fun x => (orderSign_spec x).1.trans Rat.cast_pos.symm)
    p g (.finite I.lower.toRat) (.finite I.upper.toRat)
  have hc : ((ZPoly.clearDenominators p).1 : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (ZPoly.clearDenominators_pos p)
  have hC : (Polynomial.C ((ZPoly.clearDenominators p).1 : ℝ) : Polynomial ℝ) ≠ 0 :=
    Polynomial.C_ne_zero.mpr hc
  have hsf := (associated_unit_mul_left
    (interpret (fun x : Rat => (x : ℝ)) (fun _ => Rat.cast_eq_zero) p)
    (Polynomial.C ((ZPoly.clearDenominators p).1 : ℝ))
    ((isUnit_iff_ne_zero.mpr hc).map Polynomial.C)).squarefree_iff
  have horder : (I.lower.toRat : ℝ) < (I.upper.toRat : ℝ) := by
    simpa only [toReal_eq_cast_toRat] using (toReal_lt_toReal I.lt)
  have hnz : (ZPoly.clearDenominators p).2 ≠ 0 ↔
      toPolyℝ (ZPoly.clearDenominators p).2 ≠ 0 :=
    not_congr toPolyℝ_eq_zero_iff.symm
  apply Bool.eq_iff_iff.mpr
  rw [hfield, Query.integer_domain, hnz, clear_real]
  simp only [Domain, EndpointLt, Nonvanishing, horder, true_and, hsf,
    mul_ne_zero_iff, Polynomial.eval_mul, Polynomial.eval_C, toReal_eq_cast_toRat]
  constructor
  · rintro ⟨hp, hs, ha, hb⟩
    exact ⟨⟨hC, hp⟩, hs, ⟨hc, ha⟩, hc, hb⟩
  · rintro ⟨⟨_, hp⟩, hs, ⟨_, ha⟩, _, hb⟩
    exact ⟨hp, hs, ha, hb⟩

end HexSturmMathlib
