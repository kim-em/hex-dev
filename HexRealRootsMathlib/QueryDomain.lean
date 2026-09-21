/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsMathlib.QueryInteger
public import HexRealRootsMathlib.ChainCorrespond

public section

namespace HexRealRootsMathlib.Query

open Hex DensePoly HexPolyMathlib.Interpret

/-- The actual dyadic sign reflects strict negativity of its real value. -/
theorem dyadicSign_neg (d : Dyadic) : dyadicSign d < 0 ↔ Dyadic.toReal d < 0 := by
  have h : (dyadicSign d : ℝ) < 0 ↔ Dyadic.toReal d < 0 := by
    rw [← sign_eq_neg_one_iff, sign_dyadicSign, sign_eq_neg_one_iff]
  exact Int.cast_lt_zero.symm.trans h

/-- The integer frontend's executable endpoint guards are exactly head and
endpoint nonvanishing. Its interval already certifies strict endpoint order. -/
theorem integer_guards (p : ZPoly) (I : DyadicInterval) :
    QueryReplay.endpointGuards ZPoly.queryAdapter p (.finite I.lower) (.finite I.upper) = true ↔
      p ≠ 0 ∧ (toPolyℝ p).eval (Dyadic.toReal I.lower) ≠ 0 ∧
        (toPolyℝ p).eval (Dyadic.toReal I.upper) ≠ 0 := by
  have horder : dyadicSign (I.lower - I.upper) < 0 := by
    apply (dyadicSign_neg _).mpr
    simpa only [toReal_eq_cast_toRat, Dyadic.toRat_sub, Rat.cast_sub] using
      sub_neg.mpr (toReal_lt_toReal I.lt)
  have hp : (!p.isZero) = true ↔ p ≠ 0 := by
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    change (¬ p.isZero = true) ↔ _
    rw [DensePoly.isZero_eq_true_iff, DensePoly.size_eq_zero_iff]
  have he (x : Dyadic) : (dyadicSign (p.evalDyadic x) != 0) = true ↔
      (toPolyℝ p).eval (Dyadic.toReal x) ≠ 0 := by
    rw [bne_iff_ne]
    exact not_congr (evalSign_zero_iff p x)
  simp only [QueryReplay.endpointGuards, Endpoint.lt, Endpoint.rootFree, ZPoly.queryAdapter,
    Bool.and_eq_true, decide_eq_true_eq, hp, horder, he, and_true, and_assoc]

/-- The generic integer interpretation agrees with the existing real-polynomial
correspondence, rather than defining a second semantic polynomial. -/
theorem interpret_int_real (p : ZPoly) :
    interpret (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero) p = toPolyℝ p := by
  ext i
  simp only [coeff_interpret, coeff_toPolyℝ]

/-- Integer/dyadic Tarski production succeeds exactly on its mathematical
open-interval domain. No root-sum theorem or resource bound is assumed. -/
theorem integer_domain (p g : ZPoly) (I : DyadicInterval) :
    (ZPoly.tarskiQuery p g I).isSome = true ↔
      p ≠ 0 ∧ Squarefree (toPolyℝ p) ∧
        (toPolyℝ p).eval (Dyadic.toReal I.lower) ≠ 0 ∧
        (toPolyℝ p).eval (Dyadic.toReal I.upper) ≠ 0 := by
  have h := query_isSome (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero)
    (fun a b => Int.cast_add a b) (fun a b => Int.cast_sub a b) (fun a b => Int.cast_mul a b)
    (fun n => by simp only [Int.cast_natCast]) Int.sign
    (fun a => by simp only [Int.sign_eq_one_iff_pos, Int.cast_pos]) Int.cast_one
    ZPoly.queryAdapter ZPoly.queryNormalize integer_chain_checks p g (.finite I.lower) (.finite I.upper)
  change (QueryReplay.query Int.sign ZPoly.queryAdapter ZPoly.queryNormalize p g
    (.finite I.lower) (.finite I.upper)).isSome = true ↔ _
  rw [h, integer_guards, interpret_int_real]
  simp only [and_left_comm, and_comm]

/-- An accepted integer certificate proves the same mathematical domain using
only its supplied squarefree chain and exact dyadic endpoint checks. -/
theorem integer_replay_domain (p g : ZPoly) (I : DyadicInterval) (value : Int) (cert : TarskiReplay)
    (hc : TarskiReplay.check p g I value cert = true) :
    p ≠ 0 ∧ Squarefree (toPolyℝ p) ∧
      (toPolyℝ p).eval (Dyadic.toReal I.lower) ≠ 0 ∧
      (toPolyℝ p).eval (Dyadic.toReal I.upper) ≠ 0 := by
  simp only [TarskiReplay.check, QueryReplay.check, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] at hc
  obtain ⟨_, _, _, _, _, _, hg, hsf, hconst, _⟩ := hc
  obtain ⟨hp, ha, hb⟩ := (integer_guards p I).mp hg
  have h := (check_squarefree (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero)
    (fun a b => Int.cast_add a b) (fun a b => Int.cast_sub a b) (fun a b => Int.cast_mul a b)
    (fun n => by simp only [Int.cast_natCast]) Int.sign
    (fun a => by simp only [Int.sign_eq_one_iff_pos, Int.cast_pos]) Int.cast_one
    p cert.squarefree hsf).mp hconst
  rw [interpret_int_real] at h
  exact ⟨hp, h, ha, hb⟩

end HexRealRootsMathlib.Query
