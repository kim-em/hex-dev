/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsMathlib.QueryGcd
public import Mathlib.Data.Rat.Cast.Order

public section

namespace HexRealRootsMathlib.Query

open Hex DensePoly HexPolyMathlib.Interpret

theorem int_zero (z : Int) : (z : Rat) = 0 ↔ z = 0 := Int.cast_eq_zero

/-- Interpret the actual integer coefficient array in the fraction field. -/
noncomputable abbrev integerPoly := interpret (fun z : Int => (z : Rat)) int_zero

/-- Nonzero integer polynomials have positive content, regardless of the sign
of their leading coefficient. -/
theorem content_pos (p : ZPoly) (hp : p ≠ 0) : 0 < content p := by
  have hnonneg : 0 ≤ content p := by
    change 0 ≤ (contentNat p : Int)
    exact Int.natCast_nonneg _
  have hn : content p ≠ 0 := by
    intro hc
    apply hp
    apply ext_coeff
    intro i
    rw [coeff_zero]
    have hd := content_dvd_coeff p i
    rw [hc] at hd
    exact zero_dvd_iff.mp hd
  exact lt_of_le_of_ne hnonneg (Ne.symm hn)

/-- The integer backend's exact content division has the shared positive
normalization law in the semantic fraction field. -/
theorem integer_normalize (p : ZPoly) (hp : p ≠ 0) :
    0 < ((ZPoly.queryNormalize p).1 : Rat) ∧
      Polynomial.C ((ZPoly.queryNormalize p).1 : Rat) * integerPoly (ZPoly.queryNormalize p).2 =
        integerPoly p := by
  constructor
  · exact Int.cast_pos.mpr (content_pos p hp)
  · change Polynomial.C (content p : Rat) * integerPoly (primitivePart p) = integerPoly p
    exact (interpret_scale (fun z : Int => (z : Rat)) int_zero (fun a b => Int.cast_mul a b)
      (content p) (primitivePart p)).symm.trans (congrArg integerPoly (content_mul_primitivePart p))

/-- Every produced integer signed chain passes literal replay, including
singleton chains and chains with a nonconstant terminal gcd. -/
theorem integer_chain_checks (p g : ZPoly) (hp : p ≠ 0) :
    SignedRemainderChain.check Int.sign p g (SignedRemainderChain.build Int.sign ZPoly.queryNormalize p g) = true :=
  build_checks (fun z : Int => (z : Rat)) int_zero
    (fun a b => Int.cast_add a b) (fun a b => Int.cast_sub a b) (fun a b => Int.cast_mul a b)
    Int.cast_one (fun a => Int.cast_neg a) Int.sign
    (fun a => by simp only [Int.sign_eq_one_iff_pos, Int.cast_pos])
    (fun a => by simp only [Int.sign_neg_iff, Int.cast_lt_zero])
    ZPoly.queryNormalize integer_normalize p g hp

/-- Exact dyadic evaluation and the infinity adapter return three-valued signs. -/
theorem integer_signs (p : ZPoly) (e : Endpoint Dyadic) :
    -1 ≤ e.signAt Int.sign ZPoly.queryAdapter p ∧ e.signAt Int.sign ZPoly.queryAdapter p ≤ 1 := by
  apply Endpoint.signAt_bounds
  · intro c
    rcases Int.sign_trichotomy c with h | h | h <;> omega
  · intro q x
    change -1 ≤ dyadicSign (ZPoly.evalDyadic q x) ∧ dyadicSign (ZPoly.evalDyadic q x) ≤ 1
    cases ZPoly.evalDyadic q x with
    | zero => simp only [dyadicSign]; omega
    | ofOdd n k hn =>
      simp only [dyadicSign]
      split <;> omega

/-- Every produced integer/dyadic certificate is accepted with its literal
input bindings and the same value returned by the query frontend. -/
theorem integer_certify_checks (p g : ZPoly) (I : DyadicInterval) (cert : TarskiReplay)
    (hcert : TarskiReplay.certify p g I = some cert) :
    TarskiReplay.check p g I cert.value cert = true ∧ ZPoly.tarskiQuery p g I = some cert.value := by
  constructor
  · exact QueryReplay.certify_checks Int.sign ZPoly.queryAdapter ZPoly.queryNormalize
      integer_chain_checks integer_signs () p g (.finite I.lower) (.finite I.upper) cert hcert
  · change (QueryReplay.certify Int.sign ZPoly.queryAdapter ZPoly.queryNormalize () p g
      (.finite I.lower) (.finite I.upper)).map QueryReplay.value = some cert.value
    rw [show QueryReplay.certify Int.sign ZPoly.queryAdapter ZPoly.queryNormalize () p g
      (.finite I.lower) (.finite I.upper) = some cert from hcert]
    rfl

/-- The integer frontend has no resource-exhaustion failure: its `Option`
records exactly the endpoint guards and squarefreeness over the fraction field. -/
theorem integer_query_isSome (p g : ZPoly) (I : DyadicInterval) :
    (ZPoly.tarskiQuery p g I).isSome = true ↔
      QueryReplay.endpointGuards ZPoly.queryAdapter p (.finite I.lower) (.finite I.upper) = true ∧
        Squarefree (integerPoly p) := by
  exact query_isSome (fun z : Int => (z : Rat)) int_zero
    (fun a b => Int.cast_add a b) (fun a b => Int.cast_sub a b) (fun a b => Int.cast_mul a b)
    (fun n => by simp only [Int.cast_natCast]) Int.sign
    (fun a => by simp only [Int.sign_eq_one_iff_pos, Int.cast_pos]) Int.cast_one
    ZPoly.queryAdapter ZPoly.queryNormalize integer_chain_checks p g (.finite I.lower) (.finite I.upper)

end HexRealRootsMathlib.Query

