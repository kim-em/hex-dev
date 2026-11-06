/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.PolynomialBounds
public import HexRCF.RealCoefficients.QueryReplay
public import HexMvPolyTheory.Aeval
public import HexOrderedFnTheory.Oracle
public section

namespace Hex.RCF.RealCoefficients.PolynomialBounds
open Hex.OrderedFn.Oracle
open scoped Hex.RCF.RealCoefficients.PolynomialBounds

/-- Evaluate coefficient polynomials at the same fixed real values. -/
@[expose] noncomputable def value (values : Fin n → ℝ) (p : Poly n) : ℝ :=
  MvPoly.eval₂ (Rat.castHom ℝ) values p

/-- Fixed coefficient substitution is a total ring interpretation. It may
identify different stored polynomials and requires no transcendence premise. -/
theorem closed (values : Fin n → ℝ) :
    Hex.RealClosure.Transport.Closed (value values) (fun _ => True) := by
  let f : Poly n →+* ℝ := HexMvPolyTheory.eval₂Hom (Rat.castHom ℝ) values
  exact {
    zero := trivial
    one := trivial
    add := fun _ _ _ _ => trivial
    mul := fun _ _ _ _ => trivial
    sub := fun _ _ _ _ => trivial
    natCast := fun _ => trivial
    read_zero := f.map_zero
    read_one := f.map_one
    read_add := fun a b _ _ => f.map_add a b
    read_mul := fun a b _ _ => f.map_mul a b
    read_sub := fun a b _ _ => map_sub f a b
    read_natCast := fun k => map_natCast f k }

private theorem power (b : Bounds) (x : ℝ) (contained : Contains b x) (k : Nat) :
    Contains (Mono.powBySq b k) (Mono.powBySq x k) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simpa [Mono.powBySq] using Contains.singleton 1
    | succ k =>
      have smaller : (k + 1) / 2 < k + 1 := Nat.div_lt_self (by omega) (by decide)
      have square := (ih _ smaller).mul (ih _ smaller)
      by_cases even : (k + 1) % 2 = 0
      · simpa only [Mono.powBySq, ite_eq_left even, mul_eq] using square
      · simpa only [Mono.powBySq, ite_eq_right even, mul_eq] using square.mul contained

private theorem monomial (bounds : Fin n → Bounds) (values : Fin n → ℝ)
    (contained : ∀ i, Contains (bounds i) (values i)) (m : Mono n) :
    Contains (Mono.prod bounds m) (Mono.prod values m) := by
  have fold (indices : List (Fin n)) (b : Bounds) (x : ℝ) (hb : Contains b x) :
      Contains (indices.foldl (fun acc i => acc * Mono.powBySq (bounds i) m[i]) b)
        (indices.foldl (fun acc i => acc * Mono.powBySq (values i) m[i]) x) := by
    induction indices generalizing b x with
    | nil => exact hb
    | cons i rest ih =>
      exact ih _ _ (hb.mul (power _ _ (contained i) _))
  simpa only [Mono.prod, one_eq] using fold (List.finRange n) (Bounds.singleton 1) 1
    (by simpa using Contains.singleton 1)

/-- Enclosure uses the same fixed valuation as polynomial interpretation.
No narrowing, convergence, independence or coefficient-field law is assumed. -/
theorem enclose_sound (bounds : Fin n → Bounds) (values : Fin n → ℝ)
    (contained : ∀ i, Contains (bounds i) (values i)) (p : Poly n) :
    Contains (enclose bounds p) (value values p) := by
  unfold enclose value
  rw [MvPoly.eval₂_eq]
  have fold (terms : List (Mono n × Rat)) (b : Bounds) (x : ℝ) (hb : Contains b x) :
      Contains
        (terms.foldl (fun acc term => acc.add
          ((Bounds.singleton term.2).mul (Mono.prod bounds term.1))) b)
        (terms.foldl (fun acc term => acc + (term.2 : ℝ) * Mono.prod values term.1) x) := by
    induction terms generalizing b x with
    | nil => exact hb
    | cons term rest ih =>
      exact ih _ _ (hb.add ((Contains.singleton term.2).mul
        (monomial bounds values contained term.1)))
  exact fold p.termsList _ _ (by simpa using Contains.singleton 0)

theorem sign_spec (bounds : Fin n → Bounds) (values : Fin n → ℝ)
    (contained : ∀ i, Contains (bounds i) (values i)) (p : Poly n)
    (observed : Int) (accepted : sign? bounds p = some observed) :
    observed = (SignType.sign (value values p) : Int) :=
  (enclose_sound bounds values contained p).exactSign accepted

section Native
attribute [local instance 2500] MvPoly.instZero MvPoly.instOneOfLawfulBEq
  MvPoly.instAddOfLawfulBEq
  MvPoly.instMulOfAddOfLawfulBEq MvPoly.instNegOfLawfulBEq MvPoly.instSubOfAddOfNegOfLawfulBEq
  MvPoly.instNatCast

/-- Interpret the computational operations captured by the Mathlib-free
compiler, independently of Mathlib's bundled polynomial ring instances. -/
theorem closed_native (values : Fin n → ℝ) :
    Hex.RealClosure.Transport.Closed (value values) (fun _ => True) := by
  exact {
    zero := trivial, one := trivial
    add := fun _ _ _ _ => trivial, mul := fun _ _ _ _ => trivial
    sub := fun _ _ _ _ => trivial, natCast := fun _ => trivial
    read_zero := by
      unfold value
      rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
      simp
    read_one := by
      unfold value
      rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
      simp
    read_add := by
      intro a b _ _
      unfold value
      rw [← HexMvPolyTheory.eval₂_toMvPolynomial, HexMvPolyTheory.toMvPolynomial_add,
        MvPolynomial.eval₂_add, HexMvPolyTheory.eval₂_toMvPolynomial,
        HexMvPolyTheory.eval₂_toMvPolynomial]
    read_mul := by
      intro a b _ _
      unfold value
      rw [← HexMvPolyTheory.eval₂_toMvPolynomial, HexMvPolyTheory.toMvPolynomial_mul,
        MvPolynomial.eval₂_mul, HexMvPolyTheory.eval₂_toMvPolynomial,
        HexMvPolyTheory.eval₂_toMvPolynomial]
    read_sub := by
      intro a b _ _
      unfold value
      rw [← HexMvPolyTheory.eval₂_toMvPolynomial, HexMvPolyTheory.toMvPolynomial_sub,
        MvPolynomial.eval₂_sub, HexMvPolyTheory.eval₂_toMvPolynomial,
        HexMvPolyTheory.eval₂_toMvPolynomial]
    read_natCast := by
      intro k
      have literal : (k : Poly n) = MvPoly.C (k : Rat) := by
        apply MvPoly.ext
        intro m
        rw [MvPoly.coeff_natCast, MvPoly.coeff_C]
      rw [literal]
      unfold value
      rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
      simp }

theorem value_neg (values : Fin n → ℝ) (p : Poly n) :
    value values (-p) = -value values p := by
  unfold value
  rw [← HexMvPolyTheory.eval₂_toMvPolynomial, HexMvPolyTheory.toMvPolynomial_neg,
    MvPolynomial.eval₂_neg, HexMvPolyTheory.eval₂_toMvPolynomial]

end Native

end Hex.RCF.RealCoefficients.PolynomialBounds
