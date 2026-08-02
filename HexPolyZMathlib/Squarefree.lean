/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexPolyMathlib.Euclid
public import HexPolyZMathlib.PolynomialEquivalence

public section

/-!
# Rational squarefreeness of executable integer polynomials

This module identifies the executable rational-gcd test with squarefreeness
after mapping the integer polynomial to `ℚ[X]`. The statement is deliberately
about the rational cast: integral-polynomial squarefreeness additionally sees
square factors in the content.
-/

namespace HexPolyZMathlib

open Polynomial

noncomputable section

/-- The rational cast of an executable integer polynomial. -/
abbrev toPolyℚ (p : Hex.ZPoly) : Polynomial ℚ :=
  (toPolynomial p).map (Int.castRingHom ℚ)

/-- A dense polynomial stores at most one coefficient exactly when its
Mathlib image has natural degree zero. -/
theorem size_le_one_iff_natDegree_eq_zero {R : Type*} [Semiring R] [DecidableEq R]
    (g : Hex.DensePoly R) :
    g.size ≤ 1 ↔ (HexPolyMathlib.toPolynomial g).natDegree = 0 := by
  rw [HexPolyMathlib.natDegree_toPolynomial]
  by_cases h : g.size = 0
  · rw [(Hex.DensePoly.degree?_eq_none_iff g).mpr h]
    simp [h]
  · rw [Hex.DensePoly.degree?_eq_some_of_pos_size g (Nat.pos_of_ne_zero h),
      Option.getD_some]
    omega

/-- `toRatPoly` corresponds to the rational cast under `toPolynomial`. -/
theorem toPolynomial_toRatPoly (f : Hex.ZPoly) :
    HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly f) = toPolyℚ f := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Hex.ZPoly.coeff_toRatPoly, toPolyℚ,
    Polynomial.coeff_map, coeff_toPolynomial]
  simp

/-- Coefficients of the rational cast are the rational casts of the integer
coefficients. -/
@[simp] theorem coeff_toPolyℚ (p : Hex.ZPoly) (n : Nat) :
    (toPolyℚ p).coeff n = (p.coeff n : ℚ) := by
  simp [toPolyℚ]

/-- Evaluation of the rational cast is the degree-indexed coefficient sum. -/
theorem eval_toPolyℚ (p : Hex.ZPoly) (x : ℚ) :
    (toPolyℚ p).eval x = ∑ i ∈ Finset.range p.size, (p.coeff i : ℚ) * x ^ i := by
  rw [toPolyℚ, Polynomial.eval_map, HexPolyMathlib.eval₂_toPolynomial]
  simp

/-- The rational cast of a nonzero executable polynomial is nonzero. -/
theorem toPolyℚ_ne_zero {f : Hex.ZPoly} (hf : f ≠ 0) : toPolyℚ f ≠ 0 := by
  rw [toPolyℚ, Ne,
    Polynomial.map_eq_zero_iff (RingHom.injective_int (Int.castRingHom ℚ))]
  intro h
  exact hf (by have := congrArg ofPolynomial h; simpa using this)

/-- For a nonzero executable integer polynomial, the executable rational-gcd
test is equivalent to squarefreeness of its rational cast. -/
theorem squareFreeRat_iff (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.ZPoly.SquareFreeRat f ↔ Squarefree (toPolyℚ f) := by
  unfold Hex.ZPoly.SquareFreeRat
  set a := Hex.ZPoly.toRatPoly f with ha
  set a' := Hex.DensePoly.derivative a with ha'
  have hPa : HexPolyMathlib.toPolynomial a = toPolyℚ f :=
    toPolynomial_toRatPoly f
  have hPa' : HexPolyMathlib.toPolynomial a' = derivative (toPolyℚ f) := by
    rw [ha', HexPolyMathlib.toPolynomial_derivative, hPa]
  have hP0 : toPolyℚ f ≠ 0 := toPolyℚ_ne_zero hf
  rw [size_le_one_iff_natDegree_eq_zero]
  have hassoc := HexPolyMathlib.toPolynomial_gcd_associated a a'
  have hdeg : (HexPolyMathlib.toPolynomial (Hex.DensePoly.gcd a a')).natDegree
      = (EuclideanDomain.gcd (toPolyℚ f) (derivative (toPolyℚ f))).natDegree := by
    have h := Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hassoc)
    rw [hPa, hPa'] at h
    exact h
  rw [hdeg]
  set G := EuclideanDomain.gcd (toPolyℚ f) (derivative (toPolyℚ f)) with hG
  have hG0 : G ≠ 0 := by
    rw [hG, Ne, EuclideanDomain.gcd_eq_zero_iff]
    exact fun h => hP0 h.1
  have key : G.natDegree = 0 ↔ IsUnit G := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hG0]
    exact_mod_cast Iff.rfl
  rw [key, hG, EuclideanDomain.gcd_isUnit_iff, ← Polynomial.separable_def,
    PerfectField.separable_iff_squarefree]

private theorem repeatedPart_dvd_derivative_complex (f : Hex.ZPoly) :
    ((toPolynomial (Hex.ZPoly.primitiveSquareFreeDecomposition f).repeatedPart).map
        (Int.castRingHom ℂ)) ∣
      derivative ((toPolynomial (Hex.ZPoly.primitivePart f)).map
        (Int.castRingHom ℂ)) := by
  rcases Hex.ZPoly.toRatPoly_repeatedPart_dvd_derivative f with ⟨q, hq⟩
  refine ⟨(HexPolyMathlib.toPolynomial q).map (algebraMap ℚ ℂ), ?_⟩
  have hqPolynomial := congrArg HexPolyMathlib.toPolynomial hq
  rw [HexPolyMathlib.toPolynomial_mul,
    HexPolyMathlib.toPolynomial_derivative,
    toPolynomial_toRatPoly, toPolynomial_toRatPoly] at hqPolynomial
  have hmapped := congrArg
    (fun p : Polynomial ℚ => p.map (algebraMap ℚ ℂ)) hqPolynomial
  have hcomp :
      (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) =
        Int.castRingHom ℂ := RingHom.ext_int _ _
  simpa [Polynomial.map_mul, Polynomial.map_map, hcomp] using hmapped

/-- Passing to the executable square-free core preserves every complex root
of a nonzero integer polynomial. -/
theorem isRoot_squareFreeCore {f : Hex.ZPoly} (hf : f ≠ 0) {z : ℂ}
    (hz : ((toPolynomial f).map (Int.castRingHom ℂ)).IsRoot z) :
    ((toPolynomial (Hex.ZPoly.squareFreeCore f)).map
      (Int.castRingHom ℂ)).IsRoot z := by
  let d := Hex.ZPoly.primitiveSquareFreeDecomposition f
  let P : Polynomial ℂ :=
    (toPolynomial (Hex.ZPoly.primitivePart f)).map (Int.castRingHom ℂ)
  let C : Polynomial ℂ :=
    (toPolynomial d.squareFreeCore).map (Int.castRingHom ℂ)
  let R : Polynomial ℂ :=
    (toPolynomial d.repeatedPart).map (Int.castRingHom ℂ)
  have hcontent : Hex.ZPoly.content f ≠ 0 := content_ne_zero f hf
  have hdecomp := congrArg
    (fun p : Polynomial ℤ => p.map (Int.castRingHom ℂ))
    (toPolynomial_eq_C_content_mul_primitivePart f)
  rw [Polynomial.map_mul, Polynomial.map_C] at hdecomp
  have hPRoot : P.IsRoot z := by
    have hproduct : (Hex.ZPoly.content f : ℂ) * P.eval z = 0 := by
      rw [hdecomp] at hz
      change (Polynomial.C (Hex.ZPoly.content f : ℂ) * P).eval z = 0 at hz
      rw [Polynomial.eval_mul, Polynomial.eval_C] at hz
      exact hz
    exact (mul_eq_zero.mp hproduct).resolve_left (by exact_mod_cast hcontent)
  have hprimitive : Hex.ZPoly.primitivePart f ≠ 0 :=
    Hex.ZPoly.ne_zero_of_primitive _
      (Hex.ZPoly.primitivePart_primitive f hcontent)
  have hPne : P ≠ 0 := by
    intro hzero
    apply hprimitive
    have hpolynomial : toPolynomial (Hex.ZPoly.primitivePart f) = 0 :=
      (Polynomial.map_eq_zero_iff
        (RingHom.injective_int (Int.castRingHom ℂ))).mp (by
          simpa [P] using hzero)
    apply (HexPolyMathlib.equiv (R := Int)).injective
    simpa [HexPolyMathlib.equiv_apply] using hpolynomial
  have hrepDvd : R ∣ derivative P := by
    simpa [d, P, R] using repeatedPart_dvd_derivative_complex f
  rcases hrepDvd with ⟨Q, hQ⟩
  rcases Hex.ZPoly.primitiveSquareFreeDecomposition_reassembly_signed f hf with
    ⟨ε, hε, hreassembly⟩
  have hreassemblyComplex := congrArg
    (fun p : Hex.ZPoly => (toPolynomial p).map (Int.castRingHom ℂ))
    hreassembly
  have hPdvd : P ∣ derivative P * C := by
    rcases hε with rfl | rfl
    · refine ⟨Q, ?_⟩
      simp only [HexPolyMathlib.toPolynomial_scale,
        HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul,
        Polynomial.C_1, one_mul] at hreassemblyComplex
      change C * R = P at hreassemblyComplex
      rw [hQ]
      change R * Q * C = P * Q
      rw [← hreassemblyComplex]
      ring
    · refine ⟨-Q, ?_⟩
      simp [HexPolyMathlib.toPolynomial_scale,
        HexPolyMathlib.toPolynomial_mul] at hreassemblyComplex
      change -(C * R) = P at hreassemblyComplex
      rw [hQ]
      change R * Q * C = P * -Q
      rw [← hreassemblyComplex]
      ring
  have hCRoot : C.IsRoot z :=
    Polynomial.isRoot_of_isRoot_of_dvd_derivative_mul hPne hPdvd hPRoot
  simpa [d, C, Hex.ZPoly.squareFreeCore_eq] using hCRoot

end

end HexPolyZMathlib
