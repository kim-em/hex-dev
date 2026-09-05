/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Irreducibility
public import HexPolyZMathlib.PolynomialEquivalence

public section
set_option backward.proofsInPublic true

/-!
# Modular polynomials

Correspondence between executable finite-field polynomials, coefficient
reduction of integer polynomials, and modular factor products.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-! # Mathlib-side correspondence for executable certificate factor-product equalities

These lemmas identify the executable `Hex.PrimeFactorData.factorProduct` with
the Mathlib `Polynomial.map (Int.castRingHom (ZMod p))` image of the underlying
integer polynomial and with the explicit product of recorded factor transports.
Both shapes are consumed by the integer irreducibility certificate soundness
composition.
-/

/-- Executable `FpPoly p` multiplication transports to Mathlib multiplication
through `HexBerlekampMathlib.fpPolyEquiv`. -/
theorem toMathlibPolynomial_mul {p : Nat} [Hex.ZMod64.Bounds p]
    (a b : Hex.FpPoly p) :
    HexBerlekampMathlib.toMathlibPolynomial (a * b) =
      HexBerlekampMathlib.toMathlibPolynomial a *
        HexBerlekampMathlib.toMathlibPolynomial b :=
  map_mul HexBerlekampMathlib.fpPolyEquiv a b

/-- The executable `1 : FpPoly p` transports to Mathlib's `1`. -/
theorem toMathlibPolynomial_one {p : Nat} [Hex.ZMod64.Bounds p] :
    HexBerlekampMathlib.toMathlibPolynomial (1 : Hex.FpPoly p) = 1 := by
  ext n
  rw [HexBerlekampMathlib.coeff_toMathlibPolynomial, Polynomial.coeff_one]
  show HexModArithMathlib.ZMod64.toZMod
      ((Hex.DensePoly.C (1 : Hex.ZMod64 p)).coeff n) =
    if n = 0 then 1 else 0
  rw [Hex.DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn, HexModArithMathlib.ZMod64.toZMod_one]
  · simp only [hn, ↓reduceIte]
    exact HexModArithMathlib.ZMod64.toZMod_zero

/-- The executable constant polynomial `DensePoly.C c` transports to Mathlib's
`Polynomial.C` of the `ZMod p` cast of `c`. -/
theorem toMathlibPolynomial_C {p : Nat} [Hex.ZMod64.Bounds p]
    (c : Hex.ZMod64 p) :
    HexBerlekampMathlib.toMathlibPolynomial (Hex.DensePoly.C c) =
      Polynomial.C (HexModArithMathlib.ZMod64.toZMod c) := by
  ext n
  rw [HexBerlekampMathlib.coeff_toMathlibPolynomial, Hex.DensePoly.coeff_C,
      Polynomial.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    exact HexModArithMathlib.ZMod64.toZMod_zero

/-- Coefficientwise scaling on `FpPoly p` transports across
`HexBerlekampMathlib.toMathlibPolynomial` to multiplication by the
corresponding `Polynomial.C` of the `ZMod p` cast. -/
theorem toMathlibPolynomial_scale {p : Nat} [Hex.ZMod64.Bounds p]
    (c : Hex.ZMod64 p) (f : Hex.FpPoly p) :
    HexBerlekampMathlib.toMathlibPolynomial (Hex.DensePoly.scale c f) =
      Polynomial.C (HexModArithMathlib.ZMod64.toZMod c) *
        HexBerlekampMathlib.toMathlibPolynomial f := by
  ext n
  rw [HexBerlekampMathlib.coeff_toMathlibPolynomial,
      Polynomial.coeff_C_mul, HexBerlekampMathlib.coeff_toMathlibPolynomial]
  have hzero : c * (Zero.zero : Hex.ZMod64 p) = (Zero.zero : Hex.ZMod64 p) := by
    show c * (0 : Hex.ZMod64 p) = (0 : Hex.ZMod64 p)
    grind
  rw [Hex.DensePoly.coeff_scale c f n hzero]
  exact HexModArithMathlib.ZMod64.toZMod_mul c (f.coeff n)

/--
List `foldl (· * ·)` of executable `FpPoly p` factors transports across
`HexBerlekampMathlib.toMathlibPolynomial` to the explicit Mathlib `List.prod`
of the per-factor transports.
-/
theorem toMathlibPolynomial_listFoldlMul_one {p : Nat} [Hex.ZMod64.Bounds p]
    (xs : List (Hex.FpPoly p)) :
    HexBerlekampMathlib.toMathlibPolynomial (xs.foldl (· * ·) 1) =
      (xs.map HexBerlekampMathlib.toMathlibPolynomial).prod := by
  suffices h : ∀ (acc : Hex.FpPoly p),
      HexBerlekampMathlib.toMathlibPolynomial (xs.foldl (· * ·) acc) =
        HexBerlekampMathlib.toMathlibPolynomial acc *
          (xs.map HexBerlekampMathlib.toMathlibPolynomial).prod by
    have hh := h 1
    rw [toMathlibPolynomial_one] at hh
    simpa using hh
  intro acc
  induction xs generalizing acc with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih (acc * head), List.map_cons, List.prod_cons,
        toMathlibPolynomial_mul]
      ring

/--
The Mathlib transport of `Hex.PrimeFactorData.factorProduct` is the Mathlib
`List.prod` of the recorded factor transports.
-/
theorem toMathlibPolynomial_factorProduct (primeData : Hex.PrimeFactorData) :
    letI := primeData.bounds
    HexBerlekampMathlib.toMathlibPolynomial primeData.factorProduct =
      (primeData.factorPolys.toList.map
        HexBerlekampMathlib.toMathlibPolynomial).prod := by
  let := primeData.bounds
  show HexBerlekampMathlib.toMathlibPolynomial
      (primeData.factorPolys.foldl (· * ·) 1) = _
  rw [← Array.foldl_toList]
  exact toMathlibPolynomial_listFoldlMul_one _

/--
Coefficientwise reduction `Hex.ZPoly.modP` transports to Mathlib's coefficient
map from `ℤ[X]` to `(ZMod p)[X]`.  This keeps certificate soundness independent
of the integer-reduction branch proofs.
-/
theorem toMathlibPolynomial_modP_eq_map_intCast_zmod
    {p : Nat} [Hex.ZMod64.Bounds p] (f : Hex.ZPoly) :
    HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP p f) =
      (HexPolyZMathlib.toPolynomial f).map (Int.castRingHom (ZMod p)) :=
  HexPolyZMathlib.eq_map_intCast_of_coeff_eq_toZMod_modP p f
    (fun n => HexBerlekampMathlib.coeff_toMathlibPolynomial _ n)

/--
A successful `PrimeFactorData.checkForPolynomial` block exposes the Mathlib
factor-product / modular-image alignment: the Mathlib transport of the
recorded `factorProduct` equals the Mathlib `Polynomial.map (Int.castRingHom (ZMod p))`
image of the underlying integer polynomial.
-/
theorem toMathlibPolynomial_factorProduct_eq_map_intCast_zmod
    (f : Hex.ZPoly) (primeData : Hex.PrimeFactorData)
    (hcheck : primeData.checkForPolynomial f = true) :
    letI := primeData.bounds
    HexBerlekampMathlib.toMathlibPolynomial primeData.factorProduct =
      (HexPolyZMathlib.toPolynomial f).map
        (Int.castRingHom (ZMod primeData.p)) := by
  let := primeData.bounds
  have hprod : primeData.factorProduct = Hex.ZPoly.modP primeData.p f := by
    simp [Hex.PrimeFactorData.checkForPolynomial] at hcheck
    exact hcheck.1.2
  rw [hprod]
  exact toMathlibPolynomial_modP_eq_map_intCast_zmod f

/--
A successful `PrimeFactorData.checkForPolynomial` block exposes the Mathlib
modular image of the underlying integer polynomial as the explicit product of
recorded factor transports.

This is the shape used by the integer irreducibility certificate soundness
composition: the Mathlib `(toPolynomial f).map (Int.castRingHom (ZMod p))`
factors through the explicit Mathlib `List.prod` of executable monic factor
transports, enabling UFD-level identification of factor degrees against
`factorDegrees`.
-/
theorem map_intCast_zmod_toPolynomial_eq_factorPolys_product
    (f : Hex.ZPoly) (primeData : Hex.PrimeFactorData)
    (hcheck : primeData.checkForPolynomial f = true) :
    letI := primeData.bounds
    (HexPolyZMathlib.toPolynomial f).map
        (Int.castRingHom (ZMod primeData.p)) =
      (primeData.factorPolys.toList.map
        HexBerlekampMathlib.toMathlibPolynomial).prod := by
  let := primeData.bounds
  rw [← toMathlibPolynomial_factorProduct_eq_map_intCast_zmod f primeData hcheck]
  exact toMathlibPolynomial_factorProduct primeData


end

end HexBerlekampZassenhausMathlib
