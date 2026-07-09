/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.ToMonicUniqueness
public import HexBerlekampMathlib.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Polynomial.Radical
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import HexBerlekampZassenhausMathlib.IntReductionMod.Descent
import all HexBerlekampZassenhausMathlib.IntReductionMod.Descent

public section
set_option backward.proofsInPublic true

/-!
Rational repeatedPart-divides-squareFreeCore-power transport, factorPower
cover, the reassemblyExpansionComplete family, and the lifted-factor
subset-partition evidence.
-/
namespace HexBerlekampZassenhausMathlib

namespace IntReductionMod

open Polynomial

variable {p : ℕ}

set_option maxHeartbeats 4000000
/-! ### Rational repeatedPart-divides-squareFreeCore-power transport (#4675)

Base helpers consumed by the integer Gauss descent of #4618 (via
the sibling #4676). The abstract Polynomial-ℚ structure factoring out of
the executable rational decomposition: `divRadical` divides a power of
`radical` (in any UFD), `toPolynomial` of a coefficient-scaled
`DensePoly` is a constant multiplication, and the char-0 gcd-divRadical
identity composes with the radical-power inequality to produce
`R ∣ S ^ N` from associatedness with `gcd(P, P')` and a factorisation
`P ~ S * R`.

The specialisation to `(normalizeForFactor f).{repeatedPart, squareFreeCore}`
remains in a successor sub-issue. -/

/--
Local UFD helper: in a Euclidean-domain UFD with a normalization monoid,
the `divRadical` of a nonzero element divides some power of its
`radical`.

Proof: `exists_squarefree_dvd_pow_of_ne_zero` provides a squarefree `y`
with `y ∣ a` and `a ∣ y ^ n`. Squarefree elements are radical, so
`y ∣ radical y`, and `y ∣ a` lifts to `radical y ∣ radical a`; hence
`y ∣ radical a` and `y ^ n ∣ (radical a) ^ n`. Transitivity through
`divRadical_dvd_self` gives `divRadical a ∣ (radical a) ^ n`.
-/
private theorem divRadical_dvd_radical_pow_of_ne_zero
    {E : Type*} [EuclideanDomain E] [NormalizationMonoid E]
    [UniqueFactorizationMonoid E] {a : E} (ha : a ≠ 0) :
    ∃ N : Nat, EuclideanDomain.divRadical a ∣
      (UniqueFactorizationMonoid.radical a) ^ N := by
  obtain ⟨y, n, hy_sf, hy_dvd, ha_dvd⟩ :=
    exists_squarefree_dvd_pow_of_ne_zero ha
  refine ⟨n, ?_⟩
  have hy_ne : y ≠ 0 := hy_sf.ne_zero
  have hy_dvd_rad : y ∣ UniqueFactorizationMonoid.radical y :=
    hy_sf.isRadical.dvd_radical hy_ne
  have hrad_dvd_rad :
      UniqueFactorizationMonoid.radical y ∣
        UniqueFactorizationMonoid.radical a :=
    UniqueFactorizationMonoid.radical_dvd_radical hy_dvd ha
  have hy_dvd_rad_a : y ∣ UniqueFactorizationMonoid.radical a :=
    hy_dvd_rad.trans hrad_dvd_rad
  have hyn_dvd :
      y ^ n ∣ (UniqueFactorizationMonoid.radical a) ^ n :=
    pow_dvd_pow_of_dvd hy_dvd_rad_a n
  exact (EuclideanDomain.divRadical_dvd_self a).trans
    (ha_dvd.trans hyn_dvd)

/--
`HexPolyMathlib.toPolynomial` intertwines coefficient scaling with Mathlib's
constant-multiplication, for any semiring base. This is the rational analogue
of the integer-side `Hex.ZPoly.C_mul_eq_scale` used to lift the executable
`DensePoly.scale` to a `Polynomial.C` multiplication, without needing a
`GcdMonoid` or `Semiring` instance beyond what `toPolynomial` already requires.
-/
private theorem toPolynomial_scale {R : Type*} [CommSemiring R] [DecidableEq R]
    (c : R) (p : Hex.DensePoly R) :
    HexPolyMathlib.toPolynomial (Hex.DensePoly.scale c p) =
      Polynomial.C c * HexPolyMathlib.toPolynomial p := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial,
    Hex.DensePoly.coeff_scale c p n (mul_zero c),
    Polynomial.coeff_C_mul, HexPolyMathlib.coeff_toPolynomial]

/--
The abstract divisibility step for #4675: given a nonzero `Polynomial K`
(with `K` a characteristic-zero field) decomposed as `P ~ S * R` where
`R` is associated to the executable gcd `gcd P P'`, the polynomial `R`
divides some power of `S`.

This packages the char-0 gcd-divRadical identity together with the UFD
helper `divRadical_dvd_radical_pow_of_ne_zero` and the `Associated.of_mul_right`
cancellation step.
-/
private theorem rp_dvd_sf_pow_of_associated
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    {P R S : Polynomial K} (hP : P ≠ 0)
    (hR_gcd : Associated R
      (EuclideanDomain.gcd P (Polynomial.derivative P)))
    (hP_eq : Associated P (S * R)) :
    ∃ N : Nat, R ∣ S ^ N := by
  have hR_divR : Associated R (EuclideanDomain.divRadical P) :=
    hR_gcd.trans (Polynomial.gcd_derivative_associated_divRadical_of_charZero P)
  obtain ⟨N, hdivR_pow⟩ := divRadical_dvd_radical_pow_of_ne_zero hP
  have h1 : Associated P (S * EuclideanDomain.divRadical P) :=
    hP_eq.trans (Associated.mul_left S hR_divR)
  have h2 : Associated (UniqueFactorizationMonoid.radical P *
      EuclideanDomain.divRadical P) (S * EuclideanDomain.divRadical P) := by
    have hrad : UniqueFactorizationMonoid.radical P *
        EuclideanDomain.divRadical P = P :=
      EuclideanDomain.radical_mul_divRadical
    rw [hrad]; exact h1
  have hdivR_ne : EuclideanDomain.divRadical P ≠ 0 :=
    EuclideanDomain.divRadical_ne_zero hP
  have hS_rad : Associated (UniqueFactorizationMonoid.radical P) S :=
    Associated.of_mul_right h2 Associated.rfl hdivR_ne
  refine ⟨N, ?_⟩
  exact hR_divR.dvd.trans (hdivR_pow.trans (pow_dvd_pow_of_dvd hS_rad.dvd N))

/--
Identify `(primitiveSquareFreeDecomposition p).repeatedPart = 1` when the
executable rational derivative vanishes (Case B of the executable structure).
Isolated as a private helper so the unfold-then-case-split block lives
behind a clean interface and avoids `whnf` heartbeat issues in callers.
-/
private theorem psd_repeatedPart_eq_one_of_derivative_isZero
    (p : Hex.ZPoly)
    (hpp_isZero_false : (Hex.ZPoly.primitivePart p).isZero = false)
    (hderiv : (Hex.DensePoly.derivative
      (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart p))).isZero = true) :
    (Hex.ZPoly.primitiveSquareFreeDecomposition p).repeatedPart = 1 := by
  unfold Hex.ZPoly.primitiveSquareFreeDecomposition
  simp [hpp_isZero_false, hderiv]

/--
Identify `(primitiveSquareFreeDecomposition p).repeatedPart` as the
rational primitive part of `gcd ratPrimitive ratPrimitive.derivative`
in Case C (executable rational derivative nonzero). Private helper
mirroring `psd_repeatedPart_eq_one_of_derivative_isZero`.
-/
private theorem psd_repeatedPart_eq_ratPolyPrimitivePart_gcd_of_derivative_not_isZero
    (p : Hex.ZPoly)
    (hpp_isZero_false : (Hex.ZPoly.primitivePart p).isZero = false)
    (hderiv : (Hex.DensePoly.derivative
      (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart p))).isZero = false) :
    (Hex.ZPoly.primitiveSquareFreeDecomposition p).repeatedPart =
      Hex.ZPoly.ratPolyPrimitivePart
        (Hex.DensePoly.gcd
          (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart p))
          (Hex.DensePoly.derivative
            (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart p)))) := by
  unfold Hex.ZPoly.primitiveSquareFreeDecomposition
  simp [hpp_isZero_false, hderiv]

/--
Specialisation of the abstract `rp_dvd_sf_pow_of_associated` step to the
executable `normalizeForFactor` surface, transported to `Polynomial ℚ`
via `HexPolyZMathlib.toPolynomial` and `Polynomial.map (Int.castRingHom ℚ)`.

This is the rational-side divisibility theorem consumed by the integer
Gauss descent of #4618 (via sibling #4676) and ultimately by the
exponent-extraction step of #4611.
-/
theorem normalizeForFactor_repeatedPart_map_intCast_dvd_squareFreeCore_map_intCast_pow
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    ∃ N : Nat,
      (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).repeatedPart).map (Int.castRingHom ℚ) ∣
      ((HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).squareFreeCore).map (Int.castRingHom ℚ)) ^ N := by
  -- The executable `normalizeForFactor` peels off the `X^k` prefix from the
  -- primitive part of `f` and feeds the result through
  -- `primitiveSquareFreeDecomposition`. We name the resulting primitive
  -- nonzero polynomial `core` and reduce to the `core`-level statement.
  set core : Hex.ZPoly := (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core
    with hcore_def
  have hcore_ne : core ≠ 0 := Hex.extractXPower_core_ne_zero_of_ne_zero f hf
  have hcore_prim : Hex.ZPoly.Primitive core :=
    Hex.extractXPower_core_primitive_of_ne_zero f hf
  have hpp : Hex.ZPoly.primitivePart core = core :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive _ hcore_prim
  -- Rewrite the executable goal in the `core`-level form.
  have hsf_eq : (Hex.normalizeForFactor f).squareFreeCore =
      (Hex.ZPoly.primitiveSquareFreeDecomposition core).squareFreeCore := rfl
  have hrp_eq : (Hex.normalizeForFactor f).repeatedPart =
      (Hex.ZPoly.primitiveSquareFreeDecomposition core).repeatedPart := rfl
  rw [hsf_eq, hrp_eq]
  -- Move the goal into the rational view through the integer-to-rational lift.
  rw [← toPolynomial_toRatPoly_eq_map_intCast,
      ← toPolynomial_toRatPoly_eq_map_intCast]
  -- Name the rational images.
  set sf : Hex.ZPoly := (Hex.ZPoly.primitiveSquareFreeDecomposition core).squareFreeCore
    with hsf_def
  set rp : Hex.ZPoly := (Hex.ZPoly.primitiveSquareFreeDecomposition core).repeatedPart
    with hrp_def
  set P : Polynomial ℚ := HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly core) with hP_def
  set R : Polynomial ℚ := HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly rp) with hR_def
  set S : Polynomial ℚ := HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly sf) with hS_def
  -- `toRatPoly core ≠ 0` (inline analogue of the private `toRatPoly_ne_zero_of_ne_zero`).
  have hrat_ne : Hex.ZPoly.toRatPoly core ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply Hex.DensePoly.ext_coeff
    intro n
    have hcoeff : ((core.coeff n : Int) : Rat) = 0 := by
      rw [← Hex.ZPoly.coeff_toRatPoly, hzero, Hex.DensePoly.coeff_zero]
    rw [Hex.DensePoly.coeff_zero]
    exact_mod_cast hcoeff
  -- `P ≠ 0`: route through `Polynomial.map_ne_zero_iff` on the integer-side lift.
  have hP_ne : P ≠ 0 := by
    rw [hP_def, toPolynomial_toRatPoly_eq_map_intCast]
    refine (Polynomial.map_ne_zero_iff Int.cast_injective).mpr ?_
    intro h
    apply hcore_ne
    exact HexPolyZMathlib.equiv.injective (by simpa using h)
  -- Apply the rational reassembly to extract `unit` with
  -- `toRatPoly core = scale unit (toRatPoly sf * toRatPoly rp)`.
  rcases Hex.ZPoly.primitiveSquareFreeDecomposition_reassembly_over_rat core with
    ⟨unit, hunit⟩
  rw [Hex.ZPoly.primitiveSquareFreeDecomposition_primitive, hpp] at hunit
  -- `unit ≠ 0` (else `scale unit _ = 0`).
  have hunit_ne : unit ≠ 0 := by
    intro huzero
    apply hrat_ne
    rw [hunit, huzero]
    apply Hex.DensePoly.ext_coeff
    intro n
    rw [Hex.DensePoly.coeff_scale (R := Rat) 0 _ n (mul_zero 0),
        Hex.DensePoly.coeff_zero, zero_mul]
  -- `P = C unit * (S * R)`.
  have hP_factor : P = Polynomial.C unit * (S * R) := by
    rw [hP_def, hunit, toPolynomial_scale, HexPolyMathlib.toPolynomial_mul]
  have hCunit_unit : IsUnit (Polynomial.C unit) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hunit_ne)
  -- `Associated P (S * R)`.
  have hP_assoc : Associated P (S * R) := by
    rw [hP_factor]
    exact associated_unit_mul_left (S * R) (Polynomial.C unit) hCunit_unit
  -- `(primitivePart core).isZero = false` from `core ≠ 0` and `primitivePart core = core`.
  have hpp_isZero_false : (Hex.ZPoly.primitivePart core).isZero = false :=
    (Hex.DensePoly.isZero_eq_false_iff _).mpr
      (Hex.ZPoly.size_pos_of_ne_zero _ (by rw [hpp]; exact hcore_ne))
  -- Case-split on whether the rational derivative vanishes.
  by_cases hderiv :
      (Hex.DensePoly.derivative
        (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core))).isZero = true
  · -- Case B: derivative vanishes, so `rp = 1` and `P` is a constant unit.
    have hrp_one : rp = 1 :=
      psd_repeatedPart_eq_one_of_derivative_isZero core hpp_isZero_false hderiv
    -- `R = 1` by transport.
    have hR_one : R = 1 := by
      rw [hR_def, hrp_one, Hex.ZPoly.toRatPoly_one]
      show HexPolyMathlib.toPolynomial (Hex.DensePoly.C (1 : Rat)) = 1
      rw [HexPolyMathlib.toPolynomial_C]
      exact map_one Polynomial.C
    -- `(toRatPoly core).derivative = 0` from the `isZero` flag (using `primitivePart core = core`).
    have hderiv_pp : Hex.DensePoly.derivative
        (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core)) = 0 := by
      have hsize : (Hex.DensePoly.derivative
          (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core))).size = 0 :=
        (Hex.DensePoly.isZero_eq_true_iff _).mp hderiv
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_zero]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le _ (by omega)
    have hderiv_core_zero : Hex.DensePoly.derivative (Hex.ZPoly.toRatPoly core) = 0 := by
      rw [← hpp]; exact hderiv_pp
    -- `P.derivative = 0`.
    have hPderiv_zero : Polynomial.derivative P = 0 := by
      rw [hP_def, ← toPolynomial_derivative, hderiv_core_zero, HexPolyMathlib.toPolynomial_zero]
    -- `P` is a unit: derivative zero + char zero + nonzero ⇒ nonzero constant.
    have hP_isUnit : IsUnit P := by
      have hP_eq_C : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero hPderiv_zero
      have hcoeff_ne : P.coeff 0 ≠ 0 := by
        intro h
        apply hP_ne
        rw [hP_eq_C, h, map_zero]
      rw [hP_eq_C]
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcoeff_ne)
    -- `R = 1 ~ gcd P 0 = P` (using `gcd_zero_right` and `IsUnit P`).
    have hR_gcd : Associated R (EuclideanDomain.gcd P (Polynomial.derivative P)) := by
      rw [hR_one, hPderiv_zero, EuclideanDomain.gcd_zero_right]
      exact (associated_one_iff_isUnit.mpr hP_isUnit).symm
    exact rp_dvd_sf_pow_of_associated hP_ne hR_gcd hP_assoc
  · -- Case C: derivative is nonzero; `rp = ratPolyPrimitivePart (gcd ratPrim ratPrim.derivative)`.
    have hderiv_false : (Hex.DensePoly.derivative
        (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core))).isZero = false :=
      Bool.eq_false_iff.mpr hderiv
    -- Identify `rp` via the case-C helper. Work with `primitivePart core`-shaped terms.
    have hrp_pp_eq : rp =
        Hex.ZPoly.ratPolyPrimitivePart
          (Hex.DensePoly.gcd
            (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core))
            (Hex.DensePoly.derivative
              (Hex.ZPoly.toRatPoly (Hex.ZPoly.primitivePart core)))) :=
      psd_repeatedPart_eq_ratPolyPrimitivePart_gcd_of_derivative_not_isZero
        core hpp_isZero_false hderiv_false
    -- Use `hpp` to identify with `toRatPoly core`.
    set ratPrim : Hex.DensePoly Rat := Hex.ZPoly.toRatPoly core with hratPrim_def
    set der : Hex.DensePoly Rat := Hex.DensePoly.derivative ratPrim with hder_def
    set repeatedRat : Hex.DensePoly Rat := Hex.DensePoly.gcd ratPrim der with hrepeatedRat_def
    have hrp_eq_repeatedRat : rp = Hex.ZPoly.ratPolyPrimitivePart repeatedRat := by
      rw [hrp_pp_eq]
      congr 1
      rw [hpp]
    rcases Hex.ZPoly.ratPolyPrimitivePart_rational_associate repeatedRat with ⟨w, hw⟩
    rw [← hrp_eq_repeatedRat] at hw
    -- `repeatedRat ≠ 0` because `repeatedRat ∣ ratPrim` and `ratPrim ≠ 0`.
    have hrepeatedRat_ne : repeatedRat ≠ 0 := by
      intro hzero
      have hdvd : repeatedRat ∣ ratPrim := Hex.DensePoly.gcd_dvd_left ratPrim der
      rw [hzero] at hdvd
      rcases hdvd with ⟨r, hr⟩
      apply hrat_ne
      change ratPrim = 0
      rw [hr]
      exact Hex.DensePoly.zero_mul _
    -- `w ≠ 0`.
    have hw_ne : w ≠ 0 := by
      intro hzero
      apply hrepeatedRat_ne
      rw [hw, hzero]
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_scale (R := Rat) 0 _ n (mul_zero 0),
          Hex.DensePoly.coeff_zero, zero_mul]
    have hCw_unit : IsUnit (Polynomial.C w) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hw_ne)
    -- `toPolynomial repeatedRat ~ gcd P P.derivative`.
    have hToPoly_ratPrim : HexPolyMathlib.toPolynomial ratPrim = P := by rw [hP_def]
    have hToPoly_der : HexPolyMathlib.toPolynomial der = Polynomial.derivative P := by
      rw [hder_def, toPolynomial_derivative, hToPoly_ratPrim]
    have hgcd_assoc :
        Associated (HexPolyMathlib.toPolynomial repeatedRat)
          (EuclideanDomain.gcd P (Polynomial.derivative P)) := by
      have := HexPolyMathlib.toPolynomial_gcd_associated ratPrim der
      rw [hToPoly_ratPrim, hToPoly_der] at this
      exact this
    -- `toPolynomial repeatedRat = C w * R`.
    have hToPoly_repeatedRat : HexPolyMathlib.toPolynomial repeatedRat = Polynomial.C w * R := by
      rw [hw, toPolynomial_scale, ← hR_def]
    -- `R ~ gcd P P.derivative` by cancelling `C w`.
    have hR_gcd : Associated R (EuclideanDomain.gcd P (Polynomial.derivative P)) := by
      have hCwR_assoc : Associated (Polynomial.C w * R)
          (EuclideanDomain.gcd P (Polynomial.derivative P)) := by
        rw [← hToPoly_repeatedRat]; exact hgcd_assoc
      exact (associated_unit_mul_left R (Polynomial.C w) hCw_unit).symm.trans hCwR_assoc
    exact rp_dvd_sf_pow_of_associated hP_ne hR_gcd hP_assoc

/--
The repeated part of `normalizeForFactor f` divides a power of the
square-free core over integer polynomials.

This is the integer Gauss-descent form of
`normalizeForFactor_repeatedPart_map_intCast_dvd_squareFreeCore_map_intCast_pow`.
-/
theorem normalizeForFactor_repeatedPart_toPolynomial_dvd_squareFreeCore_pow
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    ∃ N : Nat,
      HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart ∣
      (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore) ^ N := by
  obtain ⟨N, hN⟩ :=
    normalizeForFactor_repeatedPart_map_intCast_dvd_squareFreeCore_map_intCast_pow f hf
  refine ⟨N, ?_⟩
  refine (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
    (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart)
    ((HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore) ^ N)
    (normalizeForFactor_repeatedPart_toPolynomial_isPrimitive f hf)
    (isPrimitive_pow
      (normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive f hf) N)).mpr ?_
  simpa using hN

/--
Every normalized irreducible factor of the repeated part is represented,
up to association in `Polynomial ℤ`, by one of the supplied irreducible
core factors.

This is the normalized-factor support step consumed by the successor
exponent-list construction for
`normalizeForFactor_repeatedPart_isPow_polyProduct_of_irreducible_factors_cover`.
It combines the landed repeated-part power-divisibility theorem with the
`polyProduct_toPolynomial` identification for the supplied `coreFactors`.
-/
theorem normalizeForFactor_repeatedPart_normalizedFactor_covered_by_coreFactors
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore) :
    ∀ r ∈ UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart),
      ∃ q ∈ coreFactors.toList,
        Associated r (HexPolyZMathlib.toPolynomial q) := by
  intro r hr
  let R : Polynomial ℤ :=
    HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart
  let S : Polynomial ℤ :=
    HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore
  have hr_irr : Irreducible r :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr
  have hr_prime : Prime r :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hr_irr
  have hr_dvd_R : r ∣ R :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hr
  obtain ⟨N, hR_dvd_pow⟩ :=
    normalizeForFactor_repeatedPart_toPolynomial_dvd_squareFreeCore_pow f hf
  have hr_dvd_pow : r ∣ S ^ N := dvd_trans hr_dvd_R hR_dvd_pow
  have hr_dvd_S : r ∣ S := hr_prime.dvd_of_dvd_pow hr_dvd_pow
  have hS_prod :
      S = (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod := by
    dsimp [S]
    rw [← hprod, polyProduct_toPolynomial]
  have hr_dvd_prod :
      r ∣ (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod := by
    rwa [← hS_prod]
  obtain ⟨qPoly, hqPoly_mem, hr_dvd_qPoly⟩ :=
    (Prime.dvd_prod_iff hr_prime).mp hr_dvd_prod
  rcases List.mem_map.mp hqPoly_mem with ⟨q, hq_mem, hqPoly_eq⟩
  refine ⟨q, hq_mem, ?_⟩
  subst qPoly
  have hq_irr_poly : Irreducible (HexPolyZMathlib.toPolynomial q) :=
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible q).mp (hirr q hq_mem)
  exact hr_irr.associated_of_dvd hq_irr_poly hr_dvd_qPoly

/-- Local copy of the integer-polynomial identification for the executable unit. -/
private theorem toPolynomial_one_zpoly :
    HexPolyZMathlib.toPolynomial (1 : Hex.ZPoly) = 1 := by
  show HexPolyZMathlib.toPolynomial (Hex.DensePoly.C (1 : Int)) = 1
  rw [HexPolyZMathlib.toPolynomial_C]
  simp

/--
The executable fold of packed powers agrees with the corresponding
`Polynomial ℤ` product after transporting every factor through
`toPolynomial`.

This is the transport half of the #4611 exponent-decomposition theorem:
once the UFD argument supplies the polynomial-level powers in core-factor
order, this lemma converts that certificate back to the exact `ZPoly` fold
shape expected by the Mathlib-free expansion helper.
-/
private theorem toPolynomial_factorPower_foldl_aux
    (entries : List (Hex.ZPoly × Nat)) (init : Hex.ZPoly) :
    HexPolyZMathlib.toPolynomial
        ((entries.map
          (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) init) =
      HexPolyZMathlib.toPolynomial init *
        (entries.map
          (fun qe => HexPolyZMathlib.toPolynomial qe.1 ^ qe.2)).prod := by
  induction entries generalizing init with
  | nil =>
      simp
  | cons qe entries ih =>
      rw [List.map_cons, List.foldl_cons, ih, HexPolyZMathlib.toPolynomial_mul,
        factorPower_toPolynomial]
      simp [List.prod_cons, mul_assoc]

/--
The ordered executable product of public `Hex.Factorization.factorPower`
entries agrees with the ordered `Polynomial ℤ` product of transported powers.

This is the product lemma consumed by repeated-part exponent decompositions
before invoking the Mathlib-free expansion helper.
-/
theorem toPolynomial_factorPower_foldl
    (entries : List (Hex.ZPoly × Nat)) :
    HexPolyZMathlib.toPolynomial
        ((entries.map
          (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1) =
      (entries.map
        (fun qe => HexPolyZMathlib.toPolynomial qe.1 ^ qe.2)).prod := by
  rw [toPolynomial_factorPower_foldl_aux, toPolynomial_one_zpoly, one_mul]

/--
Polynomial-to-executable lemma for the #4611 repeated-part power
decomposition.

The remaining mathematical side condition is the polynomial-level exact
decomposition `hpoly_decomp`.  In downstream use this is the part supplied by
the normalized-factor/UFD exponent extraction: #4745 already gives support of
the repeated part inside the supplied core factors, and the caller must still
show that the chosen exponents multiply to the transported repeated part.
This theorem then converts that certificate into the exact executable
`Factorization.factorPower` fold consumed by
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_pow_decomposition`.
-/
theorem normalizeForFactor_repeatedPart_isPow_polyProduct_of_irreducible_factors_cover
    (f : Hex.ZPoly) (_hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (_hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (_hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size)
    (hpoly_decomp :
      HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart =
        ((coreFactors.toList.zip exponents).map
          (fun qe => HexPolyZMathlib.toPolynomial qe.1 ^ qe.2)).prod) :
    ∃ exponents : List Nat,
      exponents.length = coreFactors.size ∧
      (Hex.normalizeForFactor f).repeatedPart =
        ((coreFactors.toList.zip exponents).map
          (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 := by
  refine ⟨exponents, hlen, ?_⟩
  apply HexPolyZMathlib.equiv.injective
  simp only [HexPolyZMathlib.equiv_apply]
  rw [toPolynomial_factorPower_foldl]
  exact hpoly_decomp

/-- Self-zip distributes through `List.map` on the second component. -/
private theorem zip_map_self {α β : Type*} (l : List α) (f : α → β) :
    l.zip (l.map f) = l.map (fun x => (x, f x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.zip_cons_cons, ih]

/--
If a list product in a commutative monoid with zero is squarefree and every
element of the list is irreducible, the list is `Nodup`.
-/
private theorem List.nodup_of_prod_squarefree
    {α : Type*} [CommMonoidWithZero α] [DecidableEq α]
    (l : List α) (hirr : ∀ a ∈ l, Irreducible a)
    (hsq : Squarefree l.prod) :
    l.Nodup := by
  rw [← Multiset.coe_nodup, Multiset.nodup_iff_count_le_one]
  intro p
  by_contra hcontra
  have hcount : 1 < Multiset.count p (l : Multiset α) := Nat.lt_of_not_ge hcontra
  have hp_mem : p ∈ l := by
    rw [← Multiset.mem_coe]
    exact Multiset.count_pos.mp (by omega)
  have hp_irr : Irreducible p := hirr p hp_mem
  -- `p * p ∣ l.prod`: peel two occurrences of `p` from the list.
  have hp_mul_dvd : p * p ∣ l.prod := by
    have hle : Multiset.replicate 2 p ≤ (l : Multiset α) := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x = p
      · subst hx
        rw [Multiset.count_replicate_self]
        omega
      · rw [Multiset.count_replicate, if_neg (Ne.symm hx)]
        exact Nat.zero_le _
    have hdvd_prod := Multiset.prod_dvd_prod_of_le hle
    rw [Multiset.prod_replicate, Multiset.prod_coe] at hdvd_prod
    rw [sq] at hdvd_prod
    exact hdvd_prod
  exact hp_irr.not_isUnit (hsq _ hp_mul_dvd)

/--
**#4611/#4746 capstone — `Factorization.factorPower` decomposition of the
repeated part.**

Every irreducible cover of `(Hex.normalizeForFactor f).squareFreeCore` lifts
to an exponent list whose `Hex.Factorization.factorPower`-fold reconstructs
`(Hex.normalizeForFactor f).repeatedPart` in `Hex.ZPoly`. This is the form
consumed by the public Mathlib-free expansion wrapper
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`.

The proof composes three landed base lemmas:

* `normalizeForFactor_repeatedPart_normalizedFactor_covered_by_coreFactors`
  (#4749), which guarantees every normalized factor of the repeated part is
  Associated to one of the supplied core factors;
* the normalize identifications
  `normalizeForFactor_repeatedPart_toPolynomial_normalize` and
  `HexBerlekampZassenhausMathlib.normalize_toPolynomial_of_normalizeFactorSign_id`
  (#4758), which align the repeated part and each supplied core factor with
  the `normalize`-fixed UFD canonical form in `Polynomial ℤ`;
* `normalizeForFactor_squareFreeCore_toPolynomial_squarefree`, which (via the
  local `List.nodup_of_prod_squarefree` helper) makes the transported
  core-factor list pairwise distinct so that exponents per position are
  unambiguous, and Mathlib's `Finset.prod_multiset_count_of_subset`
  re-expresses `(normalizedFactors R).prod` as a finset-product over the
  list's `toFinset`.

The constructed exponents are
`exponents[i] = Multiset.count (toPolynomial coreFactors[i]) (normalizedFactors R)`
where `R = toPolynomial (normalizeForFactor f).repeatedPart`.

The `hnorm` hypothesis (`Hex.normalizeFactorSign q = q` for each supplied core
factor) is downstream-friendly: every arm discharger reaches this point after
`multifactorLiftQuadratic`, where the lifted factors are monic, so
`normalizeFactorSign q = q` is immediate from monicity (`leadingCoeff = 1`).
-/
theorem normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q) :
    ∃ exponents : List Nat,
      exponents.length = coreFactors.size ∧
      (Hex.normalizeForFactor f).repeatedPart =
        ((coreFactors.toList.zip exponents).map
          (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 := by
  classical
  -- Abbreviations.
  set R : Polynomial ℤ :=
    HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart with hR_def
  set S : Polynomial ℤ :=
    HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore with hS_def
  -- Side facts on `R`.
  have hR_norm : normalize R = R :=
    normalizeForFactor_repeatedPart_toPolynomial_normalize f hf
  have hR_prim : R.IsPrimitive :=
    normalizeForFactor_repeatedPart_toPolynomial_isPrimitive f hf
  have hR_ne_zero : R ≠ 0 := hR_prim.ne_zero
  -- Side facts on each `HexPolyZMathlib.toPolynomial q` for `q ∈ coreFactors`.
  have hPq_irr : ∀ q ∈ coreFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial q) := fun q hq =>
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible q).mp (hirr q hq)
  have hPq_norm : ∀ q ∈ coreFactors.toList,
      normalize (HexPolyZMathlib.toPolynomial q) = HexPolyZMathlib.toPolynomial q :=
    fun q hq => normalize_toPolynomial_of_normalizeFactorSign_id
      (hirr q hq).not_zero (hnorm q hq)
  -- Translate the executable product `polyProduct` into a `List.prod` in
  -- `Polynomial ℤ`.
  have hS_eq : (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod = S := by
    show _ = HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore
    rw [← hprod, polyProduct_toPolynomial]
  have hS_sqfree : Squarefree S :=
    normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf
  have hS_ne_zero : S ≠ 0 := hS_sqfree.ne_zero
  -- The transported core-factor list is `Nodup` (every duplicate would let a
  -- square of an irreducible divide the squarefree `S`).
  have hPq_list_nodup : (coreFactors.toList.map HexPolyZMathlib.toPolynomial).Nodup := by
    apply List.nodup_of_prod_squarefree
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hPq_irr q hq
    · rw [hS_eq]; exact hS_sqfree
  -- Every normalized factor of `R` is one of the transported core factors.
  have hcover := normalizeForFactor_repeatedPart_normalizedFactor_covered_by_coreFactors
    f hf coreFactors hirr hprod
  have hsubset : ∀ r ∈ UniqueFactorizationMonoid.normalizedFactors R,
      r ∈ (coreFactors.toList.map HexPolyZMathlib.toPolynomial : List _).toFinset := by
    intro r hr
    obtain ⟨q, hq, hassoc⟩ := hcover r hr
    have hr_norm : normalize r = r :=
      UniqueFactorizationMonoid.normalize_normalized_factor r hr
    have hr_eq : r = HexPolyZMathlib.toPolynomial q := by
      have hassoc_norm : normalize r = normalize (HexPolyZMathlib.toPolynomial q) :=
        normalize_eq_normalize_iff.mpr (dvd_dvd_iff_associated.mpr hassoc)
      rw [hr_norm, hPq_norm q hq] at hassoc_norm
      exact hassoc_norm
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, hr_eq.symm⟩
  -- Define the exponent list as a count over the multiset of normalized factors.
  set exponents : List Nat :=
    coreFactors.toList.map (fun q =>
      Multiset.count (HexPolyZMathlib.toPolynomial q)
        (UniqueFactorizationMonoid.normalizedFactors R)) with hexponents_def
  have hlen : exponents.length = coreFactors.size := by
    simp [exponents]
  -- Apply the existing `_isPow` wrapper.
  refine normalizeForFactor_repeatedPart_isPow_polyProduct_of_irreducible_factors_cover
    f hf coreFactors hirr hprod exponents hlen ?_
  -- Fold the unfolded `toPolynomial …` back into `R` so subsequent rewrites match.
  change R = _
  -- The RHS reduces to a `List.map` over `coreFactors.toList.map toPolynomial`
  -- whose entries are `p ^ count p (normalizedFactors R)`. Using `Nodup`, that
  -- list-prod equals a `Finset.prod` over the `toFinset`; `R = (normalizedFactors R).prod`
  -- closes the goal via `prod_multiset_count_of_subset`.
  have hRHS_eq :
      ((coreFactors.toList.zip exponents).map
        (fun qe => HexPolyZMathlib.toPolynomial qe.1 ^ qe.2)).prod
      = ((coreFactors.toList.map HexPolyZMathlib.toPolynomial).map
          (fun p => p ^ Multiset.count p
            (UniqueFactorizationMonoid.normalizedFactors R))).prod := by
    rw [show coreFactors.toList.zip exponents
          = coreFactors.toList.map (fun q => (q,
              Multiset.count (HexPolyZMathlib.toPolynomial q)
                (UniqueFactorizationMonoid.normalizedFactors R)))
        from zip_map_self _ _]
    simp [List.map_map, Function.comp_def]
  rw [hRHS_eq, ← List.prod_toFinset _ hPq_list_nodup]
  -- Goal: R = ∏ p ∈ (coreFactors.toList.map toPoly).toFinset, p ^ count p (normalizedFactors R)
  have hR_prod_norm :
      (UniqueFactorizationMonoid.normalizedFactors R).prod = R := by
    have := UniqueFactorizationMonoid.prod_normalizedFactors_eq hR_ne_zero
    rw [hR_norm] at this
    exact this
  conv_lhs => rw [← hR_prod_norm]
  -- Goal: (normalizedFactors R).prod = ∏ p ∈ list.toFinset, p ^ count p (normalizedFactors R)
  exact Finset.prod_multiset_count_of_subset
    (UniqueFactorizationMonoid.normalizedFactors R)
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).toFinset
    (by intro r hr; rw [Multiset.mem_toFinset] at hr; exact hsubset r hr)

/-- **HO-1 base task — no-tail-divisibility for an irreducible cover of the
square-free core.**

Given an irreducible cover `coreFactors` of `(Hex.normalizeForFactor f).squareFreeCore`
and any exponent list of matching length, splitting the zipped list
`coreFactors.toList.zip exponents` at any position `(pre, (q, e), suf)` yields a
suffix whose `factorPower`-fold product is not divisible by `q`.

This is the list-shaped generalisation of
`Hex.irreducible_not_dvd_one` (which handles the singleton-suffix case where
the product collapses to `1`) and is the precondition consumed by the
exhaustive arm of
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`.

The proof transports both `q` and the suffix product to `Polynomial ℤ` through
`HexPolyZMathlib.equiv`, uses the squarefree square-free core to obtain
`Nodup` of the transported core-factor list, and finishes with a UFD
prime-divides-product argument: `toPolynomial q` is prime in `Polynomial ℤ`,
so any divisor witness would force `q` to coincide with some entry in `suf`
(by `Associated` ⟹ `normalize`-fixed equality, then injectivity), contradicting
`Nodup`. -/
theorem factorPower_cover_not_dvd_tail_of_irreducible_squarefree
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q)
    (exponents : List Nat)
    (hlen : exponents.length = coreFactors.size) :
    ∀ pre q e suf,
      coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
      ¬ q ∣ (suf.map (fun (qe : Hex.ZPoly × Nat) =>
              Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 := by
  classical
  intro pre q e suf hsplit hdvd
  -- Transported square-free core and its squarefreeness.
  set S : Polynomial ℤ :=
    HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore with hS_def
  have hS_sqfree : Squarefree S :=
    normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf
  -- Transported core-factor list product equals `S`.
  have hS_eq : (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod = S := by
    show _ = HexPolyZMathlib.toPolynomial _
    rw [← hprod, polyProduct_toPolynomial]
  -- Each transported core factor is irreducible.
  have hPq_irr : ∀ q' ∈ coreFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial q') := fun q' hq' =>
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible q').mp (hirr q' hq')
  -- Each transported core factor is `normalize`-fixed.
  have hPq_norm : ∀ q' ∈ coreFactors.toList,
      normalize (HexPolyZMathlib.toPolynomial q') = HexPolyZMathlib.toPolynomial q' :=
    fun q' hq' => normalize_toPolynomial_of_normalizeFactorSign_id
      (hirr q' hq').not_zero (hnorm q' hq')
  -- Transported core-factor list is `Nodup` (squarefree product + irreducible entries).
  have hPq_list_nodup :
      (coreFactors.toList.map HexPolyZMathlib.toPolynomial).Nodup := by
    apply List.nodup_of_prod_squarefree
    · intro p hp
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hp
      exact hPq_irr q' hq'
    · rw [hS_eq]; exact hS_sqfree
  -- Original core-factor list is `Nodup` (pulls back through injective `toPolynomial`).
  have hcore_nodup : coreFactors.toList.Nodup :=
    List.Nodup.of_map HexPolyZMathlib.toPolynomial hPq_list_nodup
  -- The zip's first-projection equals `coreFactors.toList` (lengths match).
  have hzip_fst :
      (coreFactors.toList.zip exponents).map Prod.fst = coreFactors.toList := by
    apply List.map_fst_zip
    rw [hlen]; simp
  -- Apply that to both sides of `hsplit`.
  have hcore_split :
      coreFactors.toList = pre.map Prod.fst ++ q :: suf.map Prod.fst := by
    have := congrArg (List.map Prod.fst) hsplit
    rw [hzip_fst] at this
    simpa using this
  -- `q` does not occur in `suf.map Prod.fst` (Nodup).
  have hq_not_in_suf : ∀ qe ∈ suf, q ≠ qe.1 := by
    intro qe hqe_mem hq_eq
    have hcore_nodup' : (pre.map Prod.fst ++ q :: suf.map Prod.fst).Nodup :=
      hcore_split ▸ hcore_nodup
    obtain ⟨_, hcons_nodup, _⟩ := (List.nodup_append).mp hcore_nodup'
    have hq_notin : q ∉ suf.map Prod.fst := (List.nodup_cons.mp hcons_nodup).1
    apply hq_notin
    rw [hq_eq]
    exact List.mem_map.mpr ⟨qe, hqe_mem, rfl⟩
  -- `q` itself sits in `coreFactors.toList`.
  have hq_mem : q ∈ coreFactors.toList := by
    rw [hcore_split]
    exact List.mem_append_right _ List.mem_cons_self
  -- Transport the divisibility hypothesis to `Polynomial ℤ`.
  have htrans_dvd :
      HexPolyZMathlib.toPolynomial q ∣
        (suf.map (fun qe => HexPolyZMathlib.toPolynomial qe.1 ^ qe.2)).prod := by
    rw [← toPolynomial_factorPower_foldl]
    rcases hdvd with ⟨w, hw⟩
    refine ⟨HexPolyZMathlib.toPolynomial w, ?_⟩
    rw [hw, HexPolyZMathlib.toPolynomial_mul]
  -- `toPolynomial q` is irreducible, hence prime in the UFD `Polynomial ℤ`.
  have hPq_irr_q : Irreducible (HexPolyZMathlib.toPolynomial q) := hPq_irr q hq_mem
  have hPq_prime : Prime (HexPolyZMathlib.toPolynomial q) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hPq_irr_q
  -- Prime divides the list product, hence divides some power-entry.
  obtain ⟨entry, hentry_mem, hPq_dvd_entry⟩ :=
    (Prime.dvd_prod_iff hPq_prime).mp htrans_dvd
  rcases List.mem_map.mp hentry_mem with ⟨qe, hqe_mem, hentry_eq⟩
  subst hentry_eq
  -- Prime dividing a power divides the base.
  have hPq_dvd_base :
      HexPolyZMathlib.toPolynomial q ∣ HexPolyZMathlib.toPolynomial qe.1 :=
    hPq_prime.dvd_of_dvd_pow hPq_dvd_entry
  -- `qe.1` is one of the core factors.
  have hqe_in_core : qe.1 ∈ coreFactors.toList := by
    rw [hcore_split]
    exact List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨qe, hqe_mem, rfl⟩))
  -- Both transported factors are irreducible; the divisibility forces them to be
  -- `Associated`.
  have hPqe_irr : Irreducible (HexPolyZMathlib.toPolynomial qe.1) :=
    hPq_irr qe.1 hqe_in_core
  have hassoc :
      Associated (HexPolyZMathlib.toPolynomial q) (HexPolyZMathlib.toPolynomial qe.1) :=
    hPq_irr_q.associated_of_dvd hPqe_irr hPq_dvd_base
  -- Both are `normalize`-fixed, so `Associated` collapses to equality.
  have hq_norm : normalize (HexPolyZMathlib.toPolynomial q) = HexPolyZMathlib.toPolynomial q :=
    hPq_norm q hq_mem
  have hqe_norm :
      normalize (HexPolyZMathlib.toPolynomial qe.1) = HexPolyZMathlib.toPolynomial qe.1 :=
    hPq_norm qe.1 hqe_in_core
  have hP_eq :
      HexPolyZMathlib.toPolynomial q = HexPolyZMathlib.toPolynomial qe.1 := by
    have hnormeq :
        normalize (HexPolyZMathlib.toPolynomial q) =
          normalize (HexPolyZMathlib.toPolynomial qe.1) :=
      normalize_eq_normalize_iff_associated.mpr hassoc
    rw [hq_norm, hqe_norm] at hnormeq
    exact hnormeq
  -- Injectivity of `toPolynomial` finishes: `q = qe.1`, contradicting `hq_not_in_suf`.
  exact hq_not_in_suf qe hqe_mem (HexPolyZMathlib.equiv.injective hP_eq)

/-- **#4808 base task — expansion-complete from an irreducible square-free
cover.**

Generic assembler for exhaustive-style core factor arrays.  Given an
irreducible factor cover of `(Hex.normalizeForFactor f).squareFreeCore`, the
repeated-part `factorPower` decomposition from
`normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover`
and the no-tail-divisibility theorem
`factorPower_cover_not_dvd_tail_of_irreducible_squarefree` supply the two
semantic hypotheses of the executable expansion helper.

The remaining `hmonic`, `hdegree`, and `hfuel` hypotheses are executable
compatibility shims required by
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`.
They are intentionally explicit here so branch-specific callers can discharge
or thread them without hiding another analytic obligation. -/
theorem reassemblyExpansionComplete_of_irreducible_squarefree_cover
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q)
    (hmonic : ∀ q ∈ coreFactors.toList, Hex.DensePoly.Monic q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (hfuel :
      ∀ exponents : List Nat,
        exponents.length = coreFactors.size →
        (Hex.normalizeForFactor f).repeatedPart =
          ((coreFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 →
        ∀ (qe : Hex.ZPoly × Nat),
          qe ∈ coreFactors.toList.zip exponents →
            qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors := by
  classical
  obtain ⟨exponents, hlen, hdecomp⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover
      f hf coreFactors hirr hprod hnorm
  have hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : Hex.ZPoly × Nat) =>
                Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 :=
    factorPower_cover_not_dvd_tail_of_irreducible_squarefree
      f hf coreFactors hirr hprod hnorm exponents hlen
  have hfuel' :
      ∀ (qe : Hex.ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents →
          qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    exact hfuel exponents hlen hdecomp
  unfold Hex.reassemblyExpansionComplete
  exact Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition
    (Hex.normalizeForFactor f).repeatedPart coreFactors hmonic hdegree
    exponents hlen hnot_dvd_tail hdecomp hfuel'

/-- Non-monic `_of_pos_lc` sibling of
`reassemblyExpansionComplete_of_irreducible_squarefree_cover`: replaces the
per-factor `Monic q` premise with `0 < leadingCoeff q`, delegating to the
non-monic leaf base task
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`
(`HexBerlekampZassenhaus`, landed in #4778). Mid-layer surface for
callers wanting to delegate to the assembler under a primitive + pos-lc
precondition; the existing quadratic-arm caller
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero` (below)
bypasses the mid-layer by routing through the leaf directly, but the
umbrella-internal rewiring of
`reassemblyExpansionComplete_exhaustive_of_ne_zero` consumes this sibling. -/
theorem reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q)
    (hpos_lc : ∀ q ∈ coreFactors.toList, 0 < Hex.DensePoly.leadingCoeff q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0)
    (hfuel :
      ∀ exponents : List Nat,
        exponents.length = coreFactors.size →
        (Hex.normalizeForFactor f).repeatedPart =
          ((coreFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 →
        ∀ (qe : Hex.ZPoly × Nat),
          qe ∈ coreFactors.toList.zip exponents →
            qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors := by
  classical
  obtain ⟨exponents, hlen, hdecomp⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover
      f hf coreFactors hirr hprod hnorm
  have hnot_dvd_tail :
      ∀ pre q e suf,
        coreFactors.toList.zip exponents = pre ++ (q, e) :: suf →
        ¬ q ∣ (suf.map (fun (qe : Hex.ZPoly × Nat) =>
                Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 :=
    factorPower_cover_not_dvd_tail_of_irreducible_squarefree
      f hf coreFactors hirr hprod hnorm exponents hlen
  have hfuel' :
      ∀ (qe : Hex.ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents →
          qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    exact hfuel exponents hlen hdecomp
  unfold Hex.reassemblyExpansionComplete
  exact Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc
    (Hex.normalizeForFactor f).repeatedPart coreFactors hpos_lc hdegree
    exponents hlen hnot_dvd_tail hdecomp hfuel'

/-- Sign-normalized sibling of
`reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc`:
derives the per-factor positive leading coefficient from the
sign-normalization identity plus irreducibility (hence nonzero-ness), and the
fuel bound from the per-factor `factorPower` size lower bound together with
`size_le_of_dvd_nonzero`, so callers supply only the irreducible,
sign-normalized, positive-degree cover of the square-free core. Consumed by
the classical residual arm
(`reassemblyExpansionComplete_classicalCore_of_ne_zero`) and the lattice tier
(`reassemblyExpansionComplete_latticeCore_of_ne_zero`, `LatticeTier.lean`). -/
theorem reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (coreFactors : Array Hex.ZPoly)
    (hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q)
    (hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors := by
  classical
  -- Per-factor positive leading coefficient from `normalizeFactorSign q = q`
  -- and irreducibility (hence `q ≠ 0`).
  have hpos_lc : ∀ q ∈ coreFactors.toList, 0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      by_contra hlt
      have hlt' : Hex.DensePoly.leadingCoeff q < 0 := lt_of_not_ge hlt
      unfold Hex.normalizeFactorSign at hq_norm
      rw [if_pos hlt'] at hq_norm
      apply hq_ne
      apply Hex.DensePoly.ext_coeff
      intro n
      have hcoeff :
          (Hex.DensePoly.scale (-1 : Int) q).coeff n = q.coeff n := by
        rw [hq_norm]
      rw [Hex.DensePoly.coeff_scale (R := Int) (-1) q n
        (by decide : (-1 : Int) * 0 = 0)] at hcoeff
      rw [Hex.DensePoly.coeff_zero]
      omega
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  refine reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    f hf coreFactors hirr hprod hnorm hpos_lc hdegree ?_
  -- Fuel bound.
  intro exponents hlen hdecomp
  have hsize_ge : ∀ q ∈ coreFactors.toList, 2 ≤ q.size := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_size_pos : 0 < q.size := Hex.ZPoly.size_pos_of_ne_zero q hq_ne
    have hq_deg := hdegree q hq
    have hq_deg_eq : q.degree?.getD 0 = q.size - 1 := by
      unfold Hex.DensePoly.degree?
      simp [Nat.ne_of_gt hq_size_pos]
    omega
  have hrp_ne_zero : (Hex.normalizeForFactor f).repeatedPart ≠ 0 :=
    Hex.repeatedPart_ne_zero_of_ne_zero f hf
  have dvd_foldl_one_of_mem :
      ∀ (x : Hex.ZPoly) (xs : List Hex.ZPoly),
        x ∈ xs → x ∣ xs.foldl (· * ·) (1 : Hex.ZPoly) := by
    intro x xs
    induction xs with
    | nil =>
        intro hmem
        exact absurd hmem List.not_mem_nil
    | cons y ys ih =>
        intro hmem
        rcases List.mem_cons.mp hmem with rfl | hin
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one]
          exact ⟨ys.foldl (· * ·) 1, rfl⟩
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one y ys]
          obtain ⟨k, hk⟩ := ih hin
          refine ⟨y * k, ?_⟩
          rw [hk, ← Hex.DensePoly.mul_assoc_poly (S := Int),
              Hex.DensePoly.mul_comm_poly (S := Int) y x,
              Hex.DensePoly.mul_assoc_poly (S := Int)]
  have factorPower_size_lb :
      ∀ (q : Hex.ZPoly) (e : Nat),
        2 ≤ q.size → e + 1 ≤ (Hex.Factorization.factorPower q e).size := by
    intro q e hq_size
    induction e with
    | zero =>
        show 1 ≤ (1 : Hex.ZPoly).size
        rfl
    | succ n ih =>
        rw [Hex.Factorization.factorPower_succ]
        have hprev_size_pos :
            0 < (Hex.Factorization.factorPower q n).size := by omega
        have hq_size_pos : 0 < q.size := by omega
        have hmul_size :
            (Hex.Factorization.factorPower q n * q).size =
              (Hex.Factorization.factorPower q n).size + q.size - 1 :=
          Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_size_pos hq_size_pos
        omega
  intro qe hqe_mem
  have hq_mem : qe.1 ∈ coreFactors.toList := List.of_mem_zip hqe_mem |>.1
  have hq_size := hsize_ge qe.1 hq_mem
  have hfp_size_lb :
      qe.2 + 1 ≤ (Hex.Factorization.factorPower qe.1 qe.2).size :=
    factorPower_size_lb qe.1 qe.2 hq_size
  have hfp_ne_zero : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
    intro hzero
    rw [hzero] at hfp_size_lb
    have h0 : (0 : Hex.ZPoly).size = 0 := rfl
    omega
  have hfp_mem :
      Hex.Factorization.factorPower qe.1 qe.2 ∈
        ((coreFactors.toList.zip exponents).map
          (fun qe' => Hex.Factorization.factorPower qe'.1 qe'.2)) :=
    List.mem_map.mpr ⟨qe, hqe_mem, rfl⟩
  have hfp_dvd_rp :
      Hex.Factorization.factorPower qe.1 qe.2 ∣
        (Hex.normalizeForFactor f).repeatedPart := by
    rw [hdecomp]
    exact dvd_foldl_one_of_mem _ _ hfp_mem
  have hfp_size_le :
      (Hex.Factorization.factorPower qe.1 qe.2).size ≤
        (Hex.normalizeForFactor f).repeatedPart.size :=
    Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne_zero hrp_ne_zero hfp_dvd_rp
  omega

/-- **#4597 HO-1 base task — small-mod singleton arm `factorPower` shape of
the repeated part.** Singleton specialisation of
`normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover`
(#4759, the final-assembly successor of the decomposed #4746): when the
normalized square-free core is itself irreducible, the repeated part is
exactly a `Hex.Factorization.factorPower` of the square-free core. The
`hnorm` precondition of the general theorem is discharged by
`Hex.squareFreeCore_normalizeFactorSign_of_ne_zero` (the normalized
square-free core has positive leading coefficient, hence its
sign-normalisation is the identity). Consumed by the public discharger
`Hex.reassemblyExpansionComplete_singleton_of_irreducible` (#4597
deliverable 3) to dispatch the singleton expansion specialisation
`Hex.expandRepeatedPartFactorArray_pow_singleton` (#4597 deliverable 2).
Sibling dischargers: constant arm
`Hex.reassemblyExpansionComplete_constant_of_ne_zero` (#4585 / PR #4598);
quadratic arms tracked by #4747. -/
theorem normalizeForFactor_repeatedPart_isFactorPower_squareFreeCore_of_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hirr : Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore) :
    ∃ k : Nat,
      (Hex.normalizeForFactor f).repeatedPart =
        Hex.Factorization.factorPower (Hex.normalizeForFactor f).squareFreeCore k := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hirr_arr :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList, Hex.ZPoly.Irreducible q := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    exact hq_eq ▸ hirr
  have hprod : Array.polyProduct (#[core] : Array Hex.ZPoly) = core :=
    Hex.ZPoly.polyProduct_singleton core
  have hnorm :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList, Hex.normalizeFactorSign q = q := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    subst hq_eq
    exact Hex.squareFreeCore_normalizeFactorSign_of_ne_zero f hf
  obtain ⟨exponents, hlen, hdecomp⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover
      f hf #[core] hirr_arr hprod hnorm
  -- Singleton `coreFactors` collapses the exponent list to `[k]` for some `k`.
  have hsize : (#[core] : Array Hex.ZPoly).size = 1 := rfl
  rw [hsize] at hlen
  cases exponents with
  | nil => simp at hlen
  | cons k es =>
      cases es with
      | cons _ _ => simp at hlen
      | nil =>
          refine ⟨k, ?_⟩
          simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons,
            List.map_nil, List.foldl_cons, List.foldl_nil,
            Hex.ZPoly.one_mul_zpoly] at hdecomp
          exact hdecomp

/-- **#4597 HO-1 base task — small-mod singleton arm `hcomplete` discharger
(Mathlib-side, deliverable 3).** When the normalized square-free core is
itself irreducible, the singleton-core reassembly is expansion-complete:
the `repeatedPart` of `normalizeForFactor f` is exactly a
`Hex.Factorization.factorPower` of the square-free core (deliverable 1),
and that factorPower is consumed completely by
`Hex.expandRepeatedPartFactorArray` (deliverable 2). Consumed by the
small-mod singleton arm umbrella
`factor_small_mod_singleton_branch_entry_irreducible_of_toMonicPrimeData`
(#4564 / PR #4581) so callers can drop the explicit `hcomplete` premise
once the eventual capstone wiring (#4170) lands.

**Base-task gap (Gap 1):** the explicit `hmonic` premise on the
square-free core mirrors the same gap labelled "Gap 1" in the exhaustive
arm umbrella `factor_exhaustive_branch_entry_irreducible_of_choosePrimeData`
(#4561). The underlying executable extraction
(`consumeExactPower_pow_mul_of_not_dvd` and the
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition`
wrapper) currently requires monicness of the core factor; dropping the
hypothesis would require a non-monic divMod/exactQuotient generalisation
in `HexPolyZ/Basic.lean`. The premise is documented as an explicit shim
so downstream callers thread it consistently until the base task
lands.

Sibling dischargers: constant arm
`Hex.reassemblyExpansionComplete_constant_of_ne_zero` (#4585 / PR #4598);
quadratic arm tracked by #4747. -/
theorem reassemblyExpansionComplete_singleton_of_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hirr : Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore)
    (hmonic : Hex.DensePoly.Monic (Hex.normalizeForFactor f).squareFreeCore)
    (hdeg :
      0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      #[(Hex.normalizeForFactor f).squareFreeCore] := by
  obtain ⟨k, hk⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_squareFreeCore_of_irreducible
      f hf hirr
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  -- Size of `core` is at least 2 from positive degree.
  have hcore_size_ge_two : 2 ≤ core.size := by
    have hdeg_unfold : core.degree?.getD 0 =
        (if core.size = 0 then 0 else core.size - 1) := by
      unfold Hex.DensePoly.degree?
      by_cases h : core.size = 0 <;> simp [h]
    rw [hdeg_unfold] at hdeg
    by_cases h : core.size = 0
    · simp [h] at hdeg
    · split at hdeg <;> omega
  -- For monic `core` with `core.size ≥ 2`, the executable `factorPower` of
  -- order `m` has size at least `m + 1`. This gives the fuel bound
  -- `k + 1 ≤ (factorPower core k).size + 1` consumed by deliverable 2.
  have hfactorPower_size_ge :
      ∀ m, m + 1 ≤ (Hex.Factorization.factorPower core m).size := by
    intro m
    induction m with
    | zero =>
        show 1 ≤ (1 : Hex.ZPoly).size
        rfl
    | succ n ih =>
        rw [Hex.Factorization.factorPower_succ]
        have hprev_pos : 0 < (Hex.Factorization.factorPower core n).size := by
          omega
        have hcore_pos : 0 < core.size := by omega
        have hmul_size :
            (Hex.Factorization.factorPower core n * core).size =
              (Hex.Factorization.factorPower core n).size + core.size - 1 :=
          Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_pos hcore_pos
        omega
  have hfuel :
      k + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    have := hfactorPower_size_ge k
    rw [hk]
    omega
  -- Apply deliverable 2 to conclude residual = 1.
  unfold Hex.reassemblyExpansionComplete
  have hexpand :=
    Hex.expandRepeatedPartFactorArray_pow_singleton
      core k hmonic hdeg hirr (Hex.normalizeForFactor f).repeatedPart hk hfuel
  rw [hexpand]

/-- **#4956 HO-1 base task — small-mod singleton arm `hcomplete` discharger,
non-monic primitive sibling (Mathlib-side).** Companion to the monic
`reassemblyExpansionComplete_singleton_of_irreducible` above. Drops the
`hmonic` premise on the square-free core in favour of `0 < leadingCoeff core`,
producing the same `Hex.reassemblyExpansionComplete` conclusion. The proof
routes through the non-monic array-level public surface
`Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`
(`HexBerlekampZassenhaus`, #4778), with the
no-tail-divisibility precondition discharged by
`factorPower_cover_not_dvd_tail_of_irreducible_squarefree` (#4807).
The singleton-arm umbrella
`factor_small_mod_singleton_branch_entry_irreducible_of_toMonicPrimeData`
threads `hcomplete` from the caller, so the value of this sibling is in
letting downstream dispatchers discharge `hcomplete` under a non-monic
primitive `squareFreeCore` (e.g. the `2X + 3` residual from
`(X-1)(2X+3) = 2X^2 + X - 3`). Closes the singleton-arm Gap 1 documented
on the monic sibling at the discharger layer. -/
theorem reassemblyExpansionComplete_singleton_of_irreducible_of_pos_lc
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hirr : Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore)
    (hpos_lc : 0 < Hex.DensePoly.leadingCoeff
      (Hex.normalizeForFactor f).squareFreeCore)
    (hdeg :
      0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      #[(Hex.normalizeForFactor f).squareFreeCore] := by
  obtain ⟨k, hk⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_squareFreeCore_of_irreducible
      f hf hirr
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  -- Size of `core` is at least 2 from positive degree (monicness-agnostic).
  have hcore_size_ge_two : 2 ≤ core.size := by
    have hdeg_unfold : core.degree?.getD 0 =
        (if core.size = 0 then 0 else core.size - 1) := by
      unfold Hex.DensePoly.degree?
      by_cases h : core.size = 0 <;> simp [h]
    rw [hdeg_unfold] at hdeg
    by_cases h : core.size = 0
    · simp [h] at hdeg
    · split at hdeg <;> omega
  -- For `core.size ≥ 2`, `factorPower core m` has size at least `m + 1`
  -- (monicness-agnostic; uses `mul_size_eq_top_succ_of_nonzero`).
  have hfactorPower_size_ge :
      ∀ m, m + 1 ≤ (Hex.Factorization.factorPower core m).size := by
    intro m
    induction m with
    | zero =>
        show 1 ≤ (1 : Hex.ZPoly).size
        rfl
    | succ n ih =>
        rw [Hex.Factorization.factorPower_succ]
        have hprev_pos : 0 < (Hex.Factorization.factorPower core n).size := by
          omega
        have hcore_pos : 0 < core.size := by omega
        have hmul_size :
            (Hex.Factorization.factorPower core n * core).size =
              (Hex.Factorization.factorPower core n).size + core.size - 1 :=
          Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_pos hcore_pos
        omega
  have hfuel :
      k + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    have := hfactorPower_size_ge k
    rw [hk]
    omega
  -- Singleton-shape preconditions for the array-level public non-monic surface.
  have hirr_arr :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList, Hex.ZPoly.Irreducible q := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    exact hq_eq ▸ hirr
  have hprod : Array.polyProduct (#[core] : Array Hex.ZPoly) = core :=
    Hex.ZPoly.polyProduct_singleton core
  have hnorm :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList,
        Hex.normalizeFactorSign q = q := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    subst hq_eq
    exact Hex.squareFreeCore_normalizeFactorSign_of_ne_zero f hf
  have hpos_lc_arr :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList,
        0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    exact hq_eq ▸ hpos_lc
  have hdegree_arr :
      ∀ q ∈ (#[core] : Array Hex.ZPoly).toList, 0 < q.degree?.getD 0 := by
    intro q hq
    have hq_eq : q = core := by simpa using hq
    exact hq_eq ▸ hdeg
  have hlen' :
      ([k] : List Nat).length = (#[core] : Array Hex.ZPoly).size := by
    simp
  -- No-tail-divisibility for the singleton split — discharged by the generic
  -- `factorPower_cover_not_dvd_tail_of_irreducible_squarefree` helper (#4807).
  have hnot_dvd_tail :=
    factorPower_cover_not_dvd_tail_of_irreducible_squarefree
      f hf #[core] hirr_arr hprod hnorm [k] hlen'
  -- `factorPower` decomposition collapses on the singleton split to `hk`.
  -- `#[core].toList.zip [k]` reduces to `[(core, k)]` by definitional
  -- computation; the foldl then collapses to `1 * factorPower core k`.
  have hdecomp :
      (Hex.normalizeForFactor f).repeatedPart =
        (((#[core] : Array Hex.ZPoly).toList.zip [k]).map
          (fun (qe : Hex.ZPoly × Nat) =>
            Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 := by
    show (Hex.normalizeForFactor f).repeatedPart =
      1 * Hex.Factorization.factorPower core k
    rw [Hex.ZPoly.one_mul_zpoly]
    exact hk
  -- Fuel bound for the singleton zip pair `(core, k)`.
  have hfuel' :
      ∀ (qe : Hex.ZPoly × Nat),
        qe ∈ (#[core] : Array Hex.ZPoly).toList.zip [k] →
          qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    intro qe hqe
    -- `hqe : qe ∈ [(core, k)]` reduces to `qe = (core, k)`.
    have hqe_eq : qe = (core, k) := by
      have : qe ∈ ([(core, k)] : List (Hex.ZPoly × Nat)) := hqe
      simpa using this
    rw [hqe_eq]
    exact hfuel
  unfold Hex.reassemblyExpansionComplete
  exact Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc
    (Hex.normalizeForFactor f).repeatedPart #[core] hpos_lc_arr hdegree_arr
    [k] hlen' hnot_dvd_tail hdecomp hfuel'

/-- **#4747 HO-1 base task — quadratic integer-root arm reassembly-expansion
discharger (Mathlib-side).** When the normalized square-free core
`(normalizeForFactor f).squareFreeCore` factors through the executable
`quadraticIntegerRootFactors?` short-circuit (returning `some coreFactors`),
the reassembly of the recorded core factors is expansion-complete: the
`repeatedPart` of `normalizeForFactor f` is exactly the
`Factorization.factorPower` foldl product over the core-factor / exponent
pairs supplied by #4759, and that fold is consumed completely by
`Hex.expandRepeatedPartFactorArray`. Consumed by the slow-path and fast-path
quadratic arm umbrellas
(`factor_quadratic_branch_entry_irreducible_of_quadraticRoots` #4571 and
`factor_slow_quadratic_branch_entry_irreducible_of_choosePrimeData` #4575)
so the eventual capstone wiring (#4170) can drop the explicit `hcomplete`
premise on the quadratic arms.

Composes:

* `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero` and the Mathlib-side lemma
  `zpoly_primitive_of_toPolynomial_isPrimitive` ∘
  `normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive` (#4545) —
  the squareFreeCore positive-leading-coefficient and primitivity invariants;
* `Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive` — every
  emitted core factor is irreducible under primitivity;
* `Hex.polyProduct_quadraticIntegerRootFactors?_some` (#4747 plumbing) —
  the polyProduct = squareFreeCore invariant;
* `Hex.quadraticIntegerRootFactors?_normalizeFactorSign` (#4747 plumbing) —
  the per-factor `normalizeFactorSign` identity, discharging the `hnorm`
  precondition of #4759;
* `Hex.quadraticIntegerRootFactors?_factor_size_eq_two` (#4747 plumbing) —
  every core factor has dense size two, supplying the per-factor positive
  leading coefficient and positive degree preconditions of the non-monic
  expansion-complete surface;
* `normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover`
  (#4759) — the structural `factorPower` decomposition of the repeated part;
* `factorPower_cover_not_dvd_tail_of_irreducible_squarefree` (#4807) — the
  per-position tail-non-divisibility certificate;
* `Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`
  (#4778) — the non-monic public expansion-complete surface; the non-monic
  version is required because `quadraticIntegerRootFactors?` may emit a
  primitive non-monic residual (e.g. `2X + 3` from
  `(X-1)(2X+3) = 2X^2 + X - 3`).

Sibling dischargers: constant arm
`Hex.reassemblyExpansionComplete_constant_of_ne_zero` (#4585 / PR #4598);
small-mod singleton arm `reassemblyExpansionComplete_singleton_of_irreducible`
(#4597); exhaustive arm — tracked by #4848. -/
theorem reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {coreFactors : Array Hex.ZPoly}
    (hquad : Hex.quadraticIntegerRootFactors?
              (Hex.normalizeForFactor f).squareFreeCore = some coreFactors) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) coreFactors := by
  classical
  -- Discharge prerequisites for the squareFreeCore.
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_primitive := normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  -- Per-factor invariants from the quadratic branch.
  have hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q := fun q hq =>
    Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
      hcore_pos hcore_primitive hquad hq
  have hprod :
      Array.polyProduct coreFactors =
        (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.polyProduct_quadraticIntegerRootFactors?_some hquad
  have hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q :=
    Hex.quadraticIntegerRootFactors?_normalizeFactorSign hcore_pos hquad
  have hsize_two : ∀ q ∈ coreFactors.toList, q.size = 2 := fun q hq =>
    Hex.quadraticIntegerRootFactors?_factor_size_eq_two
      hcore_pos hcore_primitive hquad hq
  -- factorPower decomposition (#4759).
  obtain ⟨exponents, hlen, hdecomp⟩ :=
    normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover
      f hf coreFactors hirr hprod hnorm
  -- No-tail divisibility (#4807).
  have hnot_dvd_tail :=
    factorPower_cover_not_dvd_tail_of_irreducible_squarefree
      f hf coreFactors hirr hprod hnorm exponents hlen
  -- Per-factor pos_lc.  From `normalizeFactorSign q = q`, the leading
  -- coefficient is nonneg (otherwise `scale (-1) q = q` would force `q = 0`),
  -- and combined with irreducibility (hence `q ≠ 0`) it is strictly positive.
  have hpos_lc :
      ∀ q ∈ coreFactors.toList, 0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      by_contra hlt
      have hlt' : Hex.DensePoly.leadingCoeff q < 0 := lt_of_not_ge hlt
      unfold Hex.normalizeFactorSign at hq_norm
      rw [if_pos hlt'] at hq_norm
      apply hq_ne
      apply Hex.DensePoly.ext_coeff
      intro n
      have hcoeff :
          (Hex.DensePoly.scale (-1 : Int) q).coeff n = q.coeff n := by
        rw [hq_norm]
      rw [Hex.DensePoly.coeff_scale (R := Int) (-1) q n
        (by decide : (-1 : Int) * 0 = 0)] at hcoeff
      rw [Hex.DensePoly.coeff_zero]
      omega
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  -- Per-factor degree positivity (from `q.size = 2`).
  have hdegree :
      ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0 := by
    intro q hq
    have hsize := hsize_two q hq
    show 0 < q.degree?.getD 0
    unfold Hex.DensePoly.degree?
    simp [hsize]
  -- Repeated part is nonzero (from primitivity of its toPolynomial image).
  have hrp_ne_zero : (Hex.normalizeForFactor f).repeatedPart ≠ 0 := by
    intro hzero
    have hR_prim :=
      normalizeForFactor_repeatedPart_toPolynomial_isPrimitive f hf
    apply hR_prim.ne_zero
    show HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart = 0
    rw [hzero]
    exact HexPolyZMathlib.toPolynomial_zero
  -- Inline helper: any element of a list divides the foldl-mul product seeded
  -- at 1.  Mirrors the proof shape of `linearFactor_dvd_listFoldl_of_mem`
  -- (`HexBerlekampZassenhaus`) for arbitrary ZPoly elements.
  have dvd_foldl_one_of_mem :
      ∀ (x : Hex.ZPoly) (xs : List Hex.ZPoly),
        x ∈ xs → x ∣ xs.foldl (· * ·) (1 : Hex.ZPoly) := by
    intro x xs
    induction xs with
    | nil =>
        intro hmem
        exact absurd hmem List.not_mem_nil
    | cons y ys ih =>
        intro hmem
        rcases List.mem_cons.mp hmem with rfl | hin
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one]
          exact ⟨ys.foldl (· * ·) 1, rfl⟩
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one y ys]
          obtain ⟨k, hk⟩ := ih hin
          refine ⟨y * k, ?_⟩
          rw [hk, ← Hex.DensePoly.mul_assoc_poly (S := Int),
              Hex.DensePoly.mul_comm_poly (S := Int) y x,
              Hex.DensePoly.mul_assoc_poly (S := Int)]
  -- For each `q` with `2 ≤ q.size`, `factorPower q e` has size at least `e + 1`.
  -- Mirrors the `hfactorPower_size_ge` inline argument in
  -- `reassemblyExpansionComplete_singleton_of_irreducible` above.
  have factorPower_size_lb :
      ∀ (q : Hex.ZPoly) (e : Nat),
        2 ≤ q.size → e + 1 ≤ (Hex.Factorization.factorPower q e).size := by
    intro q e hq_size
    induction e with
    | zero =>
        show 1 ≤ (1 : Hex.ZPoly).size
        rfl
    | succ n ih =>
        rw [Hex.Factorization.factorPower_succ]
        have hprev_size_pos :
            0 < (Hex.Factorization.factorPower q n).size := by omega
        have hq_size_pos : 0 < q.size := by omega
        have hmul_size :
            (Hex.Factorization.factorPower q n * q).size =
              (Hex.Factorization.factorPower q n).size + q.size - 1 :=
          Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_size_pos hq_size_pos
        omega
  -- Fuel bound.  Each `factorPower qe.1 qe.2` divides the decomposition
  -- foldl product (= `repeatedPart`); combined with `size_le_of_dvd_nonzero`
  -- and the size lower bound this gives `qe.2 + 1 ≤ rp.size + 1`.
  have hfuel :
      ∀ (qe : Hex.ZPoly × Nat),
        qe ∈ coreFactors.toList.zip exponents →
          qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    intro qe hqe_mem
    have hq_mem : qe.1 ∈ coreFactors.toList := List.of_mem_zip hqe_mem |>.1
    have hq_size := hsize_two qe.1 hq_mem
    have hfp_size_lb :
        qe.2 + 1 ≤ (Hex.Factorization.factorPower qe.1 qe.2).size :=
      factorPower_size_lb qe.1 qe.2 (by omega)
    have hfp_ne_zero : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
      intro hzero
      rw [hzero] at hfp_size_lb
      have h0 : (0 : Hex.ZPoly).size = 0 := rfl
      omega
    have hfp_mem :
        Hex.Factorization.factorPower qe.1 qe.2 ∈
          ((coreFactors.toList.zip exponents).map
            (fun qe' => Hex.Factorization.factorPower qe'.1 qe'.2)) :=
      List.mem_map.mpr ⟨qe, hqe_mem, rfl⟩
    have hfp_dvd_rp :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          (Hex.normalizeForFactor f).repeatedPart := by
      rw [hdecomp]
      exact dvd_foldl_one_of_mem _ _ hfp_mem
    have hfp_size_le :
        (Hex.Factorization.factorPower qe.1 qe.2).size ≤
          (Hex.normalizeForFactor f).repeatedPart.size :=
      Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne_zero hrp_ne_zero hfp_dvd_rp
    omega
  -- Apply the non-monic factorPower expansion-complete helper.
  unfold Hex.reassemblyExpansionComplete
  exact Hex.expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc
    (Hex.normalizeForFactor f).repeatedPart coreFactors hpos_lc hdegree
    exponents hlen hnot_dvd_tail hdecomp hfuel

/-- An irreducible integer divisor of a primitive polynomial has positive degree:
a degree-zero divisor would be a constant `C a`, and primitivity forces `a` to be
a unit, contradicting irreducibility. -/
private theorem one_le_degree_getD_of_irreducible_dvd_primitive
    {core f : Hex.ZPoly}
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hf_irr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hf_dvd : f ∣ core) :
    1 ≤ f.degree?.getD 0 := by
  have hnd : (HexPolyZMathlib.toPolynomial f).natDegree = f.degree?.getD 0 :=
    HexPolyMathlib.natDegree_toPolynomial f
  rw [← hnd]
  rcases Nat.eq_zero_or_pos (HexPolyZMathlib.toPolynomial f).natDegree with h0 | hpos
  · exfalso
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h0
    have hdvd_poly :
        HexPolyZMathlib.toPolynomial f ∣ HexPolyZMathlib.toPolynomial core :=
      HexPolyMathlib.toPolynomial_dvd hf_dvd
    have hprim_poly : (HexPolyZMathlib.toPolynomial core).IsPrimitive :=
      toPolynomial_isPrimitive_of_zpoly_primitive hcore_prim
    have hCa_dvd : Polynomial.C a ∣ HexPolyZMathlib.toPolynomial core := by
      rw [ha]; exact hdvd_poly
    have ha_unit : IsUnit a := hprim_poly a hCa_dvd
    exact hf_irr.not_isUnit (by rw [← ha]; exact Polynomial.isUnit_C.mpr ha_unit)
  · exact hpos

/-- **Producer for `InitialLiftedFactorSubsetPartitionEvidence` at `toMonicLiftData`.**

Assembles the five-field initial lifted-partition evidence package over
`Hex.ZPoly.toMonicLiftData core B primeData`, from a `toMonicPrimeData?` selection
witness and the standard non-monic core side conditions (positive leading
coefficient, positive degree, primitivity, `B ≠ 0`, precision bound).

The `cover` field reads each lifted index back through the mod-`p` index cover of
the monic correspondent `(toMonic core).monic`, sign-normalises the resulting
integer divisor to a monic one, and inverts the monic correspondent
(`exists_dvd_core_of_dvd_toMonic`).  `pairwise_disjoint` descends each lifted
representation to its mod-`p` subset (monic correspondent plus lifted-subset
uniqueness) and applies `modPFactorSubset_disjoint_of_choosePrimeData`.
`unique_up_to_associated` identifies each represented factor with its own recovery
candidate (primitive, positive-leading) to collapse association to equality, then
applies `toMonicLiftData_unique_subset`.  The two recovery fields are the landed
non-circular `liftedRecoveryCandidate` analytics. -/
theorem initialLiftedFactorSubsetPartitionEvidence_of_toMonicChoosePrimeData
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p) :
    InitialLiftedFactorSubsetPartitionEvidence core
      (Hex.ZPoly.toMonicLiftData core B primeData) := by
  classical
  -- Shared facts.
  have hp_prime : Hex.Nat.Prime primeData.p :=
    hval.prime
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hprec_spec : 2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB_ne_zero
  have hmodulus : 2 ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by omega
  have hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p := by
    by_contra hlt
    have hzero : Hex.precisionForCoeffBound B primeData.p = 0 := by omega
    rw [hzero, pow_zero] at hmodulus
    omega
  have hcore0 : core ≠ 0 := by
    intro h
    rw [h, Hex.DensePoly.leadingCoeff_zero] at hcore_lc_pos
    exact lt_irrefl 0 hcore_lc_pos
  have hdeg : 1 ≤ (Hex.ZPoly.toMonic core).degree := hcore_pos
  have hM_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hM_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 := zpoly_ne_zero_of_monic hM_monic
  have hmonicM_pos : 0 < (Hex.ZPoly.toMonic core).monic.degree?.getD 0 := by
    rw [Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree core hcore_lc_pos hcore_pos]
    exact hcore_pos
  have hsize : (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size =
      primeData.factorsModP.size :=
    Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData
  have hlf_monic :
      ∀ i, Hex.DensePoly.Monic
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i) :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData core B primeData
      hcore_lc_pos hcore_pos
      hval hprecision
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _
  have hk_eq : (Hex.ZPoly.toMonicLiftData core B primeData).k =
      Hex.precisionForCoeffBound B primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_k _ _ _
  have hmod2 : 2 ≤ (Hex.ZPoly.toMonicLiftData core B primeData).p ^
      (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; exact hmodulus
  have hprec_dk :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; exact hbound
  -- `scale 1` is the identity (used by the sign-normalisation divisor transport).
  have hscale_one : ∀ p : Hex.ZPoly, Hex.DensePoly.scale (1 : Int) p = p := by
    intro p
    rw [← Hex.ZPoly.C_mul_eq_scale]
    apply HexPolyZMathlib.equiv.injective
    simp
  -- A sign-normalised polynomial divides whatever the original divides.
  have hsign_dvd : ∀ {a b : Hex.ZPoly}, a ∣ b → Hex.normalizeFactorSign a ∣ b := by
    intro a b hab
    unfold Hex.normalizeFactorSign
    split
    · obtain ⟨c, hc⟩ := hab
      refine ⟨Hex.DensePoly.scale (-1) c, ?_⟩
      rw [scale_mul_scale, hc, show ((-1 : Int) * (-1)) = 1 from by norm_num, hscale_one]
    · exact hab
  -- The descent of a lifted representation to its mod-`p` correspondent subset.
  have descent : ∀ {f : Hex.ZPoly}
      {S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData)},
      Irreducible (HexPolyZMathlib.toPolynomial f) → f ∣ core →
      RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) f S →
      ∃ (gf : Hex.ZPoly) (S₀ : ModPFactorSubset primeData),
        Hex.DensePoly.Monic gf ∧
        gf ∣ (Hex.ZPoly.toMonic core).monic ∧
        Irreducible (HexPolyZMathlib.toPolynomial gf) ∧
        RepresentsIntegerFactorModP primeData gf S₀ ∧
        Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) gf) = f ∧
        S = liftedSubsetOfModPSubset primeData
          (Hex.ZPoly.toMonicLiftData core B primeData) hsize S₀ := by
    intro f S hf_irr hf_dvd hrep
    have hfsign : Hex.normalizeFactorSign f = f :=
      normalizeFactorSign_eq_of_representsAtLift hrep hcore_lc_pos hM_ne hlf_monic hprec_dk
    have hcand :
        liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) S = f :=
      toMonicLiftData_liftedRecoveryCandidate_eq core B primeData hcore_lc_pos hcore_pos
        hval hbound hfsign hrep
    have hf_prim : Hex.ZPoly.Primitive f := by
      rw [← hcand]
      exact zpoly_primitive_liftedRecoveryCandidate hcore_lc_pos hmod2 hlf_monic S
    have hfdeg : 1 ≤ f.degree?.getD 0 :=
      one_le_degree_getD_of_irreducible_dvd_primitive hcore_prim hf_irr hf_dvd
    obtain ⟨gf, hgf_monic, hgf_dvd, hrecover⟩ :=
      exists_monicCorrespondent_of_dvd core f hcore0 hcore_lc_pos hdeg hfdeg hf_dvd hf_prim hfsign
    have hgf_irr : Irreducible (HexPolyZMathlib.toPolynomial gf) :=
      irreducible_toPolynomial_monicCorrespondent (ne_of_gt hcore_lc_pos) hgf_monic hf_prim
        hf_irr hrecover
    obtain ⟨S₀, hS₀⟩ :=
      representsModP_correspondent core primeData hcore_lc_pos hcore_pos hval hgf_irr hgf_dvd
    have hliftM :
        RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core B primeData) gf
          (liftedSubsetOfModPSubset primeData (Hex.ZPoly.toMonicLiftData core B primeData)
            hsize S₀) :=
      toMonicLiftData_represents_lifted_monicCorrespondent core B primeData hcore_lc_pos
        hcore_pos hval hB_ne_zero hgf_monic hgf_irr hgf_dvd hS₀
    have hliftcore :
        RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) f
          (liftedSubsetOfModPSubset primeData (Hex.ZPoly.toMonicLiftData core B primeData)
            hsize S₀) :=
      representsIntegerFactorAtLift_of_monicCorrespondent rfl hM_monic hliftM hrecover
    have hSeq : S = liftedSubsetOfModPSubset primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) hsize S₀ :=
      toMonicLiftData_unique_subset core B primeData hcore_lc_pos hcore_pos hval
        hprecision hbound hf_irr hf_dvd hrep hliftcore
    exact ⟨gf, S₀, hgf_monic, hgf_dvd, hgf_irr, hS₀, hrecover, hSeq⟩
  refine
    { cover := ?_
      pairwise_disjoint := ?_
      unique_up_to_associated := ?_
      support_subset_of_dvd_liftedRecoveryCandidate := ?_
      liftedRecoveryCandidate_eq := ?_ }
  · -- cover
    intro i _hi
    let j : ModPFactorIndex primeData := ⟨i.val, by rw [← hsize]; exact i.isLt⟩
    have hji : liftedIndexOfModPIndex primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) hsize j = i := by
      apply Fin.ext; rfl
    obtain ⟨g, S₀, hg_irr, hg_dvd, hjS₀, hgrep⟩ :=
      modPFactor_index_cover (Hex.ZPoly.toMonic core).monic primeData hmonicM_pos
        hval j
    set gm := Hex.normalizeFactorSign g with hgm_def
    have hassoc_gm : Associated (HexPolyZMathlib.toPolynomial gm)
        (HexPolyZMathlib.toPolynomial g) := toPolynomial_normalizeFactorSign_associated g
    have hgm_irr : Irreducible (HexPolyZMathlib.toPolynomial gm) :=
      hassoc_gm.symm.irreducible hg_irr
    have hg_ne : g ≠ 0 := by
      intro h
      exact hg_irr.ne_zero (by rw [h]; exact HexPolyZMathlib.toPolynomial_zero)
    have hgm_ne : gm ≠ 0 := by
      intro h
      exact hg_irr.ne_zero
        ((hassoc_gm.eq_zero_iff).mp (by rw [h]; exact HexPolyZMathlib.toPolynomial_zero))
    have hgm_dvd : gm ∣ (Hex.ZPoly.toMonic core).monic := hsign_dvd hg_dvd
    obtain ⟨cofm, hcofm⟩ := hgm_dvd
    have hcofm_ne : cofm ≠ 0 := by
      intro h
      apply hM_ne
      apply HexPolyZMathlib.equiv.injective
      simp [hcofm, h]
    have hgm_monic : Hex.DensePoly.Monic gm := by
      have hlc_eq : Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic =
          Hex.DensePoly.leadingCoeff gm * Hex.DensePoly.leadingCoeff cofm := by
        rw [hcofm]; exact Hex.ZPoly.leadingCoeff_mul_of_nonzero gm cofm hgm_ne hcofm_ne
      have hlcM : Hex.DensePoly.leadingCoeff (Hex.ZPoly.toMonic core).monic = 1 := hM_monic
      have hnonneg : 0 ≤ Hex.DensePoly.leadingCoeff gm :=
        leadingCoeff_normalizeFactorSign_nonneg g
      have hlc_ne : Hex.DensePoly.leadingCoeff gm ≠ 0 :=
        Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero gm hgm_ne
      have hdvd1 : Hex.DensePoly.leadingCoeff gm ∣ 1 :=
        ⟨Hex.DensePoly.leadingCoeff cofm, by rw [← hlcM, hlc_eq]⟩
      have hle : Hex.DensePoly.leadingCoeff gm ≤ 1 := Int.le_of_dvd one_pos hdvd1
      show Hex.DensePoly.leadingCoeff gm = 1
      omega
    have hgm_repP : RepresentsIntegerFactorModP primeData gm S₀ :=
      representsIntegerFactorModP_of_associated hp_prime hassoc_gm.symm hgrep
    obtain ⟨f, hf_irr, hf_dvd, _hf_sign, hrecover⟩ :=
      exists_dvd_core_of_dvd_toMonic core gm hcore_lc_pos hcore_pos hcore_prim hgm_monic
        hgm_irr ⟨cofm, hcofm⟩
    have hliftM :
        RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
          (Hex.ZPoly.toMonicLiftData core B primeData) gm
          (liftedSubsetOfModPSubset primeData (Hex.ZPoly.toMonicLiftData core B primeData)
            hsize S₀) :=
      toMonicLiftData_represents_lifted_monicCorrespondent core B primeData hcore_lc_pos
        hcore_pos hval hB_ne_zero hgm_monic hgm_irr ⟨cofm, hcofm⟩ hgm_repP
    have hliftcore :
        RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) f
          (liftedSubsetOfModPSubset primeData (Hex.ZPoly.toMonicLiftData core B primeData)
            hsize S₀) :=
      representsIntegerFactorAtLift_of_monicCorrespondent rfl hM_monic hliftM hrecover
    refine ⟨f, liftedSubsetOfModPSubset primeData
      (Hex.ZPoly.toMonicLiftData core B primeData) hsize S₀, hf_irr, hf_dvd,
      Finset.subset_univ _, ?_, hliftcore⟩
    rw [← hji]
    exact (liftedIndex_mem_liftedSubset_iff primeData
      (Hex.ZPoly.toMonicLiftData core B primeData) hsize S₀ j).mpr hjS₀
  · -- pairwise_disjoint
    intro f g S T hf_irr hf_dvd hrepS hg_irr hg_dvd hrepT hnotassoc
    obtain ⟨gf, S₀, hgf_monic, hgf_dvd, hgf_irr, hS₀, hrecf, hSeq⟩ :=
      descent hf_irr hf_dvd hrepS
    obtain ⟨gg, T₀, hgg_monic, hgg_dvd, hgg_irr, hT₀, hrecg, hTeq⟩ :=
      descent hg_irr hg_dvd hrepT
    have hgf_ne : gf ≠ 0 := zpoly_ne_zero_of_monic hgf_monic
    have hgg_ne : gg ≠ 0 := zpoly_ne_zero_of_monic hgg_monic
    have hnotassoc' : ¬ Associated (HexPolyZMathlib.toPolynomial gf)
        (HexPolyZMathlib.toPolynomial gg) := by
      intro h
      exact hnotassoc (associated_of_associated_monicCorrespondent (ne_of_gt hcore_lc_pos)
        hgf_ne hgg_ne hrecf hrecg h)
    have hdisj0 : Disjoint S₀ T₀ :=
      modPFactorSubset_disjoint_of_modPFactorization
        hval
        hmonicM_pos hgf_irr hgf_dvd hgg_irr hgg_dvd
        hS₀ hT₀ hnotassoc'
    rw [hSeq, hTeq]
    exact (liftedSubsetOfModPSubset_disjoint_iff primeData
      (Hex.ZPoly.toMonicLiftData core B primeData) hsize S₀ T₀).mpr hdisj0
  · -- unique_up_to_associated
    intro f g S T hf_irr hf_dvd hrepS hg_irr hg_dvd hrepT hassoc
    have hfsignf : Hex.normalizeFactorSign f = f :=
      normalizeFactorSign_eq_of_representsAtLift hrepS hcore_lc_pos hM_ne hlf_monic hprec_dk
    have hfsigng : Hex.normalizeFactorSign g = g :=
      normalizeFactorSign_eq_of_representsAtLift hrepT hcore_lc_pos hM_ne hlf_monic hprec_dk
    have hcandf :
        liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) S = f :=
      toMonicLiftData_liftedRecoveryCandidate_eq core B primeData hcore_lc_pos hcore_pos
        hval hbound hfsignf hrepS
    have hcandg :
        liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) T = g :=
      toMonicLiftData_liftedRecoveryCandidate_eq core B primeData hcore_lc_pos hcore_pos
        hval hbound hfsigng hrepT
    have hf_prim : Hex.ZPoly.Primitive f := by
      rw [← hcandf]
      exact zpoly_primitive_liftedRecoveryCandidate hcore_lc_pos hmod2 hlf_monic S
    have hg_prim : Hex.ZPoly.Primitive g := by
      rw [← hcandg]
      exact zpoly_primitive_liftedRecoveryCandidate hcore_lc_pos hmod2 hlf_monic T
    have hf_lc : 0 < Hex.DensePoly.leadingCoeff f := by
      rw [← hcandf]
      exact leadingCoeff_liftedRecoveryCandidate_pos hcore_lc_pos hmod2 hlf_monic S
    have hg_lc : 0 < Hex.DensePoly.leadingCoeff g := by
      rw [← hcandg]
      exact leadingCoeff_liftedRecoveryCandidate_pos hcore_lc_pos hmod2 hlf_monic T
    have hfg : f = g :=
      zpoly_eq_of_toPolynomial_associated_of_primitive_pos_leading hf_prim hg_prim hf_lc hg_lc
        hassoc
    subst hfg
    exact toMonicLiftData_unique_subset core B primeData hcore_lc_pos hcore_pos hval
      hprecision hbound hf_irr hf_dvd hrepS hrepT
  · -- support_subset_of_dvd_liftedRecoveryCandidate
    intro f S T hf_irr hf_dvd hdvd_cand hrep
    have hfsign : Hex.normalizeFactorSign f = f :=
      normalizeFactorSign_eq_of_representsAtLift hrep hcore_lc_pos hM_ne hlf_monic hprec_dk
    exact toMonicLiftData_subset_of_dvd_liftedRecoveryCandidate core B primeData hcore_lc_pos
      hcore_pos hval hprecision hbound hfsign hrep hdvd_cand
  · -- liftedRecoveryCandidate_eq
    intro f S hf_irr hf_dvd hrep
    have hfsign : Hex.normalizeFactorSign f = f :=
      normalizeFactorSign_eq_of_representsAtLift hrep hcore_lc_pos hM_ne hlf_monic hprec_dk
    exact toMonicLiftData_liftedRecoveryCandidate_eq core B primeData hcore_lc_pos hcore_pos
      hval hbound hfsign hrep

/--
**Monic-correspondent descent for a represented integer factor (#8068).**

Top-level extraction of the `descent` step inside
`initialLiftedFactorSubsetPartitionEvidence_of_toMonicChoosePrimeData`.  From an
original-core represented factor `f` (irreducible, dividing `core`, represented
at the `toMonicLiftData` lift by subset `S`) this reconstructs the *monic
correspondent* `gf` of `f` from `f` alone: the monic irreducible factor of
`(toMonic core).monic`, its mod-`p` representing subset `S₀`, the
`primitivePart ∘ dilate` recovery `f = primitivePart (dilate (lc core) gf)`, and
the identification `S = liftedSubsetOfModPSubset … S₀`.

This is the keystone that lets the centered `RecoveredLift` family for
`liftedTrueSupports core d` be built directly (via
`recoveredLiftOfToMonicRepresents`), without the reverse `L' = W` separation: the
witnessing `f` carried by a `liftedTrueSupports` membership is enough to recover
the monic-coordinate representation that the recovered-lift producers consume.
-/
theorem monicCorrespondentDescent_of_representsAtLift
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p)
    {f : Hex.ZPoly}
    {S : LiftedFactorSubset (Hex.ZPoly.toMonicLiftData core B primeData)}
    (hf_irr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hf_dvd : f ∣ core)
    (hrep :
      RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) f S) :
    ∃ (gf : Hex.ZPoly) (S₀ : ModPFactorSubset primeData),
      Hex.DensePoly.Monic gf ∧
      gf ∣ (Hex.ZPoly.toMonic core).monic ∧
      Irreducible (HexPolyZMathlib.toPolynomial gf) ∧
      RepresentsIntegerFactorModP primeData gf S₀ ∧
      Hex.ZPoly.primitivePart
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) gf) = f ∧
      S = liftedSubsetOfModPSubset primeData
        (Hex.ZPoly.toMonicLiftData core B primeData)
        (Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData) S₀ := by
  classical
  have hp_prime : Hex.Nat.Prime primeData.p :=
    hval.prime
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hprec_spec : 2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB_ne_zero
  have hmodulus : 2 ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by omega
  have hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p := by
    by_contra hlt
    have hzero : Hex.precisionForCoeffBound B primeData.p = 0 := by omega
    rw [hzero, pow_zero] at hmodulus
    omega
  have hcore0 : core ≠ 0 := by
    intro h
    rw [h, Hex.DensePoly.leadingCoeff_zero] at hcore_lc_pos
    exact lt_irrefl 0 hcore_lc_pos
  have hdeg : 1 ≤ (Hex.ZPoly.toMonic core).degree := hcore_pos
  have hM_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hM_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 := zpoly_ne_zero_of_monic hM_monic
  have hsize : (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size =
      primeData.factorsModP.size :=
    Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData
  have hlf_monic :
      ∀ i, Hex.DensePoly.Monic
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i) :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData core B primeData
      hcore_lc_pos hcore_pos
      hval hprecision
  have hp_eq : (Hex.ZPoly.toMonicLiftData core B primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _
  have hk_eq : (Hex.ZPoly.toMonicLiftData core B primeData).k =
      Hex.precisionForCoeffBound B primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_k _ _ _
  have hmod2 : 2 ≤ (Hex.ZPoly.toMonicLiftData core B primeData).p ^
      (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; exact hmodulus
  have hprec_dk :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        (Hex.ZPoly.toMonicLiftData core B primeData).p ^
          (Hex.ZPoly.toMonicLiftData core B primeData).k := by
    rw [hp_eq, hk_eq]; exact hbound
  have hfsign : Hex.normalizeFactorSign f = f :=
    normalizeFactorSign_eq_of_representsAtLift hrep hcore_lc_pos hM_ne hlf_monic hprec_dk
  have hcand :
      liftedRecoveryCandidate core (Hex.ZPoly.toMonicLiftData core B primeData) S = f :=
    toMonicLiftData_liftedRecoveryCandidate_eq core B primeData hcore_lc_pos hcore_pos
      hval hbound hfsign hrep
  have hf_prim : Hex.ZPoly.Primitive f := by
    rw [← hcand]
    exact zpoly_primitive_liftedRecoveryCandidate hcore_lc_pos hmod2 hlf_monic S
  have hfdeg : 1 ≤ f.degree?.getD 0 :=
    one_le_degree_getD_of_irreducible_dvd_primitive hcore_prim hf_irr hf_dvd
  obtain ⟨gf, hgf_monic, hgf_dvd, hrecover⟩ :=
    exists_monicCorrespondent_of_dvd core f hcore0 hcore_lc_pos hdeg hfdeg hf_dvd hf_prim hfsign
  have hgf_irr : Irreducible (HexPolyZMathlib.toPolynomial gf) :=
    irreducible_toPolynomial_monicCorrespondent (ne_of_gt hcore_lc_pos) hgf_monic hf_prim
      hf_irr hrecover
  obtain ⟨S₀, hS₀⟩ :=
    representsModP_correspondent core primeData hcore_lc_pos hcore_pos hval hgf_irr hgf_dvd
  have hliftM :
      RepresentsIntegerFactorAtLift (Hex.ZPoly.toMonic core).monic
        (Hex.ZPoly.toMonicLiftData core B primeData) gf
        (liftedSubsetOfModPSubset primeData (Hex.ZPoly.toMonicLiftData core B primeData)
          hsize S₀) :=
    toMonicLiftData_represents_lifted_monicCorrespondent core B primeData hcore_lc_pos
      hcore_pos hval hB_ne_zero hgf_monic hgf_irr hgf_dvd hS₀
  have hliftcore :
      RepresentsIntegerFactorAtLift core (Hex.ZPoly.toMonicLiftData core B primeData) f
        (liftedSubsetOfModPSubset primeData (Hex.ZPoly.toMonicLiftData core B primeData)
          hsize S₀) :=
    representsIntegerFactorAtLift_of_monicCorrespondent rfl hM_monic hliftM hrecover
  have hSeq : S = liftedSubsetOfModPSubset primeData
      (Hex.ZPoly.toMonicLiftData core B primeData) hsize S₀ :=
    toMonicLiftData_unique_subset core B primeData hcore_lc_pos hcore_pos hval
      hprecision hbound hf_irr hf_dvd hrep hliftcore
  exact ⟨gf, S₀, hgf_monic, hgf_dvd, hgf_irr, hS₀, hrecover, hSeq⟩


end IntReductionMod
end HexBerlekampZassenhausMathlib
