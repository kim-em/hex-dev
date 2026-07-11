/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib

public section

/-!
# Root-product form of the polynomial discriminant

This module derives the classical root-product formula for `Polynomial.discr`
and the consequences needed by the real-root separation development
(`hex-real-roots-mathlib`): non-vanishing of the discriminant of a separable
polynomial, and the integer corollary `1 ≤ |discr f|` used in Mahler's
separation bound.

The main statement is `Polynomial.discr_eq_prod_roots`: for a polynomial `f`
over a field that splits, with `0 < degree f`,
`discr f = (-1) ^ (n (n-1) / 2) * leadingCoeff f ^ (2 n - 2) * D`, where
`n = natDegree f` and `D` is the off-diagonal root product
`∏_{x ∈ roots} ∏_{y ∈ roots.erase x} (x - y)`. The off-diagonal product `D` is
order-free (it never needs an ordering of the roots), which is what lets the
statement live over an arbitrary splitting field, `ℂ` included. The familiar
`∏_{i < j} (rᵢ - rⱼ)²` form is `(-1) ^ (n(n-1)/2) * D`, so absorbing the sign
into `D` recovers `discr f = leadingCoeff f ^ (2 n - 2) * ∏_{i<j} (rᵢ - rⱼ)²`.

The derivation runs through Mathlib's resultant API
(`Polynomial.resultant_deriv`, `Polynomial.resultant_eq_prod_eval`) and the
derivative-at-a-root product `Polynomial.Splits.eval_root_derivative`.

Everything here is stated in ordinary Mathlib generality (an arbitrary field,
or an arbitrary injective base change for `discr_map_of_injective`) and is
upstreamable: Mathlib currently has the root-product discriminant formula only
for cubics (`Cubic.discr_eq_prod_three_roots`), not in general degree.
-/

open Multiset

namespace Polynomial

variable {K : Type*} [Field K]

/-- Derivative of a split polynomial evaluated at one of its roots, as a product
over the remaining roots: `f'(x) = leadingCoeff f * ∏_{y ∈ roots.erase x} (x - y)`.

This is the non-monic companion of `Polynomial.Splits.eval_root_derivative`;
it scales that monic statement by the leading coefficient. When `x` is a
repeated root both sides vanish. -/
theorem eval_derivative_of_mem_roots [DecidableEq K] {f : K[X]} (hsplit : f.Splits)
    {x : K} (hx : x ∈ f.roots) :
    f.derivative.eval x = f.leadingCoeff * ((f.roots.erase x).map (x - ·)).prod := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hx
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hcne : f.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero hlc
  have hgm : (C f.leadingCoeff⁻¹ * f).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hgs : (C f.leadingCoeff⁻¹ * f).Splits := (Splits.C _).mul hsplit
  have hgr : (C f.leadingCoeff⁻¹ * f).roots = f.roots := roots_C_mul f hcne
  have hxg : x ∈ (C f.leadingCoeff⁻¹ * f).roots := hgr ▸ hx
  have key := hgs.eval_root_derivative hgm hxg
  rw [derivative_C_mul, eval_mul, eval_C, hgr] at key
  -- key : f.leadingCoeff⁻¹ * f.derivative.eval x = ((f.roots.erase x).map (x - ·)).prod
  rw [← key, ← mul_assoc, mul_inv_cancel₀ hlc, one_mul]

/-- The root-product form of the discriminant of a split polynomial of positive
degree: with `n = natDegree f`,
`discr f = (-1) ^ (n (n-1) / 2) * leadingCoeff f ^ (2 n - 2)
             * ∏_{x ∈ roots} ∏_{y ∈ roots.erase x} (x - y)`.

The double product is the off-diagonal product of root differences; it equals
`(-1) ^ (n(n-1)/2) * ∏_{i<j} (rᵢ - rⱼ)²`, so this is the classical formula. -/
theorem discr_eq_prod_roots [DecidableEq K] {f : K[X]} (hf : 0 < f.degree)
    (hsplit : f.Splits) :
    f.discr = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
        f.leadingCoeff ^ (2 * f.natDegree - 2) *
        (f.roots.map (fun x => ((f.roots.erase x).map (x - ·)).prod)).prod := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hn : 0 < f.natDegree := natDegree_pos_iff_degree_pos.mpr hf
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hcard : f.roots.card = f.natDegree := (splits_iff_card_roots.mp hsplit)
  -- rewrite the resultant of `f` and `f'` as `lc ^ (n-1) * lc ^ n * D`
  have hprodeval : (f.roots.map f.derivative.eval).prod =
      f.leadingCoeff ^ f.natDegree *
        (f.roots.map (fun x => ((f.roots.erase x).map (x - ·)).prod)).prod := by
    rw [show (f.roots.map f.derivative.eval) =
          f.roots.map (fun x => f.leadingCoeff * ((f.roots.erase x).map (x - ·)).prod) from
        Multiset.map_congr rfl (fun x hx => eval_derivative_of_mem_roots hsplit hx),
      Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]
  have hres1 := resultant_deriv hf
  have hres2 := resultant_eq_prod_eval f f.derivative (f.natDegree - 1)
    (natDegree_derivative_le f) hsplit
  rw [hprodeval] at hres2
  -- E : (-1)^e * lc * discr f = lc^(n-1) * (lc^n * D)
  have E := hres1.symm.trans hres2
  -- cancel the nonzero factor `(-1)^e * lc`
  have hne : (-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hlc
  have h1 : (-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2) *
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have h2 : f.leadingCoeff ^ (f.natDegree - 1) * f.leadingCoeff ^ f.natDegree =
      f.leadingCoeff ^ (2 * f.natDegree - 1) := by
    rw [← pow_add]; congr 1; omega
  have h3 : f.leadingCoeff * f.leadingCoeff ^ (2 * f.natDegree - 2) =
      f.leadingCoeff ^ (2 * f.natDegree - 1) := by
    rw [← pow_succ']; congr 1; omega
  apply mul_left_cancel₀ hne
  calc (-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff * f.discr
      = f.leadingCoeff ^ (f.natDegree - 1) *
          (f.leadingCoeff ^ f.natDegree *
            (f.roots.map (fun x => ((f.roots.erase x).map (x - ·)).prod)).prod) := E
    _ = f.leadingCoeff ^ (2 * f.natDegree - 1) *
          (f.roots.map (fun x => ((f.roots.erase x).map (x - ·)).prod)).prod := by
        rw [← mul_assoc, h2]
    _ = ((-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2) *
            (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
          (f.leadingCoeff * f.leadingCoeff ^ (2 * f.natDegree - 2)) *
          (f.roots.map (fun x => ((f.roots.erase x).map (x - ·)).prod)).prod := by
        rw [h1, h3, one_mul]
    _ = (-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff *
          ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff ^ (2 * f.natDegree - 2) *
            (f.roots.map (fun x => ((f.roots.erase x).map (x - ·)).prod)).prod) := by ring

/-- The discriminant of a split polynomial of positive degree with distinct
roots is nonzero. -/
theorem discr_ne_zero_of_nodup_roots {f : K[X]} (hf : 0 < f.degree)
    (hsplit : f.Splits) (hnd : f.roots.Nodup) : f.discr ≠ 0 := by
  classical
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  rw [discr_eq_prod_roots hf hsplit]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf0))) ?_
  apply Multiset.prod_ne_zero
  intro hmem
  rw [Multiset.mem_map] at hmem
  obtain ⟨x, _, hPx⟩ := hmem
  rw [Multiset.prod_eq_zero_iff, Multiset.mem_map] at hPx
  obtain ⟨y, hy, hxy⟩ := hPx
  have hxy' := sub_eq_zero.mp hxy
  subst hxy'
  exact (hnd.mem_erase_iff.mp hy).1 rfl

/-- Base change of the discriminant along an injective ring homomorphism into a
domain: `discr (f.map φ) = φ (discr f)`, for `f` of positive degree. The
discriminant is a universal polynomial in the coefficients, so this holds for
any injective `φ`; the proof cancels the (nonzero) leading coefficient in the
resultant identity `Polynomial.resultant_deriv`. -/
theorem discr_map_of_injective {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (hφ : Function.Injective φ) {f : R[X]} (hf : 0 < f.degree) :
    (f.map φ).discr = φ f.discr := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hfm : 0 < (f.map φ).degree := by rw [degree_map_eq_of_injective hφ]; exact hf
  have hmn : (f.map φ).natDegree = f.natDegree := natDegree_map_eq_of_injective hφ f
  have h1 := resultant_deriv hfm
  rw [derivative_map, hmn, resultant_map_map, resultant_deriv hf] at h1
  simp only [map_mul, map_pow, map_neg, map_one, leadingCoeff_map_of_injective hφ] at h1
  -- h1 : (-1)^e * φ lc * φ (discr f) = (-1)^e * φ lc * discr (f.map φ)
  have hlc' : φ f.leadingCoeff ≠ 0 := by
    rw [ne_eq, ← _root_.map_zero φ]; exact fun h => hlc (hφ h)
  have hne : (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) * φ f.leadingCoeff ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hlc'
  exact (mul_left_cancel₀ hne h1).symm

/-- The discriminant of a separable polynomial of positive degree over a field is
nonzero. This is the non-vanishing input Mahler's separation bound needs; it does
not assume `f` splits (it passes to the splitting field). -/
theorem discr_ne_zero_of_separable {f : K[X]} (hf : 0 < f.degree)
    (hsep : f.Separable) : f.discr ≠ 0 := by
  classical
  have hφ : Function.Injective (algebraMap K f.SplittingField) := (algebraMap K _).injective
  have hmap : (f.map (algebraMap K f.SplittingField)).discr =
      algebraMap K f.SplittingField f.discr := discr_map_of_injective _ hφ hf
  have hdeg : 0 < (f.map (algebraMap K f.SplittingField)).degree := by
    rw [degree_map_eq_of_injective hφ]; exact hf
  have hsplit : (f.map (algebraMap K f.SplittingField)).Splits := SplittingField.splits f
  have hnd : (f.map (algebraMap K f.SplittingField)).roots.Nodup := nodup_roots hsep.map
  have hres := discr_ne_zero_of_nodup_roots hdeg hsplit hnd
  rw [hmap] at hres
  exact fun h => hres (by rw [h, _root_.map_zero])

/-- Mahler's lower bound input: the discriminant of an integer polynomial of
positive degree whose rational image is separable (equivalently squarefree over
`ℚ`) is a nonzero integer, hence has absolute value at least `1`. -/
theorem one_le_abs_discr {f : ℤ[X]} (hf : 0 < f.degree)
    (hsep : (f.map (Int.castRingHom ℚ)).Separable) : 1 ≤ |f.discr| := by
  have hφ : Function.Injective (Int.castRingHom ℚ) := (Int.castRingHom ℚ).injective_int
  apply Int.one_le_abs
  intro hd
  have hmap := discr_map_of_injective (Int.castRingHom ℚ) hφ hf
  have hne : (f.map (Int.castRingHom ℚ)).discr ≠ 0 :=
    discr_ne_zero_of_separable (by rwa [degree_map_eq_of_injective hφ]) hsep
  rw [hmap, hd] at hne
  simp at hne

end Polynomial
