/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexPolyZMathlib.Discriminant
public import HexPolyZMathlib.Hadamard

public section

/-!
# Generic Mahler separation analysis

This module develops the Hex-independent analytic part of Mahler's
root-separation argument over complex roots. It bounds ordinary and differenced
Vandermonde columns, applies the sharp column form of Hadamard's determinant inequality,
and identifies the discriminant root product with the squared Vandermonde
norm.

Executable precision arithmetic and root-isolation specializations remain in
the corresponding roots companions.
-/

open Polynomial Finset Matrix

namespace HexPolyZMathlib

noncomputable section

/-- Squarefreeness of an integral polynomial is preserved after extending
coefficients to `ℚ`.  Constant prime factors become units; the primitive part
is handled by Gauss's lemma. -/
private theorem squarefree_map_rat {p : ℤ[X]} (hp : Squarefree p) :
    Squarefree (p.map (Int.castRingHom ℚ)) := by
  let p0 := p.primPart
  have hp0sq : Squarefree p0 :=
    hp.squarefree_of_dvd (p.primPart_dvd)
  have hp0ne : p0 ≠ 0 := p.primPart_ne_zero
  have hmap0ne : p0.map (Int.castRingHom ℚ) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (RingHom.injective_int _)]
    exact hp0ne
  have hmap0sq : Squarefree (p0.map (Int.castRingHom ℚ)) := by
    rw [squarefree_iff_no_irreducibles hmap0ne]
    intro r hr hrr
    let g : ℤ[X] :=
      IsLocalization.integerNormalization (nonZeroDivisors ℤ) r
    let h : ℤ[X] := g.primPart
    obtain ⟨c, hc, hcg⟩ :=
      IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) r
    have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
    have hg0 : g ≠ 0 := by
      change IsLocalization.integerNormalization (nonZeroDivisors ℤ) r ≠ 0
      rw [Ne, IsLocalization.integerNormalization_eq_zero_iff
        (show nonZeroDivisors ℤ ≤ nonZeroDivisors ℤ from le_rfl)]
      exact hr.ne_zero
    have hcontent0 : g.content ≠ 0 :=
      fun h0 => hg0 (content_eq_zero_iff.mp h0)
    have hcunit : IsUnit (C (c : ℚ) : ℚ[X]) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hc0))
    have hcontentUnit : IsUnit (C (g.content : ℚ) : ℚ[X]) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hcontent0))
    have hgr : Associated (g.map (Int.castRingHom ℚ)) r := by
      rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hcg
      exact (Associated.of_eq hcg).trans
        (associated_unit_mul_left r _ hcunit)
    have hgh : Associated (g.map (Int.castRingHom ℚ))
        (h.map (Int.castRingHom ℚ)) := by
      have heq := congrArg (Polynomial.map (Int.castRingHom ℚ))
        g.eq_C_content_mul_primPart
      rw [Polynomial.map_mul, map_C] at heq
      exact (Associated.of_eq heq).trans
        (associated_unit_mul_left _ _ hcontentUnit)
    have hhr : Associated (h.map (Int.castRingHom ℚ)) r :=
      hgh.symm.trans hgr
    have hhprim : h.IsPrimitive := g.isPrimitive_primPart
    have hhmapIrr : Irreducible (h.map (Int.castRingHom ℚ)) :=
      hhr.symm.irreducible hr
    have hhIrr : Irreducible h :=
      hhprim.irreducible_of_irreducible_map_of_injective
        (RingHom.injective_int _) hhmapIrr
    have hmapDvd : (h * h).map (Int.castRingHom ℚ) ∣
        p0.map (Int.castRingHom ℚ) := by
      rw [Polynomial.map_mul]
      exact (hhr.mul_mul hhr).dvd_iff_dvd_left.mpr hrr
    have hDvd : h * h ∣ p0 :=
      (hhprim.mul hhprim).dvd_of_fraction_map_dvd_fraction_map hmapDvd
    exact hhIrr.not_isUnit (hp0sq h hDvd)
  have hcontent0 : p.content ≠ 0 :=
    fun h0 => hp.ne_zero (content_eq_zero_iff.mp h0)
  have hcontentUnit : IsUnit (C (p.content : ℚ) : ℚ[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hcontent0))
  have hassoc : Associated (p.map (Int.castRingHom ℚ))
      (p0.map (Int.castRingHom ℚ)) := by
    have heq := congrArg (Polynomial.map (Int.castRingHom ℚ))
      p.eq_C_content_mul_primPart
    rw [Polynomial.map_mul, map_C] at heq
    exact (Associated.of_eq heq).trans
      (associated_unit_mul_left _ _ hcontentUnit)
  exact hassoc.squarefree_iff.mpr hmap0sq

/-- The divided-difference entry bound: `‖yⁱ − xⁱ‖ ≤ i · Cⁱ⁻¹ · ‖y − x‖` when
`‖x‖, ‖y‖ ≤ C` and `1 ≤ C`. Follows from the geometric factorisation
`yⁱ − xⁱ = (∑_{l<i} yˡ xⁱ⁻¹⁻ˡ)(y − x)`. -/
theorem norm_pow_sub_pow_le {x y : ℂ} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C)
    (hC : 1 ≤ C) (i : ℕ) : ‖y ^ i - x ^ i‖ ≤ (i : ℝ) * C ^ (i - 1) * ‖y - x‖ := by
  rw [← geom_sum₂_mul y x i, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖∑ l ∈ Finset.range i, y ^ l * x ^ (i - 1 - l)‖
      ≤ ∑ l ∈ Finset.range i, ‖y ^ l * x ^ (i - 1 - l)‖ := norm_sum_le _ _
    _ ≤ ∑ _l ∈ Finset.range i, C ^ (i - 1) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl' : l ≤ i - 1 := by have := Finset.mem_range.mp hl; omega
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖y‖ ^ l * ‖x‖ ^ (i - 1 - l) ≤ C ^ l * C ^ (i - 1 - l) := by
              gcongr
          _ = C ^ (l + (i - 1 - l)) := by rw [← pow_add]
          _ = C ^ (i - 1) := by rw [Nat.add_sub_cancel' hl']
    _ = (i : ℝ) * C ^ (i - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The L² norm of an ordinary Vandermonde column: `√(∑ᵢ ‖aⁱ‖²) ≤ √N · max(1,‖a‖)^{N-1}`. -/
theorem sqrt_sum_pow_sq_le (a : ℂ) (N : ℕ) :
    Real.sqrt (∑ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2) ≤ Real.sqrt N * (max 1 ‖a‖) ^ (N - 1) := by
  have hBnn : (0 : ℝ) ≤ max 1 ‖a‖ := le_trans zero_le_one (le_max_left _ _)
  have hbound : ∑ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2 ≤ (N : ℝ) * (max 1 ‖a‖) ^ (2 * (N - 1)) := by
    have : ∀ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2 ≤ (max 1 ‖a‖) ^ (2 * (N - 1)) := by
      intro i
      rw [norm_pow, ← pow_mul]
      calc ‖a‖ ^ ((i : ℕ) * 2) ≤ (max 1 ‖a‖) ^ ((i : ℕ) * 2) := by
            gcongr
            exact le_max_right _ _
        _ ≤ (max 1 ‖a‖) ^ (2 * (N - 1)) := by
            apply pow_le_pow_right₀ (le_max_left _ _)
            have := i.isLt; omega
    calc ∑ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2
        ≤ ∑ _i : Fin N, (max 1 ‖a‖) ^ (2 * (N - 1)) := Finset.sum_le_sum (fun i _ => this i)
      _ = (N : ℝ) * (max 1 ‖a‖) ^ (2 * (N - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i : Fin N, ‖a ^ (i : ℕ)‖ ^ 2)
      ≤ Real.sqrt ((N : ℝ) * (max 1 ‖a‖) ^ (2 * (N - 1))) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt N * (max 1 ‖a‖) ^ (N - 1) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg N), show 2 * (N - 1) = (N - 1) * 2 by ring,
          pow_mul, Real.sqrt_sq (by positivity)]

/-- The L² norm of the isolating (differenced) Vandermonde column:
`√(∑ᵢ ‖yⁱ − xⁱ‖²) ≤ C^{N-2} · ‖y − x‖ · √(∑ᵢ i²)`. -/
theorem sqrt_sum_sub_pow_sq_le {x y : ℂ} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C)
    (hC : 1 ≤ C) (N : ℕ) :
    Real.sqrt (∑ i : Fin N, ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ^ 2)
      ≤ C ^ (N - 2) * ‖y - x‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) := by
  have hCnn : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have hbound : ∑ i : Fin N, ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ^ 2
      ≤ (C ^ (N - 2) * ‖y - x‖) ^ 2 * ∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hentry : ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ≤ ((i : ℕ) : ℝ) * C ^ (N - 2) * ‖y - x‖ := by
      refine (norm_pow_sub_pow_le hx hy hC (i : ℕ)).trans ?_
      have hstep : C ^ ((i : ℕ) - 1) ≤ C ^ (N - 2) := by
        apply pow_le_pow_right₀ hC; have := i.isLt; omega
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)) (norm_nonneg _)
    calc ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ^ 2
        ≤ (((i : ℕ) : ℝ) * C ^ (N - 2) * ‖y - x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hentry 2
      _ = (C ^ (N - 2) * ‖y - x‖) ^ 2 * ((i : ℕ) : ℝ) ^ 2 := by ring
  calc Real.sqrt (∑ i : Fin N, ‖y ^ (i : ℕ) - x ^ (i : ℕ)‖ ^ 2)
      ≤ Real.sqrt ((C ^ (N - 2) * ‖y - x‖) ^ 2 * ∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = C ^ (N - 2) * ‖y - x‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- `√(∑_{i<N} i²) ≤ (√N)³`. -/
theorem sqrt_sum_sq_le (N : ℕ) :
    Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) ≤ Real.sqrt N ^ 3 := by
  have hb : ∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by
    calc ∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2
        ≤ ∑ _i : Fin N, (N : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi : ((i : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt i.isLt
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) hi 2
      _ = (N : ℝ) ^ 3 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsq : (Real.sqrt N ^ 3) ^ 2 = (N : ℝ) ^ 3 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg N)]
  refine (Real.sqrt_le_sqrt hb).trans (le_of_eq ?_)
  rw [← hsq, Real.sqrt_sq (by positivity)]

/-- **Mahler's isolating-column bound.** For a leading coefficient `c` and points
`α : Fin N → ℂ` with `‖α i₀‖ ≤ ‖α i₁‖`, the scaled Vandermonde determinant is
bounded by `√N^{N-1} · √(∑ i²) · (‖c‖ · ∏ max(1,‖α j‖))^{N-1} · ‖α i₁ − α i₀‖`. -/
theorem norm_det_vandermonde_le {N : ℕ} (hN : 2 ≤ N) (c : ℂ) (α : Fin N → ℂ)
    {i₀ i₁ : Fin N} (hne : i₀ ≠ i₁) (hle : ‖α i₀‖ ≤ ‖α i₁‖) :
    ‖c‖ ^ (N - 1) * ‖(Matrix.vandermonde α).det‖ ≤
      Real.sqrt N ^ (N - 1) * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2)
        * (‖c‖ * ∏ j, max 1 ‖α j‖) ^ (N - 1) * ‖α i₁ - α i₀‖ := by
  classical
  set B : Fin N → ℝ := fun j => max 1 ‖α j‖ with hBdef
  have hB1 : ∀ j, (1 : ℝ) ≤ B j := fun j => le_max_left _ _
  have hBnorm : ∀ j, ‖α j‖ ≤ B j := fun j => le_max_right _ _
  have hB0 : ∀ j, (0 : ℝ) ≤ B j := fun j => le_trans zero_le_one (hB1 j)
  -- The row-reduced matrix `W`: subtract row `i₀` from row `i₁`.
  set W : Matrix (Fin N) (Fin N) ℂ :=
    (Matrix.vandermonde α).updateRow i₁
      ((Matrix.vandermonde α) i₁ + (-1 : ℂ) • (Matrix.vandermonde α) i₀) with hWdef
  have hWdet : W.det = (Matrix.vandermonde α).det :=
    Matrix.det_updateRow_add_smul_self _ (Ne.symm hne) _
  have hWne : ∀ j, j ≠ i₁ → ∀ i : Fin N, W j i = α j ^ (i : ℕ) := by
    intro j hj i
    rw [hWdef, Matrix.updateRow_ne hj, Matrix.vandermonde_apply]
  have hWeq : ∀ i : Fin N, W i₁ i = α i₁ ^ (i : ℕ) - α i₀ ^ (i : ℕ) := by
    intro i
    rw [hWdef, Matrix.updateRow_self]
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.vandermonde_apply, smul_eq_mul, neg_one_mul]
    ring
  -- Hadamard's inequality applied to the transpose.
  have hHad : ‖(Matrix.vandermonde α).det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖W j i‖ ^ 2) := by
    rw [← hWdet, ← Matrix.det_transpose W]
    exact Matrix.norm_det_le_prod_norm_column Wᵀ
  -- Column bounds.
  have hRi1 : Real.sqrt (∑ i, ‖W i₁ i‖ ^ 2)
      ≤ B i₁ ^ (N - 2) * ‖α i₁ - α i₀‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) := by
    rw [show (∑ i, ‖W i₁ i‖ ^ 2) = ∑ i : Fin N, ‖α i₁ ^ (i : ℕ) - α i₀ ^ (i : ℕ)‖ ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [hWeq i])]
    exact sqrt_sum_sub_pow_sq_le (le_trans hle (hBnorm i₁)) (hBnorm i₁) (hB1 i₁) N
  have hRj : ∀ j, j ≠ i₁ →
      Real.sqrt (∑ i, ‖W j i‖ ^ 2) ≤ Real.sqrt N * B j ^ (N - 1) := by
    intro j hj
    rw [show (∑ i, ‖W j i‖ ^ 2) = ∑ i : Fin N, ‖α j ^ (i : ℕ)‖ ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [hWne j hj i])]
    exact sqrt_sum_pow_sq_le (α j) N
  -- Product of column bounds.
  have herasecard : (univ.erase i₁).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₁), Finset.card_univ, Fintype.card_fin]
  have hprodEnn : (0 : ℝ) ≤ ∏ j ∈ univ.erase i₁, B j := Finset.prod_nonneg (fun j _ => hB0 j)
  have hprodbound : ∏ j, Real.sqrt (∑ i, ‖W j i‖ ^ 2)
      ≤ (B i₁ ^ (N - 2) * ‖α i₁ - α i₀‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2))
        * ∏ j ∈ univ.erase i₁, (Real.sqrt N * B j ^ (N - 1)) := by
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i₁)]
    refine mul_le_mul hRi1 ?_ (Finset.prod_nonneg (fun j _ => Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (pow_nonneg (hB0 i₁) _) (norm_nonneg _)) (Real.sqrt_nonneg _))
    exact Finset.prod_le_prod (fun j _ => Real.sqrt_nonneg _)
      (fun j hj => hRj j (Finset.mem_erase.mp hj).1)
  have hprodrw : ∏ j ∈ univ.erase i₁, (Real.sqrt N * B j ^ (N - 1))
      = Real.sqrt N ^ (N - 1) * (∏ j ∈ univ.erase i₁, B j) ^ (N - 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, herasecard, Finset.prod_pow]
  -- Combine.
  have hcombine : ‖c‖ ^ (N - 1) * ‖(Matrix.vandermonde α).det‖
      ≤ ‖c‖ ^ (N - 1) * (B i₁ ^ (N - 2) * ‖α i₁ - α i₀‖
          * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2)
          * (Real.sqrt N ^ (N - 1) * (∏ j ∈ univ.erase i₁, B j) ^ (N - 1))) := by
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg c) _)
    calc ‖(Matrix.vandermonde α).det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖W j i‖ ^ 2) := hHad
      _ ≤ (B i₁ ^ (N - 2) * ‖α i₁ - α i₀‖ * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2))
            * ∏ j ∈ univ.erase i₁, (Real.sqrt N * B j ^ (N - 1)) := hprodbound
      _ = _ := by rw [hprodrw]
  refine hcombine.trans ?_
  -- The final algebra: `(B i₁)^{N-2} ≤ (B i₁)^{N-1}` absorbs the leftover factor.
  set K := Real.sqrt N ^ (N - 1) * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2) * ‖c‖ ^ (N - 1)
      * (∏ j ∈ univ.erase i₁, B j) ^ (N - 1) * ‖α i₁ - α i₀‖ with hKdef
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg (Real.sqrt_nonneg _) _) (Real.sqrt_nonneg _))
      (pow_nonneg (norm_nonneg _) _)) (pow_nonneg hprodEnn _)) (norm_nonneg _)
  have hBig : ‖c‖ ^ (N - 1) * (B i₁ ^ (N - 2) * ‖α i₁ - α i₀‖
        * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2)
        * (Real.sqrt N ^ (N - 1) * (∏ j ∈ univ.erase i₁, B j) ^ (N - 1)))
      = K * B i₁ ^ (N - 2) := by rw [hKdef]; ring
  have hTar : Real.sqrt N ^ (N - 1) * Real.sqrt (∑ i : Fin N, ((i : ℕ) : ℝ) ^ 2)
        * (‖c‖ * ∏ j, B j) ^ (N - 1) * ‖α i₁ - α i₀‖ = K * B i₁ ^ (N - 1) := by
    rw [show (∏ j, B j) = B i₁ * ∏ j ∈ univ.erase i₁, B j from
      (Finset.mul_prod_erase univ B (Finset.mem_univ i₁)).symm, mul_pow, mul_pow, hKdef]
    ring
  rw [hBig, hTar]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hB1 i₁) (by omega)) hKnn

/-- The off-diagonal root-difference product equals `‖det V‖²` in norm. -/
theorem norm_prod_roots_eq_sq {N : ℕ} (α : Fin N → ℂ) (hα : Function.Injective α) :
    ‖((Multiset.map α univ.val).map
        (fun x => (((Multiset.map α univ.val).erase x).map (fun y => x - y)).prod)).prod‖
      = ‖(Matrix.vandermonde α).det‖ ^ 2 := by
  classical
  -- Reduce the multiset double product to a `Finset` double product.
  have hD : ((Multiset.map α univ.val).map
      (fun x => (((Multiset.map α univ.val).erase x).map (fun y => x - y)).prod)).prod
        = ∏ i, ∏ j ∈ univ.erase i, (α i - α j) := by
    rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [Function.comp_apply]
    rw [← Multiset.map_erase α hα, ← Finset.erase_val, Multiset.map_map,
      ← Finset.prod_eq_multiset_prod]
    rfl
  rw [hD, det_vandermonde]
  simp only [norm_prod]
  -- Symmetry of the norm of a difference.
  have hsym : ∀ a b : ℂ, ‖a - b‖ = ‖b - a‖ := fun a b => norm_sub_rev a b
  -- Rewrite the Vandermonde side to `∏ i, ∏ j ∈ Ioi i, ‖α i - α j‖`.
  have hQ : ∏ i, ∏ j ∈ Ioi i, ‖α j - α i‖ = ∏ i, ∏ j ∈ Ioi i, ‖α i - α j‖ :=
    Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => hsym _ _))
  rw [hQ]
  -- The lower-triangular product equals the upper-triangular product by symmetry.
  have hPIio : ∏ i, ∏ j ∈ Iio i, ‖α i - α j‖ = ∏ i, ∏ j ∈ Ioi i, ‖α i - α j‖ := by
    rw [Finset.prod_comm' (s := univ) (t := fun i => Iio i) (t' := univ) (s' := fun j => Ioi j)
      (by intro x y; simp only [Finset.mem_univ, true_and, and_true,
        Finset.mem_Iio, Finset.mem_Ioi])]
    exact Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => hsym _ _))
  -- Split `univ.erase i = Ioi i ⊔ Iio i` and recombine.
  have hsplit2 : ∀ i : Fin N,
      univ.erase i = (Ioi i).disjUnion (Iio i) (Finset.disjoint_Ioi_Iio i) := by
    intro i; rw [Finset.Ioi_disjUnion_Iio, Finset.compl_singleton]
  calc ∏ i, ∏ j ∈ univ.erase i, ‖α i - α j‖
      = ∏ i, ((∏ j ∈ Ioi i, ‖α i - α j‖) * ∏ j ∈ Iio i, ‖α i - α j‖) :=
        Finset.prod_congr rfl (fun i _ => by rw [hsplit2 i, Finset.prod_disjUnion])
    _ = (∏ i, ∏ j ∈ Ioi i, ‖α i - α j‖) * ∏ i, ∏ j ∈ Iio i, ‖α i - α j‖ :=
        Finset.prod_mul_distrib
    _ = (∏ i, ∏ j ∈ Ioi i, ‖α i - α j‖) ^ 2 := by rw [hPIio, sq]

/-- The discriminant in root-enumeration form: `‖disc f‖ = ‖lc‖^{2n-2} · ‖det V‖²`. -/
theorem norm_discr_eq {N : ℕ} (α : Fin N → ℂ) (hα : Function.Injective α) {f : ℂ[X]}
    (hf : 0 < f.degree) (hsplit : f.Splits) (hroots : f.roots = Multiset.map α univ.val) :
    ‖f.discr‖ = ‖f.leadingCoeff‖ ^ (2 * f.natDegree - 2) * ‖(Matrix.vandermonde α).det‖ ^ 2 := by
  classical
  rw [discr_eq_prod_roots hf hsplit]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [hroots, norm_prod_roots_eq_sq α hα]

/-- The exponent-independent assembly of Mahler's root-separation argument.
For two distinct roots of a separable integral polynomial, the product of
their distance with the Hadamard degree factor and the appropriate power of
the Mahler measure is at least one. Executable precision specializations need
only bound the final two factors. -/
theorem one_le_mahlerDist_of_separable (p : ℤ[X])
    (hsep : (p.map (Int.castRingHom ℚ)).Separable) {z₁ z₂ : ℂ}
    (hr₁ : (p.map (Int.castRingHom ℂ)).IsRoot z₁)
    (hr₂ : (p.map (Int.castRingHom ℂ)).IsRoot z₂) (hne : z₁ ≠ z₂) :
    (1 : ℝ) ≤ Real.sqrt p.natDegree ^ (p.natDegree + 2) *
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ^ (p.natDegree - 1) *
        ‖z₁ - z₂‖ := by
  classical
  let f := p.map (Int.castRingHom ℂ)
  suffices key : ∀ w₁ w₂ : ℂ, f.IsRoot w₁ → f.IsRoot w₂ → w₁ ≠ w₂ →
      ‖w₁‖ ≤ ‖w₂‖ →
      (1 : ℝ) ≤ Real.sqrt p.natDegree ^ (p.natDegree + 2) *
        f.mahlerMeasure ^ (p.natDegree - 1) * ‖w₁ - w₂‖ by
    rcases le_total ‖z₁‖ ‖z₂‖ with h | h
    · exact key z₁ z₂ hr₁ hr₂ hne h
    · simpa only [f, norm_sub_rev] using
        key z₂ z₁ hr₂ hr₁ hne.symm h
  intro w₁ w₂ hw₁ hw₂ hwne hnorm
  have hp0 : p ≠ 0 := fun h => hsep.ne_zero (by rw [h, Polynomial.map_zero])
  have hf0 : f ≠ 0 := by
    dsimp only [f]
    rw [ne_eq, Polynomial.map_eq_zero_iff (RingHom.injective_int _)]
    exact hp0
  have hsplit : f.Splits := IsAlgClosed.splits f
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) =
      Int.castRingHom ℂ := RingHom.ext_int _ _
  have hsepℂ : f.Separable := by
    have hff : f = (p.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) := by
      dsimp only [f]
      rw [Polynomial.map_map, hcomp]
    rw [hff]
    exact hsep.map
  have hnd : f.roots.Nodup := nodup_roots hsepℂ
  let roots := f.roots.toList
  have hrootsNodup : roots.Nodup := Multiset.coe_nodup.mp (by
    dsimp only [roots]
    rw [Multiset.coe_toList]
    exact hnd)
  let α : Fin roots.length → ℂ := roots.get
  have hαinj : Function.Injective α :=
    List.nodup_iff_injective_get.mp hrootsNodup
  have hroots : Multiset.map α univ.val = f.roots := by
    rw [Fin.univ_val_map]
    dsimp only [α]
    rw [List.ofFn_get]
    dsimp only [roots]
    rw [Multiset.coe_toList]
  have hw₁List : w₁ ∈ roots := by
    dsimp only [roots]
    rw [← Multiset.mem_coe, Multiset.coe_toList]
    exact (mem_roots hf0).mpr hw₁
  have hw₂List : w₂ ∈ roots := by
    dsimp only [roots]
    rw [← Multiset.mem_coe, Multiset.coe_toList]
    exact (mem_roots hf0).mpr hw₂
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.mp hw₁List
  obtain ⟨i₁, hi₁⟩ := List.mem_iff_get.mp hw₂List
  have hαi₀ : α i₀ = w₁ := hi₀
  have hαi₁ : α i₁ = w₂ := hi₁
  have hii : i₀ ≠ i₁ := fun h => hwne (by rw [← hαi₀, ← hαi₁, h])
  have hcard : Multiset.card f.roots = f.natDegree :=
    splits_iff_card_roots.mp hsplit
  have hlen : roots.length = f.natDegree := by
    dsimp only [roots]
    rw [Multiset.length_toList, hcard]
  have hnatf : f.natDegree = roots.length := hlen.symm
  have hnatp : p.natDegree = f.natDegree := by
    dsimp only [f]
    exact (Polynomial.natDegree_map_eq_of_injective
      (RingHom.injective_int _) p).symm
  have hN2 : 2 ≤ roots.length := by
    have h₀ := i₀.isLt
    have h₁ := i₁.isLt
    have : i₀.val ≠ i₁.val := fun h => hii (Fin.ext h)
    omega
  have hdegf : 0 < f.degree :=
    natDegree_pos_iff_degree_pos.mp (by omega)
  have hdegp : 0 < p.degree :=
    natDegree_pos_iff_degree_pos.mp (by rw [hnatp, hnatf]; omega)
  have hdiscZ : 1 ≤ |p.discr| := Polynomial.one_le_abs_discr hdegp hsep
  have hdiscnorm : (1 : ℝ) ≤ ‖f.discr‖ := by
    have hmap : f.discr = ((p.discr : ℤ) : ℂ) := by
      dsimp only [f]
      rw [Polynomial.discr_map_of_injective (Int.castRingHom ℂ)
        (RingHom.injective_int _) hdegp]
      simp
    rw [hmap, Complex.norm_intCast]
    exact_mod_cast hdiscZ
  have hdisceq := norm_discr_eq α hαinj hdegf hsplit hroots.symm
  rw [hnatf] at hdisceq
  let V := (Matrix.vandermonde α).det
  have hAsq : (‖f.leadingCoeff‖ ^ (roots.length - 1) * ‖V‖) ^ 2 =
      ‖f.leadingCoeff‖ ^ (2 * roots.length - 2) * ‖V‖ ^ 2 := by
    rw [mul_pow, ← pow_mul]
    congr 2
    omega
  have hAnn : (0 : ℝ) ≤
      ‖f.leadingCoeff‖ ^ (roots.length - 1) * ‖V‖ := by positivity
  have hA1 : (1 : ℝ) ≤
      ‖f.leadingCoeff‖ ^ (roots.length - 1) * ‖V‖ := by
    have hsq1 : (1 : ℝ) ≤
        (‖f.leadingCoeff‖ ^ (roots.length - 1) * ‖V‖) ^ 2 := by
      rw [hAsq, ← hdisceq]
      exact hdiscnorm
    nlinarith [hsq1, hAnn]
  have hnormα : ‖α i₀‖ ≤ ‖α i₁‖ := by
    rw [hαi₀, hαi₁]
    exact hnorm
  have hcrux := norm_det_vandermonde_le
    hN2 f.leadingCoeff α hii hnormα
  have hsqrtstep :
      Real.sqrt roots.length ^ (roots.length - 1) *
          Real.sqrt (∑ i : Fin roots.length, ((i : ℕ) : ℝ) ^ 2) ≤
        Real.sqrt roots.length ^ (roots.length + 2) := by
    calc
      Real.sqrt roots.length ^ (roots.length - 1) *
          Real.sqrt (∑ i : Fin roots.length, ((i : ℕ) : ℝ) ^ 2)
          ≤ Real.sqrt roots.length ^ (roots.length - 1) *
              Real.sqrt roots.length ^ 3 :=
            mul_le_mul_of_nonneg_left (sqrt_sum_sq_le roots.length)
              (by positivity)
      _ = Real.sqrt roots.length ^ (roots.length + 2) := by
            rw [← pow_add]
            congr 1
            omega
  have hMprod : (f.roots.map (fun a => max 1 ‖a‖)).prod =
      ∏ j, max 1 ‖α j‖ := by
    rw [← hroots, Multiset.map_map]
    rfl
  have hM : ‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖ =
      f.mahlerMeasure := by
    rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hMprod]
  have hdiff : ‖α i₁ - α i₀‖ = ‖w₁ - w₂‖ := by
    rw [hαi₀, hαi₁, norm_sub_rev]
  rw [hnatp, hnatf]
  calc
    (1 : ℝ) ≤ ‖f.leadingCoeff‖ ^ (roots.length - 1) * ‖V‖ := hA1
    _ ≤ Real.sqrt roots.length ^ (roots.length - 1) *
          Real.sqrt (∑ i : Fin roots.length, ((i : ℕ) : ℝ) ^ 2) *
          (‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖) ^
            (roots.length - 1) * ‖α i₁ - α i₀‖ := hcrux
    _ = (Real.sqrt roots.length ^ (roots.length - 1) *
          Real.sqrt (∑ i : Fin roots.length, ((i : ℕ) : ℝ) ^ 2)) *
          ((‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖) ^
            (roots.length - 1) * ‖α i₁ - α i₀‖) := by ring
    _ ≤ Real.sqrt roots.length ^ (roots.length + 2) *
          ((‖f.leadingCoeff‖ * ∏ j, max 1 ‖α j‖) ^
            (roots.length - 1) * ‖α i₁ - α i₀‖) :=
        mul_le_mul_of_nonneg_right hsqrtstep
          (mul_nonneg (pow_nonneg (mul_nonneg (norm_nonneg _)
            (Finset.prod_nonneg (fun j _ => le_trans zero_le_one
              (le_max_left _ _)))) _) (norm_nonneg _))
    _ = Real.sqrt roots.length ^ (roots.length + 2) *
          f.mahlerMeasure ^ (roots.length - 1) * ‖w₁ - w₂‖ := by
        rw [hM, hdiff]
        ring

/-- **Mahler separation for arbitrary nonzero integral polynomials.**  Repeated
factors do not affect the set of roots: applying the separable theorem to the
integral radical gives the same two roots, no larger degree, and no larger
Mahler measure. -/
theorem one_le_mahlerDist (p : ℤ[X]) (hp : p ≠ 0) {z₁ z₂ : ℂ}
    (hr₁ : (p.map (Int.castRingHom ℂ)).IsRoot z₁)
    (hr₂ : (p.map (Int.castRingHom ℂ)).IsRoot z₂) (hne : z₁ ≠ z₂) :
    (1 : ℝ) ≤ Real.sqrt p.natDegree ^ (p.natDegree + 2) *
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ^ (p.natDegree - 1) *
        ‖z₁ - z₂‖ := by
  classical
  let q : ℤ[X] := UniqueFactorizationMonoid.radical p
  let f : ℂ[X] := p.map (Int.castRingHom ℂ)
  let g : ℂ[X] := q.map (Int.castRingHom ℂ)
  have hq0 : q ≠ 0 := UniqueFactorizationMonoid.radical_ne_zero
  have hqsep : (q.map (Int.castRingHom ℚ)).Separable :=
    PerfectField.separable_iff_squarefree.mpr
      (squarefree_map_rat UniqueFactorizationMonoid.squarefree_radical)
  obtain ⟨k, hpk⟩ :=
    UniqueFactorizationMonoid.exists_dvd_radical_self_pow hp
  have hmapDvd : f ∣ g ^ k := by
    rcases hpk with ⟨s, hs⟩
    refine ⟨s.map (Int.castRingHom ℂ), ?_⟩
    dsimp only [f, g, q]
    rw [← Polynomial.map_mul, ← hs, Polynomial.map_pow]
  have hqroot₁ : g.IsRoot z₁ := by
    have hpow := hr₁.dvd hmapDvd
    rw [IsRoot.def, eval_pow] at hpow
    exact eq_zero_of_pow_eq_zero hpow
  have hqroot₂ : g.IsRoot z₂ := by
    have hpow := hr₂.dvd hmapDvd
    rw [IsRoot.def, eval_pow] at hpow
    exact eq_zero_of_pow_eq_zero hpow
  have hshared := one_le_mahlerDist_of_separable q hqsep hqroot₁ hqroot₂ hne
  have hdeg : q.natDegree ≤ p.natDegree :=
    natDegree_le_of_dvd UniqueFactorizationMonoid.radical_dvd_self hp
  have hg0 : g ≠ 0 := by
    dsimp only [g]
    rw [Polynomial.map_ne_zero_iff (RingHom.injective_int _)]
    exact hq0
  have hnatg : g.natDegree = q.natDegree := by
    dsimp only [g]
    exact Polynomial.natDegree_map_eq_of_injective
      (RingHom.injective_int _) q
  have hqdegPos : 0 < q.natDegree := by
    have hgdeg : 0 < g.degree := degree_pos_of_root hg0 hqroot₁
    have : 0 < g.natDegree := natDegree_pos_iff_degree_pos.mpr hgdeg
    rwa [hnatg] at this
  have hqdegTwo : 2 ≤ q.natDegree := by
    by_contra h
    have hqdegOne : q.natDegree = 1 := by omega
    have hgdegOne : g.natDegree = 1 := by
      rw [hnatg]
      exact hqdegOne
    exact hne (subsingleton_isRoot_of_natDegree_eq_one hgdegOne hqroot₁ hqroot₂)
  have hpdegTwo : 2 ≤ p.natDegree := hqdegTwo.trans hdeg
  have hsqrt : Real.sqrt q.natDegree ≤ Real.sqrt p.natDegree :=
    Real.sqrt_le_sqrt (by exact_mod_cast hdeg)
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt p.natDegree :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ p.natDegree by omega))
  have hdegreeFactor :
      Real.sqrt q.natDegree ^ (q.natDegree + 2) ≤
        Real.sqrt p.natDegree ^ (p.natDegree + 2) := by
    calc
      Real.sqrt q.natDegree ^ (q.natDegree + 2)
          ≤ Real.sqrt p.natDegree ^ (q.natDegree + 2) :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt _
      _ ≤ Real.sqrt p.natDegree ^ (p.natDegree + 2) :=
        pow_le_pow_right₀ hsqrtOne (by omega)
  obtain ⟨r, hpr⟩ := UniqueFactorizationMonoid.radical_dvd_self (a := p)
  have hr0 : r ≠ 0 := fun hr => hp (by rw [hpr, hr, mul_zero])
  have hfEq : f = g * r.map (Int.castRingHom ℂ) := by
    dsimp only [f, g, q]
    simpa only [Polynomial.map_mul] using
      congrArg (Polynomial.map (Int.castRingHom ℂ)) hpr
  have hmeasure : g.mahlerMeasure ≤ f.mahlerMeasure := by
    have hrOne : (1 : ℝ) ≤
        (r.map (Int.castRingHom ℂ)).mahlerMeasure :=
      Polynomial.one_le_mahlerMeasure_of_ne_zero hr0
    calc
      g.mahlerMeasure
          ≤ g.mahlerMeasure * (r.map (Int.castRingHom ℂ)).mahlerMeasure :=
        le_mul_of_one_le_right g.mahlerMeasure_nonneg hrOne
      _ = f.mahlerMeasure := by
        rw [← Polynomial.mahlerMeasure_mul, ← hfEq]
  have hfOne : (1 : ℝ) ≤ f.mahlerMeasure :=
    Polynomial.one_le_mahlerMeasure_of_ne_zero hp
  have hmeasurePow : g.mahlerMeasure ^ (q.natDegree - 1) ≤
      f.mahlerMeasure ^ (p.natDegree - 1) := by
    calc
      g.mahlerMeasure ^ (q.natDegree - 1)
          ≤ f.mahlerMeasure ^ (q.natDegree - 1) :=
        pow_le_pow_left₀ g.mahlerMeasure_nonneg hmeasure _
      _ ≤ f.mahlerMeasure ^ (p.natDegree - 1) :=
        pow_le_pow_right₀ hfOne (by omega)
  calc
    (1 : ℝ) ≤ Real.sqrt q.natDegree ^ (q.natDegree + 2) *
        g.mahlerMeasure ^ (q.natDegree - 1) * ‖z₁ - z₂‖ := hshared
    _ ≤ Real.sqrt p.natDegree ^ (p.natDegree + 2) *
        f.mahlerMeasure ^ (p.natDegree - 1) * ‖z₁ - z₂‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul hdegreeFactor hmeasurePow
        (pow_nonneg g.mahlerMeasure_nonneg _)
        (pow_nonneg (Real.sqrt_nonneg _) _)

end

end HexPolyZMathlib
