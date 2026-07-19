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

This module develops the Hex-independent analytic core of Mahler's
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

end

end HexPolyZMathlib
