/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.NKRecertification
public import HexRootsMathlib.Completeness.PelletConverse

public section

/-!
# A quantitative Newton converse from remote roots

This module turns coefficient bounds for the normalized product of the roots
remote from one designated root into the two estimates consumed by the
executable Newton--Kantorovich witness.
-/

open Finset Polynomial

namespace HexRootsMathlib.NKData

noncomputable section

/-- The exact-centre coefficient norm is the sup-operator norm of the ratio
of the corresponding Taylor coefficient to the linear coefficient. -/
theorem exactCoeffNorm_eq (p : Hex.ZPoly) (s : Hex.DyadicSquare) (k : Nat) :
    exactCoeffNorm (toPolyℂ p) k (centerSup s) =
      ‖NewtonKantorovich.ComplexSup.mul
        ((((toPolyℂ p).comp (X + C (DyadicSquare.center s))).coeff 1)⁻¹ *
          ((toPolyℂ p).comp (X + C (DyadicSquare.center s))).coeff k)‖ := by
  unfold exactCoeffNorm centerSup
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff_one,
    Polynomial.taylor_coeff]

/-- A translated polynomial with one designated root is a nonzero scalar
times its near-root linear factor and the normalized remote-root product. -/
theorem translated_eq_factor {p : ℂ[X]} {c z : ℂ} {roots : Multiset ℂ}
    (hp : p ≠ 0) (hroots : p.roots = z ::ₘ roots)
    (hremote : ∀ w ∈ roots, w ≠ c) :
    ∃ K : ℂ, K ≠ 0 ∧
      p.comp (X + C c) = C K *
        ((X - C (z - c)) *
          remotePoly ((roots.map fun w => w - c).map Inv.inv)) := by
  let q := p.comp (X + C c)
  let t := roots.map fun w => w - c
  let a := z - c
  let g := remotePoly (t.map Inv.inv)
  let K := q.leadingCoeff * (t.map Neg.neg).prod
  have hq : q ≠ 0 := (comp_X_add_C_ne_zero_iff (p := p) (t := c)).mpr hp
  have hqroots : q.roots = a ::ₘ t := by
    have htranslate : q.roots = p.roots.map fun w => w - c := by
      dsimp [q]
      convert roots_comp_C_mul_X_add_C p 1 c isUnit_one using 1 <;> simp
    rw [htranslate, hroots]
    simp [a, t]
  have ht0 : ∀ w ∈ t, w ≠ 0 := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
    simpa using sub_ne_zero.mpr (hremote u hu)
  have hnorm := normalize_root_product t ht0
  have hfactor : q = C K * ((X - C a) * g) := by
    calc
      q = C q.leadingCoeff * (q.roots.map fun w => X - C w).prod :=
        (IsAlgClosed.splits q).eq_prod_roots
      _ = C q.leadingCoeff *
          ((X - C a) * (t.map fun w => X - C w).prod) := by
        rw [hqroots]
        simp
      _ = C (q.leadingCoeff * (t.map Neg.neg).prod) *
          ((X - C a) * remotePoly (t.map Inv.inv)) := by
        rw [← hnorm, map_mul]
        ring
      _ = C K * ((X - C a) * g) := rfl
  have hK : K ≠ 0 := by
    apply mul_ne_zero (leadingCoeff_ne_zero.mpr hq)
    apply Multiset.prod_ne_zero
    intro hw
    obtain ⟨u, hu, hzero⟩ := Multiset.mem_map.mp hw
    exact (neg_ne_zero.mpr (ht0 u hu)) hzero
  exact ⟨K, hK, hfactor⟩

private theorem two_mul_index_le_pow (k : Nat) (hk : 2 ≤ k) :
    2 * k ≤ 4 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
      omega

private theorem eight_mul_index_le_pow (k : Nat) (hk : 2 ≤ k) :
    8 * k ≤ 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      omega

private theorem sum_prev_eq {M : Type*} [AddCommMonoid M]
    (f : Nat → M) (n : Nat) :
    (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then f (k - 1) else 0) =
      ∑ j ∈ (Finset.range n).erase 0, f j := by
  calc
    (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then f (k - 1) else 0) =
        ∑ k ∈ (Finset.range (n + 1)).filter (2 ≤ ·), f (k - 1) := by
      rw [Finset.sum_filter]
    _ = ∑ j ∈ (Finset.range n).erase 0, f j := by
      apply Finset.sum_bij (fun k _ => k - 1)
      · intro k hk
        rw [Finset.mem_filter] at hk
        simp only [Finset.mem_range] at hk
        simp only [Finset.mem_erase, Finset.mem_range]
        constructor
        · omega
        · have hsub : k - 1 < k := Nat.sub_lt (by omega) (by omega)
          omega
      · intro k₁ hk₁ k₂ hk₂ heq
        rw [Finset.mem_filter] at hk₁ hk₂
        simp only [Finset.mem_range] at hk₁ hk₂
        omega
      · intro j hj
        simp only [Finset.mem_erase, Finset.mem_range] at hj
        refine ⟨j + 1, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro k hk
        rfl

private theorem sum_curr_le (f : Nat → ℝ) (n : Nat)
    (hf : ∀ k, 0 ≤ f k) (hfn : f n = 0) :
    (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then f k else 0) ≤
      ∑ j ∈ (Finset.range n).erase 0, f j := by
  rw [Finset.sum_range_succ]
  simp only [hfn, ite_self, add_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  · intro k hk hnot
    exact hf k

/-- The weighted higher-coefficient mass of a near-root linear factor times
a normalized remote product is controlled by the remote product's ordinary
coefficient tail at four times the working radius. -/
theorem weighted_coeff_le {g : ℂ[X]} {a : ℂ} {n : Nat} {rho E : ℝ}
    (hrho : 0 < rho) (hdeg : g.natDegree < n)
    (htail :
      (∑ j ∈ (Finset.range n).erase 0,
        ‖g.coeff j‖ * (4 * rho) ^ j) ≤ E)
    (ha : ‖a‖ ≤ rho / 2) :
    (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then
        (k : ℝ) * ‖((X - C a) * g).coeff k‖ * rho ^ (k - 2)
      else 0) ≤ (9 / (16 * rho)) * E := by
  let prev : Nat → ℝ := fun k => ‖g.coeff (k - 1)‖ * (4 * rho) ^ (k - 1)
  let curr : Nat → ℝ := fun k => ‖g.coeff k‖ * (4 * rho) ^ k
  have hterm (k : Nat) (hk : 2 ≤ k) :
      (k : ℝ) * ‖((X - C a) * g).coeff k‖ * rho ^ (k - 2) ≤
        (1 / (2 * rho)) * prev k + (1 / (16 * rho)) * curr k := by
    have hcoeff := coeff_X_sub_C_mul (p := g) (r := a) (a := k - 1)
    rw [show k - 1 + 1 = k by omega] at hcoeff
    rw [hcoeff]
    have hk₁ : 2 * (k : ℝ) ≤ 4 ^ (k - 1) := by
      exact_mod_cast two_mul_index_le_pow k hk
    have hk₂ : 8 * (k : ℝ) ≤ 4 ^ k := by
      exact_mod_cast eight_mul_index_le_pow k hk
    have hpow₁ : rho ^ (k - 1) = rho ^ (k - 2) * rho := by
      rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
    have hpow₂ : rho ^ k = rho ^ (k - 2) * rho ^ 2 := by
      calc
        rho ^ k = rho ^ ((k - 2) + 2) := by congr 1; omega
        _ = rho ^ (k - 2) * rho ^ 2 := pow_add _ _ _
    have hprev :
        (k : ℝ) * ‖g.coeff (k - 1)‖ * rho ^ (k - 2) ≤
          (1 / (2 * rho)) * prev k := by
      dsimp [prev]
      rw [mul_pow, hpow₁]
      have hnonneg : 0 ≤ ‖g.coeff (k - 1)‖ * rho ^ (k - 2) := by positivity
      calc
        (k : ℝ) * ‖g.coeff (k - 1)‖ * rho ^ (k - 2) =
            (k : ℝ) * (‖g.coeff (k - 1)‖ * rho ^ (k - 2)) := by ring
        _ ≤ (4 ^ (k - 1) / 2) *
            (‖g.coeff (k - 1)‖ * rho ^ (k - 2)) := by
              gcongr
              nlinarith
        _ = (1 / (2 * rho)) *
            (‖g.coeff (k - 1)‖ * (4 ^ (k - 1) * (rho ^ (k - 2) * rho))) := by
              field_simp
    have hcurr :
        (k : ℝ) * ‖a‖ * ‖g.coeff k‖ * rho ^ (k - 2) ≤
          (1 / (16 * rho)) * curr k := by
      dsimp [curr]
      rw [mul_pow, hpow₂]
      have hnonneg : 0 ≤ ‖g.coeff k‖ * rho ^ (k - 2) := by positivity
      calc
        (k : ℝ) * ‖a‖ * ‖g.coeff k‖ * rho ^ (k - 2) ≤
            (k : ℝ) * (rho / 2) * ‖g.coeff k‖ * rho ^ (k - 2) := by
              gcongr
        _ ≤ (4 ^ k / 8) * (rho / 2) * ‖g.coeff k‖ *
            rho ^ (k - 2) := by gcongr; nlinarith
        _ = (1 / (16 * rho)) *
            (‖g.coeff k‖ * (4 ^ k * (rho ^ (k - 2) * rho ^ 2))) := by
              field_simp
              ring
    calc
      (k : ℝ) * ‖g.coeff (k - 1) - a * g.coeff k‖ * rho ^ (k - 2) ≤
          (k : ℝ) * (‖g.coeff (k - 1)‖ + ‖a‖ * ‖g.coeff k‖) *
            rho ^ (k - 2) := by
              gcongr
              simpa only [norm_mul] using norm_sub_le (g.coeff (k - 1)) (a * g.coeff k)
      _ = (k : ℝ) * ‖g.coeff (k - 1)‖ * rho ^ (k - 2) +
          (k : ℝ) * ‖a‖ * ‖g.coeff k‖ * rho ^ (k - 2) := by ring
      _ ≤ (1 / (2 * rho)) * prev k + (1 / (16 * rho)) * curr k :=
        add_le_add hprev hcurr
  calc
    (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then
        (k : ℝ) * ‖((X - C a) * g).coeff k‖ * rho ^ (k - 2) else 0) ≤
      ∑ k ∈ Finset.range (n + 1), if 2 ≤ k then
        ((1 / (2 * rho)) * prev k + (1 / (16 * rho)) * curr k) else 0 := by
          apply Finset.sum_le_sum
          intro k hk
          split_ifs with hk₂
          · exact hterm k hk₂
          · exact le_rfl
    _ = (1 / (2 * rho)) *
          (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then prev k else 0) +
        (1 / (16 * rho)) *
          (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then curr k else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs <;> ring
    _ ≤ (1 / (2 * rho)) * E + (1 / (16 * rho)) * E := by
      have hprevSum := sum_prev_eq
        (fun j => ‖g.coeff j‖ * (4 * rho) ^ j) n
      have hcurrSum :
          (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then curr k else 0) ≤ E := by
        apply (sum_curr_le curr n (fun k => by dsimp [curr]; positivity) ?_).trans htail
        dsimp [curr]
        rw [coeff_eq_zero_of_natDegree_lt hdeg, norm_zero, zero_mul]
      rw [show (∑ k ∈ Finset.range (n + 1), if 2 ≤ k then prev k else 0) =
          ∑ j ∈ (Finset.range n).erase 0,
            ‖g.coeff j‖ * (4 * rho) ^ j by simpa [prev] using hprevSum]
      gcongr
    _ = (9 / (16 * rho)) * E := by ring

/-- A nonzero scalar factor cancels from every exact inverse-normalized
Taylor coefficient. -/
theorem exactCoeffNorm_factor {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {K : ℂ} {h : ℂ[X]} (hK : K ≠ 0)
    (hfactor : (toPolyℂ p).comp (X + C (DyadicSquare.center s)) = C K * h)
    (hlinear : h.coeff 1 ≠ 0) (k : Nat) :
    exactCoeffNorm (toPolyℂ p) k (centerSup s) ≤
      √2 * (‖h.coeff k‖ / ‖h.coeff 1‖) := by
  rw [exactCoeffNorm_eq, hfactor]
  simp only [coeff_C_mul]
  have hcancel : (K * h.coeff 1)⁻¹ * (K * h.coeff k) =
      (h.coeff 1)⁻¹ * h.coeff k := by
    field_simp
  rw [hcancel]
  calc
    ‖NewtonKantorovich.ComplexSup.mul ((h.coeff 1)⁻¹ * h.coeff k)‖ ≤
        √2 * ‖(h.coeff 1)⁻¹ * h.coeff k‖ :=
      NewtonKantorovich.ComplexSup.norm_mul_le_sqrt_two _
    _ = √2 * (‖h.coeff k‖ / ‖h.coeff 1‖) := by
      rw [norm_mul, norm_inv, div_eq_mul_inv]
      ring

/-- A small multiplicative perturbation of the exact near-root correction
keeps its sup norm well inside the executable residual margin. -/
theorem supNorm_inverse_mul_le {a e : ℂ} {r rho : ℝ}
    (hr : 0 < r) (hrho : 0 < rho) (hrho' : rho ≤ 3 * r / 2)
    (haSup : HexRootsMathlib.supNorm a ≤ r / 2) (ha : ‖a‖ ≤ rho / 2)
    (he : ‖e‖ ≤ 1 / 256) :
    HexRootsMathlib.supNorm ((1 - e)⁻¹ * (-a)) ≤ (9 / 14 : ℝ) * r := by
  have he1 : ‖e‖ < 1 := he.trans_lt (by norm_num)
  have hden : 1 - e ≠ 0 := by
    intro hzero
    have : e = 1 := by linear_combination -hzero
    rw [this, norm_one] at he1
    exact lt_irrefl 1 he1
  let v := (1 - e)⁻¹ * (-a)
  have hv : v = -a + e * v := by
    dsimp [v]
    field_simp
    ring
  have hvnorm : ‖v‖ ≤ ‖a‖ / (1 - ‖e‖) := by
    dsimp [v]
    have hdenlower : 1 - ‖e‖ ≤ ‖1 - e‖ := by
      simpa using norm_sub_norm_le (1 : ℂ) e
    rw [norm_mul, norm_inv, norm_neg, div_eq_mul_inv, mul_comm]
    gcongr
  have hsupNorm (z : ℂ) : HexRootsMathlib.supNorm z ≤ ‖z‖ :=
    max_le (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)
  calc
    HexRootsMathlib.supNorm v = HexRootsMathlib.supNorm (-a + e * v) :=
      congrArg HexRootsMathlib.supNorm hv
    _ ≤ HexRootsMathlib.supNorm (-a) + HexRootsMathlib.supNorm (e * v) :=
      HexRootsMathlib.supNorm_add_le _ _
    _ ≤ HexRootsMathlib.supNorm a + ‖e * v‖ := by
      gcongr
      · simp [HexRootsMathlib.supNorm]
      · exact hsupNorm _
    _ = HexRootsMathlib.supNorm a + ‖e‖ * ‖v‖ := by rw [norm_mul]
    _ ≤ r / 2 + (1 / 256) * (rho / 2 / (1 - 1 / 256)) := by
      have hdenpos : 0 < 1 - ‖e‖ := sub_pos.mpr he1
      have hfrac : ‖a‖ / (1 - ‖e‖) ≤
          (rho / 2) / (1 - 1 / 256) := by
        exact div_le_div₀ (by positivity) ha (by norm_num) (by nlinarith)
      have hv' := hvnorm.trans hfrac
      gcongr
    _ ≤ (9 / 14 : ℝ) * r := by norm_num; nlinarith

/-- A simple root with a small normalized remote-root tail makes the actual
dyadic Newton--Kantorovich witness succeed. The centre hypothesis is in the
sup norm, matching the doubled enclosing-square geometry. -/
theorem witness_of_remote_roots {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {z : ℂ} {roots : Multiset ℂ} {d : ℝ}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hroots : (toPolyℂ p).roots = z ::ₘ roots) (hd : 0 < d)
    (hremote : ∀ w ∈ roots, d ≤ ‖w - DyadicSquare.center s‖)
    (hcenter : HexRootsMathlib.supNorm (z - DyadicSquare.center s) ≤
      DyadicSquare.halfWidth s / 2)
    (htailSmall :
      (1 + (4 * Dyadic.toReal s.radiusHi) / d) ^ roots.card - 1 ≤
        (1 / 32 : ℝ)) :
    Hex.nkWitness p s := by
  let c := DyadicSquare.center s
  let a := z - c
  let t := roots.map fun w => w - c
  let g := remotePoly (t.map Inv.inv)
  let h := (X - C a) * g
  let r := DyadicSquare.halfWidth s
  let rho := Dyadic.toReal s.radiusHi
  let E := (1 + (4 * rho) / d) ^ roots.card - 1
  have hr : 0 < r := by
    dsimp [r]
    rw [DyadicSquare.halfWidth_eq]
    positivity
  have hrho : 0 < rho := by
    dsimp [rho]
    rw [DyadicSquare.radiusHi_eq]
    have hsqrt2Hi : 0 < Dyadic.toReal Hex.sqrt2Hi := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    exact mul_pos hr hsqrt2Hi
  have hrhoLower : r ≤ rho := by
    dsimp [r, rho]
    exact (show DyadicSquare.halfWidth s ≤ DyadicSquare.radius s by
      rw [DyadicSquare.radius]
      have hsqrt : 1 ≤ √2 := (Real.one_le_sqrt).2 (by norm_num)
      nlinarith).trans (DyadicSquare.radius_lt_radiusHi s).le
  have hrhoUpper : rho ≤ 3 * r / 2 := by
    rw [show rho = DyadicSquare.halfWidth s * (1449 / 1024 : ℝ) by
      dsimp [rho]
      rw [DyadicSquare.radiusHi_eq]
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]]
    dsimp [r]
    nlinarith
  have ha : ‖a‖ ≤ rho / 2 := by
    have hnorm : ‖a‖ ≤ √2 * HexRootsMathlib.supNorm a :=
      Complex.norm_le_sqrt_two_mul_max a
    have hsqrt : √2 * r < rho := by
      dsimp [r, rho]
      simpa only [DyadicSquare.radius, mul_comm] using
        DyadicSquare.radius_lt_radiusHi s
    dsimp [a] at hnorm hcenter ⊢
    calc
      ‖z - c‖ ≤ √2 * (r / 2) :=
        hnorm.trans (mul_le_mul_of_nonneg_left hcenter (Real.sqrt_nonneg 2))
      _ = (√2 * r) / 2 := by ring
      _ ≤ rho / 2 := by linarith
  have hremote0 : ∀ w ∈ roots, w ≠ c := by
    intro w hw heq
    subst w
    have hpos := hd.trans_le (hremote c hw)
    simpa [c] using hpos.ne'
  obtain ⟨K, hK, hfactor⟩ := translated_eq_factor hp hroots hremote0
  change (toPolyℂ p).comp (X + C c) = C K * h at hfactor
  have hremote' : ∀ w ∈ t, d ≤ ‖w‖ := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
    exact hremote u hu
  have hgdeg : g.natDegree < roots.card + 1 := by
    dsimp [g, t]
    exact (natDegree_remotePoly_le _).trans_lt (by simp)
  have hg0 : g.coeff 0 = 1 := by
    dsimp [g]
    exact coeff_remotePoly_zero _
  have htail :
      (∑ j ∈ (Finset.range (roots.card + 1)).erase 0,
        ‖g.coeff j‖ * (4 * rho) ^ j) ≤ E := by
    dsimp [g]
    simpa [E, t] using
      remotePoly_tail_le hd (by positivity : 0 ≤ 4 * rho) hremote'
  have hE : E ≤ 1 / 32 := by simpa [E, rho] using htailSmall
  have hone : ‖g.coeff 1‖ * (4 * rho) ≤ E := by
    dsimp [g]
    simpa [E, t] using
      coeff_one_remotePoly_le hd (by positivity : 0 ≤ 4 * rho) hremote'
  have hE0 : 0 ≤ E :=
    (mul_nonneg (norm_nonneg (g.coeff 1)) (by positivity : 0 ≤ 4 * rho)).trans hone
  let e := a * g.coeff 1
  have he : ‖e‖ ≤ 1 / 256 := by
    have hg1 : ‖g.coeff 1‖ ≤ E / (4 * rho) :=
      (le_div_iff₀ (by positivity : 0 < 4 * rho)).2 hone
    calc
      ‖e‖ = ‖a‖ * ‖g.coeff 1‖ := norm_mul _ _
      _ ≤ (rho / 2) * (E / (4 * rho)) := by gcongr
      _ = E / 8 := by field_simp; ring
      _ ≤ 1 / 256 := by nlinarith
  have hh0 : h.coeff 0 = -a := by
    dsimp [h]
    simp [hg0]
  have hh1 : h.coeff 1 = 1 - e := by
    dsimp [h, e]
    rw [show 1 = 0 + 1 by omega, coeff_X_sub_C_mul, hg0]
  have hh1norm : 255 / 256 ≤ ‖h.coeff 1‖ := by
    rw [hh1]
    have := norm_sub_norm_le (1 : ℂ) e
    rw [norm_one] at this
    nlinarith
  have hh1ne : h.coeff 1 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hh1norm
    norm_num at hh1norm
  have hderiv : (toPolyℂ p).derivative.eval c ≠ 0 := by
    rw [← Polynomial.taylor_coeff_one, Polynomial.taylor_apply, hfactor,
      coeff_C_mul]
    exact mul_ne_zero hK hh1ne
  have hnorm : 0 < normSq p s := by
    apply normSq_pos
    simpa [c] using hderiv
  have hsizeEq : p.size = roots.card + 2 := by
    have hnat := natDegree_eq_of_roots hroots
    rw [natDegree_toPolyℂ] at hnat
    have hdegree : p.degree? = some (p.size - 1) := by
      simp [Hex.DensePoly.degree?, Nat.ne_of_gt (by omega : 0 < p.size)]
    rw [hdegree, Option.getD_some] at hnat
    omega
  apply witness_of_estimates p s (by rw [coeffs_size]; omega) hnorm
  · have hexact :
        NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p) c
          (NewtonKantorovich.ComplexSup.eval (toPolyℂ p) (centerSup s)) =
        NewtonKantorovich.ComplexSup.equiv ((h.coeff 1)⁻¹ * h.coeff 0) := by
      apply NewtonKantorovich.ComplexSup.equiv.symm.injective
      simp only [NewtonKantorovich.ComplexSup.inverseAt,
        NewtonKantorovich.ComplexSup.eval,
        NewtonKantorovich.ComplexSup.equiv_symm_mul,
        ContinuousLinearEquiv.symm_apply_apply, centerSup]
      change (Polynomial.eval c (toPolyℂ p).derivative)⁻¹ *
        Polynomial.eval c (toPolyℂ p) = _
      rw [← Polynomial.taylor_coeff_one, ← Polynomial.taylor_coeff_zero,
        Polynomial.taylor_apply, hfactor]
      simp only [coeff_C_mul]
      field_simp
    rw [← norm_residual]
    calc
      ‖approxInverse p s
          (NewtonKantorovich.ComplexSup.eval (toPolyℂ p) (centerSup s))‖ ≤
          ‖NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p) c
            (NewtonKantorovich.ComplexSup.eval (toPolyℂ p) (centerSup s))‖ := by
        simpa [c] using norm_approxInverse_le p s hnorm _
      _ = HexRootsMathlib.supNorm ((h.coeff 1)⁻¹ * h.coeff 0) := by
        rw [hexact]
        rw [NewtonKantorovich.ComplexSup.norm_equiv]
        rfl
      _ ≤ (9 / 14 : ℝ) * r := by
        rw [hh0, hh1]
        exact supNorm_inverse_mul_le hr hrho hrhoUpper hcenter ha he
      _ = (9 / 14 : ℝ) * DyadicSquare.halfWidth s := rfl
  · rw [z2, Dyadic.toReal_mul, Dyadic.toReal_two, toReal_z2Sum,
      coeffs_size, hsizeEq]
    have hweighted := weighted_coeff_le (g := g) (a := a) (n := roots.card + 1)
      hrho hgdeg htail ha
    have hsum :
        (∑ k ∈ Finset.range (roots.card + 2), if 2 ≤ k then
          (k : ℝ) * exactCoeffNorm (toPolyℂ p) k (centerSup s) *
            rho ^ (k - 2) else 0) ≤
          √2 * (256 / 255 : ℝ) * ((9 / (16 * rho)) * E) := by
      calc
        _ ≤ ∑ k ∈ Finset.range (roots.card + 2), if 2 ≤ k then
            (k : ℝ) * (√2 * (‖h.coeff k‖ / ‖h.coeff 1‖)) *
              rho ^ (k - 2) else 0 := by
          apply Finset.sum_le_sum
          intro k hk
          split_ifs with hk2
          · gcongr
            exact exactCoeffNorm_factor hK hfactor hh1ne k
          · exact le_rfl
        _ = √2 * (1 / ‖h.coeff 1‖) *
            (∑ k ∈ Finset.range (roots.card + 2), if 2 ≤ k then
              (k : ℝ) * ‖h.coeff k‖ * rho ^ (k - 2) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          split_ifs
          · simp [div_eq_mul_inv]
            ring
          · simp
        _ ≤ √2 * (256 / 255 : ℝ) * ((9 / (16 * rho)) * E) := by
          have hinv : 1 / ‖h.coeff 1‖ ≤ (256 / 255 : ℝ) := by
            apply (div_le_iff₀ (norm_pos_iff.mpr hh1ne)).2
            nlinarith [hh1norm]
          gcongr
    have hresidual :
        (∑ k ∈ Finset.range (roots.card + 2), if 2 ≤ k then
          (k : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi (residual p s k)) *
            rho ^ (k - 2) else 0) ≤
        (∑ k ∈ Finset.range (roots.card + 2), if 2 ≤ k then
          (k : ℝ) * exactCoeffNorm (toPolyℂ p) k (centerSup s) *
            rho ^ (k - 2) else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs with hk2
      · gcongr
        exact hi_residual_le p s hnorm k
      · exact le_rfl
    change 2 *
        (∑ k ∈ Finset.range (roots.card + 2), if 2 ≤ k then
          (k : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi (residual p s k)) *
            rho ^ (k - 2) else 0) * r < 1 / 8
    calc
      _ ≤ 2 * (√2 * (256 / 255 : ℝ) * ((9 / (16 * rho)) * E)) * r := by
        gcongr
        exact hresidual.trans hsum
      _ ≤ 2 * ((3 / 2 : ℝ) * (256 / 255) *
          ((9 / (16 * rho)) * (1 / 32))) * r := by
        have hsqrt : √2 ≤ (3 / 2 : ℝ) := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
        gcongr
      _ < 1 / 8 := by
        have hrRatio : r / rho ≤ 1 := (div_le_one hrho).2 hrhoLower
        rw [show 2 * ((3 / 2 : ℝ) * (256 / 255) *
          ((9 / (16 * rho)) * (1 / 32))) * r =
            (9 / 170 : ℝ) * (r / rho) by field_simp; ring]
        nlinarith

end


end HexRootsMathlib.NKData
