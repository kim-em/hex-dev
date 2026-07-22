/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexRootsMathlib.Basic
public import HexPolyZMathlib.MahlerSeparation

public section

/-!
# The Mahler separation precision

This module proves that the executable `Hex.mahlerPrec` is fine enough to
separate distinct complex roots.  The analytic input is the shared
discriminant/Vandermonde development in `HexPolyZMathlib.MahlerSeparation`;
the remaining work connects `Hex.ZPoly.coeffAbsMax` to the polynomial sup norm
and certifies the exact integer exponent computed by `Hex.mahlerPrec`.
-/

open Polynomial Finset Matrix

namespace HexRootsMathlib

noncomputable section

/-- A maximum fold over `List.range` is the corresponding finite supremum. -/
private theorem range_foldl_max_eq_sup (g : Nat → Nat) (m : Nat) :
    (List.range m).foldl (fun acc i => max acc (g i)) 0 =
      (Finset.range m).sup g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih, Finset.range_add_one, Finset.sup_insert]
    exact Nat.max_comm _ _

/-- Every coefficient is bounded by the executable coefficient maximum. -/
theorem coeff_natAbs_le_coeffAbsMax (p : Hex.ZPoly) (i : Nat) :
    (p.coeff i).natAbs ≤ p.coeffAbsMax := by
  by_cases hi : i < p.size
  · unfold Hex.ZPoly.coeffAbsMax
    rw [range_foldl_max_eq_sup]
    exact Finset.le_sup (f := fun j => (p.coeff j).natAbs) (Finset.mem_range.mpr hi)
  · rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hi)]
    exact Nat.zero_le _

/-- The sup norm of the complex cast is bounded by the executable coefficient
maximum. -/
theorem supNorm_toPolyℂ_le (p : Hex.ZPoly) :
    (toPolyℂ p).supNorm ≤ (p.coeffAbsMax : ℝ) := by
  obtain ⟨i, hi⟩ := (toPolyℂ p).exists_eq_supNorm
  rw [hi, coeff_toPolyℂ, Complex.norm_intCast]
  have habs : |(p.coeff i : ℝ)| = ((p.coeff i).natAbs : ℝ) := by
    rw [← Int.cast_abs]
    exact (Nat.cast_natAbs (α := ℝ) (p.coeff i)).symm
  rw [habs]
  exact
    (show ((p.coeff i).natAbs : ℝ) ≤ (p.coeffAbsMax : ℝ) by
      exact_mod_cast coeff_natAbs_le_coeffAbsMax p i)

/-- The exact exponent used by `mahlerPrec` dominates the analytic coefficient
factor in the Mahler separation estimate. -/
theorem mahlerFactor_le_twoPow (n A : Nat) :
    Real.sqrt n ^ (n + 2) *
        (Real.sqrt (n + 1) * (A : ℝ)) ^ (n - 1) ≤
      (2 : ℝ) ^ (((n + 2) * Hex.ceilLog2 n +
        (n - 1) * Hex.ceilLog2 (n + 1) +
        2 * (n - 1) * Hex.ceilLog2 A + 1) / 2) := by
  set T := (n + 2) * Hex.ceilLog2 n +
    (n - 1) * Hex.ceilLog2 (n + 1) +
    2 * (n - 1) * Hex.ceilLog2 A with hT
  set E := (T + 1) / 2 with hE
  have hn : (n : ℝ) ≤ 2 ^ Hex.ceilLog2 n := by
    exact_mod_cast le_two_pow_ceilLog2 n
  have hn1 : ((n + 1 : Nat) : ℝ) ≤ 2 ^ Hex.ceilLog2 (n + 1) := by
    exact_mod_cast le_two_pow_ceilLog2 (n + 1)
  have hA : (A : ℝ) ≤ 2 ^ Hex.ceilLog2 A := by
    exact_mod_cast le_two_pow_ceilLog2 A
  have hbase : (n : ℝ) ^ (n + 2) *
        ((n + 1 : Nat) : ℝ) ^ (n - 1) * (A : ℝ) ^ (2 * (n - 1)) ≤
      (2 : ℝ) ^ T := by
    calc
      (n : ℝ) ^ (n + 2) * ((n + 1 : Nat) : ℝ) ^ (n - 1) *
          (A : ℝ) ^ (2 * (n - 1))
          ≤ ((2 : ℝ) ^ Hex.ceilLog2 n) ^ (n + 2) *
              ((2 : ℝ) ^ Hex.ceilLog2 (n + 1)) ^ (n - 1) *
              ((2 : ℝ) ^ Hex.ceilLog2 A) ^ (2 * (n - 1)) := by
            gcongr
      _ = (2 : ℝ) ^ T := by
            simp only [← pow_mul, ← pow_add]
            congr 1
            simp only [hT]
            ring
  have hTle : T ≤ E * 2 := by omega
  have hpow : (2 : ℝ) ^ T ≤ (2 : ℝ) ^ (E * 2) := by
    exact pow_le_pow_right₀ (by norm_num) hTle
  have hsqrtn : (Real.sqrt n ^ (n + 2)) ^ 2 = (n : ℝ) ^ (n + 2) := by
    rw [← pow_mul, show (n + 2) * 2 = 2 * (n + 2) by omega, pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg n)]
  have hsecond :
      ((Real.sqrt (n + 1) * (A : ℝ)) ^ (n - 1)) ^ 2 =
        ((n + 1 : Nat) : ℝ) ^ (n - 1) * (A : ℝ) ^ (2 * (n - 1)) := by
    rw [← pow_mul, show (n - 1) * 2 = 2 * (n - 1) by omega, pow_mul,
      mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1), mul_pow, ← pow_mul]
    norm_num
  have hsquare :
      (Real.sqrt n ^ (n + 2) *
          (Real.sqrt (n + 1) * (A : ℝ)) ^ (n - 1)) ^ 2 =
        (n : ℝ) ^ (n + 2) * ((n + 1 : Nat) : ℝ) ^ (n - 1) *
          (A : ℝ) ^ (2 * (n - 1)) := by
    rw [mul_pow, hsqrtn, hsecond]
    ring
  have hsq :
      (Real.sqrt n ^ (n + 2) *
          (Real.sqrt (n + 1) * (A : ℝ)) ^ (n - 1)) ^ 2 ≤
        ((2 : ℝ) ^ E) ^ 2 := by
    rw [hsquare, ← pow_mul]
    exact hbase.trans hpow
  have hleft : 0 ≤ Real.sqrt n ^ (n + 2) *
      (Real.sqrt (n + 1) * (A : ℝ)) ^ (n - 1) := by positivity
  have hright : 0 ≤ (2 : ℝ) ^ E := by positivity
  simpa only [hT, hE] using (sq_le_sq₀ hleft hright).mp hsq

/-- The executable `mahlerPrec` separates any two distinct complex roots of a
polynomial whose rational cast is separable.  The left side is the rational
upper bound on the circumscribed-disc radius used by `HexRoots`. -/
theorem mahlerPrec_separates (p : Hex.ZPoly)
    (hsep : ((HexPolyZMathlib.toPolynomial p).map (Int.castRingHom ℚ)).Separable) :
    ∀ z₁ z₂ : ℂ, (toPolyℂ p).IsRoot z₁ → (toPolyℂ p).IsRoot z₂ → z₁ ≠ z₂ →
      (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ) <
        ‖z₁ - z₂‖ / 4 := by
  intro z₁ z₂ hr1 hr2 hne
  classical
  set p' := HexPolyZMathlib.toPolynomial p with hp'
  set f := toPolyℂ p with hf
  have hfmap : f = p'.map (Int.castRingHom ℂ) := rfl
  have hp'0 : p' ≠ 0 := fun h => hsep.ne_zero (by rw [h, Polynomial.map_zero])
  have hf0 : f ≠ 0 := by
    rw [hfmap, ne_eq, Polynomial.map_eq_zero_iff (RingHom.injective_int _)]
    exact hp'0
  have hsplit : f.Splits := IsAlgClosed.splits f
  set roots := f.roots.toList with hrootsList
  have hz1List : z₁ ∈ roots := by
    rw [hrootsList, ← Multiset.mem_coe, Multiset.coe_toList]
    exact (mem_roots hf0).mpr hr1
  have hz2List : z₂ ∈ roots := by
    rw [hrootsList, ← Multiset.mem_coe, Multiset.coe_toList]
    exact (mem_roots hf0).mpr hr2
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.mp hz1List
  obtain ⟨i₁, hi₁⟩ := List.mem_iff_get.mp hz2List
  have hii : i₀ ≠ i₁ := fun h => hne (by rw [← hi₀, ← hi₁, h])
  have hcard : Multiset.card f.roots = f.natDegree := splits_iff_card_roots.mp hsplit
  have hlen : roots.length = f.natDegree := by
    rw [hrootsList, Multiset.length_toList, hcard]
  have hnatf : f.natDegree = roots.length := hlen.symm
  have hN2 : 2 ≤ roots.length := by
    have h0 := i₀.isLt
    have h1 := i₁.isLt
    have : i₀.val ≠ i₁.val := fun h => hii (Fin.ext h)
    omega
  have hnatp' : p'.natDegree = f.natDegree := by
    rw [hfmap]
    exact (Polynomial.natDegree_map_eq_of_injective
      (RingHom.injective_int _) p').symm
  have hML : f.mahlerMeasure ≤
      Real.sqrt (roots.length + 1) * (p.coeffAbsMax : ℝ) := by
    calc
      f.mahlerMeasure ≤ Real.sqrt (f.natDegree + 1) * f.supNorm :=
        Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm f
      _ ≤ Real.sqrt (roots.length + 1) * (p.coeffAbsMax : ℝ) := by
        rw [hnatf]
        exact mul_le_mul_of_nonneg_left (by
          simpa only [hf] using supNorm_toPolyℂ_le p) (Real.sqrt_nonneg _)
  have hMLpow :
      f.mahlerMeasure ^ (roots.length - 1) ≤
        (Real.sqrt (roots.length + 1) * (p.coeffAbsMax : ℝ)) ^
          (roots.length - 1) :=
    pow_le_pow_left₀ (Polynomial.mahlerMeasure_nonneg _) hML
      (roots.length - 1)
  have hbig : (1 : ℝ) ≤ Real.sqrt roots.length ^ (roots.length + 2) *
      (Real.sqrt (roots.length + 1) * (p.coeffAbsMax : ℝ)) ^
        (roots.length - 1) * ‖z₁ - z₂‖ := by
    have hshared := HexPolyZMathlib.one_le_mahlerDist
      p' hsep (by simpa only [hfmap] using hr1)
        (by simpa only [hfmap] using hr2) hne
    rw [hnatp', hnatf] at hshared
    calc
      (1 : ℝ) ≤ Real.sqrt roots.length ^ (roots.length + 2) *
            f.mahlerMeasure ^ (roots.length - 1) * ‖z₁ - z₂‖ := hshared
      _ ≤ Real.sqrt roots.length ^ (roots.length + 2) *
            (Real.sqrt (roots.length + 1) * (p.coeffAbsMax : ℝ)) ^
              (roots.length - 1) * ‖z₁ - z₂‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hMLpow (by positivity)
  have hx0 : (0 : ℝ) < ‖z₁ - z₂‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hdeg? : p.degree? = some roots.length := by
    have h := natDegree_toPolyℂ p
    rw [show (toPolyℂ p).natDegree = roots.length from hnatf] at h
    cases hd : p.degree? with
    | none =>
        exfalso
        rw [hd] at h
        simp only [Option.getD_none] at h
        omega
    | some k =>
        rw [hd] at h
        simp only [Option.getD_some] at h
        rw [h]
  set T := (roots.length + 2) * Hex.ceilLog2 roots.length +
    (roots.length - 1) * Hex.ceilLog2 (roots.length + 1) +
    2 * (roots.length - 1) * Hex.ceilLog2 p.coeffAbsMax with hT
  set E := (T + 1) / 2 with hE
  have hfactor : Real.sqrt roots.length ^ (roots.length + 2) *
      (Real.sqrt (roots.length + 1) * (p.coeffAbsMax : ℝ)) ^
        (roots.length - 1) ≤ (2 : ℝ) ^ E := by
    simpa only [hT, hE] using mahlerFactor_le_twoPow roots.length p.coeffAbsMax
  have hEx : (1 : ℝ) ≤ (2 : ℝ) ^ E * ‖z₁ - z₂‖ := by
    calc
      (1 : ℝ) ≤ Real.sqrt roots.length ^ (roots.length + 2) *
          (Real.sqrt (roots.length + 1) * (p.coeffAbsMax : ℝ)) ^
            (roots.length - 1) * ‖z₁ - z₂‖ := hbig
      _ ≤ (2 : ℝ) ^ E * ‖z₁ - z₂‖ :=
        mul_le_mul_of_nonneg_right hfactor (le_of_lt hx0)
  have hmp : Hex.mahlerPrec p = 3 + E := by
    simp only [Hex.mahlerPrec, hdeg?, Option.getD_some]
    rw [show (roots.length + 2) * Hex.ceilLog2 roots.length +
        (roots.length - 1) * Hex.ceilLog2 (roots.length + 1) +
        2 * (roots.length - 1) * Hex.ceilLog2 p.coeffAbsMax = T from hT.symm,
      show (T + 1) / 2 = E from hE.symm]
  rw [hmp]
  have h2E : (0 : ℝ) < (2 : ℝ) ^ E := by positivity
  have hExp : (-(((3 + E : ℕ)) : ℤ)) = -(E : ℤ) - 3 := by
    push_cast
    ring
  rw [hExp]
  have hzpow : (2 : ℝ) ^ (-(E : ℤ) - 3) = ((2 : ℝ) ^ E)⁻¹ / 8 := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), _root_.zpow_neg, zpow_natCast]
    norm_num
  rw [hzpow]
  have hinv : ((2 : ℝ) ^ E)⁻¹ ≤ ‖z₁ - z₂‖ := by
    rw [inv_eq_one_div, div_le_iff₀ h2E, mul_comm]
    exact hEx
  have hinv0 : (0 : ℝ) < ((2 : ℝ) ^ E)⁻¹ := by positivity
  have hconst : (1449 / 1024 : ℝ) < 2 := by norm_num
  calc
    ((2 : ℝ) ^ E)⁻¹ / 8 * (1449 / 1024 : ℝ) =
        (((2 : ℝ) ^ E)⁻¹ * (1449 / 1024 : ℝ)) / 8 := by ring
    _ < (((2 : ℝ) ^ E)⁻¹ * 2) / 8 :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hconst hinv0) (by norm_num)
    _ = ((2 : ℝ) ^ E)⁻¹ / 4 := by ring
    _ ≤ ‖z₁ - z₂‖ / 4 := by linarith

end

end HexRootsMathlib
