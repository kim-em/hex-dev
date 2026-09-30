/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseAlgebraicity

public section

namespace Hex.RealClosure

open Polynomial Finset

/-- An ordered-field root is bounded by its coefficients without assuming an
Archimedean field or a real-valued norm. -/
private theorem root_lt_bound {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (p : Polynomial F) (hp : p ≠ 0) (x : F) (hx : 0 ≤ x)
    (hr : p.eval x = 0) :
    x < (∑ i ∈ range p.natDegree, |p.coeff i|) / |p.leadingCoeff| + 1 := by
  let d := p.natDegree
  let s : F := ∑ i ∈ range d, |p.coeff i|
  have hd : 0 < d := by
    exact natDegree_pos_iff_degree_pos.mpr
      (degree_pos_of_root hp (by simpa [IsRoot] using hr))
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hleadpos : 0 < |p.leadingCoeff| := abs_pos.mpr hlead
  have hs : 0 ≤ s := sum_nonneg fun i hi => abs_nonneg _
  by_cases hsmall : x < 1
  · have hdiv : 0 ≤ s / |p.leadingCoeff| := div_nonneg hs hleadpos.le
    exact lt_of_lt_of_le hsmall (by linarith)
  have hxone : 1 ≤ x := le_of_not_gt hsmall
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxone
  have hroot :
      (∑ i ∈ range d, p.coeff i * x ^ i) + p.leadingCoeff * x ^ d = 0 := by
    simpa only [d, eval_eq_sum_range, sum_range_succ, coeff_natDegree] using hr
  have hsum :
      |p.leadingCoeff| * x ^ d ≤ s * x ^ (d - 1) := by
    have hpow (i : ℕ) (hi : i ∈ range d) : x ^ i ≤ x ^ (d - 1) :=
      pow_le_pow_right₀ hxone (Nat.le_pred_of_lt (mem_range.mp hi))
    have hterms :
        (∑ i ∈ range d, |p.coeff i * x ^ i|) ≤ s * x ^ (d - 1) := by
      calc
        _ = ∑ i ∈ range d, |p.coeff i| * x ^ i := by
          apply sum_congr rfl
          intro i hi
          rw [abs_mul, abs_of_nonneg (pow_nonneg hx i)]
        _ ≤ ∑ i ∈ range d, |p.coeff i| * x ^ (d - 1) := by
          apply sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hpow i hi) (abs_nonneg _)
        _ = s * x ^ (d - 1) := by rw [sum_mul]
    have habs := abs_sum_le_sum_abs (fun i => p.coeff i * x ^ i) (range d)
    have heq : |p.leadingCoeff| * x ^ d =
        |∑ i ∈ range d, p.coeff i * x ^ i| := by
      have hneg : p.leadingCoeff * x ^ d =
          -(∑ i ∈ range d, p.coeff i * x ^ i) := eq_neg_of_add_eq_zero_right hroot
      calc
        |p.leadingCoeff| * x ^ d = |p.leadingCoeff * x ^ d| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hx d)]
        _ = |∑ i ∈ range d, p.coeff i * x ^ i| := by rw [hneg, abs_neg]
    rw [heq]
    exact habs.trans hterms
  have hmul : |p.leadingCoeff| * x ≤ s := by
    have hpowpos : 0 < x ^ (d - 1) := pow_pos hxpos _
    apply le_of_mul_le_mul_right ?_ hpowpos
    have hpow_eq : x ^ d = x ^ (d - 1) * x := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hd]
      rw [pow_succ]
      congr 1
    calc
      (|p.leadingCoeff| * x) * x ^ (d - 1) =
          |p.leadingCoeff| * (x ^ (d - 1) * x) := by ring
      _ = |p.leadingCoeff| * x ^ d := by rw [hpow_eq]
      _ ≤ s * x ^ (d - 1) := hsum
  have hbound : x ≤ s / |p.leadingCoeff| :=
    (le_div_iff₀ hleadpos).mpr (by simpa [mul_comm] using hmul)
  exact lt_of_le_of_lt hbound (lt_add_one _)

/-- An element algebraic over an ordered base is below some base element. -/
theorem exists_base_upper {B R : Type*} [Field B] [LinearOrder B]
    [IsStrictOrderedRing B] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (f : B →+* R) (ordered : StrictMono f)
    (x : R) (hx : 0 ≤ x)
    (algebraic : letI : Algebra B R := f.toAlgebra; IsAlgebraic B x) :
    ∃ b : B, x < f b := by
  letI : Algebra B R := f.toAlgebra
  obtain ⟨p, hp, hroot⟩ := algebraic
  have hmap : p.map f ≠ 0 :=
    (Polynomial.map_ne_zero_iff ordered.injective).mpr hp
  have hrootMap : (p.map f).eval x = 0 := by
    change (p.map (algebraMap B R)).eval x = 0
    rw [Polynomial.eval_map_algebraMap]
    exact hroot
  have hnonneg (a : B) (ha : 0 ≤ a) : 0 ≤ f a := by
    simpa only [f.map_zero] using ordered.monotone ha
  have habs (a : B) : f |a| = |f a| := by
    rcases le_total 0 a with ha | ha
    · rw [abs_of_nonneg ha, abs_of_nonneg (hnonneg a ha)]
    · have hfa : f a ≤ 0 := by simpa only [f.map_zero] using ordered.monotone ha
      rw [abs_of_nonpos ha, f.map_neg, abs_of_nonpos hfa]
  let b : B := (∑ i ∈ range p.natDegree, |p.coeff i|) / |p.leadingCoeff| + 1
  have hmapb : f b =
      (∑ i ∈ range (p.map f).natDegree, |(p.map f).coeff i|) /
        |(p.map f).leadingCoeff| + 1 := by
    simp only [b, map_add, map_one, map_div₀, map_sum, habs,
      Polynomial.natDegree_map, Polynomial.coeff_map, Polynomial.leadingCoeff_map]
  exact ⟨b, by rw [hmapb]; exact root_lt_bound (p.map f) hmap x hx hrootMap⟩

/-- Every positive algebraic element admits a smaller positive base element. -/
theorem exists_base_lower {B R : Type*} [Field B] [LinearOrder B]
    [IsStrictOrderedRing B] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (f : B →+* R) (ordered : StrictMono f)
    (x : R) (hx : 0 < x)
    (algebraic : letI : Algebra B R := f.toAlgebra; IsAlgebraic B x) :
    ∃ b : B, 0 < b ∧ f b < x := by
  letI : Algebra B R := f.toAlgebra
  obtain ⟨b, hb⟩ := exists_base_upper f ordered x⁻¹ (inv_nonneg.mpr hx.le)
    algebraic.inv
  have hfb : 0 < f b := (inv_pos.mpr hx).trans hb
  have hbpos : 0 < b := by
    by_contra h
    have hbnonpos : b ≤ 0 := le_of_not_gt h
    have hfbnonpos : f b ≤ 0 := by
      simpa only [f.map_zero] using ordered.monotone hbnonpos
    exact not_lt_of_ge hfbnonpos hfb
  refine ⟨b⁻¹, inv_pos.mpr hbpos, ?_⟩
  have hlt := (inv_lt_inv₀ hfb (inv_pos.mpr hx)).mpr hb
  simpa only [map_inv₀, inv_inv] using hlt

/-- Infinitesimality relative to the base extends to every positive element
of an ordered algebraic extension of that base. -/
theorem infinitesimal_lt_algebraic {B R S : Type*}
    [Field B] [LinearOrder B] [IsStrictOrderedRing B]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field S] [LinearOrder S] [IsStrictOrderedRing S]
    (f : B →+* R) (hf : StrictMono f)
    (algebraic : letI : Algebra B R := f.toAlgebra;
      ∀ x : R, IsAlgebraic B x)
    (e : R →+* S) (he : StrictMono e)
    (δ : S) (hδ : ∀ b : B, 0 < b → δ < e (f b))
    (x : R) (hx : 0 < x) : δ < e x := by
  obtain ⟨b, hbpos, hbx⟩ := exists_base_lower f hf x hx (algebraic x)
  exact (hδ b hbpos).trans (he hbx)

end Hex.RealClosure

/-- info: 'Hex.RealClosure.exists_base_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.exists_base_lower

/-- info: 'Hex.RealClosure.infinitesimal_lt_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.infinitesimal_lt_algebraic
