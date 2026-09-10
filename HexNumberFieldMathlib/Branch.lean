/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Radical
public import HexNumberFieldMathlib.RootSelection
public import HexNumberFieldMathlib.PrincipalRoot
public import HexNumberFieldMathlib.Order
public section

/-! The principal half circle and soundness of lazy radical branch selection. -/
namespace Hex.AlgebraicNumber.Radical
open Complex Real HexNumberFieldMathlib

/-- The exact side of the principal radical for a nonzero input and index at least two. -/
theorem principalSide_value (a : AlgebraicNumber) {n : Nat} (hn : 1 < n)
    (ha : a.toComplex ≠ 0) :
    (if (a.toComplex ^ ((n : ℂ)⁻¹)).im = 0 then RootSide.real
      else if 0 < (a.toComplex ^ ((n : ℂ)⁻¹)).im then .upper else .lower) = principalSide a := by
  let v := a.toComplex ^ ((n : ℂ)⁻¹)
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlarge : (1 : ℝ) < n := by exact_mod_cast hn
  have hv0 : v ≠ 0 := by
    intro hv
    apply ha
    rw [← Complex.cpow_nat_inv_pow a.toComplex hn0]
    change v ^ n = 0
    rw [hv, zero_pow hn0]
  have harg : v.arg = a.toComplex.arg / n := PrincipalRoot.arg_root ha hn0
  have hpi : v.arg < π := by
    rw [harg]
    exact (div_le_div_of_nonneg_right (arg_le_pi _) hnpos.le).trans_lt
      (div_lt_self pi_pos hnlarge)
  have hs := a.isolation.sign
  change match a.side with
    | .real => a.toComplex.im = 0
    | .upper => 0 < a.toComplex.im
    | .lower => a.toComplex.im < 0 at hs
  change (if v.im = 0 then RootSide.real else if 0 < v.im then .upper else .lower) = _
  unfold principalSide
  cases hside : a.side with
  | real =>
    simp only [hside] at hs ⊢
    have har : a.isReal = true := (isReal_iff a).mpr hs
    have hzr : (0 : AlgebraicNumber).isReal = true := (isReal_iff _).mpr (by simp)
    rw [realCompare_eq a 0 har hzr, zero_toComplex]
    simp only [Complex.zero_re, beq_iff_eq, compare_lt_iff_lt]
    by_cases hr : a.toComplex.re < 0
    · have hav := arg_eq_pi_iff.mpr ⟨hr, hs⟩
      have him : 0 < v.im := PrincipalRoot.im_pos hv0
        (by rw [harg, hav]; exact div_pos pi_pos hnpos) hpi
      simp [hr, him, ne_of_gt him]
    · have hav := arg_eq_zero_iff.mpr ⟨le_of_not_gt hr, hs⟩
      have hvarg : v.arg = 0 := by rw [harg, hav, zero_div]
      have him := (arg_eq_zero_iff.mp hvarg).2
      simp [hr, him]
  | upper =>
    simp only [hside] at hs ⊢
    have han : 0 ≤ a.toComplex.arg := arg_nonneg_iff.mpr hs.le
    have hane : a.toComplex.arg ≠ 0 := fun h => (ne_of_gt hs) (arg_eq_zero_iff.mp h).2
    have hap : 0 < a.toComplex.arg := lt_of_le_of_ne han (Ne.symm hane)
    have him : 0 < v.im := PrincipalRoot.im_pos hv0 (by rw [harg]; exact div_pos hap hnpos) hpi
    simp [him, ne_of_gt him]
  | lower =>
    simp only [hside] at hs ⊢
    have hav : v.arg < 0 := by rw [harg]; exact div_neg_of_neg_of_pos (arg_neg_iff.mpr hs) hnpos
    have him := arg_neg_iff.mp hav
    simp [ne_of_lt him, not_lt_of_ge him.le]

/-- A successful lazy branch selection is the principal root of the input. -/
theorem fast?_sound (a : AlgebraicNumber) {n : Nat} (hn : 1 < n) (ha : a.toComplex ≠ 0)
    (roots : Array RootCount)
    (hroots : ∀ r ∈ roots.toList, r.root.toComplex ^ n = a.toComplex)
    (hprincipal : ∃ r ∈ roots.toList, r.root.toComplex = a.toComplex ^ ((n : ℂ)⁻¹))
    {out : AlgebraicRoot} (h : fast? a roots = some out) :
    out.toComplex = a.toComplex ^ ((n : ℂ)⁻¹) := by
  let rs := (roots.toList.map RootCount.root).filter (fun r => decide (r.side = principalSide a))
  obtain ⟨hm, hmax⟩ := RootSelection.select?_spec rs h
  obtain ⟨w, hw, hwout⟩ := List.mem_map.mp hm
  obtain ⟨hwroots, hwside⟩ := List.mem_filter.mp hw
  have hwside' : w.side = principalSide a := of_decide_eq_true hwside
  obtain ⟨r, hr, hrw⟩ := List.mem_map.mp hwroots
  obtain ⟨p, hp, hpv⟩ := hprincipal
  have hpside : p.root.side = principalSide a := by
    rw [AlgebraicRoot.side_value, hpv]
    exact principalSide_value a hn ha
  have hpmem : p.root ∈ rs := List.mem_filter.mpr
    ⟨List.mem_map.mpr ⟨p, hp, rfl⟩, decide_eq_true hpside⟩
  have hre := hmax p.root.toComplex (List.mem_map.mpr ⟨p.root, hpmem, rfl⟩)
  rw [hpv] at hre
  refine PrincipalRoot.eq_of_re (by omega : n ≠ 0) ?_ hre ?_
  · rw [← hwout, ← hrw]
    exact hroots r hr
  · intro _ hvim
    have hpnonneg : p.root.side ≠ .lower :=
      (AlgebraicRoot.side_nonneg p.root).mpr (by rwa [hpv])
    have hwnonneg : 0 ≤ w.toComplex.im := (AlgebraicRoot.side_nonneg w).mp
      (by rwa [hwside', ← hpside])
    rwa [hwout] at hwnonneg

end Hex.AlgebraicNumber.Radical
