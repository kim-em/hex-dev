/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRootsMathlib.SimpleRoot
public section

/-! Conjugation and exact half-plane tests on refined isolations. -/
namespace HexRootsMathlib
open Hex
namespace RefinedIsolation

/-- Equal dependent isolation data select equal roots. -/
theorem root_heq {p q : Hex.ZPoly} (hp : p = q)
    {r : Hex.RefinedIsolation p} {s : Hex.RefinedIsolation q} (h : HEq r s) :
    r.root = s.root := by
  cases hp
  cases eq_of_heq h
  rfl

/-- Reflecting the isolation conjugates its unique root. -/
@[simp] theorem root_conj {p : Hex.ZPoly} (a : Hex.RefinedIsolation p) :
    a.conj.root = starRingEnd ℂ a.root := by
  symm
  apply (root_spec a.conj).2.2.2
  · exact ZPoly.isRoot_conj (isRoot a)
  · have hm := root_mem_region a
    simp only [DyadicRootIsolation.region, Hex.RefinedIsolation.conj,
      Hex.AtomCertificate.isNK] at hm ⊢
    by_cases hk : a.1.witness.isNK = true
    · simp only [hk, ite_true] at hm ⊢
      exact DyadicSquare.closedSquare_conj.mpr hm
    · simp only [hk] at hm ⊢
      exact DyadicSquare.closedDisc_conj.mpr hm

/-- The imaginary part of a stored isolation's centre. -/
private theorem center_im (s : DyadicSquare) :
    (HexRootsMathlib.DyadicSquare.center s).im = Dyadic.toReal s.im := by
  simp [HexRootsMathlib.DyadicSquare.center_eq, Hex.DyadicSquare.center]

/-- The reality test is exact at the stored separation precision. -/
theorem meetsRealAxis_iff {p : Hex.ZPoly} (a : Hex.RefinedIsolation p) :
    a.1.square.meetsRealAxis = true ↔ a.root.im = 0 := by
  have hpne : p ≠ 0 := RefinedIsolation.poly_ne_zero a
  set s := a.1.square with hs
  have hmem : a.root ∈ DyadicSquare.closedDisc s :=
    RefinedIsolation.root_mem_closedDisc a
  have hdist : dist a.root (HexRootsMathlib.DyadicSquare.center s) ≤
      DyadicSquare.radius s := by
    simpa only [DyadicSquare.closedDisc, Metric.mem_closedBall] using hmem
  have hradiusHi : DyadicSquare.radius s < Dyadic.toReal s.radiusHi := by
    rw [DyadicSquare.radius_eq, DyadicSquare.radiusHi_eq, DyadicSquare.halfWidth_eq]
    exact mul_lt_mul_of_pos_left sqrt_two_lt_sqrt2Hi (zpow_pos (by norm_num) _)
  have himDist : |a.root.im - Dyadic.toReal s.im| ≤ DyadicSquare.radius s := by
    have h := Complex.abs_im_le_norm (a.root - HexRootsMathlib.DyadicSquare.center s)
    rw [Complex.sub_im, center_im] at h
    rw [dist_eq_norm] at hdist
    exact h.trans hdist
  have hHiSep : Dyadic.toReal s.radiusHi ≤
      (2 : ℝ) ^ (-(mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ) := by
    rw [DyadicSquare.radiusHi_eq, DyadicSquare.halfWidth_eq]
    have hsqrt : Dyadic.toReal Hex.sqrt2Hi = (1449 / 1024 : ℝ) := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    rw [hsqrt]
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hprop := a.property
    rw [← hs] at hprop
    omega
  unfold Hex.DyadicSquare.meetsRealAxis
  simp only [Bool.and_eq_true, decide_eq_true_eq, ← Dyadic.toReal_le_toReal_iff,
    Dyadic.toReal_neg]
  constructor
  · rintro ⟨hlo, hhi⟩
    by_contra hne
    have hconj := ZPoly.isRoot_conj (RefinedIsolation.isRoot a)
    have hne' : a.root ≠ starRingEnd ℂ a.root := by
      intro h
      exact hne (Complex.conj_eq_iff_im.mp h.symm)
    have hsep := mahlerPrec_separates p hpne a.root (starRingEnd ℂ a.root)
      (RefinedIsolation.isRoot a) hconj hne'
    rw [Complex.sub_conj, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_mul, abs_two] at hsep
    have himLarge : 2 * Dyadic.toReal s.radiusHi < |a.root.im| := by
      linarith
    have hcenter : |Dyadic.toReal s.im| ≤ Dyadic.toReal s.radiusHi := abs_le.mpr ⟨hlo, hhi⟩
    have htri := abs_sub_abs_le_abs_sub a.root.im (Dyadic.toReal s.im)
    linarith
  · intro him
    have : |Dyadic.toReal s.im| ≤ DyadicSquare.radius s := by
      simpa [him] using himDist
    exact abs_le.mp (this.trans hradiusHi.le)

/-- The stored upper-half-plane test is exact. -/
theorem upper_iff {p : Hex.ZPoly} (a : Hex.RefinedIsolation p) :
    a.1.square.radiusHi < a.1.square.im ↔ 0 < a.root.im := by
  have hdist := root_mem_closedDisc a
  change dist a.root (DyadicSquare.center a.1.square) ≤
    DyadicSquare.radius a.1.square at hdist
  have hbound := Complex.abs_im_le_norm (a.root - DyadicSquare.center a.1.square)
  rw [Complex.sub_im, center_im] at hbound
  rw [dist_eq_norm] at hdist
  have hhi : DyadicSquare.radius a.1.square < Dyadic.toReal a.1.square.radiusHi := by
    rw [DyadicSquare.radius_eq, DyadicSquare.radiusHi_eq, DyadicSquare.halfWidth_eq]
    exact mul_lt_mul_of_pos_left sqrt_two_lt_sqrt2Hi (zpow_pos (by norm_num) _)
  have hgap := abs_lt.mp (lt_of_le_of_lt (hbound.trans hdist) hhi)
  rw [← Dyadic.toReal_lt_toReal_iff]
  constructor
  · intro h
    linarith
  · intro h
    by_contra hn
    have hreal : a.1.square.meetsRealAxis = true := by
      simp only [Hex.DyadicSquare.meetsRealAxis, Bool.and_eq_true, decide_eq_true_eq,
        ← Dyadic.toReal_le_toReal_iff, Dyadic.toReal_neg]
      constructor <;> linarith
    have := (meetsRealAxis_iff a).mp hreal
    linarith


end RefinedIsolation
end HexRootsMathlib
