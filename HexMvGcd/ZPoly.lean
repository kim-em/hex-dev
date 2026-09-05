/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Coeff
public import HexPolyZGcd

@[expose] public section
set_option backward.proofsInPublic true

/-!
Lawful gcd operations for the integer-polynomial kernel.
-/

namespace Hex

instance instGcdOpsZPoly : GcdOps ZPoly where
  gcd := ZPoly.gcd
  exactDiv f g := (ZPoly.divExact? f g).getD 0
  isUnit f := decide (f.size = 1 ∧ (f.coeff 0 = 1 ∨ f.coeff 0 = -1))
  normUnit f := if f = 0 ∨ 0 < f.leadingCoeff then 1 else -1

private theorem eqC_of_size_one {f : ZPoly} (hsize : f.size = 1) :
    f = DensePoly.C (f.coeff 0) := by
  apply DensePoly.ext_coeff
  intro k
  rw [DensePoly.coeff_C]
  cases k with
  | zero => rfl
  | succ k =>
      rw [DensePoly.coeff_eq_zero_of_size_le f (by omega)]
      rfl

private theorem unit_of_mul_eq_one {f g : ZPoly} (hfg : f * g = 1) :
    f.size = 1 ∧ (f.coeff 0 = 1 ∨ f.coeff 0 = -1) := by
  have hf : f ≠ 0 := by
    intro hf
    rw [hf, DensePoly.zero_mul] at hfg
    exact (by decide : (0 : ZPoly) ≠ 1) hfg
  have hg : g ≠ 0 := by
    intro hg
    rw [hg, DensePoly.mul_comm_poly f 0, DensePoly.zero_mul] at hfg
    exact (by decide : (0 : ZPoly) ≠ 1) hfg
  have hfpos : 0 < f.size := ZPoly.size_pos_of_ne_zero f hf
  have hgpos : 0 < g.size := ZPoly.size_pos_of_ne_zero g hg
  have hsize := ZPoly.mul_size_eq_top_succ_of_nonzero f g hfpos hgpos
  have honeSize : (1 : ZPoly).size = 1 := rfl
  rw [hfg, honeSize] at hsize
  have hfsize : f.size = 1 := by omega
  have hgsize : g.size = 1 := by omega
  have hfC := eqC_of_size_one hfsize
  have hgC := eqC_of_size_one hgsize
  have hcoeff := congrArg (fun p : ZPoly => p.coeff 0) hfg
  rw [hfC, hgC, ZPoly.C_mul_eq_scale,
    DensePoly.coeff_scale_semiring] at hcoeff
  rw [DensePoly.coeff_C] at hcoeff
  change f.coeff 0 * g.coeff 0 = 1 at hcoeff
  refine ⟨hfsize, ?_⟩
  by_cases hnonneg : 0 ≤ f.coeff 0
  · exact Or.inl (Int.eq_one_of_mul_eq_one_right hnonneg hcoeff)
  · right
    have hnegNonneg : 0 ≤ -f.coeff 0 := by omega
    have hnegMul : (-f.coeff 0) * (-g.coeff 0) = 1 := by
      calc
        (-f.coeff 0) * (-g.coeff 0) = f.coeff 0 * g.coeff 0 := by grind
        _ = 1 := hcoeff
    have hnegOne := Int.eq_one_of_mul_eq_one_right hnegNonneg hnegMul
    omega

private theorem normalized_gcd (f h : ZPoly) :
    ZPoly.NormalizedGcd (ZPoly.gcd f h) = true := by
  rw [ZPoly.gcd_eq_cert]
  have hc := ZPoly.gcdCert_checks f h
  unfold ZPoly.checkGcd at hc
  simp only [Bool.and_eq_true] at hc
  exact hc.1.1.2

private theorem normalize_eq_sign (f : ZPoly) :
    normalize f = ZPoly.normalizePrimitiveSign f := by
  unfold normalize ZPoly.normalizePrimitiveSign
  change f * (if f = 0 ∨ 0 < f.leadingCoeff then 1 else -1) =
    if f.leadingCoeff < 0 then DensePoly.scale (-1) f else f
  by_cases hf : f = 0
  · subst f
    simp [DensePoly.zero_mul]
  · have hlc : f.leadingCoeff ≠ 0 :=
      ZPoly.leadingCoeff_ne_zero_of_ne_zero f hf
    by_cases hpos : 0 < f.leadingCoeff
    · rw [ite_eq_left (Or.inr hpos), ite_eq_right (by omega)]
      exact DensePoly.mul_one_right_poly f
    · have hneg : f.leadingCoeff < 0 := by omega
      rw [ite_eq_right (by simp [hf, hpos]), ite_eq_left hneg]
      rw [DensePoly.mul_comm_poly]
      exact ZPoly.C_mul_eq_scale (-1) f

private theorem normalize_mul_sign (f h : ZPoly) :
    ZPoly.normalizePrimitiveSign (f * h) =
      ZPoly.normalizePrimitiveSign f * ZPoly.normalizePrimitiveSign h := by
  by_cases hf : f = 0
  · subst f
    simp [ZPoly.normalizePrimitiveSign, DensePoly.zero_mul]
  · by_cases hh : h = 0
    · subst h
      have hzero : ZPoly.normalizePrimitiveSign (0 : ZPoly) = 0 := rfl
      rw [DensePoly.mul_comm_poly f 0, DensePoly.zero_mul, hzero]
      symm
      exact (DensePoly.mul_comm_poly (ZPoly.normalizePrimitiveSign f) 0).trans
        (DensePoly.zero_mul _)
    · have hfLead := ZPoly.leadingCoeff_ne_zero_of_ne_zero f hf
      have hhLead := ZPoly.leadingCoeff_ne_zero_of_ne_zero h hh
      have hmulLead := ZPoly.leadingCoeff_mul_of_nonzero f h hf hh
      unfold ZPoly.normalizePrimitiveSign
      by_cases hfNeg : f.leadingCoeff < 0
      · by_cases hhNeg : h.leadingCoeff < 0
        · have hprodPos : 0 < (f * h).leadingCoeff := by
            rw [hmulLead]
            exact Int.mul_pos_of_neg_of_neg hfNeg hhNeg
          rw [ite_eq_right (by omega), ite_eq_left hfNeg,
            ite_eq_left hhNeg]
          symm
          calc
            DensePoly.scale (-1) f * DensePoly.scale (-1) h =
                DensePoly.scale (-1) (f * DensePoly.scale (-1) h) :=
              (DensePoly.scale_mul (-1) f (DensePoly.scale (-1) h)).symm
            _ = DensePoly.scale (-1) (DensePoly.scale (-1) (f * h)) := by
              rw [DensePoly.mul_scale (-1) f h]
            _ = DensePoly.scale ((-1 : Int) * -1) (f * h) :=
              DensePoly.scale_scale (-1) (-1) (f * h)
            _ = f * h := by
              apply DensePoly.ext_coeff
              intro k
              rw [DensePoly.coeff_scale_semiring]
              omega
        · have hhPos : 0 < h.leadingCoeff := by omega
          have hprodNeg : (f * h).leadingCoeff < 0 := by
            rw [hmulLead]
            exact Int.mul_neg_of_neg_of_pos hfNeg hhPos
          rw [ite_eq_left hprodNeg, ite_eq_left hfNeg,
            ite_eq_right hhNeg]
          exact DensePoly.scale_mul (-1) f h
      · have hfPos : 0 < f.leadingCoeff := by omega
        by_cases hhNeg : h.leadingCoeff < 0
        · have hprodNeg : (f * h).leadingCoeff < 0 := by
            rw [hmulLead]
            exact Int.mul_neg_of_pos_of_neg hfPos hhNeg
          rw [ite_eq_left hprodNeg, ite_eq_right hfNeg,
            ite_eq_left hhNeg]
          exact DensePoly.mul_scale (-1) f h
        · have hhPos : 0 < h.leadingCoeff := by omega
          have hprodPos : 0 < (f * h).leadingCoeff := by
            rw [hmulLead]
            exact Int.mul_pos hfPos hhPos
          rw [ite_eq_right (by omega), ite_eq_right hfNeg,
            ite_eq_right hhNeg]

instance instLawfulGcdOpsZPoly : LawfulGcdOps ZPoly := by
  refine {
    dvd_iff := ?_
    one_ne_zero := ?_
    no_zero_div := ?_
    gcd_dvd_left := ZPoly.gcd_dvd_left
    gcd_dvd_right := ZPoly.gcd_dvd_right
    dvd_gcd := ?_
    gcd_normalized := ?_
    exactDiv_cancel := ?_
    isUnit_iff := ?_
    normUnit_unit := ?_
    normalize_mul := ?_
    normalize_idem := ?_
    normalize_unit := ?_ }
  · intro a b
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, hq⟩
  · decide
  · intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    · by_cases hb : b = 0
      · exact Or.inr hb
      · exact False.elim (ZPoly.mul_ne_zero_of_ne_zero a b ha hb hab)
  · intro a b d hda hdb
    exact ZPoly.dvd_gcd d a b hda hdb
  · intro a b
    rw [normalize_eq_sign]
    change ZPoly.normalizePrimitiveSign (ZPoly.gcd a b) = ZPoly.gcd a b
    have hnorm := normalized_gcd a b
    unfold ZPoly.NormalizedGcd at hnorm
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hnorm
    rcases hnorm with hzero | hpos
    · rw [hzero]
      rfl
    · unfold ZPoly.normalizePrimitiveSign
      rw [ite_eq_right (by omega)]
  · intro a b hb
    change (ZPoly.divExact? (a * b) b).getD 0 = a
    have hdiv : ZPoly.divExact? (a * b) b = some a :=
      (ZPoly.divExact?_eq hb).mpr rfl
    simp [hdiv]
  · intro a
    change decide (a.size = 1 ∧ (a.coeff 0 = 1 ∨ a.coeff 0 = -1)) = true ↔
      ∃ b, a * b = 1
    rw [decide_eq_true_eq]
    constructor
    · rintro ⟨hsize, hone | hneg⟩
      · refine ⟨1, ?_⟩
        rw [eqC_of_size_one hsize, hone]
        rfl
      · refine ⟨-1, ?_⟩
        rw [eqC_of_size_one hsize, hneg]
        decide
    · rintro ⟨b, hab⟩
      exact unit_of_mul_eq_one hab
  · intro a
    change ∃ b : ZPoly,
      (if a = 0 ∨ 0 < a.leadingCoeff then 1 else -1) * b = 1
    split
    · exact ⟨1, by rfl⟩
    · exact ⟨-1, by decide⟩
  · intro a b
    rw [normalize_eq_sign, normalize_eq_sign, normalize_eq_sign]
    exact normalize_mul_sign a b
  · intro a
    rw [normalize_eq_sign, normalize_eq_sign]
    unfold ZPoly.normalizePrimitiveSign
    split
    · rename_i hneg
      have hlead : 0 < (DensePoly.scale (-1) a).leadingCoeff := by
        rw [ZPoly.leadingCoeff_scale_of_nonzero (-1) a (by decide)]
        omega
      rw [ite_eq_right (by omega)]
    · rfl
  · intro a ha
    change decide (a.size = 1 ∧ (a.coeff 0 = 1 ∨ a.coeff 0 = -1)) = true at ha
    rw [decide_eq_true_eq] at ha
    rw [normalize_eq_sign]
    rcases ha with ⟨hsize, hone | hneg⟩
    · rw [eqC_of_size_one hsize, hone]
      rfl
    · rw [eqC_of_size_one hsize, hneg]
      rfl

end Hex
