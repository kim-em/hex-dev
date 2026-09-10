/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Interval
public import HexNumberFieldMathlib.IntegerRoots
public section

/-! Coordinate probes are sound for the roots of their certified isolations. -/
namespace Hex.Interval
open HexRootsMathlib

/-- Both coordinate projections lie in the dyadic radius bounds. -/
theorem bounds {p : ZPoly} (a : RefinedIsolation p) :
    (Dyadic.toReal (a.1.square.re - a.1.square.radiusHi) ≤ a.root.re ∧
      a.root.re ≤ Dyadic.toReal (a.1.square.re + a.1.square.radiusHi)) ∧
    (Dyadic.toReal (a.1.square.im - a.1.square.radiusHi) ≤ a.root.im ∧
      a.root.im ≤ Dyadic.toReal (a.1.square.im + a.1.square.radiusHi)) := by
  have hd := RefinedIsolation.root_mem_closedDisc a
  change dist a.root (HexRootsMathlib.DyadicSquare.center a.1.square) ≤ HexRootsMathlib.DyadicSquare.radius a.1.square at hd
  rw [dist_eq_norm] at hd
  have hre := (Complex.abs_re_le_norm (a.root - HexRootsMathlib.DyadicSquare.center a.1.square)).trans
    (hd.trans (DyadicSquare.radius_lt_radiusHi _).le)
  have him := (Complex.abs_im_le_norm (a.root - HexRootsMathlib.DyadicSquare.center a.1.square)).trans
    (hd.trans (DyadicSquare.radius_lt_radiusHi _).le)
  simp only [Complex.sub_re, Complex.sub_im, DyadicSquare.center_eq,
    Hex.DyadicSquare.center, GaussDyadic.toComplex] at hre him
  simp only [Dyadic.toReal_sub, Dyadic.toReal_add]
  obtain ⟨hrl, hru⟩ := abs_le.mp hre
  obtain ⟨hil, hiu⟩ := abs_le.mp him
  constructor <;> constructor <;> linarith

/-- A disjoint real interval comparison agrees with comparison of the real values. -/
theorem realOrder?_sound {p q : ZPoly} (a : RefinedIsolation p) (b : RefinedIsolation q)
    {o : Ordering} (h : realOrder? a.1.square b.1.square = some o) :
    compare a.root.re b.root.re = o := by
  have ha := bounds a
  have hb := bounds b
  unfold realOrder? at h
  split at h
  · rename_i hlt
    have : a.root.re < b.root.re := lt_of_le_of_lt ha.1.2
      ((Dyadic.toReal_lt_toReal_iff.mpr hlt).trans_le hb.1.1)
    exact (compare_lt_iff_lt.mpr this).trans (Option.some.inj h)
  · split at h
    · rename_i hgt
      have : b.root.re < a.root.re := lt_of_le_of_lt hb.1.2
        ((Dyadic.toReal_lt_toReal_iff.mpr hgt).trans_le ha.1.1)
      exact (compare_gt_iff_gt.mpr this).trans (Option.some.inj h)
    · contradiction

/-- Separated imaginary intervals cannot have equal imaginary coordinates. -/
theorem imagApart_sound {p q : ZPoly} (a : RefinedIsolation p) (b : RefinedIsolation q)
    (h : imagApart a.1.square b.1.square = true) : a.root.im ≠ b.root.im := by
  have ha := (bounds a).2
  have hb := (bounds b).2
  simp only [imagApart, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact ne_of_lt (ha.2.trans_lt ((Dyadic.toReal_lt_toReal_iff.mpr h).trans_le hb.1))
  · exact ne_of_gt (hb.2.trans_lt ((Dyadic.toReal_lt_toReal_iff.mpr h).trans_le ha.1))

/-- A strict-order rejection is sound. -/
theorem notLt_sound {p q : ZPoly} (a : RefinedIsolation p) (b : RefinedIsolation q)
    (h : notLt a.1.square b.1.square = true) : ¬ a.root.re < b.root.re := by
  have ha := (bounds a).1
  have hb := (bounds b).1
  simp only [notLt, decide_eq_true_eq] at h
  exact not_lt_of_ge (hb.2.trans ((Dyadic.toReal_le_toReal_iff.mpr h).trans ha.1))

/-- A non-strict-order rejection is sound. -/
theorem notLe_sound {p q : ZPoly} (a : RefinedIsolation p) (b : RefinedIsolation q)
    (h : notLe a.1.square b.1.square = true) : ¬ a.root.re ≤ b.root.re := by
  have ha := (bounds a).1
  have hb := (bounds b).1
  simp only [notLe, decide_eq_true_eq] at h
  exact not_le_of_gt (hb.2.trans_lt ((Dyadic.toReal_lt_toReal_iff.mpr h).trans_le ha.1))

/-- Threaded refinement preserves any sound coordinate probe. -/
theorem search_sound {α : Type} (probe : DyadicSquare → DyadicSquare → Option α)
    (R : ℂ → ℂ → α → Prop)
    (sound : ∀ {p q : ZPoly} (a : RefinedIsolation p) (b : RefinedIsolation q) v,
      probe a.1.square b.1.square = some v → R a.root b.root v)
    {p q : ZPoly} (targets : List (Int × Int)) (a : RefinedIsolation p)
    (b : RefinedIsolation q) {v : α} (h : search probe targets a b = some v) :
    R a.root b.root v := by
  induction targets generalizing a b with
  | nil =>
    cases hp : probe a.1.square b.1.square with
    | none => simp [search, hp] at h
    | some w =>
      have hw : w = v := by simpa [search, hp] using h
      subst w
      exact sound a b v hp
  | cons t ts ih =>
    rw [search] at h
    cases hp : probe a.1.square b.1.square with
    | some w =>
      have hw : w = v := by simpa [hp] using h
      subst w
      exact sound a b v hp
    | none =>
      simp only [hp] at h
      obtain ⟨ar, har, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨br, hbr, h⟩ := Option.bind_eq_some_iff.mp h
      have hout := ih ar.1 br.1 h
      have hra : ar.1.root = a.root := RefinedIsolation.refineTo_root a t.1 .nkThenPellet har
      have hrb : br.1.root = b.root := RefinedIsolation.refineTo_root b t.2 .nkThenPellet hbr
      rwa [hra, hrb] at hout

end Hex.Interval
