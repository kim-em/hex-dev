/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Basic
public import HexRootsMathlib.Conjugate
public section

/-! The canonical orientation agrees with the imaginary part of the root. -/
namespace Hex.AlgebraicNumber
open HexRootsMathlib

namespace OrientedIsolation

/-- The orientation records the exact sign of the imaginary part. -/
theorem sign {p : ZPoly} (r : OrientedIsolation p) :
    match r.side with
    | .real => r.rep.root.im = 0
    | .upper => 0 < r.rep.root.im
    | .lower => r.rep.root.im < 0 := by
  rcases r with ⟨base, side, valid⟩
  cases side with
  | real => exact (RefinedIsolation.meetsRealAxis_iff base).mp valid
  | upper => exact (RefinedIsolation.upper_iff base).mp valid
  | lower =>
    have h := (RefinedIsolation.upper_iff base).mp valid
    simpa [rep, RefinedIsolation.root_conj] using h

/-- The real tag characterizes real values. -/
theorem real_iff {p : ZPoly} (r : OrientedIsolation p) :
    r.side = .real ↔ r.rep.root.im = 0 := by
  have h := r.sign
  cases hs : r.side <;> simp_all <;> linarith

/-- Equal imaginary parts have the same orientation, even in different fields. -/
theorem side_eq_of_im_eq {p q : ZPoly} (r : OrientedIsolation p) (s : OrientedIsolation q)
    (h : r.rep.root.im = s.rep.root.im) : r.side = s.side := by
  have hr := r.sign
  have hs := s.sign
  cases hrside : r.side <;> cases hsside : s.side <;>
    simp_all <;> linarith

/-- Equal complex values have the same orientation. -/
theorem side_eq {p : ZPoly} (r s : OrientedIsolation p)
    (h : r.rep.root = s.rep.root) : r.side = s.side :=
  side_eq_of_im_eq r s (congrArg Complex.im h)

/-- Equal oriented values have equal base values. -/
theorem base_root_eq {p : ZPoly} (r s : OrientedIsolation p)
    (h : r.rep.root = s.rep.root) : r.base.root = s.base.root := by
  have hs := side_eq r s h
  unfold rep at h
  rw [← hs] at h
  cases hr : r.side with
  | real => simpa [hr] using h
  | upper => simpa [hr] using h
  | lower =>
    apply (starRingEnd ℂ).injective
    simpa [hr] using h

/-- Orientation and the base determine all stored data. -/
theorem ext {p : ZPoly} (r s : OrientedIsolation p)
    (hb : r.base = s.base) (hs : r.side = s.side) : r = s := by
  rcases r with ⟨rb, rs, rv⟩
  rcases s with ⟨sb, ss, sv⟩
  cases hb
  cases hs
  rfl

/-- Flipping orientation conjugates the represented value. -/
theorem conj_root {p : ZPoly} (r : OrientedIsolation p) :
    r.conj.rep.root = starRingEnd ℂ r.rep.root := by
  rcases r with ⟨base, side, valid⟩
  cases side with
  | real =>
    exact (Complex.conj_eq_iff_im.mpr
      ((RefinedIsolation.meetsRealAxis_iff base).mp valid)).symm
  | upper => exact RefinedIsolation.root_conj base
  | lower => simp [conj, rep]

end OrientedIsolation
/-- Half-plane classification depends only on the represented complex value. -/
theorem sideOf_root {p : ZPoly} (r : RefinedIsolation p) :
    sideOf r = if r.root.im = 0 then .real else if 0 < r.root.im then .upper else .lower := by
  simp only [sideOf, HexRootsMathlib.RefinedIsolation.meetsRealAxis_iff,
    HexRootsMathlib.RefinedIsolation.upper_iff]

/-- Reorienting a matching upper representative succeeds and preserves the root. -/
theorem orient?_exists {p : ZPoly} (r base : RefinedIsolation p)
    (hb : base.root = (if sideOf r = .lower then r.conj else r).root) :
    ∃ s, orient? base (sideOf r) = some s ∧ s.rep.root = r.root := by
  by_cases hr : r.root.im = 0
  · have hs : sideOf r = .real := by simp [sideOf_root, hr]
    simp only [hs, reduceCtorEq, ite_false] at hb
    have hbase : base.1.square.meetsRealAxis = true :=
      (HexRootsMathlib.RefinedIsolation.meetsRealAxis_iff base).mpr (by rw [hb, hr])
    refine ⟨⟨base, .real, hbase⟩, ?_, hb⟩
    simp [hs, orient?, hbase]
  · by_cases hu : 0 < r.root.im
    · have hs : sideOf r = .upper := by simp [sideOf_root, hr, hu]
      simp only [hs, reduceCtorEq, ite_false] at hb
      have hbase : base.1.square.radiusHi < base.1.square.im :=
        (HexRootsMathlib.RefinedIsolation.upper_iff base).mpr (by rw [hb]; exact hu)
      refine ⟨⟨base, .upper, hbase⟩, ?_, hb⟩
      simp [hs, orient?, hbase]
    · have hs : sideOf r = .lower := by simp [sideOf_root, hr, hu]
      simp only [hs, ite_true, HexRootsMathlib.RefinedIsolation.root_conj] at hb
      have hbase : base.1.square.radiusHi < base.1.square.im := by
        apply (HexRootsMathlib.RefinedIsolation.upper_iff base).mpr
        rw [hb, Complex.conj_im]
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hu) hr)
      refine ⟨⟨base, .lower, hbase⟩, ?_, ?_⟩
      · simp [hs, orient?, hbase]
      · simp [OrientedIsolation.rep, hb]

end Hex.AlgebraicNumber
