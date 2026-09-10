/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Rational
public import HexRealAlgebraicMathlib.Approx
public import Mathlib.Data.Rat.Floor

public section

/-! Exact floor and ceiling from a bounded enclosure and one comparison. -/

namespace Hex.RealAlgebraicNumber

/-- The real interpretation preserves integer casts. -/
@[simp] theorem intCast_toReal (n : Int) : (n : RealAlgebraicNumber).toReal = n :=
  map_intCast toRealHom n

private theorem rat_floor_bounds (q : Rat) :
    (q.floor : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (q.floor : ℝ) + 1 := by
  simpa only [Rat.floor_cast, Rat.floor_def', Rat.floor_def] using
    And.intro (Int.floor_le (q : ℝ)) (Int.lt_floor_add_one (q : ℝ))

/-- The lower candidate lies below the value; the successor of the upper lies above it. -/
theorem floor_enclosure (a : RealAlgebraicNumber) :
    (a.floorLower : ℝ) ≤ a.toReal ∧ a.toReal < (a.floorUpper : ℝ) + 1 := by
  have h := approx_enclosure a 2
  exact ⟨(rat_floor_bounds _).1.trans h.1, h.2.trans_lt (rat_floor_bounds _).2⟩

/-- There are at most two consecutive integer floor candidates. -/
theorem floor_candidates (a : RealAlgebraicNumber) :
    a.floorLower ≤ a.floorUpper ∧ a.floorUpper ≤ a.floorLower + 1 := by
  let lo := (a.approxBall 2).re.toRat - (a.approxBall 2).radius.toRat
  let hi := (a.approxBall 2).re.toRat + (a.approxBall 2).radius.toRat
  have he := approx_enclosure a 2
  have hwidth := rounding_width a
  have hl := (rat_floor_bounds lo).2
  have hh := (rat_floor_bounds hi).1
  have hlt : (hi.floor : ℝ) < (lo.floor : ℝ) + 2 := by
    change (hi : ℝ) - (lo : ℝ) ≤ 1 / 2 at hwidth
    linarith
  constructor
  · change (⌊lo⌋ : Int) ≤ ⌊hi⌋
    apply Int.floor_mono
    exact_mod_cast he.1.trans he.2
  · have hltInt : hi.floor < lo.floor + 2 := by exact_mod_cast hlt
    change hi.floor ≤ lo.floor + 1
    omega

private theorem floor_of_none (a : RealAlgebraicNumber) (h : a.toRat? = none) :
    a.floor = if a.floorLower = a.floorUpper then a.floorLower
      else if a < (a.floorUpper : RealAlgebraicNumber) then a.floorLower else a.floorUpper := by
  simp only [floor, h]
  rfl

/-- The executable floor satisfies the defining real inequalities. -/
theorem floor_bounds (a : RealAlgebraicNumber) :
    (a.floor : ℝ) ≤ a.toReal ∧ a.toReal < (a.floor : ℝ) + 1 := by
  cases h : a.toRat? with
  | some q =>
    rw [floor, h]
    have ha := (toRat?_eq_some a q).mp h
    rw [ha, ofRat_toReal]
    exact rat_floor_bounds q
  | none =>
    have he := floor_enclosure a
    have hc := floor_candidates a
    rw [floor_of_none a h]
    split
    · rename_i heq
      exact ⟨he.1, by simpa only [heq] using he.2⟩
    · rename_i hne
      have hadj : a.floorUpper = a.floorLower + 1 := by omega
      split
      · rename_i hlt
        have hv := (lt_iff a (a.floorUpper : RealAlgebraicNumber)).mp hlt
        rw [intCast_toReal, hadj, Int.cast_add, Int.cast_one] at hv
        exact ⟨he.1, hv⟩
      · rename_i hge
        have hv : (a.floorUpper : ℝ) ≤ a.toReal := by
          simpa only [lt_iff, intCast_toReal, not_lt] using hge
        exact ⟨hv, he.2⟩

/-- Executable floor agrees with real floor. -/
theorem floor_toReal (a : RealAlgebraicNumber) : a.floor = ⌊a.toReal⌋ :=
  (Int.floor_eq_iff.mpr (floor_bounds a)).symm

/-- Executable ceiling agrees with real ceiling. -/
theorem ceil_toReal (a : RealAlgebraicNumber) : a.ceil = ⌈a.toReal⌉ := by
  rw [ceil, floor_toReal, neg_toReal, Int.floor_neg, neg_neg]

instance : FloorRing RealAlgebraicNumber :=
  FloorRing.ofFloor RealAlgebraicNumber floor fun n a => by
    rw [le_iff, intCast_toReal, floor_toReal, Int.le_floor]

/-- Floor is below its argument in the executable ordered field. -/
theorem floor_le (a : RealAlgebraicNumber) : (a.floor : RealAlgebraicNumber) ≤ a := by
  simpa only [le_iff, intCast_toReal] using (floor_bounds a).1

/-- The successor of floor is strictly above its argument. -/
theorem lt_floor_add_one (a : RealAlgebraicNumber) :
    a < ((a.floor + 1 : Int) : RealAlgebraicNumber) := by
  simpa only [lt_iff, intCast_toReal, Int.cast_add, Int.cast_one, add_toReal,
    one_toReal] using (floor_bounds a).2

/-- Ceiling encloses its argument between consecutive integers. -/
theorem ceil_bounds (a : RealAlgebraicNumber) :
    ((a.ceil - 1 : Int) : RealAlgebraicNumber) < a ∧ a ≤ (a.ceil : RealAlgebraicNumber) := by
  simp only [lt_iff, le_iff, intCast_toReal, Int.cast_sub, Int.cast_one, ceil_toReal,
    sub_toReal, one_toReal]
  exact ⟨Int.le_ceil_iff.mp (le_refl _), Int.le_ceil a.toReal⟩

example (a : RealAlgebraicNumber) : ⌊a⌋ = a.floor := rfl
example (a : RealAlgebraicNumber) : ⌈a⌉ = a.ceil := rfl

end Hex.RealAlgebraicNumber
