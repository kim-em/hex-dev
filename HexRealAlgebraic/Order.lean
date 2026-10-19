/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraic.Basic
public import Init.Data.Order

public section

/-! Exact comparison and rounding of canonical real algebraic numbers. -/

namespace Hex.RealAlgebraicNumber

/-- Exact comparison, using the separation precision of the product polynomial. -/
@[expose] def compare (a b : RealAlgebraicNumber) : Ordering :=
  a.toAlgebraic.realCompare b.toAlgebraic

instance : Ord RealAlgebraicNumber := ⟨compare⟩
instance : LT RealAlgebraicNumber := ⟨fun a b => compare a b = .lt⟩
instance : LE RealAlgebraicNumber := ⟨fun a b => compare a b ≠ .gt⟩
instance : DecidableLT RealAlgebraicNumber := fun a b =>
  inferInstanceAs (Decidable (compare a b = .lt))
instance : DecidableLE RealAlgebraicNumber := fun a b =>
  inferInstanceAs (Decidable (compare a b ≠ .gt))

/-- Minimum, returning the left argument on a tie. -/
@[expose] def min (a b : RealAlgebraicNumber) : RealAlgebraicNumber :=
  if a ≤ b then a else b
/-- Maximum, returning the left argument on a tie. -/
@[expose] def max (a b : RealAlgebraicNumber) : RealAlgebraicNumber :=
  if b ≤ a then a else b

instance : Min RealAlgebraicNumber := ⟨min⟩
instance : Max RealAlgebraicNumber := ⟨max⟩

/-- The exact sign, valued in minus one, zero, and one. -/
@[expose] def sign (a : RealAlgebraicNumber) : Int :=
  match compare a 0 with
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- Absolute value computed by exact sign comparison. -/
@[expose] def abs (a : RealAlgebraicNumber) : RealAlgebraicNumber :=
  if a < 0 then -a else a

/-- The coefficients of a primitive linear minimal polynomial are coprime. -/
private theorem linear_coprime (a : RealAlgebraicNumber)
    (degree : a.toAlgebraic.p.natDegree = 1) :
    (a.toAlgebraic.p.coeff 0).natAbs.Coprime (a.toAlgebraic.p.coeff 1).natAbs := by
  have size := DensePoly.natDegree_eq_size_sub_one a.toAlgebraic.p
  have hsize : a.toAlgebraic.p.size = 2 := by omega
  let d := (a.toAlgebraic.p.coeff 0).natAbs.gcd (a.toAlgebraic.p.coeff 1).natAbs
  have divides : (d : Int) ∣ ZPoly.content a.toAlgebraic.p := by
    apply ZPoly.dvd_content_of_nat_dvd_coeff
    intro n
    cases n with
    | zero => exact Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left ..)
    | succ n =>
      cases n with
      | zero => exact Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_right ..)
      | succ n =>
        rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega)]
        change (d : Int) ∣ (0 : Int)
        exact Int.dvd_zero _
  rw [a.toAlgebraic.prim] at divides
  exact Nat.dvd_one.mp (Int.ofNat_dvd.mp divides)

private theorem linear_pos (a : RealAlgebraicNumber)
    (degree : a.toAlgebraic.p.natDegree = 1) : 0 < a.toAlgebraic.p.coeff 1 := by
  have size := DensePoly.natDegree_eq_size_sub_one a.toAlgebraic.p
  have hsize : a.toAlgebraic.p.size = 2 := by omega
  have last := DensePoly.leadingCoeff_eq_coeff_last a.toAlgebraic.p (by omega)
  rw [hsize] at last
  simpa only [last] using a.toAlgebraic.pos_lc

/-- Recognize a rational by its linear canonical minimal polynomial. Its
primitive coefficients already supply a reduced numerator and denominator;
the erased proofs avoid another runtime gcd and rational division. -/
@[expose] def toRat? (a : RealAlgebraicNumber) : Option Rat :=
  let p := a.toAlgebraic.p
  if degree : p.natDegree = 1 then
    some {
      num := -p.coeff 0
      den := (p.coeff 1).natAbs
      den_nz := by
        exact Int.natAbs_ne_zero.mpr (Int.ne_of_gt (linear_pos a degree))
      reduced := by simpa only [Int.natAbs_neg] using linear_coprime a degree }
  else none

/-- Rational recognition preserves the coefficient quotient of the canonical
linear polynomial. The runtime constructor only omits redundant normalization. -/
theorem toRat?_formula (a : RealAlgebraicNumber) :
    a.toRat? = if a.toAlgebraic.p.natDegree = 1 then
      some (-(a.toAlgebraic.p.coeff 0 : Rat) / (a.toAlgebraic.p.coeff 1 : Rat))
    else none := by
  dsimp only [toRat?]
  split
  · rename_i degree
    congr 1
    rw [Rat.mk_eq_divInt, Int.natAbs_of_nonneg (Int.le_of_lt (linear_pos a degree)),
      Rat.divInt_eq_div, Rat.intCast_neg]
  · rfl

/-- The floor of the lower endpoint of the precision-two enclosure. -/
@[expose] def floorLower (a : RealAlgebraicNumber) : Int :=
  let b := a.approxBall 2
  (b.re.toRat - b.radius.toRat).floor

/-- The floor of the upper endpoint of the precision-two enclosure. -/
@[expose] def floorUpper (a : RealAlgebraicNumber) : Int :=
  let b := a.approxBall 2
  (b.re.toRat + b.radius.toRat).floor

/-- Exact floor: the enclosure supplies at most two consecutive candidates,
with one comparison at the intervening integer when necessary. -/
@[expose] def floor (a : RealAlgebraicNumber) : Int :=
  match a.toRat? with
  | some q => q.floor
  | none =>
    let b := a.approxBall 2
    let lo := (b.re.toRat - b.radius.toRat).floor
    let hi := (b.re.toRat + b.radius.toRat).floor
    if lo = hi then lo
    else if a < (hi : RealAlgebraicNumber) then lo else hi

/-- Exact ceiling. Rational values use rational ceiling; a nonrational value
is never an integer, so its ceiling is one more than its floor. This avoids
canonicalizing a negation solely to round it. The companion proves both the
ceiling inequalities and the unchanged negation relation `ceil_eq`. -/
@[expose] def ceil (a : RealAlgebraicNumber) : Int :=
  match a.toRat? with
  | some q => q.ceil
  | none => a.floor + 1

end Hex.RealAlgebraicNumber
