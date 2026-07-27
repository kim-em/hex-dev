/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField
public meta import HexNumberField

public section

/-!
# Successive number-field towers

This module fixes the runtime representation used by the tower library. Levels
are stored top-first, while element coordinates use the mixed-radix order in
which the oldest generator varies fastest. A level stores only the lower
coefficients of its monic defining polynomial; the leading coefficient is
implicitly one.
-/
namespace Hex

namespace NumberTower

/-- Runtime data for one monic algebraic extension. `defining[j]` is the
flattened lower-tower coefficient of `X^j`; the omitted coefficient of
`X^degree` is one. -/
structure Level where
  degree : Nat
  defining : Array (Array Rat)
  root : AlgebraicRoot

/-- Dimension represented by a top-first list of extension levels. -/
@[expose]
def levelsDim : List Level → Nat
  | [] => 1
  | level :: lower => level.degree * levelsDim lower

/-- Structural validity of one level above a lower field of dimension
`lowerDim`. The semantic irreducibility and fixed-embedding checks are owned by
the smart constructors in `Embed`. -/
@[expose]
def Level.Valid (level : Level) (lowerDim : Nat) : Prop :=
  0 < level.degree ∧
    level.defining.size = level.degree ∧
    ∀ i, ∀ h : i < level.defining.size,
      (level.defining[i]'h).size = lowerDim

/-- Every top-first level has canonical coefficient widths relative to the
tail beneath it. -/
@[expose]
def LevelsValid : List Level → Prop
  | [] => True
  | level :: lower =>
      level.Valid (levelsDim lower) ∧ LevelsValid lower

end NumberTower

/-- A validated, fixed-embedding tower of successive algebraic extensions of
`Rat`. Construction is sealed; later modules extend towers only through checked
smart constructors. -/
structure NumberTower where
  private mk ::
  levels : Array NumberTower.Level
  valid : NumberTower.LevelsValid levels.toList

namespace NumberTower

/-- The rational tower, with no algebraic extension levels. -/
def rat : NumberTower :=
  .mk #[] (by simp [LevelsValid])

/-- Absolute dimension over `Rat`. -/
@[expose]
def dim (T : NumberTower) : Nat :=
  levelsDim T.levels.toList

/-- Number of proper algebraic extension levels. -/
@[expose]
def height (T : NumberTower) : Nat :=
  T.levels.size

/-- Canonical mixed-radix rational coordinates in a fixed tower. -/
structure Elem (T : NumberTower) where
  private mk ::
  data : Array Rat
  size_eq : data.size = T.dim

/-- Normalize an arbitrary coordinate array to the tower dimension by
truncating excess coordinates and padding missing coordinates with zero. -/
@[expose]
def normalizeCoeffs (T : NumberTower) (coefficients : Array Rat) : Array Rat :=
  (Vector.ofFn fun i : Fin T.dim => coefficients.getD i.val 0).toArray

/-- Construct the unique fixed-width element represented by a raw coordinate
array. -/
def ofCoeffs (T : NumberTower) (coefficients : Array Rat) : Elem T :=
  .mk (normalizeCoeffs T coefficients) (by simp [normalizeCoeffs])

/-- Canonical flattened rational coordinates. -/
@[expose]
def coeffs {T : NumberTower} (a : Elem T) : Array Rat :=
  a.data

/-- Equality is exact coordinate equality inside a fixed tower. -/
@[ext]
theorem Elem.ext {T : NumberTower} {a b : Elem T}
    (h : coeffs a = coeffs b) : a = b := by
  cases a
  cases b
  change _ = _ at h
  cases h
  rfl

instance {T : NumberTower} : DecidableEq (Elem T) := fun a b =>
  match decEq (coeffs a).toList (coeffs b).toList with
  | isTrue h =>
      isTrue (Elem.ext (by simpa using h))
  | isFalse h =>
      isFalse fun hab => h (by simp [hab])

/-- Embed a rational number into the constant mixed-radix coordinate. -/
def ofRat (T : NumberTower) (q : Rat) : Elem T :=
  ofCoeffs T #[q]

/-! Compiled representation checks. -/

#guard rat.dim = 1 && rat.height = 0

#guard
    let a := ofCoeffs rat #[3, 4]
    let b := ofRat rat 3
    a == b && coeffs a = #[3]

end NumberTower
end Hex
