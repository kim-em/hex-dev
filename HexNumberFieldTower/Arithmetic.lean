/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Basic
public import HexNumberFieldTower.RawArithmetic
public meta import HexNumberFieldTower.Basic
public meta import HexNumberFieldTower.RawArithmetic

public section

/-!
# Certified fixed-tower arithmetic

The public dependent carrier delegates to the runtime-indexed mixed-radix
operations after the `NumberTower` wrapper has certified its complete level
list.
-/
namespace Hex.NumberTower

/-- Boolean zero test on fixed mixed-radix coordinates. -/
@[expose]
def isZero {T : NumberTower} (a : Elem T) : Bool :=
  (coeffs a).all fun q => q = 0

/-- Additive identity. -/
@[expose]
def zero (T : NumberTower) : Elem T :=
  ofCoeffs T #[]

instance {T : NumberTower} : Zero (Elem T) := ⟨zero T⟩

/-- The coordinate zero is the rational embedding of zero. -/
theorem zero_eq_ofRat (T : NumberTower) :
    (0 : Elem T) = T.ofRat 0 := by
  change ofCoeffs T #[] = T.ofRat 0
  rw [ofRat_eq_ofCoeffs]
  apply Elem.ext
  simp only [coeffs_ofCoeffs, normalizeCoeffs, Vector.toArray_ofFn]
  congr 1
  funext i
  rcases i with ⟨_ | i, hi⟩
  · simp
  · simp

/-- Zero exposes the all-zero fixed-width coordinate array. -/
@[simp]
theorem coeffs_zero (T : NumberTower) :
    coeffs (0 : Elem T) = Array.replicate T.dim 0 := by
  rw [zero_eq_ofRat, ofRat_eq_ofCoeffs, coeffs_ofCoeffs]
  apply Array.ext
  · simp [normalizeCoeffs]
  · intro i hi₁ hi₂
    rcases i with _ | i
    · simp [normalizeCoeffs]
    · simp [normalizeCoeffs, Array.getD]

/-- The Boolean coordinate test recognizes exactly the tower zero. -/
theorem isZero_iff_eq_zero {T : NumberTower} (a : Elem T) :
    NumberTower.isZero a ↔ a = 0 := by
  constructor
  · intro h
    apply Elem.ext
    rw [coeffs_zero]
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      change (coeffs a).all (fun q => q = 0) = true at h
      rw [Array.all_eq_true] at h
      simpa using h i hi₁
  · rintro rfl
    change (coeffs (0 : Elem T)).all (fun q => q = 0) = true
    rw [coeffs_zero, Array.all_eq_true]
    intro i hi
    simp

/-- Multiplicative identity. -/
@[expose]
def one (T : NumberTower) : Elem T :=
  ofCoeffs T #[1]

instance {T : NumberTower} : One (Elem T) := ⟨one T⟩

/-- The coordinate one is the rational embedding of one. -/
theorem one_eq_ofRat (T : NumberTower) :
    (1 : Elem T) = T.ofRat 1 := by
  rw [ofRat_eq_ofCoeffs]
  rfl

/-- Coordinatewise addition. -/
@[expose]
def add {T : NumberTower} (a b : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.addCoords T.dim (coeffs a) (coeffs b))

instance {T : NumberTower} : Add (Elem T) := ⟨add⟩

/-- Addition exposes its fixed-width coordinate result. -/
@[simp]
theorem coeffs_add {T : NumberTower} (a b : Elem T) :
    coeffs (a + b) = Arithmetic.addCoords T.dim (coeffs a) (coeffs b) := by
  change coeffs (add a b) = _
  unfold add
  rw [coeffs_ofCoeffs]
  apply normalizeCoeffs_eq_self
  simp [Arithmetic.addCoords]

/-- Coordinatewise subtraction. -/
@[expose]
def sub {T : NumberTower} (a b : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.subCoords T.dim (coeffs a) (coeffs b))

instance {T : NumberTower} : Sub (Elem T) := ⟨sub⟩

/-- Subtraction exposes its fixed-width coordinate result. -/
@[simp]
theorem coeffs_sub {T : NumberTower} (a b : Elem T) :
    coeffs (a - b) = Arithmetic.subCoords T.dim (coeffs a) (coeffs b) := by
  change coeffs (sub a b) = _
  unfold sub
  rw [coeffs_ofCoeffs]
  apply normalizeCoeffs_eq_self
  simp [Arithmetic.subCoords]

/-- Coordinatewise additive inverse. -/
@[expose]
def neg {T : NumberTower} (a : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.negCoords T.dim (coeffs a))

instance {T : NumberTower} : Neg (Elem T) := ⟨neg⟩

/-- Negation exposes its fixed-width coordinate result. -/
@[simp]
theorem coeffs_neg {T : NumberTower} (a : Elem T) :
    coeffs (-a) = Arithmetic.negCoords T.dim (coeffs a) := by
  change coeffs (neg a) = _
  unfold neg
  rw [coeffs_ofCoeffs]
  apply normalizeCoeffs_eq_self
  simp [Arithmetic.negCoords]

/-- Coordinate subtraction is addition of the coordinatewise negation. -/
theorem sub_eq_add_neg {T : NumberTower} (a b : Elem T) :
    a - b = a + (-b) := by
  apply Elem.ext
  rw [coeffs_sub, coeffs_add, coeffs_neg]
  simp only [Arithmetic.subCoords, Arithmetic.addCoords,
    Arithmetic.negCoords, Vector.toArray_ofFn]
  congr 1
  funext i
  simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    dif_pos i.isLt, Option.getD_some] using Rat.sub_eq_add_neg
      ((coeffs a).getD i 0) ((coeffs b).getD i 0)

/-- Coordinatewise negation is an additive inverse. -/
theorem add_neg_self {T : NumberTower} (a : Elem T) :
    a + (-a) = 0 := by
  apply Elem.ext
  rw [coeffs_add, coeffs_neg, coeffs_zero]
  apply Array.ext
  · simp [Arithmetic.addCoords]
  · intro i hi₁ hi₂
    have hi : i < (coeffs a).size := by
      simpa using hi₂
    simpa [Arithmetic.addCoords, Arithmetic.negCoords] using
      Rat.add_neg_cancel ((coeffs a)[i]'hi)

/-- Recursive convolution and monic reduction. -/
@[expose]
def mul {T : NumberTower} (a b : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.mulCoords T.levels.toList (coeffs a) (coeffs b))

instance {T : NumberTower} : Mul (Elem T) := ⟨mul⟩

/-- Multiplication exposes its fixed-width recursively reduced coordinates. -/
@[simp]
theorem coeffs_mul {T : NumberTower} (a b : Elem T) :
    coeffs (a * b) =
      Arithmetic.mulCoords T.levels.toList (coeffs a) (coeffs b) := by
  change coeffs (mul a b) = _
  unfold mul
  rw [coeffs_ofCoeffs]
  apply normalizeCoeffs_eq_self
  simp [dim]

/-- Recursive extended-gcd inversion, totalized by `0⁻¹ = 0`. -/
@[expose]
def inv {T : NumberTower} (a : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.invCoords T.levels.toList (coeffs a))

instance {T : NumberTower} : Inv (Elem T) := ⟨inv⟩

/-- Tower division. -/
@[expose]
def div {T : NumberTower} (a b : Elem T) : Elem T :=
  a * b⁻¹

instance {T : NumberTower} : Div (Elem T) := ⟨div⟩

/-- Rational scalar multiplication acts on every mixed-radix coordinate. -/
@[expose]
def smul {T : NumberTower} (q : Rat) (a : Elem T) : Elem T :=
  ofCoeffs T ((coeffs a).map fun c => q * c)

instance {T : NumberTower} : SMul Rat (Elem T) := ⟨smul⟩

/-- Rational scalar multiplication exposes coordinatewise multiplication. -/
@[simp]
theorem coeffs_smul {T : NumberTower} (q : Rat) (a : Elem T) :
    coeffs (q • a) = (coeffs a).map fun c => q * c := by
  change coeffs (smul q a) = _
  unfold smul
  rw [coeffs_ofCoeffs]
  apply normalizeCoeffs_eq_self
  simp

/-- Dense univariate polynomials over a fixed tower. -/
abbrev Poly (T : NumberTower) := DensePoly (Elem T)

/-! Compiled rational-tower arithmetic checks. -/

#guard
    let a := ofRat rat 7
    let b := ofRat rat 3
    coeffs (a + b) = #[10] && coeffs (a - b) = #[4] &&
      coeffs (a * b) = #[21] && coeffs (a / b) = #[7 / 3] &&
      coeffs (0⁻¹ : Elem rat) = #[0]

end Hex.NumberTower
