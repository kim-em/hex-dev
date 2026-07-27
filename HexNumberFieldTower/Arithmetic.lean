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

/-- Multiplicative identity. -/
@[expose]
def one (T : NumberTower) : Elem T :=
  ofCoeffs T #[1]

instance {T : NumberTower} : One (Elem T) := ⟨one T⟩

/-- Coordinatewise addition. -/
@[expose]
def add {T : NumberTower} (a b : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.addCoords T.dim (coeffs a) (coeffs b))

instance {T : NumberTower} : Add (Elem T) := ⟨add⟩

/-- Coordinatewise subtraction. -/
@[expose]
def sub {T : NumberTower} (a b : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.subCoords T.dim (coeffs a) (coeffs b))

instance {T : NumberTower} : Sub (Elem T) := ⟨sub⟩

/-- Coordinatewise additive inverse. -/
@[expose]
def neg {T : NumberTower} (a : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.negCoords T.dim (coeffs a))

instance {T : NumberTower} : Neg (Elem T) := ⟨neg⟩

/-- Recursive convolution and monic reduction. -/
@[expose]
def mul {T : NumberTower} (a b : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.mulCoords T.levels.toList (coeffs a) (coeffs b))

instance {T : NumberTower} : Mul (Elem T) := ⟨mul⟩

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
