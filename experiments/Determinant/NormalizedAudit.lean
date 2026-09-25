/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Determinant.Normalized
import Mathlib.Data.ZMod.Basic

namespace Determinant.NormalizedAudit

theorem generic {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a, b; c, d] = a * d - b * c := by normalized_bird

theorem reordered {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a + b, c; d, a - b] = -(d * c) - b ^ 2 + a ^ 2 := by
  normalized_bird

theorem cancellation {R : Type*} [CommRing R] (a b : R) :
    Matrix.det !![a, b; (a + b)^2 - (a^2 + 2*a*b + b^2), a] = a^2 := by
  normalized_bird

theorem rational (a b : Rat) :
    Matrix.det !![a / 2, b / 3; a / 5, b / 7] = a*b * (1/14 - 1/15) := by
  normalized_bird

theorem composite (a b : ZMod 6) :
    Matrix.det !![a, b; 3*b, 2*a] = 2*a^2 - 3*b^2 := by normalized_bird

theorem singleton {R : Type*} [CommRing R] (a : R) :
    Matrix.det !![a] = a := by normalized_bird

example {R : Type*} [CommRing R] (a b c d : R)
    (h : Matrix.det !![a, b; c, d] = a * d - b * c + 1) :
    Matrix.det !![a, b; c, d] = a * d - b * c + 1 := by
  fail_if_success normalized_bird
  exact h

example {R : Type*} [CommRing R] (a b c d extra : R)
    (h : Matrix.det !![a, b; c, d] = a * d - b * c + extra) :
    Matrix.det !![a, b; c, d] = a * d - b * c + extra := by
  fail_if_success normalized_bird
  exact h

#print axioms generic
#print axioms reordered
#print axioms cancellation
#print axioms rational
#print axioms composite
#print axioms singleton

theorem composed {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a, b; c, d] = a * d - b * c := by composed_bird

theorem composedZero {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a*c, a*d; b*c, b*d] = 0 := by composed_bird

theorem composedRat (a b : Rat) :
    Matrix.det !![a / 2, b / 3; a / 5, b / 7] = a*b / 210 := by composed_bird

example {R : Type*} [CommRing R] (a b c d : R)
    (h : Matrix.det !![a, b; c, d] = a * d - b * c + 1) :
    Matrix.det !![a, b; c, d] = a * d - b * c + 1 := by
  fail_if_success composed_bird
  exact h

#print axioms composed
#print axioms composedZero
#print axioms composedRat

theorem direct {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a, b; c, d] = a*d - b*c := by direct_bird

theorem directZero {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a*c, a*d; b*c, b*d] = 0 := by direct_bird

theorem directRat (a b : Rat) :
    Matrix.det !![a / 2, b / 3; a / 5, b / 7] = a*b / 210 := by direct_bird

example {R : Type*} [CommRing R] (a b c d : R)
    (h : Matrix.det !![a, b; c, d] = a*d - b*c + 1) :
    Matrix.det !![a, b; c, d] = a*d - b*c + 1 := by
  fail_if_success direct_bird
  exact h

#print axioms direct
#print axioms directZero
#print axioms directRat

theorem literal {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a, b; c, d] = a*d - b*c := by literal_bird

theorem literalZero {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a*c, a*d; b*c, b*d] = 0 := by literal_bird

theorem literalRat (a b : Rat) :
    Matrix.det !![a / 2, b / 3; a / 5, b / 7] = a*b / 210 := by literal_bird

example {R : Type*} [CommRing R] (a b c d : R)
    (h : Matrix.det !![a, b; c, d] = a*d - b*c + 1) :
    Matrix.det !![a, b; c, d] = a*d - b*c + 1 := by
  fail_if_success literal_bird
  exact h

#print axioms literal
#print axioms literalZero
#print axioms literalRat

theorem characteristicTwo (a b c d : ZMod 2) :
    Matrix.det !![a + b, c; d, a - b] = a^2 - b^2 - c*d := by direct_bird

#print axioms characteristicTwo

end Determinant.NormalizedAudit
