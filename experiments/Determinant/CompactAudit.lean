/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Determinant.Normalized
import Mathlib.Data.ZMod.Basic

namespace Determinant.CompactAudit

theorem generic {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a, b; c, d] = a * d - b * c := by compact_bird

theorem reordered {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a + b, c; d, a - b] = -(d * c) - b ^ 2 + a ^ 2 := by
  compact_bird

theorem cancellation {R : Type*} [CommRing R] (a b : R) :
    Matrix.det !![a, b; (a + b)^2 - (a^2 + 2*a*b + b^2), a] = a^2 := by
  compact_bird

theorem rational (a b : Rat) :
    Matrix.det !![a / 2, b / 3; a / 5, b / 7] = a*b * (1/14 - 1/15) := by
  compact_bird

theorem composite (a b : ZMod 6) :
    Matrix.det !![a, b; 3*b, 2*a] = 2*a^2 - 3*b^2 := by compact_bird

theorem singleton {R : Type*} [CommRing R] (a : R) :
    Matrix.det !![a] = a := by compact_bird

example {R : Type*} [CommRing R] (a b c d : R)
    (h : Matrix.det !![a, b; c, d] = a * d - b * c + 1) :
    Matrix.det !![a, b; c, d] = a * d - b * c + 1 := by
  fail_if_success compact_bird
  exact h

example {R : Type*} [CommRing R] (a b c d extra : R)
    (h : Matrix.det !![a, b; c, d] = a * d - b * c + extra) :
    Matrix.det !![a, b; c, d] = a * d - b * c + extra := by
  fail_if_success compact_bird
  exact h

#print axioms generic
#print axioms reordered
#print axioms cancellation
#print axioms rational
#print axioms composite
#print axioms singleton

theorem zero {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a*c, a*d; b*c, b*d] = 0 := by compact_bird

theorem characteristicTwo (a b c d : ZMod 2) :
    Matrix.det !![a + b, c; d, a - b] = a^2 - b^2 - c*d := by compact_bird

#print axioms zero
#print axioms characteristicTwo
#print axioms Determinant.Compact.add_eq
#print axioms Determinant.Compact.mul_eq
#print axioms Determinant.Compact.neg_eq
end Determinant.CompactAudit
