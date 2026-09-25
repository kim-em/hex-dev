/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Determinant.Normalized
import Mathlib.Data.ZMod.Basic

namespace Determinant.FreshAudit

theorem generic {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a, b; c, d] = a * d - b * c := by fresh_bird

theorem reordered {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a + b, c; d, a - b] = -(d * c) - b ^ 2 + a ^ 2 := by
  fresh_bird

theorem cancellation {R : Type*} [CommRing R] (a b : R) :
    Matrix.det !![a, b; (a + b)^2 - (a^2 + 2*a*b + b^2), a] = a^2 := by
  fresh_bird

theorem rational (a b : Rat) :
    Matrix.det !![a / 2, b / 3; a / 5, b / 7] = a*b * (1/14 - 1/15) := by
  fresh_bird

theorem composite (a b : ZMod 6) :
    Matrix.det !![a, b; 3*b, 2*a] = 2*a^2 - 3*b^2 := by fresh_bird

theorem singleton {R : Type*} [CommRing R] (a : R) :
    Matrix.det !![a] = a := by fresh_bird

example {R : Type*} [CommRing R] (a b c d : R)
    (h : Matrix.det !![a, b; c, d] = a * d - b * c + 1) :
    Matrix.det !![a, b; c, d] = a * d - b * c + 1 := by
  fail_if_success fresh_bird
  exact h

example {R : Type*} [CommRing R] (a b c d extra : R)
    (h : Matrix.det !![a, b; c, d] = a * d - b * c + extra) :
    Matrix.det !![a, b; c, d] = a * d - b * c + extra := by
  fail_if_success fresh_bird
  exact h

#print axioms generic
#print axioms reordered
#print axioms cancellation
#print axioms rational
#print axioms composite
#print axioms singleton

theorem zero {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a*c, a*d; b*c, b*d] = 0 := by fresh_bird

theorem characteristicTwo (a b c d : ZMod 2) :
    Matrix.det !![a + b, c; d, a - b] = a^2 - b^2 - c*d := by fresh_bird

#print axioms zero
#print axioms characteristicTwo
#print axioms Determinant.Compact.add_eq
#print axioms Determinant.Compact.mul_eq
#print axioms Determinant.Compact.neg_eq
#print axioms Determinant.Steps.iter_zero
#print axioms Determinant.Steps.iter_step

theorem symbolicThree {R : Type*} [CommRing R] (a b c d e f g h : R) :
    Matrix.det !![a, b, c; d, 0, e; f, g, h] =
      -a*e*g - b*d*h + b*e*f + c*d*g := by fresh_bird

theorem integerFour :
    Matrix.det (!![2, 1, 0, 0; 1, 2, 1, 0; 0, 1, 2, 1; 0, 0, 1, 2] :
      Matrix (Fin 4) (Fin 4) Int) = 5 := by fresh_bird

#print axioms symbolicThree
#print axioms integerFour

theorem quotientRows {R : Type*} [Field R] (a b c d e f g h i j k l u v w x y z : R) :
    Matrix.det !![(a+b)/u, (c+d)/v, (e+f)/w;
      (g+h)/x, (i+j)/y, (k+l)/z;
      (a+b)/u + (g+h)/x, (c+d)/v + (i+j)/y, (e+f)/w + (k+l)/z] = 0 := by
  fresh_bird

theorem quotientProduct {R : Type*} [Field R] (a b c d u v : R) :
    Matrix.det !![a/u, b/u; c/v, d/v] = (a*d-b*c)/(u*v) := by fresh_bird

#print axioms quotientRows
#print axioms quotientProduct

open Lean Meta Qq Mathlib.Tactic.Ring Mathlib.Tactic.Determinant in
run_meta do
  let reified ← reifyBirdDet q(BirdDet.birdDet 4
    (#[(1 : Int), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]))
  let cα ← Mathlib.Tactic.Ring.Common.mkCache
    (commSemiringOfCommRing reified.rα)
  let ctx := { reified.ctx with cα, rc := ringCompute cα }
  let (_, baseline) ← (certBirdDet (rα := reified.rα)).run {} |>.run ctx |>.run .reducible
  let (_, plain) ← (Compact.certBirdDet (rα := reified.rα) false).run {} |>.run ctx |>.run .reducible
  let (_, fused) ← (Compact.certBirdDet (rα := reified.rα) true).run {} |>.run ctx |>.run .reducible
  let (_, coeff) ← (Compact.certBirdDet (rα := reified.rα) true true).run {} |>.run ctx |>.run .reducible
  unless coeff.iterStepEntryCache.size == fused.iterStepEntryCache.size &&
      coeff.diagCache.size == fused.diagCache.size &&
      coeff.entryCache.size == fused.entryCache.size &&
      plain.iterStepEntryCache.size > 0 &&
      baseline.iterStepEntryCache.size == fused.iterStepEntryCache.size &&
      baseline.diagCache.size == fused.diagCache.size &&
      baseline.entryCache.size == fused.entryCache.size &&
      plain.iterStepEntryCache.size == fused.iterStepEntryCache.size &&
      plain.diagCache.size == fused.diagCache.size &&
      plain.entryCache.size == fused.entryCache.size do
    throwError "recurrence variant bypassed a certificate cache"
  logInfo m!"CACHE_CHECK entries={fused.entryCache.size}, iterations={fused.iterStepEntryCache.size}, diagonals={fused.diagCache.size}"
end Determinant.FreshAudit
