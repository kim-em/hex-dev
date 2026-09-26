/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Determinant.Normalized
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormDet

namespace Determinant.BoundedAudit

theorem generic {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a, b; c, d] = a * d - b * c := by bounded_bird

theorem reordered {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a + b, c; d, a - b] = -(d * c) - b ^ 2 + a ^ 2 := by
  bounded_bird

theorem cancellation {R : Type*} [CommRing R] (a b : R) :
    Matrix.det !![a, b; (a + b)^2 - (a^2 + 2*a*b + b^2), a] = a^2 := by
  bounded_bird

theorem rational (a b : Rat) :
    Matrix.det !![a / 2, b / 3; a / 5, b / 7] = a*b * (1/14 - 1/15) := by
  bounded_bird

theorem composite (a b : ZMod 6) :
    Matrix.det !![a, b; 3*b, 2*a] = 2*a^2 - 3*b^2 := by bounded_bird

theorem singleton {R : Type*} [CommRing R] (a : R) :
    Matrix.det !![a] = a := by bounded_bird

example {R : Type*} [CommRing R] (a b c d : R)
    (h : Matrix.det !![a, b; c, d] = a * d - b * c + 1) :
    Matrix.det !![a, b; c, d] = a * d - b * c + 1 := by
  fail_if_success bounded_bird
  exact h

example {R : Type*} [CommRing R] (a b c d extra : R)
    (h : Matrix.det !![a, b; c, d] = a * d - b * c + extra) :
    Matrix.det !![a, b; c, d] = a * d - b * c + extra := by
  fail_if_success bounded_bird
  exact h

#print axioms generic
#print axioms reordered
#print axioms cancellation
#print axioms rational
#print axioms composite
#print axioms singleton

theorem zero {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a*c, a*d; b*c, b*d] = 0 := by bounded_bird

theorem characteristicTwo (a b c d : ZMod 2) :
    Matrix.det !![a + b, c; d, a - b] = a^2 - b^2 - c*d := by bounded_bird

#print axioms zero
#print axioms characteristicTwo
#print axioms Determinant.Compact.add_eq
#print axioms Determinant.Compact.mul_eq
#print axioms Determinant.Compact.neg_eq
#print axioms Determinant.Steps.iter_zero
#print axioms Determinant.Steps.iter_step

theorem symbolicThree {R : Type*} [CommRing R] (a b c d e f g h : R) :
    Matrix.det !![a, b, c; d, 0, e; f, g, h] =
      -a*e*g - b*d*h + b*e*f + c*d*g := by bounded_bird

theorem integerFour :
    Matrix.det (!![2, 1, 0, 0; 1, 2, 1, 0; 0, 1, 2, 1; 0, 0, 1, 2] :
      Matrix (Fin 4) (Fin 4) Int) = 5 := by bounded_bird

#print axioms symbolicThree
#print axioms integerFour

theorem quotientRows {R : Type*} [Field R] (a b c d e f g h i j k l u v w x y z : R) :
    Matrix.det !![(a+b)/u, (c+d)/v, (e+f)/w;
      (g+h)/x, (i+j)/y, (k+l)/z;
      (a+b)/u + (g+h)/x, (c+d)/v + (i+j)/y, (e+f)/w + (k+l)/z] = 0 := by
  bounded_bird

theorem quotientProduct {R : Type*} [Field R] (a b c d u v : R) :
    Matrix.det !![a/u, b/u; c/v, d/v] = (a*d-b*c)/(u*v) := by bounded_bird

#print axioms quotientRows
#print axioms quotientProduct

theorem nestedQuotient {R : Type*} [Field R] (a d u v : R) :
    Matrix.det !![(a/u)/v, 0; 0, d] = a*d/(u*v) := by bounded_first

theorem scaledRankOne {R : Type*} [Field R] (a b c d u v : R) :
    Matrix.det !![a*c/u, a*d/u; b*c/v, b*d/v] = 0 := by bounded_first

theorem productDenominators {R : Type*} [Field R] (a b c d u v w z : R) :
    Matrix.det !![a*c/(u*w), a*d/(u*z); b*c/(v*w), b*d/(v*z)] = 0 := by
  bounded_first

theorem inverseProduct {R : Type*} [Field R] (a u v : R) :
    Matrix.det !![a*(u*v)⁻¹] = (a/u)/v := by bounded_first

#print axioms scaledRankOne
#print axioms productDenominators
#print axioms inverseProduct

theorem zeroNumerator {R : Type*} [Field R] (a b c u v w : R) :
    Matrix.det !![((a+b)^2 - (a^2+2*a*b+b^2))/u, b/v; 0, c/w] = 0 := by
  bounded_bird

theorem zeroDenominator {R : Type*} [Field R] (a b c d : R) :
    Matrix.det !![(a+b)/0, c/0; c, d] = 0 := by bounded_bird

-- These valid identities require simplifications beyond the ring normalizer.
-- Retain the limitation explicitly, and check that the Mathlib arm also fails.
-- Keep the exact comparator, including its behavior when simp closes the goal.
set_option linter.unnecessarySeqFocus false in
theorem inverseCancellation {R : Type*} [Field R] (a b d u v : R) :
    Matrix.det !![(a/u)/(b/v), 0; 0, d] = a*v*d/(u*b) := by
  fail_if_success bounded_bird
  fail_if_success (solve | simp only [norm_det] <;> ring)
  simp [Matrix.det_fin_two, div_eq_mul_inv, mul_inv_rev]
  ring

set_option linter.unnecessarySeqFocus false in
theorem finiteCharacteristic (a b c d : ZMod 2) :
    Matrix.det !![(a+b)/2, c/2; c, d] = 0 := by
  fail_if_success bounded_bird
  fail_if_success (solve | simp only [norm_det] <;> ring)
  have hz : (2 : ZMod 2) = 0 := rfl
  simp [hz, Matrix.det_fin_two]

#print axioms inverseCancellation
#print axioms finiteCharacteristic

#print axioms nestedQuotient
#print axioms zeroNumerator
#print axioms zeroDenominator

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
  let (_, coeff) ← (Compact.certBirdDet (rα := reified.rα) true true true true).run {} |>.run ctx |>.run .reducible
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
end Determinant.BoundedAudit

open Lean Meta Qq Mathlib.Tactic.Ring in
run_meta do
  withLocalDeclD `a q(Rat) fun a =>
    withLocalDeclD `b q(Rat) fun b =>
      withLocalDeclD `c q(Rat) fun c => do
        have a : Q(Rat) := a
        have b : Q(Rat) := b
        have c : Q(Rat) := c
        let cache ← Common.mkCache q(inferInstance : CommSemiring Rat)
        for term in ([q(($a + $b)^8 / $c), q(((2 : Nat) • ($a + $b)) / $c),
            q(($a / $c + $b) / $c)] : List Q(Rat)) do
          let check : Mathlib.Tactic.AtomM Unit := do
            let _ ← Determinant.Bounded.eval rcℕ (ringCompute cache) cache term
            let state ← getThe Mathlib.Tactic.AtomM.State
            unless state.atoms.size == 1 && state.atoms[0]! == term do
              throwError "discarded numerator normalization leaked atoms: {term}"
            logInfo "ATOM_CHECK retained only the original quotient"
          check.run .reducible
        let check : Mathlib.Tactic.AtomM Unit := do
          let result ← Determinant.Bounded.eval rcℕ (ringCompute cache) cache q(($a * $b) / $c)
          let state ← getThe Mathlib.Tactic.AtomM.State
          unless Determinant.Bounded.atMostOne result.val && state.atoms.contains a &&
              state.atoms.contains b && state.atoms.contains c &&
              (← state.atoms.anyM fun atom => withReducible <| isDefEq atom q($c⁻¹)) do
            throwError "monomial quotient did not split into factors: {state.atoms}"
          logInfo "ATOM_CHECK expanded a monomial quotient"
        check.run .reducible

open Lean Meta Qq Mathlib.Tactic.Ring Mathlib.Tactic.Determinant in
run_meta do
  let reified ← reifyBirdDet q(BirdDet.birdDet 4
    (#[(1 : Int), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]))
  let cα ← Common.mkCache (commSemiringOfCommRing reified.rα)
  let ctx := { reified.ctx with cα, rc := ringCompute cα }
  let check (label : String) (action : CertM reified.rα (Cert reified.rα)) :
      CertM reified.rα Unit := do
    let first ← action
    let second ← action
    let proposition ← inferType first.proof
    let pair := mkApp2 (mkConst ``And.intro) proposition proposition
    let repeated ← (mkApp2 pair first.proof first.proof).numObjs
    let actual ← (mkApp2 pair first.proof second.proof).numObjs
    unless actual == repeated do
      throwError "{label} lookup rebuilt its proof instead of returning the cached object"
    logInfo m!"CACHE_HIT {label}"
  let audit : CertM reified.rα Unit := do
    check "entry" (Determinant.Compact.coeffEntry true true true 1 2)
    check "iteration" (Determinant.Compact.certIterStepEntry true true true true pure 3 0 0)
    check "diagonal" (Determinant.Compact.certDiag true true true true pure 2 1)
  audit.run' {} |>.run ctx |>.run .reducible
