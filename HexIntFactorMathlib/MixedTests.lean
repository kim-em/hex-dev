/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactorMathlib.Mixed
import HexIntFactor.Mixed.Frozen.Small

/-! Proof conformance for unconditional mixed multiplicities and residual overlap. -/

open Hex.Nat.Mixed

example : (578 : Nat).factorization 17 = 2 := by
  have h := Frozen.partialOverlap_checked.factorization_eq 17
  have hp : _root_.Nat.Prime 17 := by decide
  simpa [Frozen.partialOverlap_checked, Frozen.partialOverlap, Frozen.ecpp17, hp.factorization_self] using h

example : (34 : Nat).factorization 17 = 1 := by
  have h := Frozen.small_checked.factorization_eq 17
  simpa [Frozen.small_checked, Frozen.small] using h

example : (34 : Nat).factorization 5 = 0 := by
  have h := Frozen.small_checked.factorization_eq 5
  simpa [Frozen.small_checked, Frozen.small] using h

example : 1 ≤ (578 : Nat).factorization 17 :=
  Frozen.partialOverlap_checked.exponent_le (e := ⟨17, 1, .ecpp Frozen.ecpp17⟩) (by simp [Frozen.partialOverlap_checked, Frozen.partialOverlap])

/-- info: 'Hex.Nat.Mixed.CheckedFactorization.factorization_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Nat.Mixed.CheckedFactorization.factorization_eq

/-- info: 'Hex.Nat.Mixed.CheckedPartialFactorization.factorization_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Nat.Mixed.CheckedPartialFactorization.factorization_eq

/-- info: 'Hex.Nat.Mixed.CheckedFactorization.prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Nat.Mixed.CheckedFactorization.prime

/-- info: 'Hex.Nat.Mixed.CheckedPartialFactorization.primeSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Nat.Mixed.CheckedPartialFactorization.primeSupport

/-- info: 'Hex.Nat.Mixed.CheckedFactorization.multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Nat.Mixed.CheckedFactorization.multiplicity
