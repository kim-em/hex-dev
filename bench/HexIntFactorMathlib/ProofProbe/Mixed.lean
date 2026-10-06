/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactorMathlib.Mixed
public import HexIntFactor.Mixed.Frozen.CaseA
public import HexIntFactor.Mixed.Frozen.CaseB
public import HexIntFactor.Mixed.Frozen.Partial

public section

/-! Mathematical clients of the frozen mixed acceptance corpus. -/

open Hex.Nat.Mixed Hex.IntFactorMixedFrozen

example (p : Nat) :
    caseA.subject.factorization p =
      (caseA.factors.find? fun e => e.prime == p).elim 0 (·.exponent) :=
  caseA_checked.factorization_eq p

example (p : Nat) :
    caseB.subject.factorization p =
      (caseB.factors.find? fun e => e.prime == p).elim 0 (·.exponent) :=
  caseB_checked.factorization_eq p

example (p : Nat) :
    partial.subject.factorization p =
      (partial.factors.find? fun e => e.prime == p).elim 0 (·.exponent) +
        partial.residual.factorization p :=
  partial_checked.factorization_eq p

/-- info: 'Hex.Nat.Mixed.CheckedFactorization.factorization_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Nat.Mixed.CheckedFactorization.factorization_eq

/-- info: 'Hex.Nat.Mixed.CheckedPartialFactorization.factorization_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.Nat.Mixed.CheckedPartialFactorization.factorization_eq
