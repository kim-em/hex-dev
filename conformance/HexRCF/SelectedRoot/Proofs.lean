/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SelectedRoot.RowCollect
public import HexRCF.SelectedRoot.Source

public section

namespace Hex.RCF.SelectedRootTests.Proofs
open Hex.RCF.SelectedRootTests

theorem rowAccepted : Row.rowResult RowCollect.facts = .ok true := by
  have accepted := RowCollect.rowAccepted
  unfold Row.rowProgram at accepted
  cases result : Row.rowResult RowCollect.facts with
  | error message =>
    rw [result] at accepted
    change false = true at accepted
    contradiction
  | ok value =>
    cases value with
    | false =>
      rw [result] at accepted
      change false = true at accepted
      contradiction
    | true => rfl

theorem exists_nested : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 :=
  Source.source RowCollect.facts rowAccepted

/-- info: 'Hex.RCF.SelectedRootTests.Proofs.rowAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowAccepted
/-- info: 'Hex.RCF.SelectedRootTests.Proofs.exists_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nested
end Hex.RCF.SelectedRootTests.Proofs
