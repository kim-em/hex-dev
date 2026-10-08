/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.InverseReplay
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests.Data
namespace Hex.RCF.SelectedRootTests.InverseControls
open Hex.RCF.SelectedRootTests.InverseReplay

def emptyMemo : Array (Dag.Checked base.sign base.signature lower.raw.head
    lower.raw.lower lower.raw.upper) := #[]

/-- A zero original divisor refuses before an empty evidence memo, preserving
preflight even when polynomial simplification could erase the quotient. -/
theorem zero_guard :
    Hex.RCF.RealCoefficients.InverseReplay.check [alpha, 0] alpha packet.entry emptyMemo 0 = .error .divisor := by
  rfl

theorem zero_argument :
    Hex.RCF.RealCoefficients.InverseReplay.check [] (0 : Algebraic.Element native) packet.entry emptyMemo 0 =
      .error .divisor := by
  rfl

theorem missing_evidence :
    Hex.RCF.RealCoefficients.InverseReplay.check [alpha] alpha packet.entry emptyMemo 0 = .error .evidence := by
  have preflight : (!([alpha].all (fun divisor => divisor.sign != 0)) || alpha.sign == 0) =
      false := rfl
  simp only [Hex.RCF.RealCoefficients.InverseReplay.check, preflight, Bool.false_eq_true, ↓reduceIte]
  have hroot : native.root = lower := Algebraic.Context.root_adjoin lower base.isClean
  have absent : SelectedSigns.readMemo? native.root
      [alpha.polynomial, alpha.polynomial * packet.entry.value.polynomial - 1]
      #v[alpha.sign, 0] emptyMemo 0 = none := by
    rw [hroot, SelectedSigns.readMemo_same]
    simp [SelectedSigns.ofMemo?, Dag.select?, emptyMemo]
  unfold Algebraic.Packing.Inverse.Equation.readMemo?
  simp only [absent, bind, Option.bind]

theorem out_of_range :
    Hex.RCF.RealCoefficients.InverseReplay.check [alpha] alpha packet.entry packet.memo packet.memo.size =
      .error .evidence := by
  have preflight : (!([alpha].all (fun divisor => divisor.sign != 0)) || alpha.sign == 0) =
      false := rfl
  simp only [Hex.RCF.RealCoefficients.InverseReplay.check, preflight, Bool.false_eq_true, ↓reduceIte]
  have hroot : native.root = lower := Algebraic.Context.root_adjoin lower base.isClean
  have absent : SelectedSigns.readMemo? native.root
      [alpha.polynomial, alpha.polynomial * packet.entry.value.polynomial - 1]
      #v[alpha.sign, 0] packet.memo packet.memo.size = none := by
    rw [hroot, SelectedSigns.readMemo_same]
    simp [SelectedSigns.ofMemo?, Dag.select?]
  unfold Algebraic.Packing.Inverse.Equation.readMemo?
  simp only [absent, bind, Option.bind]

/-- info: 'Hex.RCF.SelectedRootTests.InverseControls.zero_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_guard
/-- info: 'Hex.RCF.SelectedRootTests.InverseControls.zero_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_argument
/-- info: 'Hex.RCF.SelectedRootTests.InverseControls.missing_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms missing_evidence
/-- info: 'Hex.RCF.SelectedRootTests.InverseControls.out_of_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms out_of_range
end Hex.RCF.SelectedRootTests.InverseControls
