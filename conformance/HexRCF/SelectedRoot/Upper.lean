/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.FrozenCollect
import HexRCF.RealCoefficients.SelectedFormula
import HexRealClosureMathlib.FactReplay

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests.Data
namespace Hex.RCF.SelectedRootTests.Upper
open Hex.RCF.SelectedRootTests

def raw := Frozen.raw

theorem rootAccepted : raw.check parent.sign parent.signature Frozen.tree = true := by
  have accepted := FrozenCollect.accepted
  rw [Frozen.check_eq] at accepted
  exact accepted

def root := Descriptor.ofChecked parent.sign parent.signature raw Frozen.tree rootAccepted

theorem raw_eq : raw = root.raw := rfl

theorem subjectRead : Algebraic.SignRequests.readRoot
    (Algebraic.Element.signCodec base.codec Collect.facts) Tower.Signature.codec
      Literals.upperSubject = .ok raw := by
  have decoded : Frozen.rawRead.toOption = some raw :=
    (Option.some_get Frozen.rawAccepted).symm
  cases hr : Frozen.rawRead with
  | error message => simp only [hr, Except.toOption] at decoded; contradiction
  | ok descriptor =>
    simp only [hr, Except.toOption] at decoded
    exact hr.trans (congrArg Except.ok (Option.some.inj decoded))

def context : Algebraic.Context parent.Value Tower.Signature parent.sign parent.signature :=
  Algebraic.Context.adjoin root parent.isClean

def schema : RealFormula.QF 2 :=
  let x : RealFormula.Poly 2 := MvPoly.X 1
  .and (.atom ⟨x^2-MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨x-1, .gt⟩) (.atom ⟨x-2, .lt⟩))
def values : Fin 1 → parent.Value := fun _ => alpha

/-- info: 'Hex.RCF.SelectedRootTests.Upper.rootAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootAccepted
/-- info: 'Hex.RCF.SelectedRootTests.Upper.subjectRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subjectRead
/-- info: 'Hex.RCF.SelectedRootTests.Upper.raw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_eq
end Hex.RCF.SelectedRootTests.Upper
