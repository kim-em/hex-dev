/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Selected
import HexRCF.FiniteMatrix.Binding
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Data
open Hex Hex.SignDet Hex.RealClosure Hex.RealClosure.Algebraic
open Hex.RealClosure.Algebraic.KernelReplay Semantics
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

theorem descriptor : Transport.Finite.DescriptorData read Element.sign
    (fun x : ℝ => (SignType.sign x : Int)) FiniteJoint.next.root.raw FiniteJoint.next.root.evidence :=
  Transport.Finite.DescriptorData.of_closed read (fun _ => True) closed Element.sign _ _ _
    (Transport.Inventory.descriptor_data closed _ _ (agreement _))

def selected (guarded : Bool) : SelectedSigns FiniteJoint.next.root
    (Schema.allQueries guarded Packings.facts) :=
  match guarded with
  | false => Selected.canonical
  | true => Selected.guarded

theorem replay (guarded : Bool) : Transport.Finite.ReplayData read Element.sign
    (fun x : ℝ => (SignType.sign x : Int)) FiniteJoint.next.root.raw.head
    FiniteJoint.next.root.raw.lower FiniteJoint.next.root.raw.upper
    (FiniteJoint.next.root.raw.queries ++ Schema.allQueries guarded Packings.facts)
    (selected guarded).evidence :=
  Transport.Finite.ReplayData.of_closed read (fun _ => True) closed Element.sign _ _ _ _ _ _
    (Transport.Inventory.replay_data closed _ _ _ _ _ (agreement _))

theorem accepted (guarded : Bool) : FiniteSigns.check FiniteJoint.next
    (Schema.guards guarded Packings.facts) (Schema.queries Packings.facts) (selected guarded)
    Schema.formula = .ok true := by cases guarded <;> decide +kernel

theorem guardIdentity : read (Schema.guard Packings.facts) = (2 : ℝ) - 1 := by
  unfold Schema.guard
  erw [Element.replayOne_eq]
  change read (1 : Element FiniteTower.first) = 2 - 1
  rw [Transport.Closed.read_one closed]
  norm_num

/-- The same packet gives a false point for the negated matrix. -/
theorem falseAccepted : FiniteSigns.check FiniteJoint.next
    (Schema.guards false Packings.facts) (Schema.queries Packings.facts) (selected false)
    (RealFormula.QF.not Schema.formula) = .ok false := by decide +kernel

theorem falsePoint : ∃ x : ℝ, ¬ (RealFormula.QF.not Schema.formula).toProp
    (RealFormula.append Binding.valuation x) :=
  FiniteSigns.check_false FiniteJoint.next read zero (Transport.Closed.read_one closed)
    descriptor (Schema.guards false Packings.facts) (Schema.queries Packings.facts)
    (selected false) (replay false) Binding.valuation (RealFormula.QF.not Schema.formula)
    (fun x => by simpa only [RealFormula.QF.polys_not] using Binding.bind Packings.facts x)
    falseAccepted

open Lean Meta Elab Command in
elab "#finite_matrix_accepted" : command => liftTermElabM do
  for guarded in [false, true] do
    let proof ← mkAppM ``accepted #[toExpr guarded]
    let type ← inferType proof
    -- Rebuild the actual decision, so an earlier `decide` auxiliary cannot hide production.
    Hex.RCF.SelectedRootTests.KernelCheck.addChecked
      (Name.str `Hex.RCF.RealCoefficients.FiniteMatrixTests.Data s!"accepted{guarded}") type
      (← mkDecideProof type) #[``Descriptor.validate, ``Descriptor.ofReplay?]
      #[``FiniteSigns.Row.check]
open Lean Meta in
run_meta do
  let type ← inferType (mkConst ``falseAccepted)
  Hex.RCF.SelectedRootTests.KernelCheck.addChecked
    `Hex.RCF.RealCoefficients.FiniteMatrixTests.Data.falseDecision type
    (← mkDecideProof type) #[``Descriptor.validate, ``Descriptor.ofReplay?] #[``FiniteSigns.Row.check]
#finite_matrix_accepted
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Data
