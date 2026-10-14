/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Records
import HexRCF.FiniteMatrix.Guards.Binding
open Hex Hex.SignDet Hex.RealClosure Hex.RealClosure.Algebraic
open Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients Hex.RCF.RealCoefficients.FiniteMatrixTests
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data
open Semantics
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

theorem replay : Transport.Finite.ReplayData read Element.sign
    (fun x : ℝ => (SignType.sign x : Int)) FiniteJoint.next.root.raw.head
    FiniteJoint.next.root.raw.lower FiniteJoint.next.root.raw.upper
    (FiniteJoint.next.root.raw.queries ++ Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.allQueries false Packings.facts)
    Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.positive.evidence :=
  Transport.Finite.ReplayData.of_closed read (fun _ => True) closed Element.sign _ _ _ _ _ _
    (Transport.Inventory.replay_data closed _ _ _ _ _ (agreement _))

theorem accepted : FiniteSigns.check FiniteJoint.next (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.positive Packings.facts)
    (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.queries Packings.facts) Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.positive Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.formula =
    .ok true := by decide +kernel

theorem first : read ((Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.positive Packings.facts).get
    ⟨0, by decide +kernel⟩) = Real.sqrt 2 - 1 := (List.cons.inj (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Meaning.values Packings.facts)).1

theorem second : read ((Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.positive Packings.facts).get
    ⟨1, by decide +kernel⟩) = -1 := (List.cons.inj (List.cons.inj (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Meaning.values Packings.facts)).2).1

theorem zero_rejected : FiniteSigns.check FiniteJoint.next (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.guards true Packings.facts)
    (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.queries Packings.facts) Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.zero Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.formula =
    .error .divisor := by decide +kernel

theorem before_constant : FiniteSigns.check FiniteJoint.next (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.guards true Packings.facts)
    (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.queries Packings.facts) Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.zero (.tt : RealFormula.QF 3) =
    .error .divisor := by decide +kernel

open Lean Meta in
run_meta do
  for name in #[``accepted, ``zero_rejected, ``before_constant] do
    let type ← inferType (mkConst name)
    let extra := #[``Descriptor.validate, ``Descriptor.ofReplay?] ++
      (if name == ``accepted then #[] else #[``Samples.Row.eval])
    Hex.RCF.SelectedRootTests.KernelCheck.addChecked (Name.str name "decision") type
      (← mkDecideProof type) extra #[``FiniteSigns.Row.check]
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data
