/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Data
import HexRCF.ProofEvidence
open Hex Hex.RealClosure Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients Hex.RCF.RealCoefficients.FiniteMatrixTests
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Domains
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

theorem signs : FiniteSigns.guardSigns FiniteJoint.next
    (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.positive Hex.RCF.RealCoefficients.FiniteMatrixTests.Packings.facts)
    (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.queries Hex.RCF.RealCoefficients.FiniteMatrixTests.Packings.facts) Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.positive = [1, -1] := by
  decide +kernel

theorem original : Real.sqrt 2 - 1 ≠ 0 ∧ (-1 : ℝ) ≠ 0 := by
  have domain := FiniteSigns.check_domains FiniteJoint.next Semantics.read Semantics.zero
    (Transport.Closed.read_one Semantics.closed) Hex.RCF.RealCoefficients.FiniteMatrixTests.Data.descriptor
    (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.positive Hex.RCF.RealCoefficients.FiniteMatrixTests.Packings.facts)
    (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.queries Hex.RCF.RealCoefficients.FiniteMatrixTests.Packings.facts) Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.positive
    Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.replay Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.formula true Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.accepted
  constructor
  · have first := domain ((Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.positive Hex.RCF.RealCoefficients.FiniteMatrixTests.Packings.facts).get
      ⟨0, by decide +kernel⟩) (List.get_mem _ _)
    simpa only [Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.first] using first
  · have second := domain ((Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.positive Hex.RCF.RealCoefficients.FiniteMatrixTests.Packings.facts).get
      ⟨1, by decide +kernel⟩) (List.get_mem _ _)
    simpa only [Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.second] using second

open Lean Meta in
run_meta do
  let type ← inferType (mkConst ``signs)
  Hex.RCF.SelectedRootTests.KernelCheck.addChecked `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Domains.signDecision type
    (← mkDecideProof type) #[``Hex.SignDet.Descriptor.validate, ``Hex.SignDet.Descriptor.ofReplay?]
    #[``FiniteSigns.guardSigns]
  let .thmInfo info ← getConstInfo ``original | throwError "expected original divisor theorem"
  let _ ← Hex.RCF.checkProof ``original info.type info.value
  unless ← Hex.RCF.ProofEvidence.contains ``original (fun e => e.isConstOf ``FiniteSigns.check_domains) do
    throwError "original divisor proof omitted the actual joint checker law"
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Domains
