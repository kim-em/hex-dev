/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Context
import HexRealClosureTheory.SignEvidence
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Fields
open Hex.RCF.RealCoefficients.NestedTransportTests.Context
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
theorem fields (required : List (DensePoly Data.parent.Value))
    (evidence : Algebraic.SignEvidence Data.parent.Value Signature)
    (facts : Vector (Algebraic.SignFact native) required.length)
    (accepted : native.readEvidence? Data.original.value Data.original.zero_iff Data.original.one
      Data.original.add Data.original.sub Data.original.mul Data.original.nat Data.original.sign
      Data.original.neg Data.original.inv required evidence = some facts)
    (i : Fin required.length) :
    facts[i.val].polynomial = required[i.val] ∧
      some facts[i.val].sign = evidence.values.toList[i.val]? := by
  obtain ⟨signs, checked, equal⟩ := native.readEvidence_evidence Data.original.value
    Data.original.zero_iff Data.original.one Data.original.add Data.original.sub Data.original.mul
    Data.original.nat Data.original.sign Data.original.neg Data.original.inv required evidence facts accepted
  obtain ⟨same, selected⟩ := evidence.check_evidence native required signs checked
  cases same
  obtain ⟨tree, _, values, _⟩ := Dag.selectedSigns_evidence selected
  have literal := native.signFacts_fields Data.original.value Data.original.zero_iff Data.original.one
    Data.original.add Data.original.sub Data.original.mul Data.original.nat Data.original.sign
    Data.original.neg Data.original.inv signs i
  rw [equal]
  refine ⟨literal.1, (congrArg some literal.2).trans ?_⟩
  have point := congrArg (fun v : Vector Int evidence.queries.length => some v[i.val]) values
  exact point.trans (by simp [i.isLt])
end Hex.RCF.RealCoefficients.NestedTransportTests.Fields
