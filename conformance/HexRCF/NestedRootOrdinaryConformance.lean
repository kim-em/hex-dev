/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedRootProduceConformance
import HexRCF.ProofEvidence
open Lean Meta
namespace Hex.RCF.RealCoefficients.NestedRootOrdinaryConformance
theorem source : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := Hex.RCF.RealCoefficients.NestedRootProduceConformance.source
/-- info: 'Hex.RCF.RealCoefficients.NestedRootOrdinaryConformance.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source
run_meta do
  for name in #[``Hex.RCF.RealCoefficients.NestedRootProduceConformance.source, ``Hex.RCF.RealCoefficients.NestedRootProduceConformance.root_sound, ``Hex.RCF.RealCoefficients.NestedRootOrdinaryConformance.source] do
    let axioms ← collectAxioms name
    unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "nested root source has a forbidden axiom"
end Hex.RCF.RealCoefficients.NestedRootOrdinaryConformance
