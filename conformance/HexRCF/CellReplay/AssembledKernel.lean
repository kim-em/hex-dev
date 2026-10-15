/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Assembled
import KernelReplay.AxiomClosure
open Hex Lean Meta Hex.RCF.RealCoefficients
set_option maxHeartbeats 2400000
set_option maxRecDepth 32768

namespace Hex.RCF.RealCoefficients.CellReplayTests.AssembledKernel
example : True := Assembled.controlsComplete

/-- A fresh consumer of the actual assembled original-goal proof. -/
theorem witness : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 := by
  obtain ⟨x, lower, upper, _⟩ := Assembled.source
  exact ⟨x, sub_eq_zero.mp (le_antisymm upper lower)⟩

run_meta do
  let .thmInfo declaration ← getConstInfo ``witness
    | throwError "fresh assembled real witness is missing"
  let _ ← Hex.RCF.checkProof ``witness declaration.type declaration.value
  let actual ← Hex.RealClosure.Algebraic.KernelReplay.AxiomClosure.collect
    #[``witness,``Assembled.source]
  unless actual == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "fresh real witness checked-body dependencies changed"
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[``witness]
  for required in #[``Assembled.source,``CellOperations.accept?_iff,
      ``CompleteReplay.check_sound,``Hex.RealClosure.Tower.Model.root,
      ``Hex.RealClosure.Algebraic.Element.replayMul_eq] do
    unless seen.contains required do throwError "fresh real witness omitted actual assembly: {required}"
  for forbidden in Assembled.forbidden do
    if seen.contains forbidden then throwError "fresh witness reused fixture acceptance: {forbidden}"
  logInfo "fresh ordinary-kernel real witness checked from actual record assembly; complete body audit has standard three axioms"
  addDecl (.thmDecl {
    name := `Hex.RCF.RealCoefficients.CellReplayTests.AssembledKernel.auditComplete
    levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })

-- An interrupted audit cannot leave an apparently completed module.
example : True := auditComplete
end Hex.RCF.RealCoefficients.CellReplayTests.AssembledKernel
