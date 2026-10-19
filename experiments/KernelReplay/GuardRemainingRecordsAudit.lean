/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardRemainingRecordsPublic
import KernelReplay.GuardRemainingNodesAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRecordsAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let mut proofs := #[mkConst ``GuardDescriptorInputs.firstPointBinding,
    mkConst ``GuardDescriptorPoint.spec]
  let mut records : Nat := 0
  for record in #[1,2] do
    let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRecords ++
      Name.mkSimple s!"record{record}"
    for tag in #[`nativeReplay, `replay, `difference, `data] do
      let name := root ++ tag
      let _ ← getConstInfo name
      proofs := proofs.push (mkConst name)
    for tag in #["position", "data", "value"] do
      let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRecordsPublic ++
        Name.mkSimple s!"{tag}{record}"
      let _ ← getConstInfo name
      proofs := proofs.push (mkConst name)
    records := records + 1
  unless records == 2 do throwError "original packing record audit omitted an entry"
  let count ← audit began proofs
  logInfo m!"complete original remaining packing records public consumer audit: originalSecondInventoryIndices=[1,2] originalInventoryPositionsChecked=true fullOriginalReplayNodesEach=5 everyOriginalSplitChildAndMomentRetained=true originalReplayAndDifferenceChecked=true valueAndSignAtSameSecondPointChecked=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRecordsAudit
