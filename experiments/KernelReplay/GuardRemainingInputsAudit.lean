/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardRemainingInput09
import KernelReplay.GuardRemainingControlAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingInputsAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let mut proofs := #[mkConst ``GuardDescriptorInputs.firstPointBinding]
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingInputs
  let mut inputFields : Nat := 0
  for record in #[1, 2] do
    for node in [:5] do
      let prefixName := root ++ Name.mkSimple s!"record{record}" ++ Name.mkSimple s!"node{node}"
      for tag in #[`head, `preparation, `products, `reductions] do
        let name := prefixName ++ tag
        let info ← getConstInfo name
        unless info.isTheorem && info.levelParams.isEmpty do
          throwError "original remaining input field was not retained as a closed checked theorem: {name}"
        proofs := proofs.push (mkConst name)
        inputFields := inputFields + 1
  unless inputFields == 40 do throwError "remaining input audit omitted an original field"
  let count ← audit began proofs
  logInfo m!"all original remaining packing node inputs module audit: originalRecordIndices=[1,2] originalNodesEach=5 inputFieldsEach=4 allOriginalInputFields=40 originalGuardsRetained=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingInputsAudit
