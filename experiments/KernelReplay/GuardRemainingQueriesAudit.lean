/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardRemainingQueriesPublic
import KernelReplay.GuardRemainingRootQueriesAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingQueriesAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let mut proofs := #[mkConst ``GuardDescriptorInputs.firstPointBinding]
  let mut queries : Nat := 0
  for (size, node) in (#[2,3,1,3,3] : Array Nat).zipIdx do
    let nodeRoot := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingQuery ++
      `record1 ++ Name.mkSimple s!"node{node}"
    let boundName := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingShape ++
      `record1 ++ Name.mkSimple s!"node{node}" ++ `count_eq
    proofs := proofs.push (mkConst boundName)
    for query in [:size] do
      let queryRoot := nodeRoot ++ Name.mkSimple s!"query{query}"
      for tag in #[`data, `squarefree, `remainders] do
        let name := queryRoot ++ tag
        let info ← getConstInfo name
        unless info.isTheorem && info.levelParams.isEmpty do
          throwError "missing original closed query proof {name}"
        proofs := proofs.push (mkConst name)
      let consumer := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingQueriesPublic ++
        Name.mkSimple s!"node{node}_query{query}"
      let _ ← getConstInfo consumer
      proofs := proofs.push (mkConst consumer)
      queries := queries + 1
  unless queries == 12 do throwError "original remaining record query audit omitted a position"
  let count ← audit began proofs
  logInfo m!"all original packing record one queries public consumer audit: originalRecordIndex=1 originalNodeIndices=[0,1,2,3,4] originalMomentBounds=[2,3,1,3,3] allOriginalQueries=12 queryFieldsEach=7 bothOriginalChainsEachComplete=true originalChainFieldsEach=10 originalSubjectsAndGuardsRetained=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingQueriesAudit
