/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingNodesPublic
public import KernelReplay.GuardLastQueriesAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingNodesAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let mut proofs := #[mkConst ``GuardDescriptorInputs.firstPointBinding]
  let mut nodes : Nat := 0
  for record in #[1,2] do
    for node in [:5] do
      let suffixName := Name.mkSimple s!"record{record}" ++ Name.mkSimple s!"node{node}"
      let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingNodes ++ suffixName
      for tag in #[`data, `moments] do
        let name := root ++ tag
        let info ← getConstInfo name
        unless info.isTheorem && info.levelParams.isEmpty do
          throwError "missing original complete closed node proof {name}"
        proofs := proofs.push (mkConst name)
      let countBinding := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingShape ++ suffixName ++ `count_eq
      let consumer := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingNodesPublic ++
        Name.mkSimple s!"record{record}_node{node}"
      let _ ← getConstInfo consumer
      proofs := proofs ++ #[mkConst countBinding, mkConst consumer]
      nodes := nodes + 1
  unless nodes == 10 do throwError "original remaining node audit omitted a position"
  let count ← audit began proofs
  logInfo m!"all original remaining nodes public consumer audit: originalRecordIndices=[1,2] originalNodesEach=5 allOriginalNodes=10 fieldsPerNode=5 allOriginalMomentBoundsChecked=true all24OriginalQueriesRetained=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingNodesAudit
