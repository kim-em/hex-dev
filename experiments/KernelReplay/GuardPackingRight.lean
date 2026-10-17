/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingRightQueries
public meta import KernelReplay.GuardPackingRightQueries
import all KernelReplay.GuardPackingRightQueries
import all KernelReplay.GuardPackingNodeInputs
import all KernelReplay.GuardPackingShape
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRight

private theorem three {p : Fin 3 → Prop} (zero : p 0) (one : p 1) (two : p 2) : ∀ i, p i :=
  Fin.cases zero (Fin.cases one (Fin.cases two (fun i => i.elim0)))

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRight

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRight
open Lean Meta Elab FiniteData GuardDescriptorInputs


set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let mut proofs := #[]
  for nodeIndex in #[3, 4] do
    let name := Name.mkSimple s!"node{nodeIndex}"
    let (target, parts) ← GuardPackingNodeInputs.node nodeIndex
    let family := parts[4]!
    let .forallE _ domain body _ := family | throwError "actual right packing node lost its moment index"
    unless domain.getAppFn.isConstOf ``Fin do throwError "actual right packing moment index changed"
    let countProof := mkConst
      (`Hex.RealClosure.Algebraic.KernelReplay.GuardPackingShape ++ name ++ `count_eq)
    kernelCheck `__packingRightOriginalMomentCount
      (← mkEq domain.getAppArgs.back! (toExpr (3 : Nat))) countProof
    let predicate ← withLocalDeclD `index (← mkAppM ``Fin #[toExpr (3 : Nat)]) fun index =>
      mkLambdaFVars #[index] (body.instantiate1 index)
    let queryRoot := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRightQueries ++ name
    let moments ← mkAppOptM ``three #[some predicate,
      some (mkConst (queryRoot ++ `query0 ++ `data)),
      some (mkConst (queryRoot ++ `query1 ++ `data)),
      some (mkConst (queryRoot ++ `query2 ++ `data))]
    let moments ← withTransparency .all do mkAppOptM ``id #[some family, some moments]
    let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRight ++ name
    let moments ← retain began (root ++ `moments) moments
    let inputRoot := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRightInputs ++ name
    let value := mkAppN (mkConst ``Packing.NodeData.mk target.getAppFn.constLevels!)
      (target.getAppArgs ++ #[mkConst (inputRoot ++ `head), mkConst (inputRoot ++ `preparation),
        mkConst (inputRoot ++ `products), mkConst (inputRoot ++ `reductions), moments])
    let value ← withTransparency .all do mkAppOptM ``id #[some target, some value]
    let complete ← retain began (root ++ `data) value
    proofs := proofs ++ #[complete, moments, countProof]
  logInfo m!"actual first packing right nodes module export: originalNodeIndices=[3,4] fieldsPerNode=5 originalMomentBoundEach=3 allOriginalMomentsAndGuardsRetained=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRight
