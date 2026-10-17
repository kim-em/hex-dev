/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingBranchQueries
public meta import KernelReplay.GuardPackingBranchQueries
import all KernelReplay.GuardPackingBranchQueries
import all KernelReplay.GuardPackingNodeInputs
import all KernelReplay.GuardPackingShape
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranch

private theorem three {p : Fin 3 → Prop} (zero : p 0) (one : p 1) (two : p 2) : ∀ i, p i :=
  Fin.cases zero (Fin.cases one (Fin.cases two (fun i => i.elim0)))

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranch

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranch
open Lean Meta Elab FiniteData GuardDescriptorInputs


set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let (target, parts) ← GuardPackingNodeInputs.node 1
  let family := parts[4]!
  let .forallE _ domain body _ := family | throwError "actual first packing branch lost its moment index"
  unless domain.getAppFn.isConstOf ``Fin do throwError "actual packing branch moment index changed"
  kernelCheck `__packingBranchOriginalMomentCount
    (← mkEq domain.getAppArgs.back! (toExpr (3 : Nat)))
    (mkConst ``GuardPackingShape.node1.count_eq)
  let predicate ← withLocalDeclD `index (← mkAppM ``Fin #[toExpr (3 : Nat)]) fun index =>
    mkLambdaFVars #[index] (body.instantiate1 index)
  let moments ← mkAppOptM ``three #[some predicate,
    some (mkConst ``GuardPackingBranchQueries.query0.data),
    some (mkConst ``GuardPackingBranchQueries.query1.data),
    some (mkConst ``GuardPackingBranchQueries.query2.data)]
  let moments ← withTransparency .all do mkAppOptM ``id #[some family, some moments]
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranch
  let moments ← retain began (root ++ `moments) moments
  let value := mkAppN (mkConst ``Packing.NodeData.mk target.getAppFn.constLevels!)
    (target.getAppArgs ++ #[mkConst ``GuardPackingBranchInputs.head,
      mkConst ``GuardPackingBranchInputs.preparation, mkConst ``GuardPackingBranchInputs.products,
      mkConst ``GuardPackingBranchInputs.reductions, moments])
  let value ← withTransparency .all do mkAppOptM ``id #[some target, some value]
  let _complete ← retain began (root ++ `data) value
  logInfo m!"actual first packing branch node module export: originalNodeIndex=1 fields=5 originalMomentBound=3 allOriginalMomentsAndGuardsRetained=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranch
