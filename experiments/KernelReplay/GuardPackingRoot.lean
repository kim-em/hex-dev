/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingQueries
public meta import KernelReplay.GuardPackingQueries
import all KernelReplay.GuardPackingQueries
import all KernelReplay.GuardPackingNodeInputs
import all KernelReplay.GuardPackingShape
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRoot

private theorem two {p : Fin 2 → Prop} (zero : p 0) (one : p 1) : ∀ i, p i :=
  Fin.cases zero (Fin.cases one (fun i => i.elim0))

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRoot

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRoot
open Lean Meta Elab FiniteData GuardDescriptorInputs


set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let (target, parts) ← GuardPackingNodeInputs.node 0
  let family := parts[4]!
  let .forallE _ domain body _ := family | throwError "actual first packing root lost its moment index"
  unless domain.getAppFn.isConstOf ``Fin do throwError "actual packing root moment index changed"
  kernelCheck `__packingRootOriginalMomentCount
    (← mkEq domain.getAppArgs.back! (toExpr (2 : Nat)))
    (mkConst ``GuardPackingShape.node0.count_eq)
  let predicate ← withLocalDeclD `index (← mkAppM ``Fin #[toExpr (2 : Nat)]) fun index =>
    mkLambdaFVars #[index] (body.instantiate1 index)
  let moments ← mkAppOptM ``two #[some predicate,
    some (mkConst ``GuardPackingQueries.query0.data),
    some (mkConst ``GuardPackingQueries.query1.data)]
  let moments ← withTransparency .all do mkAppOptM ``id #[some family, some moments]
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRoot
  let moments ← retain began (root ++ `moments) moments
  let value := mkAppN (mkConst ``Packing.NodeData.mk target.getAppFn.constLevels!)
    (target.getAppArgs ++ #[mkConst ``GuardPackingNodeInputs.head,
      mkConst ``GuardPackingNodeInputs.preparation, mkConst ``GuardPackingNodeInputs.products,
      mkConst ``GuardPackingNodeInputs.reductions, moments])
  let value ← withTransparency .all do mkAppOptM ``id #[some target, some value]
  let _complete ← retain began (root ++ `data) value
  logInfo m!"actual first packing root node module export: fields=5 originalMomentBound=2 allOriginalMomentsAndGuardsRetained=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRoot
