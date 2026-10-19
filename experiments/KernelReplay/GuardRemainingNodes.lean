/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingProof23
public meta import KernelReplay.GuardRemainingProof23
import all KernelReplay.GuardRemainingProof23
import all KernelReplay.GuardRemainingQuery
import all KernelReplay.GuardRemainingInputs
import all KernelReplay.GuardRemainingShape
import all KernelReplay.GuardDescriptorInputs

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingNodes

private theorem single {p : Fin 1 → Prop} (zero : p 0) : ∀ i, p i :=
  Fin.cases zero (fun i => i.elim0)

private theorem two {p : Fin 2 → Prop} (zero : p 0) (one : p 1) : ∀ i, p i :=
  Fin.cases zero (Fin.cases one (fun i => i.elim0))

private theorem three {p : Fin 3 → Prop} (zero : p 0) (one : p 1) (two : p 2) : ∀ i, p i :=
  Fin.cases zero (Fin.cases one (Fin.cases two (fun i => i.elim0)))

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingNodes

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingNodes
open Lean Meta Elab FiniteData GuardDescriptorInputs


def assemble (record : Nat) : MetaM Unit := withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let recordName := Name.mkSimple s!"record{record}"
  let mut proofs := #[]
  for (size, nodeIndex) in (#[2, 3, 1, 3, 3] : Array Nat).zipIdx do
    let name := recordName ++ Name.mkSimple s!"node{nodeIndex}"
    let (target, parts) ← GuardRemainingInputs.node record nodeIndex
    let family := parts[4]!
    let .forallE _ domain body _ := family | throwError "remaining packing node lost its moment index"
    unless domain.getAppFn.isConstOf ``Fin do throwError "remaining packing moment index changed"
    let countProof := mkConst
      (`Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingShape ++ name ++ `count_eq)
    kernelCheck `__remainingOriginalMomentCount
      (← mkEq domain.getAppArgs.back! (toExpr size)) countProof
    let predicate ← withLocalDeclD `index (← mkAppM ``Fin #[toExpr size]) fun index =>
      mkLambdaFVars #[index] (body.instantiate1 index)
    let queryRoot := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingQuery ++ name
    let data := (Array.range size).map fun index =>
      mkConst (queryRoot ++ Name.mkSimple s!"query{index}" ++ `data)
    let rule := if size == 1 then ``single else if size == 2 then ``two else ``three
    let moments ← mkAppOptM rule (#[some predicate] ++ data.map some)
    let moments ← withTransparency .all do mkAppOptM ``id #[some family, some moments]
    let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingNodes ++ name
    let moments ← retain began (root ++ `moments) moments
    let inputRoot := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingInputs ++ name
    let value := mkAppN (mkConst ``Packing.NodeData.mk target.getAppFn.constLevels!)
      (target.getAppArgs ++ #[mkConst (inputRoot ++ `head), mkConst (inputRoot ++ `preparation),
        mkConst (inputRoot ++ `products), mkConst (inputRoot ++ `reductions), moments])
    let value ← withTransparency .all do mkAppOptM ``id #[some target, some value]
    let complete ← retain began (root ++ `data) value
    proofs := proofs ++ #[complete, moments, countProof]
  logInfo m!"actual remaining packing nodes module export: originalRecordIndex={record} fullOriginalNodes=5 fieldsPerNode=5 originalMomentBounds=[2,3,1,3,3] allOriginalMomentsAndGuardsRetained=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta assemble 1

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta assemble 2

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingNodes
