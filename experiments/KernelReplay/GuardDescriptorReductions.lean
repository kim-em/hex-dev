/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardCoefficientIndex
public meta import KernelReplay.GuardCoefficientIndex
import all KernelReplay.GuardCoefficientIndex
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorReductions
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

syntax (name := descriptorReductionControl) "#descriptor_reduction_control" : command
@[command_elab descriptorReductionControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let setup ← prepare
  let closed := mkConst ``GuardInventoryReplay.closed
  let origin ← Base.ofClosed closed
  let agreement := mkConst ``GuardInventoryReplay.agreement
  let indexed ← GuardCoefficientIndex.prepare began agreement
  let walk ← IO.mkRef (none : Option CoefficientWalk)
  let fallback := agreementSupplier agreement (some walk)
  let domains := origin.domains (fun type => do
    if let some proof ← indexed type then return some proof
    fallback type)
  let known ← IO.mkRef (#[] : Array KnownLookup)
  let baseSupplier := origin.supply domains (lookupSupplier known FiniteDataProbe.supply)
  let pointEquation ← mkEq setup.first.point (mkConst ``GuardInventoryReplay.firstPoint)
  kernelCheck `__retainedFirstDescriptorPoint pointEquation
    (mkConst ``GuardDescriptorInputs.firstPointBinding)
  let environment ← getEnv
  let checked := environment.checked.get
  let candidates := checked.constants.fold (fun found name info =>
    if info.isTheorem && info.type.getAppFn.isConstOf ``Eq &&
        info.type.getAppArgs[0]!.isConstOf ``Bool &&
        info.type.getAppArgs.back!.isConstOf ``Bool.true then found.push name else found) (#[] : Array Name)
  let mut pool : PHashMap Expr Expr := {}
  let mut poolProofs : Array Expr := #[]
  for name in candidates do
    let _ ← bounded began
    let some index := environment.getModuleIdxFor? name | continue
    unless environment.header.moduleNames[index.toNat]! == `KernelReplay.GuardDescriptorInputs do
      continue
    let info ← getConstInfo name
    unless info.levelParams.isEmpty do continue
    pool := pool.insert info.type (mkConst name)
    poolProofs := poolProofs.push (mkConst name)
  let facts := pool
  let hits ← IO.mkRef (0 : Nat)
  let supplier : Supplier := fun type => do
    if !type.hasFVar && !type.hasMVar then
      if let some proof := facts.find? type then
        let remaining ← bounded began
        withOptions (maxHeartbeats.set · remaining) do
          kernelCheck `__retainedDescriptorLookup type proof
        hits.modify (· + 1)
        return some proof
    baseSupplier type
  logInfo m!"actual second descriptor reductions begin: retainedClosedLookupProofs={poolProofs.size}"
  let remaining ← bounded began
  let proof ← withOptions (maxHeartbeats.set · remaining) do build setup.nodeFields[3]! supplier
  let proof ← retain began
    `Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorReductions.reductions proof
  logInfo m!"actual descriptor reductions module export: sameFirstPointChecked=true retainedClosedLookupProofs={poolProofs.size} reusedLookups={← hits.get} dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#descriptor_reduction_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorReductions
