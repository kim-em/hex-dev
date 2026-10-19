/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardMomentAll
public meta import KernelReplay.GuardMomentAll
import all KernelReplay.GuardMomentAll
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorReductions
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorPoint
open Lean Meta Elab FiniteData GuardDescriptorInputs

private def typed (type value : Expr) : MetaM Expr := withTransparency .all do
  mkAppOptM ``id #[some type, some value]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let setup ← GuardDescriptorInputs.prepare
  let first := setup.first
  kernelCheck `__descriptorSameFirstPoint
    (← mkEq first.point (mkConst ``GuardInventoryReplay.firstPoint))
    (mkConst ``GuardDescriptorInputs.firstPointBinding)
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorPoint
  let _ ← retain began (root ++ `predecessor) first.reader
  let mut node := mkAppN (mkConst ``Packing.NodeData.mk setup.nodeType.getAppFn.constLevels!)
    setup.nodeType.getAppArgs
  for (type, name) in setup.nodeFields.zip #[``GuardDescriptorInputs.nodeHead,
      ``GuardDescriptorInputs.preparation, ``GuardDescriptorInputs.products,
      ``GuardDescriptorReductions.reductions, ``GuardMomentAll.moments] do
    node := mkApp node (← typed type (mkConst name))
  let checkedNode ← retain began (root ++ `nodeData) (← typed setup.nodeType node)
  let native := mkAppN
    (mkConst ``Packing.DescriptorData.mk setup.nativeType.getAppFn.constLevels!)
    (setup.nativeType.getAppArgs ++ #[mkConst ``GuardDescriptorInputs.derivatives,
      mkConst ``GuardDescriptorInputs.head, ← typed setup.nativeFields[2]! checkedNode])
  let native ← retain began (root ++ `nativeData) (← typed setup.nativeType native)
  let arguments := setup.target.getAppArgs
  let raw := arguments[arguments.size - 2]!
  let evidence := arguments.back!
  let descriptor ← mkAppM ``Packing.lift_descriptor
    #[first.entries, first.records, first.read, first.zero, first.unit,
      first.descriptor, first.packings, first.signs, raw, evidence, native]
  let descriptor ← retain began (root ++ `descriptorData) (← typed setup.target descriptor)
  logInfo m!"actual complete second descriptor kernel checked: heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  let zero ← retain began (root ++ `zero)
    (← mkAppM ``Context.finiteRead_zero
      #[first.context, first.read, first.zero, first.unit, first.descriptor])
  let unitLemma ← mkAppM ``Context.finiteRead_one
    #[first.context, first.read, first.zero, first.unit, first.descriptor,
      first.entries, first.packings]
  let .forallE _ key _ _ ← inferType unitLemma | throwError "actual first reader has no unit lookup guard"
  let unitKey ← build key setup.supplier
  let unit ← retain began (root ++ `unit) (mkApp unitLemma unitKey)
  let point ← retain began (root ++ `point)
    (← mkAppM ``Context.finitePoint #[setup.context, first.reader, zero, unit, descriptor])
  let spec ← retain began (root ++ `spec)
    (← mkAppM ``Context.finitePoint_spec #[first.reader, zero, unit, descriptor])
  let reader ← retain began (root ++ `reader)
    (← mkAppM ``Context.finiteRead #[setup.context, first.reader, zero, unit, descriptor])
  logInfo m!"actual second selected point module export: completeOriginalDescriptor=true sameFirstPointChecked=true rootIntervalAndThomSpecChecked=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorPoint
