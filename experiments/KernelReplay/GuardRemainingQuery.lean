/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingInput09
public import KernelReplay.GuardCoefficientFence
public meta import KernelReplay.GuardRemainingInput09
public meta import KernelReplay.GuardCoefficientFence
import all KernelReplay.GuardRemainingInput09
import all KernelReplay.GuardCoefficientFence
import all KernelReplay.GuardRemainingInputs
import all KernelReplay.GuardRemainingShape
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingQuery
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

/-- The shape census retains these checked data aliases without compiling them.
Expand their bodies before compiling a coefficient that projects from them. -/
private def expandEntries (value : Expr) : MetaM Expr := do
  let mut value := value
  for name in #[``GuardRemainingShape.record1.entry, ``GuardRemainingShape.record2.entry] do
    let .defnInfo info ← getConstInfo name | throwError "packing entry is not checked data"
    value := value.replace fun expression =>
      if expression.isConstOf name then some info.value else none
  return value

syntax (name := remainingQueryControl) "#remaining_packing_query " num num num : command
@[command_elab remainingQueryControl]
unsafe def elaborate : CommandElab := fun stx => liftTermElabM <| withExporting (isExporting := false) do
  let some record := stx[1].isNatLit? | throwError "remaining record index is not literal"
  let some nodeIndex := stx[2].isNatLit? | throwError "remaining node index is not literal"
  let some index := stx[3].isNatLit? | throwError "remaining query index is not literal"
  let began ← IO.getNumHeartbeats
  let setup ← GuardDescriptorInputs.prepare
  let origin ← Base.ofClosed (mkConst ``GuardInventoryReplay.closed)
  let domains ← GuardCoefficientFence.prepare began origin (mkConst ``GuardInventoryReplay.agreement)
    (compileValue := expandEntries)
  let known ← IO.mkRef (#[] : Array KnownLookup)
  let supplier := origin.supply domains (lookupSupplier known FiniteDataProbe.supply)
  let target ← GuardRemainingInputs.query record nodeIndex index
  let parts ← fields target ``Packing.QueryData.mk
  unless parts.size == 7 do throwError "actual remaining packing query fields changed"
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingQuery ++
    Name.mkSimple s!"record{record}" ++ Name.mkSimple s!"node{nodeIndex}" ++
    Name.mkSimple s!"query{index}"
  let _ ← retain began (root ++ `statement) target
  let mut value := mkAppN (mkConst ``Packing.QueryData.mk target.getAppFn.constLevels!) target.getAppArgs
  let mut proofs := #[]
  for (tag, part) in #[`squarefree, `remainders, `order, `lower, `upper, `lowerRows, `upperRows].zip parts do
    let remaining ← bounded began
    logInfo m!"actual remaining packing query begins: record={record} node={nodeIndex} index={index} field={tag} heartbeat={1500000 - remaining}"
    let proof ← if (← getEnv).contains (root ++ tag) then do
        let proof := mkConst (root ++ tag)
        kernelCheck `__sameOriginalRemainingQueryField part proof
        pure proof
      else do
        let proof ← withOptions (maxHeartbeats.set · remaining) do build part supplier
        let proof ← withTransparency .all do mkAppOptM ``id #[some part, some proof]
        retain began (root ++ tag) proof
    proofs := proofs.push proof
    value := mkApp value proof
  let _complete ← retain began (root ++ `data) value
  logInfo m!"actual complete remaining packing query module export: originalRecordIndex={record} originalNodeIndex={nodeIndex} originalQueryIndex={index} fields=7 sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

syntax (name := remainingChainControl) "#remaining_query_chain " num num num num : command
@[command_elab remainingChainControl]
unsafe def elaborateChain : CommandElab := fun stx => liftTermElabM <| withExporting (isExporting := false) do
  let some record := stx[1].isNatLit? | throwError "record index is not literal"
  let some nodeIndex := stx[2].isNatLit? | throwError "node index is not literal"
  let some index := stx[3].isNatLit? | throwError "query index is not literal"
  let some side := stx[4].isNatLit? | throwError "chain index is not literal"
  unless side < 2 do throwError "chain index must select the original squarefree or remainder field"
  let began ← IO.getNumHeartbeats
  let origin ← Base.ofClosed (mkConst ``GuardInventoryReplay.closed)
  let domains ← GuardCoefficientFence.prepare began origin (mkConst ``GuardInventoryReplay.agreement)
    (compileValue := expandEntries)
  let known ← IO.mkRef (#[] : Array KnownLookup)
  let supplier := origin.supply domains (lookupSupplier known FiniteDataProbe.supply)
  let target ← GuardRemainingInputs.query record nodeIndex index
  let parts ← fields target ``Packing.QueryData.mk
  unless parts.size == 7 do throwError "actual remaining query fields changed"
  let part := parts[side]!
  unless part.getAppFn.isConstOf ``Packing.ChainData do throwError "actual query chain changed its predicate"
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingQuery ++
    Name.mkSimple s!"record{record}" ++ Name.mkSimple s!"node{nodeIndex}" ++
    Name.mkSimple s!"query{index}"
  let tag := if side == 0 then `squarefree else `remainders
  let remaining ← bounded began
  let proof ← withOptions (maxHeartbeats.set · remaining) do build part supplier
  let proof ← withTransparency .all do mkAppOptM ``id #[some part, some proof]
  let proof ← retain began (root ++ tag) proof
  logInfo m!"actual complete remaining query chain module export: originalRecordIndex={record} originalNodeIndex={nodeIndex} originalQueryIndex={index} originalSide={side} originalChainFields=10 sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingQuery
