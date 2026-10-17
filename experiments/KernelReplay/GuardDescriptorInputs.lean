/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardInventoryReplay
public meta import KernelReplay.GuardInventoryReplay
import all KernelReplay.GuardInventoryReplay
import all KernelReplay.FrameJoint

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorInputs
open Lean Meta Elab Command FiniteData

def bounded (began : Nat) : MetaM Nat := do
  Core.checkSystem "actual descriptor input proofs"
  let used := ((← IO.getNumHeartbeats) - began) / 1000
  if used ≥ 1500000 then throwError "aggregate descriptor input budget exhausted"
  return 1500000 - used

def retain (began : Nat) (name : Name) (value : Expr) : MetaM Expr := do
  let type ← inferType value
  for expression in #[value, type] do
    if expression.hasMVar || expression.hasFVar || expression.hasSorry then
      throwError "incomplete descriptor input declaration"
  let declaration ← if ← isProp type then
      pure (Declaration.thmDecl { name, levelParams := [], type, value })
    else pure (Declaration.defnDecl {
      name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  return mkConst name

/-- Inspect independent structure fields without supplying any proof. -/
def fields (type : Expr) (constructor : Name) : MetaM (Array Expr) := do
  let value := mkAppN (mkConst constructor type.getAppFn.constLevels!) type.getAppArgs
  let mut signature ← inferType value
  let mut result := #[]
  for _ in [:16] do
    signature ← whnf signature
    let .forallE _ field body _ := signature | return result
    if body.hasLooseBVars then throwError "dependent descriptor structure field"
    result := result.push field
    signature := body
  throwError "descriptor structure exceeds the fixed field bound"

structure Setup where
  first : Prefix
  supplier : Supplier
  context : Expr
  target : Expr
  nativeType : Expr
  nativeFields : Array Expr
  nodeType : Expr
  nodeFields : Array Expr

/-- Use the exact first prefix and actual captured second descriptor. -/
def prepare : MetaM Setup := do
  let closed := mkConst ``GuardInventoryReplay.closed
  let origin ← Base.ofClosed closed
  let zero ← mkAppM ``Transport.Closed.read_zero #[closed]
  let unit ← mkAppM ``Transport.Closed.read_one #[closed]
  let first ← Prefix.ofData (mkConst ``GuardInventoryReplay.firstData) zero unit
  let cache ← IO.mkRef (none : Option CoefficientWalk)
  let domains := origin.domains
    (agreementSupplier (mkConst ``GuardInventoryReplay.agreement) (some cache))
  let known ← IO.mkRef (#[] : Array KnownLookup)
  let supplier := origin.supply domains (lookupSupplier known FiniteDataProbe.supply)
  let source := (← getConstInfo ``GuardCapture.second.data).type.getAppArgs
  let context := source[source.size - 5]!
  let data ← mkAppM ``Packing.Inventory.Data
    #[context, mkConst ``GuardInventoryReplay.second.entries,
      mkConst ``GuardInventoryReplay.second.records, mkConst ``GuardInventoryReplay.second.facts,
      first.reader]
  let dataFields ← fields data ``Packing.Inventory.Data.mk
  unless dataFields.size == 4 do throwError "actual second inventory fields changed"
  let target := dataFields[0]!
  unless target.getAppFn.isConstOf ``Transport.Finite.DescriptorData do
    throwError "actual second descriptor target changed"
  let arguments := target.getAppArgs
  let nativeType ← mkAppM ``Packing.DescriptorData
    #[first.entries, first.records, first.read, arguments[arguments.size - 2]!, arguments.back!]
  let nativeFields ← fields nativeType ``Packing.DescriptorData.mk
  unless nativeFields.size == 3 do throwError "native descriptor fields changed"
  let nodeType ← withOptions (smartUnfolding.set · true) do
    withTransparency .all (whnf nativeFields[2]!)
  unless nodeType.getAppFn.isConstOf ``Packing.NodeData do
    throwError "actual second descriptor is not the expected single complete replay node"
  let nodeFields ← fields nodeType ``Packing.NodeData.mk
  unless nodeFields.size == 5 do throwError "actual second node fields changed"
  for type in nativeFields ++ nodeFields do
    if type.hasMVar || type.hasFVar || type.hasLooseBVars || type.hasSorry then
      throwError "incomplete actual second descriptor field type"
  return ⟨first, supplier, context, target, nativeType, nativeFields, nodeType, nodeFields⟩

private def dependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo info => info.type.getUsedConstants
  | .defnInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
  | .thmInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
  | .opaqueInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
  | .ctorInfo info => info.type.getUsedConstants
  | .recInfo info => info.type.getUsedConstants
  | .inductInfo info => info.type.getUsedConstants ++ info.ctors.toArray
  | .quotInfo _ => #[]

/-- Audit complete checked proof bodies, including every predecessor premise. -/
def audit (began : Nat) (proofs : Array Expr) : MetaM Nat := do
  let roots := proofs.flatMap Expr.getUsedConstants
  let axioms ← AxiomClosure.collect roots
  unless axioms == (#[`propext, `Classical.choice, `Quot.sound].qsort Name.lt) do
    throwError "actual descriptor inputs changed axiom closure"
  let forbidden := #[`Hex.RealClosure.BaseContext.PackedContext.Realization.reference,
    `Hex.RealClosure.Ambient.ofField, `Hex.RealClosure.Ambient.exists_ambient,
    `TauCeti.RealClosure.exists_realClosure]
  let environment := (← getEnv).checked.get
  let initial := roots.foldl (fun found name => found.insert name) ({} : NameSet)
  let mut queue := initial.toArray
  let mut queued := initial
  let mut cursor := 0
  while cursor < queue.size do
    let _ ← bounded began
    if queue.size > 150000 then throwError "descriptor input dependency bound exhausted"
    let name := queue[cursor]!
    cursor := cursor + 1
    if forbidden.contains name then throwError "descriptor input retained whole-field construction {name}"
    let some info := environment.find? name | throwError "missing descriptor input checked body {name}"
    if info.isUnsafe || info.isPartial then throwError "unsafe descriptor input dependency {name}"
    for dependency in dependencies info do
      unless queued.contains dependency do
        queued := queued.insert dependency
        queue := queue.push dependency
  return cursor

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let setup ← prepare
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorInputs
  let pointEquation ← mkEq setup.first.point (mkConst ``GuardInventoryReplay.firstPoint)
  let typedBinding ← withTransparency .all do
    mkAppOptM ``id #[some pointEquation, some (← mkEqRefl (mkConst ``GuardInventoryReplay.firstPoint))]
  let pointBinding ← retain began (root ++ `firstPointBinding) typedBinding
  let mut proofs := #[pointBinding]
  for (tag, type) in #[(`derivatives, setup.nativeFields[0]!), (`head, setup.nativeFields[1]!),
      (`nodeHead, setup.nodeFields[0]!), (`preparation, setup.nodeFields[1]!),
      (`products, setup.nodeFields[2]!)] do
    let remaining ← bounded began
    logInfo m!"actual descriptor input begins: field={tag} heartbeat={1500000 - remaining}"
    let proof ← withOptions (maxHeartbeats.set · remaining) do build type setup.supplier
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    logInfo m!"actual descriptor input checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  logInfo m!"actual descriptor input module export: fields=5 sameFirstPointChecked=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorInputs
