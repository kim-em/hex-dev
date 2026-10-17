/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardNativeFrontier
public meta import KernelReplay.GuardNativeBindings
public meta import KernelReplay.GuardRecordStore
import all KernelReplay.GuardNativeBindings
import all KernelReplay.GuardNativeFrontier
import all KernelReplay.FrameJoint
import all HexSignDet.QueryHandle
import all HexSignDet.SelectedSigns

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRecordReplay
open Lean Meta Elab Command FiniteData

private def bounded (began : Nat) : MetaM Nat := do
  Core.checkSystem "original native inventory replay"
  let used := ((← IO.getNumHeartbeats) - began) / 1000
  if used ≥ 1500000 then throwError "aggregate inventory replay budget exhausted"
  return 1500000 - used

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

private def factList (roots : Array Name) (owner : Expr) : MetaM Expr := do
  let type ← withTransparency .all (whnf (← inferType owner))
  let expected := mkAppN (mkConst ``SignFact type.getAppFn.constLevels!) (type.getAppArgs.push owner)
  let mut facts : Array Expr := #[]
  for name in roots do
    if ← withTransparency .all (isDefEq (← getConstInfo name).type expected) then
      facts := facts.push (mkConst name)
  unless !facts.isEmpty do throwError "native inventory owner has no proved scalar facts"
  mkListLit expected facts.toList

private structure OwnerData where
  owner : Expr
  type : Expr
  producer : Expr
  strict : Expr
  contextCodec : Expr
  facts : Expr
  retained : Array Expr

private def ownerData (roots : Array Name) (owner : Expr) : MetaM OwnerData := do
  let type ← withTransparency .all (whnf (← inferType owner))
  let coefficient := type.getAppArgs[0]!
  let ctx ← mkAppM ``Tower.contextCodec #[type.getAppArgs.back!]
  let facts ← factList roots owner
  if coefficient.getAppFn.isConstOf ``BaseContext.Element then
    let codec ← mkAppM ``BaseContext.Element.codec #[coefficient.getAppArgs.back!]
    return ⟨owner, type, codec, codec, ctx, facts, #[owner]⟩
  unless coefficient.getAppFn.isConstOf ``Element do throwError "unsupported native coefficient carrier"
  let parent := coefficient.getAppArgs.back!
  let parentType ← withTransparency .all (whnf (← inferType parent))
  let base := parentType.getAppArgs[0]!
  unless base.getAppFn.isConstOf ``BaseContext.Element do throwError "captured inventory exceeds two owners"
  let baseCodec ← mkAppM ``BaseContext.Element.codec #[base.getAppArgs.back!]
  let parentFacts ← factList roots parent
  let strict := mkAppN (mkConst ``Element.signCodec)
    (parentType.getAppArgs ++ #[parent, baseCodec, parentFacts])
  let producer := mkAppN (mkConst ``Element.codec)
    (parentType.getAppArgs ++ #[parent, baseCodec])
  return ⟨owner, type, producer, strict, ctx, facts, #[parent, owner]⟩

/-- Reuse only an identical closed reader that already passed the kernel. -/
private def read (began : Nat) (cache : IO.Ref (PHashMap Expr Expr)) (reader : Expr) : MetaM Expr := do
  if reader.hasFVar || reader.hasMVar || reader.hasSorry then throwError "incomplete inventory reader"
  if let some result := (← cache.get).find? reader then return result
  let remaining ← bounded began
  let result ← withOptions (maxHeartbeats.set · remaining) do checkedRecord reader
  cache.modify (·.insert reader result)
  return result

private def checkSource (began : Nat) (source : Name) (result : Expr)
    (fields : Array Name) : MetaM Unit := do
  let original := mkConst source
  let originalInfo ← getConstInfo source
  let typed ← mkAppOptM ``Eq.refl #[some originalInfo.type, some result]
  let remaining ← bounded began
  withOptions (maxHeartbeats.set · remaining) do
    kernelCheck `__inventoryOriginalOwner (← inferType typed) typed
  let mut equations : Array Expr := #[]
  let mut proofs : Array Expr := #[]
  for field in fields do
    let actual ← mkAppM field #[result]
    let expected ← mkAppM field #[original]
    let equation ← mkEq actual expected
    let proof ← mkEqRefl expected
    let remaining ← bounded began
    withOptions (maxHeartbeats.set · remaining) do
      kernelCheck `__inventoryOriginalField equation proof
    equations := equations.push equation
    proofs := proofs.push proof
  let mut statement := equations.back!
  let mut proof := proofs.back!
  for index in (List.range (equations.size - 1)).reverse do
    statement ← mkAppM ``And #[equations[index]!, statement]
    proof ← mkAppM ``And.intro #[proofs[index]!, proof]
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__recordSource)
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    (.thmDecl { name, levelParams := [], type := statement, value := proof }) none (doCheck := true))

syntax (name := inventoryReplayControl) "#inventory_replay_control" : command
@[command_elab inventoryReplayControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let environment := (← getEnv).checked.get
  let scalarRoots := environment.constants.fold (fun found name info =>
    if name.toString.startsWith "_private.KernelReplay.GuardNativeFrontier." &&
        info.type.getAppFn.isConstOf ``SignFact then found.push name else found) (#[] : Array Name)
  unless scalarRoots.size == 17 do throwError "missing proved scalar source inventory"
  let mut sourceFacts : NameSet := {}
  for name in scalarRoots do sourceFacts := sourceFacts.insert (← GuardNativeAudit.origin name)
  let root := ``GuardCapture.second.data
  let mut queue := #[root]
  let mut queued : NameSet := ({} : NameSet).insert root
  let mut cursor := 0
  let mut sources : Array Name := #[]
  let mut reverse : NameMap (Array Name) := {}
  while cursor < queue.size do
    let _ ← bounded began
    if queue.size > 150000 then throwError "original inventory graph bound exhausted"
    let name := queue[cursor]!
    cursor := cursor + 1
    if sourceFacts.contains name then continue
    let some info := environment.find? name | throwError "missing original native inventory declaration"
    if info.type.getAppFn.isConstOf ``Packing || info.type.getAppFn.isConstOf ``ValueSign then
      sources := sources.push name
    for dependency in dependencies info do
      reverse := reverse.insert dependency (((reverse.find? dependency).getD #[]).push name)
      unless queued.contains dependency do
        queued := queued.insert dependency
        queue := queue.push dependency
  unless sources.size == 35 do throwError "original native inventory count changed: {sources.size}"
  let mut ancestors := sourceFacts.toArray
  let mut affected := sourceFacts
  let mut ancestorCursor := 0
  while ancestorCursor < ancestors.size do
    let _ ← bounded began
    if ancestors.size > 150000 then throwError "inventory source ancestor bound exhausted"
    let name := ancestors[ancestorCursor]!
    ancestorCursor := ancestorCursor + 1
    for parent in (reverse.find? name).getD #[] do
      unless affected.contains parent do
        affected := affected.insert parent
        ancestors := ancestors.push parent
  unless (sources.filter affected.contains).size == 31 do
    throwError "affected native inventory count changed"
  logInfo m!"original native inventory discovered: records={sources.size} affectedRecords=31 declarations={cursor}"
  let cache ← IO.mkRef ({} : PHashMap Expr Expr)
  let mut owners : Array (Expr × OwnerData) := #[]
  let mut results : Array Expr := #[]
  let mut inputRoots : Array Name := #[]
  let mut packingCount : Nat := 0
  let mut signCount : Nat := 0
  let mut unaffectedCount : Nat := 0
  for source in sources do
    let _ ← bounded began
    let original := mkConst source
    let originalInfo ← getConstInfo source
    if !affected.contains source then
      unaffectedCount := unaffectedCount + 1
    let owner := originalInfo.type.getAppArgs.back!
    let data ← match owners.find? (fun entry => entry.1 == owner) with
      | some (_, data) => pure data
      | none =>
        let data ← ownerData scalarRoots owner
        owners := owners.push (owner, data)
        pure data
    logInfo m!"native record replay begins: index={results.size} source={source} kind={originalInfo.type.getAppFn.constName?}"
    let result ← if originalInfo.type.getAppFn.isConstOf ``Packing then do
        let oldPolynomial ← mkAppM ``Packing.original #[original]
        let encoded ← NativePackets.polynomial data.producer oldPolynomial data.retained
        let decode ← mkAppM ``Except.toOption
          #[← mkAppM ``SignDet.Codec.readPoly #[data.strict, jsonExpr encoded]]
        let polynomial ← read began cache decode
        let reduction ← mkAppM ``Context.reduce #[owner]
        let packet ← NativePackets.packing data.producer data.contextCodec owner reduction
          oldPolynomial data.retained
        let reader ← mkAppM ``Packing.readPacket?
          #[data.strict, data.contextCodec, reduction, ← mkEqRefl reduction,
            data.facts, polynomial, jsonExpr packet]
        let result ← read began cache reader
        checkSource began source result
          #[``Packing.original, ``Packing.representative, ``Packing.value, ``Packing.sign]
        inputRoots := inputRoots ++ decode.getUsedConstants ++ reader.getUsedConstants
        packingCount := packingCount + 1
        pure result
      else do
        let oldValue ← mkAppM ``ValueSign.value #[original]
        let producer := mkAppN (mkConst ``Element.codec)
          (data.type.getAppArgs ++ #[owner, data.producer])
        let strict := mkAppN (mkConst ``Element.signCodec)
          (data.type.getAppArgs ++ #[owner, data.strict, data.facts])
        let program ← mkAppM ``SignDet.ValueCodec.encode #[producer, oldValue]
        let encoded ← evalExpr SignDet.Codec.Json (← inferType program) program (checkMeta := false)
        let decode ← mkAppM ``Except.toOption
          #[← mkAppM ``SignDet.ValueCodec.decode #[strict, jsonExpr encoded]]
        let value ← read began cache decode
        let packet ← NativePackets.storedSign data.producer data.contextCodec oldValue data.retained
        let reader ← mkAppM ``ValueSign.readPacket?
          #[data.strict, data.contextCodec, value, jsonExpr packet]
        let result ← read began cache reader
        checkSource began source result #[``ValueSign.value]
        inputRoots := inputRoots ++ decode.getUsedConstants ++ reader.getUsedConstants
        signCount := signCount + 1
        pure result
    let kind := if originalInfo.type.getAppFn.isConstOf ``Packing then "packing" else "valueSign"
    let index := if kind == "packing" then packingCount-1 else signCount-1
    let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardRecordReplay ++
      Name.mkSimple s!"{kind}{index}"
    let remaining ← bounded began
    let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
    let recordType ← inferType result
    setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      (.defnDecl {
        name, levelParams := [], type := recordType, value := result,
        hints := .abbrev, safety := .safe }) none (doCheck := true))
    results := results.push (mkConst name)
    logInfo m!"native record replay checked: index={results.size - 1} source={source} originalNativeFieldsBound=true"
  unless packingCount == 23 && signCount == 12 do throwError "native inventory record kinds changed"
  unless unaffectedCount == 4 && results.size == 35 do throwError "native inventory coverage changed"
  let roots := inputRoots ++ results.flatMap Expr.getUsedConstants
  for name in roots do
    modifyEnv fun environment => GuardRecordStore.roots.addEntry environment name
  logInfo m!"native inventory module export: packings={packingCount} cachedSigns={signCount} storedSourceBindings={packingCount+signCount} unaffectedAlsoReplayed={unaffectedCount} totalRecords={results.size} originalNativeFieldsBound=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
#inventory_replay_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardRecordReplay
