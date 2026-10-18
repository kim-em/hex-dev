/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRecordReplay
public meta import KernelReplay.GuardRecordReplay
import all KernelReplay.GuardRecordReplay
import all KernelReplay.FrameJoint

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardInventoryReplay
open Lean Meta Elab Command FiniteData

private def bounded (began : Nat) : MetaM Nat := do
  Core.checkSystem "source inventory reconstruction"
  let used := ((← IO.getNumHeartbeats) - began) / 1000
  if used ≥ 1500000 then throwError "aggregate source inventory budget exhausted"
  return 1500000 - used

private def stage (began : Nat) (message : String) : MetaM Unit := do
  let remaining ← bounded began
  logInfo m!"inventory reconstruction: {message}; heartbeat={1500000 - remaining}"
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"inventory reconstruction: {message}; heartbeat={1500000 - remaining}"
      handle.flush

private def retain (began : Nat) (tag : Name) (value : Expr) : MetaM Expr := do
  let type ← inferType value
  for expression in #[value, type] do
    if expression.hasMVar || expression.hasFVar || expression.hasSorry then
      throwError "incomplete reconstructed inventory declaration"
  let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardInventoryReplay ++ tag
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

private def subject (field : Expr) : MetaM Expr := do
  if let .proj _ _ value := field then return value
  unless field.isApp do throwError "source binding has no field subject"
  return field.getAppArgs.back!

private def equations (type : Expr) : MetaM (Array Expr) := do
  let mut result := #[]
  let mut rest := type
  for _ in [:8] do
    if !rest.getAppFn.isConstOf ``And then return result.push rest
    result := result.push rest.getAppArgs[0]!
    rest := rest.getAppArgs[1]!
  throwError "source binding exceeds its fixed conjunction bound"

/-- Recover the checked original-to-fresh record map from stored field
equalities. These archival comparisons are not inputs of the new inventory. -/
private def bindings (began : Nat) : MetaM (NameMap Expr) := do
  let environment := (← getEnv).checked.get
  let names := environment.constants.fold (fun found name info =>
    if name.toString.startsWith "_private.KernelReplay.GuardRecordReplay." &&
        (name.toString.splitOn "__recordSource").length > 1 && info.isTheorem then
      found.push name else found) (#[] : Array Name)
  unless names.size == 35 do throwError "missing stored native record comparisons: {names.size}"
  let mut result : NameMap Expr := {}
  for name in names do
    let info ← getConstInfo name
    let fields ← equations info.type
    let first := fields[0]!
    unless first.getAppFn.isConstOf ``Eq do throwError "invalid native record comparison"
    let fresh ← subject first.getAppArgs[1]!
    let old ← subject first.getAppArgs[2]!
    let some source := old.constName? | throwError "native comparison lost its named original"
    unless fresh.isConst && !result.contains source do throwError "duplicate or unnamed record comparison"
    let originalType := (← getConstInfo source).type
    let expectedFields := if originalType.getAppFn.isConstOf ``Packing then
        #[``Packing.original, ``Packing.representative, ``Packing.value, ``Packing.sign]
      else if originalType.getAppFn.isConstOf ``ValueSign then #[``ValueSign.value]
      else #[]
    unless fields.size == expectedFields.size && !fields.isEmpty do
      throwError "source comparison changed its native record kind"
    for (equation, field) in fields.zip expectedFields do
      let actual ← mkAppM field #[fresh]
      let expected ← mkAppM field #[old]
      unless equation == (← mkEq actual expected) do throwError "source comparison changed a native field"
    let .thmInfo theoremInfo := info | throwError "source comparison is not a theorem"
    let remaining ← bounded began
    withOptions (maxHeartbeats.set · remaining) do
      kernelCheck `__importedInventorySource theoremInfo.type theoremInfo.value
    result := result.insert source fresh
  return result

private def freshList (began : Nat) (mapping : NameMap Expr) (original : Expr) : MetaM Expr := do
  let type ← withTransparency .all (whnf (← inferType original))
  unless type.getAppFn.isConstOf ``List do throwError "source inventory is not a list"
  let mut rest := original
  let mut values : Array Expr := #[]
  for _ in [:128] do
    let _ ← bounded began
    let literal ← withTransparency .all (whnf rest)
    if literal.getAppFn.isConstOf ``List.nil then
      return ← mkListLit type.getAppArgs.back! values.toList
    unless literal.getAppFn.isConstOf ``List.cons do throwError "source inventory is not literal"
    let args := literal.getAppArgs
    let some source := args[1]!.constName? | throwError "source inventory contains an unnamed record"
    let some fresh := mapping.find? source | throwError "source inventory has an unreplayed record {source}"
    values := values.push fresh
    rest := args[2]!
  throwError "source inventory exceeds the fixed list bound"

private def inventory (began : Nat) (mapping : NameMap Expr) (source tag : Name) :
    MetaM (Expr × Expr × Expr × Expr) := do
  let args := (← getConstInfo source).type.getAppArgs
  let context := args[args.size - 5]!
  let entries ← retain began (tag ++ `entries) (← freshList began mapping args[args.size - 4]!)
  let records ← retain began (tag ++ `records) (← freshList began mapping args[args.size - 3]!)
  let facts ← retain began (tag ++ `facts) (← freshList began mapping args[args.size - 2]!)
  return (context, entries, records, facts)

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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let mapping ← bindings began
  stage began "all35 stored source comparisons rechecked after import"
  let (firstOwner, firstEntries, firstRecords, firstFacts) ←
    inventory began mapping ``GuardCapture.first.data `first
  let _ ←
    inventory began mapping ``GuardCapture.second.data `second
  stage began "both actual inventories rebuilt in their original order"
  let support ← retain began `support
    (← mkAppM ``Packing.Inventory.level #[firstOwner, firstEntries, firstRecords, firstFacts])
  let base := mkConst ``FiniteBaseProbe.base
  let existence ← retain began `baseExists
    (← mkAppM ``BaseContext.Context.partial_exists #[base, mkConst ``FiniteChainProbe.following, support])
  stage began "finite base specialization existence constructed"
  let existential ← inferType existence
  let args := existential.getAppArgs
  let interpretation ← retain began `interpretation
    (← mkAppOptM ``Classical.choose #[some args[0]!, some args[1]!, some existence])
  let specification ← mkAppOptM ``Classical.choose_spec
    #[some args[0]!, some args[1]!, some existence]
  let closed ← retain began `closed
    (← mkAppM ``BaseContext.Context.partialClosed #[base, interpretation])
  let origin ← Base.ofClosed closed
  let agreement ← retain began `agreement
    (← origin.bindAgreement (← mkAppM ``And.left #[specification]))
  let data ← retain began `firstData
    (← mkAppM ``Packing.Inventory.level_data
      #[firstOwner, firstEntries, firstRecords, firstFacts,
        origin.read, origin.domain, origin.closed, agreement])
  let zero ← mkAppM ``Transport.Closed.read_zero #[closed]
  let unit ← mkAppM ``Transport.Closed.read_one #[closed]
  let first ← Prefix.ofData data zero unit
  stage began "first actual finite prefix constructed from fresh records"
  let _ ← retain began `firstPoint first.point
  let firstSpec ← retain began `firstSpec
    (← mkAppM ``Context.finitePoint_spec #[first.read, first.zero, first.unit, first.descriptor])
  stage began "complete first finite inventory and selected point exported; dependency audit pending"

end Hex.RealClosure.Algebraic.KernelReplay.GuardInventoryReplay
