/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardFrontierBindings
public meta import KernelReplay.GuardFrontierBindings
public import KernelReplay.GuardProduct
public meta import KernelReplay.GuardProduct
public import KernelReplay.GuardReplayBindings
public meta import KernelReplay.GuardReplayBindings
import all KernelReplay.GuardFrontierBindings
import all KernelReplay.GuardProduct
import all KernelReplay.GuardReplayBindings
import all KernelReplay.GuardFrontierStore
import all KernelReplay.GuardNativeBindings
import all KernelReplay.GuardNativeFrontier
import all KernelReplay.GuardRecordReplay
import all KernelReplay.GuardSecondData
import all KernelReplay.GuardDescriptorPoint
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay
import all KernelReplay.GuardCoefficientFence
import all KernelReplay.GuardOperand
import all KernelReplay.GuardRemainingShape
import all KernelReplay.FrameJoint
import all KernelReplay.FrameOperand

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardObligations
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

private def subject (field : Expr) : MetaM Expr := do
  if let .proj _ _ value := field then return value
  unless field.isApp do throwError "original field binding lost its subject"
  return field.getAppArgs.back!

/-- Use only the already checked native record and scalar correspondences.
The comparison proofs themselves never become premises of a guard proof. -/
private def replacements (began : Nat) : MetaM (NameMap Expr) := do
  let environment := (← getEnv).checked.get
  let records := environment.constants.fold (fun found name info =>
    if name.toString.startsWith "_private.KernelReplay.GuardRecordReplay." &&
        (name.toString.splitOn "__recordSource").length > 1 && info.isTheorem then
      found.push name else found) (#[] : Array Name)
  unless records.size == 35 do throwError "original record binding count changed"
  let mut mapping : NameMap Expr := {}
  for name in records do
    let _ ← bounded began
    let type := (← getConstInfo name).type
    let equation := if type.getAppFn.isConstOf ``And then type.getAppArgs[0]! else type
    unless equation.getAppFn.isConstOf ``Eq do throwError "record binding is not equality"
    let args := equation.getAppArgs
    let fresh ← subject args[1]!
    let original ← subject args[2]!
    let some source := original.constName? | throwError "original record is not named"
    if mapping.contains source then throwError "duplicate original record"
    mapping := mapping.insert source fresh
  let scalars := environment.constants.fold (fun found name info =>
    if name.toString.startsWith "_private.KernelReplay.GuardNativeFrontier." &&
        info.type.getAppFn.isConstOf ``SignFact then found.push name else found) (#[] : Array Name)
  unless scalars.size == 17 do throwError "finite scalar correspondence count changed"
  for name in scalars do
    let source ← GuardNativeAudit.origin name
    if mapping.contains source then throwError "duplicate original scalar"
    mapping := mapping.insert source (mkConst name)
  for (old, fresh) in #[(``FrameOperand.requestPoly, ``GuardOperand.polynomial),
      (``FrameOperand.beta, ``GuardOperand.beta),
      (``FrameOperand.sign_nonzero, ``GuardOperand.signNonzero),
      (``FrameOperand.beta_nonzero, ``GuardOperand.betaNonzero)] do
    mapping := mapping.insert old (mkConst fresh)
  return mapping

private def expandValue (began : Nat) (value : Expr) : MetaM Expr := do
  let environment := (← getEnv).checked.get
  let mut names := environment.constants.fold (fun found name info =>
    if name.toString.startsWith "_private.KernelReplay.GuardNativeFrontier." &&
        info.type.getAppFn.isConstOf ``SignFact then found.push name else found) (#[] : Array Name)
  unless names.size == 17 do throwError "finite scalar data aliases changed"
  names := names ++ #[``GuardOperand.polynomial, ``GuardOperand.beta,
    ``GuardRemainingShape.record1.entry, ``GuardRemainingShape.record2.entry]
  let mut bodies : NameMap Expr := {}
  for name in names do
    let .defnInfo info ← getConstInfo name | throwError "finite alias is not checked data"
    bodies := bodies.insert name info.value
  let mut value := value
  for _ in [:32] do
    let _ ← bounded began
    let next := value.replace fun term => do
      let name ← term.constName?
      bodies.find? name
    if next == value then return value
    value := next
  throwError "finite data expansion bound exhausted"

private def retainAt (began : Nat) (name : Name) (type proof : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  for expression in #[type, proof] do
    if expression.hasFVar || expression.hasMVar || expression.hasSorry || expression.hasLooseBVars then
      throwError "original guard proof is incomplete"
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    (.thmDecl { name, levelParams := [], type, value := proof }) none (doCheck := true))
  return mkConst name

syntax (name := originalGuardBatch) "#original_guard_batch " num num : command
@[command_elab originalGuardBatch]
unsafe def elaborate : CommandElab := fun stx => liftTermElabM <| withExporting (isExporting := false) do
  let some start := stx[1].isNatLit? | throwError "guard start is not literal"
  let some limit := stx[2].isNatLit? | throwError "guard limit is not literal"
  unless start < limit && limit ≤ 3773 do throwError "original guard range is invalid"
  let began ← IO.getNumHeartbeats
  let expressions := GuardFrontier.templates.getState (← getEnv)
  unless expressions.size == 3773 do throwError "original complete guard inventory changed"
  let mapping ← replacements began
  let setup ← GuardDescriptorInputs.prepare
  let first := setup.first
  let second ← Prefix.ofData (mkConst ``GuardSecondData.data)
    (mkConst ``GuardDescriptorPoint.zero) (mkConst ``GuardDescriptorPoint.unit)
  let origin ← Base.ofClosed (mkConst ``GuardInventoryReplay.closed)
  let fallbackDomains ← GuardCoefficientFence.prepare began origin
    (mkConst ``GuardInventoryReplay.agreement) (compileValue := expandValue began)
  let remembered := (← getEnv).checked.get.constants.fold (fun found name info =>
    if !info.isTheorem || !info.levelParams.isEmpty then found
    else if info.type.getAppFn == origin.domain.getAppFn then
      found.insert info.type (mkConst name)
    else if info.type.getAppFn.isConstOf ``And then
      let args := info.type.getAppArgs
      if args[0]!.getAppFn == origin.domain.getAppFn then
        found.insert args[0]! (mkAppN (mkConst ``And.left) #[args[0]!, args[1]!, mkConst name])
      else found
    else found) ({} : PHashMap Expr Expr)
  let reusedDomains ← IO.mkRef (0 : Nat)
  let domains : Supplier := fun type => do
    if let some proof := remembered.find? type then
      reusedDomains.modify (· + 1)
      return some proof
    fallbackDomains type
  let known ← IO.mkRef (#[] : Array KnownLookup)
  let base := origin.supply domains (lookupSupplier known FiniteDataProbe.supply)
  let supplier := second.supplyFrom #[origin.read, first.reader]
    (first.supplyFrom #[origin.read] base)
  let readers := #[origin.read, first.reader, second.reader]
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardObligations
  let previous := (← getEnv).checked.get.constants.fold (fun found name info =>
    if name.getPrefix == root && info.isTheorem && info.levelParams.isEmpty then
      found.insert info.type (mkConst name) else found) ({} : PHashMap Expr Expr)
  let checked ← IO.mkRef previous
  let mut reused : Nat := 0
  let mut proofs := #[]
  for index in [start:limit] do
    let _ ← bounded began
    let template := expressions[index]!.replace fun term => do
      let name ← term.constName?
      mapping.find? name
    let mut target := template
    for reader in readers do
      let .lam _ _ body _ := target | throwError "original guard lost a reader binder"
      target := body.instantiate1 reader
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"original guard begins: index={index} heartbeat={((← IO.getNumHeartbeats)-began)/1000}"
        handle.flush
    let remaining ← bounded began
    let proof ← if let some proof := (← checked.get).find? target then do
        reused := reused + 1
        pure proof
      else withOptions (maxHeartbeats.set · remaining) do build target supplier
    let name := root ++ Name.mkSimple s!"guard{index}"
    let proof ← retainAt began name target proof
    checked.modify (·.insert target proof)
    proofs := proofs.push proof
    logInfo m!"original guard kernel checked: index={index}"
  if start == 0 then
    let _ ← retain began (root ++ `firstStatement) (← inferType proofs[0]!)
  logInfo m!"original guard batch module export: start={start} limit={limit} proofs={proofs.size} exactCheckedProofsReused={reused} exactCheckedDomainProofsReused={← reusedDomains.get} originalInventory=3773 sameFirstAndSecondPoints=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#original_guard_batch 0 32

end Hex.RealClosure.Algebraic.KernelReplay.GuardObligations
