/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardBaseAgreement
public meta import KernelReplay.GuardBaseAgreement
import all KernelReplay.GuardBaseAgreement
import all KernelReplay.GuardFrontierStore
import all KernelReplay.GuardNativeBindings
import all KernelReplay.GuardNativeFrontier
import all KernelReplay.GuardRecordReplay
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardOperand
import all KernelReplay.FrameJoint
import all KernelReplay.FrameOperand

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardSupportSource
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


private def unalias (began : Nat) (value : Expr) : MetaM Expr := do
  let mut value := value
  for _ in [:64] do
    let _ ← bounded began
    let some name := value.constName? | return value
    let .defnInfo info ← getConstInfo name | return value
    unless info.levelParams.isEmpty do throwError "source data alias has universe parameters"
    value := info.value
  throwError "source data alias bound exhausted"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let mapping ← replacements began
  let support ← unalias began (mkConst ``GuardCapture.support)
  unless support.getAppFn.isConstOf ``List.append do throwError "original support lost its first/additional decomposition"
  let additional := support.getAppArgs.back!
  unless additional.isApp do throwError "original additional support lost its shared tuple"
  let mut pending := [additional.getAppArgs.back!]
  let mut original : Array Expr := #[]
  for _ in [:10000] do
    let _ ← bounded began
    let value :: tail := pending | break
    pending := tail
    let type ← withTransparency .all (whnf (← inferType value))
    if type.getAppFn.isConstOf ``Prod then
      let pair ← unalias began value
      unless pair.getAppFn.isConstOf ``Prod.mk && pair.getAppNumArgs == 4 do
        throwError "original support tuple is not constructor data"
      let args := pair.getAppArgs
      pending := args[2]! :: args[3]! :: pending
    else
      unless type.getAppFn.isConstOf ``List do throwError "original support tuple has a non-list leaf"
      let fresh := value.replace fun term => do
        let name ← term.constName?
        mapping.find? name
      original := original.push fresh
  unless pending.isEmpty do throwError "original support tuple bound exhausted"
  let templates := GuardFrontier.templates.getState (← getEnv)
  unless templates.size == 3773 do throwError "original discovery syntax count changed"
  let mut recovered : Array Expr := #[]
  for index in [:3772] do
    let _ ← bounded began
    let mut body := templates[index]!
    for _ in [:3] do
      let .lam _ _ next _ := body | throwError "original reader binder changed"
      body := next
    body := body.replace fun term => do
      let name ← term.constName?
      mapping.find? name
    let leaf : Leaf := ⟨body, ← getLCtx, ← getLocalInstances⟩
    if let some coefficients ← leaf.coefficients? then recovered := recovered.push coefficients
  let extra := original[0]!
  unless (← withTransparency .all (whnf extra)).getAppFn.isConstOf ``List.nil do
    throwError "original extra coefficients are not empty"
  original := original.extract 1 original.size
  let mut mismatches : Nat := 0
  for (old, fresh) in original.zip recovered do
    if old != fresh then mismatches := mismatches + 1
  logInfo m!"original support source comparison: capturedBlocks={original.size} recoveredBlocks={recovered.size} originalExtraEmpty=true orderedExactExpressionMismatches={mismatches} ordinaryAgreementProofClaim=false aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"
  unless original.size == recovered.size && mismatches == 0 do
    throwError "recovered support does not exactly match the original ordered coefficient blocks"

end Hex.RealClosure.Algebraic.KernelReplay.GuardSupportSource
