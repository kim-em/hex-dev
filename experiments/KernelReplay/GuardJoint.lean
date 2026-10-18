/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardObligations445
public meta import KernelReplay.GuardObligations445
public import KernelReplay.GuardAgreementPublic
public meta import KernelReplay.GuardAgreementPublic
import all KernelReplay.GuardObligations445
import all KernelReplay.GuardAgreementPublic
import all KernelReplay.GuardAgreementJoin
import all KernelReplay.GuardObligations
import all KernelReplay.GuardFrontierStore
import all KernelReplay.GuardNativeBindings
import all KernelReplay.GuardNativeFrontier
import all KernelReplay.GuardRecordReplay
import all KernelReplay.GuardSecondData
import all KernelReplay.GuardDescriptorPoint
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay
import all KernelReplay.GuardOperand
import all KernelReplay.GuardProduct
import all KernelReplay.GuardRemainingShape
import all KernelReplay.FrameJoint
import all KernelReplay.FrameOperand

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardJoint
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

private def retainAt (began : Nat) (name : Name) (type proof : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  for expression in #[type, proof] do
    if expression.hasFVar || expression.hasMVar || expression.hasSorry || expression.hasLooseBVars then
      throwError "joint proof retains an incomplete or temporary expression"
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    (.thmDecl { name, levelParams := [], type, value := proof }) none (doCheck := true))
  return mkConst name

private def stage (began : Nat) (message : String) : MetaM Unit := do
  let _ ← bounded began
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"original joint: {message} heartbeat={((← IO.getNumHeartbeats)-began)/1000}"
      handle.flush

private structure Claim where
  type : Expr
  proof : Expr

private def combine (left right : Claim) : Claim :=
  ⟨mkApp2 (mkConst ``And) left.type right.type,
    mkAppN (mkConst ``And.intro) #[left.type, right.type, left.proof, right.proof]⟩

private def balance (claims : Array Claim) : MetaM Claim := do
  let mut group := claims
  while group.size > 1 do
    let mut next := #[]
    for index in [:((group.size+1)/2)] do
      let some left := group[2*index]? | throwError "joint group lost its left clause"
      next := next.push (if let some right := group[2*index+1]? then combine left right else left)
    group := next
  let some result := group[0]? | throwError "joint conjunction lost a group"
  return result

/-- Combine complete original statements with explicit constructor arguments.
Only closed proofs are retained, and each advertised type is kernel checked. -/
private def conjunction (began : Nat) (claims : Array Claim) : MetaM Claim := do
  let mut parts : Array Claim := #[]
  for start in [:((claims.size+31)/32)] do
    let group := claims.extract (32*start) (min (32*(start+1)) claims.size)
    let result ← balance group
    let name := mkPrivateName (← getEnv) (← mkFreshUserName `jointGroup)
    let proof ← retainAt began name result.type result.proof
    parts := parts.push ⟨result.type, proof⟩
    stage began s!"group{start} checked"
  while parts.size > 1 do
    let mut next := #[]
    for index in [:((parts.size+1)/2)] do
      let some left := parts[2*index]? | throwError "joint branch lost its left clause"
      if let some right := parts[2*index+1]? then
        let result := combine left right
        let name := mkPrivateName (← getEnv) (← mkFreshUserName `jointBranch)
        let proof ← retainAt began name result.type result.proof
        next := next.push ⟨result.type, proof⟩
      else next := next.push left
    parts := next
  let some result := parts[0]? | throwError "joint conjunction is empty"
  return result

private def statement (types : Array Expr) : Expr := Id.run do
  let mut parts := types
  while parts.size > 1 do
    let mut next := #[]
    for index in [:((parts.size+1)/2)] do
      let left := parts[2*index]!
      next := next.push (if let some right := parts[2*index+1]? then
        mkApp2 (mkConst ``And) left right else left)
    parts := next
  return parts[0]!

private def instantiateReaders (template : Expr) (readers : Array Expr) : MetaM Expr := do
  let mut result := template
  for reader in readers do
    let .lam _ _ body _ := result | throwError "joint guard lost an original reader binder"
    result := body.instantiate1 reader
  return result

private def evaluation (context read point : Expr) : MetaM Expr := do
  let carrier ← mkAppM ``Element #[context]
  withLocalDeclD `value carrier fun value => do
    let polynomial ← mkAppM ``Element.polynomial #[value]
    mkLambdaFVars #[value] (← mkAppM ``Packing.eval #[read, point, polynomial])

/-- Kernel-check the fully instantiated predicate before binding the witnesses.
The same fresh binders determine both the advertised existential and its proof. -/
private partial def witnesses (began : Nat) (values : Array Expr)
    (predicate : Array Expr → MetaM Expr) (proof : Expr) : MetaM (Expr × Expr) := go 0 #[]
where
  go (index : Nat) (binders : Array Expr) : MetaM (Expr × Expr) := do
    if let some value := values[index]? then
      withLocalDeclD `witness (← inferType value) fun binder => do
        let (body, obtained) ← go (index+1) (binders.push binder)
        let abstracted ← mkLambdaFVars #[binder] body
        let instantiated := abstracted.replaceFVars binders (values.extract 0 index)
        let result ← mkAppOptM ``Exists.intro
          #[none, some instantiated, some value, some obtained]
        let required ← mkAppM ``Exists #[abstracted]
        return (required, result)
    else
      let body ← predicate binders
      let instantiated := body.replaceFVars binders values
      let name := mkPrivateName (← getEnv) (← mkFreshUserName `jointInstantiated)
      let checked ← retainAt began name instantiated proof
      stage began "fresh witness predicate checked at actual witnesses"
      return (body, checked)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let setup ← GuardDescriptorInputs.prepare
  let first := setup.first
  let second ← Prefix.ofData (mkConst ``GuardSecondData.data)
    (mkConst ``GuardDescriptorPoint.zero) (mkConst ``GuardDescriptorPoint.unit)
  let origin ← Base.ofClosed (mkConst ``GuardInventoryReplay.closed)
  let actualReaders := #[origin.read, first.reader, second.reader]
  let mapping ← replacements began
  let templates := GuardFrontier.templates.getState (← getEnv)
  unless templates.size == 3773 do throwError "joint original guard inventory changed"
  let templates := templates.map fun template => template.replace fun term => do
    let name ← term.constName?
    mapping.find? name
  let agreement := mkConst ``GuardAgreementJoin.agreement
  let fixed := mkConst ``GuardAgreementJoin.fixed
  let agreementType ← inferType agreement
  let agreementArgs := agreementType.getAppArgs
  let mut claims : Array Claim := #[⟨agreementType, agreement⟩, ⟨← inferType fixed, fixed⟩]
  for level in #[first, second] do
    let proof ← mkAppM ``Packing.Inventory.Data.conditions #[level.data, level.zero, level.unit]
    claims := claims.push ⟨← inferType proof, proof⟩
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardObligations
  for index in [:3773] do
    let _ ← bounded began
    let name := root ++ Name.mkSimple s!"guard{index}"
    let info ← getConstInfo name
    let required ← instantiateReaders templates[index]! actualReaders
    unless info.isTheorem && info.levelParams.isEmpty && info.type == required do
      throwError "original guard {index} has a different complete target"
    claims := claims.push ⟨required, mkConst name⟩
  let nativeProduct := mkConst ``GuardProduct.nativeProduct
  claims := claims.push ⟨← inferType nativeProduct, nativeProduct⟩
  unless claims.size == 3778 do throwError "joint complete clause count changed"
  stage began "all3773 original targets and both inventories collected"
  let combined ← conjunction began claims
  stage began "complete balanced conjunction checked"
  let base := mkConst ``FiniteBaseProbe.base
  let existence := mkConst ``GuardInventoryReplay.baseExists
  let existential ← inferType existence
  unless existential.getAppFn.isConstOf ``Exists do throwError "joint base existence shape changed"
  let existentialArgs := existential.getAppArgs
  let predicate := fun (binders : Array Expr) => do
    unless binders.size == 3 do throwError "joint witness count changed"
    let interpretation := binders[0]!
    let read ← mkAppM ``BaseContext.Context.partialRead #[base, interpretation]
    let domain ← mkAppM ``BaseContext.Context.partialDomain #[base, interpretation]
    let args := agreementArgs.set! (agreementArgs.size-5) read |>.set! (agreementArgs.size-4) domain
    let fullAgreement := mkAppN agreementType.getAppFn args
    let inherited ← whnf (mkApp existentialArgs[1]! interpretation)
    unless inherited.getAppFn.isConstOf ``And do throwError "joint fixed-value clause changed"
    let mut types := #[fullAgreement, inherited.getAppArgs[1]!]
    let mut previous := read
    let mut readers := #[read]
    for index in [:2] do
      let some level := #[first, second][index]? | throwError "joint level is missing"
      let point := binders[index+1]!
      types := types.push (← mkAppM ``Packing.Inventory.Conditions
        #[level.context, level.entries, level.records, level.facts, previous, point])
      previous ← evaluation level.context previous point
      readers := readers.push previous
    for template in templates do types := types.push (← instantiateReaders template readers)
    types := types.push (← mkAppM ``Transport.Product
      #[previous, mkConst ``FrameOwners.requestPoly, mkConst ``FrameOwners.requestPoly])
    unless types.size == claims.size do throwError "joint formal clause count changed"
    let body := statement types
    for chosen in #[mkConst ``GuardInventoryReplay.interpretation, first.point, second.point] ++ actualReaders do
      if body.find? (· == chosen) |>.isSome then
        throwError "joint statement retains a chosen interpretation, point or reader"
    return body
  let (type, proof) ← witnesses began
    #[mkConst ``GuardInventoryReplay.interpretation, first.point, second.point] predicate combined.proof
  let theoremName := `Hex.RealClosure.Algebraic.KernelReplay.GuardJoint.exists_points
  let _ ← retainAt began theoremName type proof
  let _ ← GuardDescriptorInputs.retain began
    `Hex.RealClosure.Algebraic.KernelReplay.GuardJoint.Statement type
  stage began "three-witness existential kernel checked"
  logInfo m!"original joint construction result: witnesses=3 originalGuards=3773 completeClauses=3778 fullOrderedBaseAgreement=true inheritedProviderValuesFixed=true bothOriginalInventories=true originalNativeProduct=true chosenWitnessesAbsentFromStatement=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardJoint
