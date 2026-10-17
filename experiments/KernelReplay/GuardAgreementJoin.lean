/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardBaseAgreement04
public meta import KernelReplay.GuardBaseAgreement04
public import KernelReplay.GuardSupportSource
public meta import KernelReplay.GuardSupportSource
import all KernelReplay.GuardBaseAgreement04
import all KernelReplay.GuardSupportSource
import all KernelReplay.GuardBaseAgreement
import all KernelReplay.GuardFrontierStore
import all KernelReplay.GuardNativeBindings
import all KernelReplay.GuardNativeFrontier
import all KernelReplay.GuardRecordReplay
import all KernelReplay.GuardCoefficientIndex
import all KernelReplay.GuardInventoryReplay
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardOperand
import all KernelReplay.GuardRemainingShape
import all KernelReplay.FrameJoint
import all KernelReplay.FrameOperand

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardAgreementJoin
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
      throwError "original guard proof is incomplete"
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    (.thmDecl { name, levelParams := [], type, value := proof }) none (doCheck := true))
  return mkConst name

private def trace (began : Nat) (message : String) : MetaM Unit := do
  let _ ← bounded began
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"ordered agreement join: {message} heartbeat={((← IO.getNumHeartbeats)-began)/1000}"
      handle.flush

private def retainData (began : Nat) (name : Name) (type value : Expr) : MetaM Expr := do
  for expression in #[type, value] do
    if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars || expression.hasSorry then
      throwError "joined support data is incomplete"
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
    none (doCheck := true))
  return mkConst name

/-- Reproduce every original coefficient occurrence in order, including the
original empty extra inventory. GuardSupportSource separately checks this exact
sequence against the frozen input; no archival comparison is a proof premise. -/
private def occurrences (began : Nat) (carrier : Expr) : MetaM (Array Expr) := do
  let mapping ← replacements began
  let templates := GuardFrontier.templates.getState (← getEnv)
  unless templates.size == 3773 do throwError "original guard inventory changed"
  let mut result := #[← mkListLit carrier []]
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
    if let some coefficients ← leaf.coefficients? then
      if coefficients.hasFVar || coefficients.hasMVar || coefficients.hasLooseBVars ||
          coefficients.hasSorry then
        throwError "original coefficient block has a temporary dependency"
      result := result.push coefficients
  unless result.size == 3602 do throwError "original ordered coefficient occurrence count changed"
  return result

private structure Part where
  support : Expr
  agreement : Expr

private unsafe def join (start limit : Nat) : TermElabM Unit := withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let template := mkConst ``GuardInventoryReplay.agreement
  let dataType ← inferType template
  let dataArgs := dataType.getAppArgs
  let carrier := dataArgs[0]!
  let listType ← inferType dataArgs.back!
  let common := dataArgs.extract 0 (dataArgs.size-1)
  let levels := dataType.getAppFn.constLevels!
  trace began "source collection begins"
  let original ← occurrences began carrier
  trace began "all3602 source occurrences collected"
  unless start < limit && limit ≤ original.size do throwError "invalid original join range"
  let mut basis : PHashMap Expr Expr := {}
  let mut basisCount : Nat := 0
  for index in [:2203] do
    let _ ← bounded began
    let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardBaseAgreement ++
      Name.mkSimple s!"block{index}"
    let some info := (← getEnv).checked.get.find? name | continue
    unless info.isTheorem && info.type.getAppFn == dataType.getAppFn do
      throwError "coefficient basis is not an agreement theorem"
    let args := info.type.getAppArgs
    unless args.size == dataArgs.size &&
        args.extract 0 (args.size-1) == dataArgs.extract 0 (dataArgs.size-1) do
      throwError "coefficient agreement has a different reader, domain or sign callback"
    if basis.contains args.back! then throwError "duplicate exact coefficient basis block"
    basis := basis.insert args.back! (mkConst name)
    basisCount := basisCount + 1
  trace began s!"checked basis loaded count={basisCount}"
  -- Reuse only checked aliases for the exact original coefficient list.
  let mut shared := (← getEnv).checked.get.constants.fold (fun found name info =>
    match info with
    | .defnInfo info =>
      if name.toString.startsWith "_private.KernelReplay.GuardAgreementJoin" &&
          (name.toString.splitOn "joinedBlock").length > 1 &&
          info.levelParams.isEmpty && info.type == listType then
        found.insert info.value (mkConst name) else found
    | _ => found) ({} : PHashMap Expr Expr)
  let mut parts : Array Part := #[]
  for index in [start:limit] do
    let block := original[index]!
    let proof ← if index == 0 then
        pure (mkAppN (mkConst ``Transport.Inventory.Agreement.nil levels) common)
      else do
        let some proof := basis.find? block | throwError "original occurrence {index} has no checked coefficient agreement"
        pure proof
    let support ← if let some value := shared.find? block then pure value else do
      let name := mkPrivateName (← getEnv) (← mkFreshUserName `joinedBlock)
      let value ← retainData began name listType block
      shared := shared.insert block value
      pure value
    parts := parts.push ⟨support, proof⟩
  let mut joins : Nat := 0
  while parts.size > 1 do
    let mut next : Array Part := #[]
    for index in [:(parts.size+1)/2] do
      let _ ← bounded began
      let some left := parts[2*index]? | throwError "joined support lost its left part"
      if let some right := parts[2*index+1]? then
        let appended ← mkAppOptM ``List.append
          #[some carrier, some left.support, some right.support]
        trace began s!"pair{joins} support check begins"
        let dataName := mkPrivateName (← getEnv) (← mkFreshUserName `joinedSupport)
        let support ← retainData began dataName listType appended
        trace began s!"pair{joins} support checked"
        let proof := mkAppN (mkConst ``Transport.Inventory.Agreement.join levels)
          (common ++ #[left.support, right.support, left.agreement, right.agreement])
        let required := mkAppN dataType.getAppFn (dataArgs.set! (dataArgs.size-1) support)
        let proofName := mkPrivateName (← getEnv) (← mkFreshUserName `joinedAgreement)
        trace began s!"pair{joins} agreement check begins"
        let proof ← retainAt began proofName required proof
        trace began s!"pair{joins} agreement checked"
        next := next.push ⟨support, proof⟩
        joins := joins + 1
      else next := next.push left
    parts := next
  let some result := parts[0]? | throwError "joined support result is empty"
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardAgreementJoin
  let support ← retainData began (root ++ Name.mkSimple s!"support{start}") listType result.support
  let required := mkAppN dataType.getAppFn (dataArgs.set! (dataArgs.size-1) support)
  let _ ← retainAt began (root ++ Name.mkSimple s!"agreement{start}") required result.agreement
  trace began "named join checked; dependency audit pending"
  logInfo m!"original ordered agreement join module export: start={start} limit={limit} occurrences={limit-start} joins={joins} availableBasis={basisCount} originalOccurrences=3602 sameBaseInterpretation=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

syntax (name := originalAgreementJoin) "#original_agreement_join " num num : command
@[command_elab originalAgreementJoin]
unsafe def elaborate : CommandElab := fun stx => do
  let some start := stx[1].isNatLit? | throwError "join start is not literal"
  let some limit := stx[2].isNatLit? | throwError "join limit is not literal"
  liftTermElabM (join start limit)

/-- Inspect only the newly retained native list aliases. This does not unfold
coefficient operations or any archived model-bearing data. -/
private def expandJoined (began : Nat) (listType value : Expr) : MetaM Expr := do
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardAgreementJoin
  let definitions := (← getEnv).checked.get.constants.fold (fun found name info =>
    match info with
    | .defnInfo info =>
      let text := name.toString
      let privateData := (text.startsWith "_private.KernelReplay.GuardAgreementJoin" ||
        text.startsWith "_private.KernelReplay.GuardAgreementFinal.") &&
        ((text.splitOn "joinedSupport").length > 1 ||
          (text.splitOn "joinedBlock").length > 1)
      if info.type == listType && (name.getPrefix == root || privateData) then
        found.insert name info.value else found
    | _ => found) ({} : NameMap Expr)
  let mut value := value
  for _ in [:64] do
    let _ ← bounded began
    let next := value.replace fun term => do
      let name ← term.constName?
      definitions.find? name
    if next == value then return value
    value := next
  throwError "joined support expansion bound exhausted"

private def sourceTree (began : Nat) (carrier : Expr) (levels : List Lean.Level)
    (blocks : Array Expr) : MetaM Expr := do
  let mut blocks := blocks
  while blocks.size > 1 do
    let mut next : Array Expr := #[]
    for index in [:(blocks.size+1)/2] do
      let _ ← bounded began
      let some left := blocks[2*index]? | throwError "source support lost its left block"
      let block := if let some right := blocks[2*index+1]? then
          mkAppN (mkConst ``List.append levels) #[carrier, left, right]
        else left
      next := next.push block
    blocks := next
  let some result := blocks[0]? | throwError "source support is empty"
  return result

syntax (name := originalAgreementFull) "#original_agreement_full" : command
@[command_elab originalAgreementFull]
unsafe def elaborateFull : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let first := mkConst ``GuardInventoryReplay.agreement
  let dataType ← inferType first
  let dataArgs := dataType.getAppArgs
  let common := dataArgs.extract 0 (dataArgs.size-1)
  let carrier := dataArgs[0]!
  let firstSupport := dataArgs.back!
  let listType ← inferType firstSupport
  let listHead ← withTransparency .all (whnf listType)
  unless listHead.getAppFn.isConstOf ``List do throwError "base support is not a list"
  let listLevels := listHead.getAppFn.constLevels!
  let levels := dataType.getAppFn.constLevels!
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardAgreementJoin
  let mut parts : Array Part := #[]
  for index in [:29] do
    let _ ← bounded began
    let start := 128*index
    let supportName := root ++ Name.mkSimple s!"support{start}"
    let proofName := root ++ Name.mkSimple s!"agreement{start}"
    let support := mkConst supportName
    let info ← getConstInfo proofName
    let required := mkAppN dataType.getAppFn (dataArgs.set! (dataArgs.size-1) support)
    unless info.isTheorem && info.type == required do
      throwError "ordered segment {start} has a different complete agreement type"
    parts := parts.push ⟨support, mkConst proofName⟩
  while parts.size > 1 do
    let mut next : Array Part := #[]
    for index in [:(parts.size+1)/2] do
      let _ ← bounded began
      let some left := parts[2*index]? | throwError "complete join lost a left segment"
      if let some right := parts[2*index+1]? then
        let appended := mkAppN (mkConst ``List.append listLevels)
          #[carrier, left.support, right.support]
        let name := mkPrivateName (← getEnv) (← mkFreshUserName `joinedSupport)
        let support ← retainData began name listType appended
        let value := mkAppN (mkConst ``Transport.Inventory.Agreement.join levels)
          (common ++ #[left.support, right.support, left.agreement, right.agreement])
        let required := mkAppN dataType.getAppFn (dataArgs.set! (dataArgs.size-1) support)
        let name := mkPrivateName (← getEnv) (← mkFreshUserName `joinedAgreement)
        let proof ← retainAt began name required value
        next := next.push ⟨support, proof⟩
      else next := next.push left
    parts := next
  let some additional := parts[0]? | throwError "complete additional support is empty"
  let appended := mkAppN (mkConst ``List.append listLevels)
    #[carrier, firstSupport, additional.support]
  let support ← retainData began (root ++ `support) listType appended
  let source ← occurrences began carrier
  let expectedAdditional ← sourceTree began carrier listLevels source
  let expected := mkAppN (mkConst ``List.append listLevels)
    #[carrier, firstSupport, expectedAdditional]
  unless (← expandJoined began listType support) == expected do
    throwError "complete support changed the original ordered coefficient occurrences"
  let value := mkAppN (mkConst ``Transport.Inventory.Agreement.join levels)
    (common ++ #[firstSupport, additional.support, first, additional.agreement])
  let required := mkAppN dataType.getAppFn (dataArgs.set! (dataArgs.size-1) support)
  let proof ← retainAt began (root ++ `agreement) required value
  let existence := mkConst ``GuardInventoryReplay.baseExists
  let existential ← inferType existence
  unless existential.getAppFn.isConstOf ``Exists do throwError "base existence shape changed"
  let args := existential.getAppArgs
  let specification ← mkAppOptM ``Classical.choose_spec
    #[some args[0]!, some args[1]!, some existence]
  let fixedValue ← mkAppM ``And.right #[specification]
  let predicate ← whnf (mkApp args[1]! (mkConst ``GuardInventoryReplay.interpretation))
  unless predicate.getAppFn.isConstOf ``And do throwError "base fixed-coefficient predicate changed"
  let fixedType := predicate.getAppArgs[1]!
  let fixed ← retainAt began (root ++ `fixed) fixedType fixedValue
  let statement := mkApp2 (mkConst ``And) required fixedType
  let combined := mkAppN (mkConst ``And.intro) #[required, fixedType, proof, fixed]
  let _ ← retainAt began (root ++ `base) statement combined
  logInfo m!"original complete base agreement module export: uniqueBlocks=2203 orderedOccurrences=3602 segments=29 originalFirstSupportRetained=true exactOriginalOrderedData=true inheritedProviderValuesFixed=true sameBaseInterpretation=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#original_agreement_join 0 128

end Hex.RealClosure.Algebraic.KernelReplay.GuardAgreementJoin
