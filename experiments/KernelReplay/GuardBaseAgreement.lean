/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardObligations06
public meta import KernelReplay.GuardObligations06
public import KernelReplay.GuardAgreementRules
public meta import KernelReplay.GuardAgreementRules
import all KernelReplay.GuardObligations06
import all KernelReplay.GuardAgreementRules
import all KernelReplay.GuardObligations
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

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardBaseAgreement
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

/-- Native encodings choose a previously checked candidate only. The complete
original point-agreement proposition is checked again by the ordinary kernel. -/
private def checkCandidate (began : Nat) (type value : Expr)
    (tag : Name := `basePointAgreement) : MetaM (Option Expr) := do
  for expression in #[type, value] do
    if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars || expression.hasSorry then
      throwError "incomplete point agreement reuse"
  let name := mkPrivateName (← getEnv) (← mkFreshUserName tag)
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  match (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      (.thmDecl {name, levelParams := [], type, value}) none (doCheck := true) with
  | .ok environment =>
    setEnv environment
    return some (mkConst name)
  | .error (.appTypeMismatch ..) => return none
  | .error (.declTypeMismatch ..) => return none
  | .error (.exprTypeMismatch ..) => return none
  | .error error => ofExceptKernelException (Except.error error)

private def current (began : Nat) (value : Expr) : MetaM Expr := do
  let type ← inferType value
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__coefficientInput)
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type, value, hints := .regular 0, safety := .safe }
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  withOptions (Elab.async.set · false) do
    withOptions (fun options => options.setBool `compiler.postponeCompile false) do
      withOptions (maxHeartbeats.set · remaining) do
        compileDecl declaration
  let _ ← bounded began
  return mkConst name


private def blocks (began : Nat) : MetaM (Array Expr) := do
  let mapping ← replacements began
  let templates := GuardFrontier.templates.getState (← getEnv)
  unless templates.size == 3773 do throwError "original guard inventory changed"
  let mut result : Array Expr := #[]
  let mut seen : ExprSet := {}
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
        throwError "original support block depends on a temporary reader or hypothesis"
      unless seen.contains coefficients do
        seen := seen.insert coefficients
        result := result.push coefficients
  unless result.size == 2203 do throwError "original distinct coefficient block count changed"
  return result

private def applyRule (agreement : Expr) (rule : Name)
    (extra : Array (Name × Expr) := #[]) : MetaM Expr := do
  let args := (← inferType agreement).getAppArgs
  let read := args[args.size-5]!
  let domain := args[args.size-4]!
  let source := args[args.size-3]!
  let target := args[args.size-2]!
  let mut signature := (← getConstInfo rule).type
  let mut parameters : Array (Option Expr) := #[]
  while let .forallE name _ body _ := signature do
    let value := if let some (_, value) := extra.find? (·.1 == name) then some value
      else if name == `read then some read
      else if name == `S then some domain
      else if name == `sourceSign then some source
      else if name == `targetSign then some target
      else none
    parameters := parameters.push value
    signature := body
  withTransparency .all (mkAppOptM rule parameters)

private def pointType (agreement value : Expr) : MetaM Expr := do
  let .forallE _ _ body _ ← whnf (← inferType (mkApp agreement value)) |
    throwError "finite agreement lost its membership premise"
  if body.hasLooseBVars then throwError "agreement data depends on its membership proof"
  return body

private def pointTrace (began : Nat) (message : String) : MetaM Unit := do
  let _ ← bounded began
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"point reuse: {message} heartbeat={((← IO.getNumHeartbeats)-began)/1000}"
      handle.flush

/-- Prove native coefficient equality before transporting point data. This
keeps comparison out of the chosen interpretation's opaque domain predicate. -/
private def reusePoint (began : Nat) (agreement type candidate : Expr) : MetaM (Option Expr) := do
  let obtained ← inferType candidate
  unless type.getAppFn.isConstOf ``And && obtained.getAppFn.isConstOf ``And do return none
  let .app domain wanted := type.getAppArgs[0]! | return none
  let .app oldDomain original := obtained.getAppArgs[0]! | return none
  unless domain == oldDomain do return none
  let equation ← mkEq wanted original
  let decision ← synthInstance (mkApp (mkConst ``Decidable) equation)
  let proposed := mkAppN (mkConst ``of_decide_eq_true)
    #[equation, decision, ← mkEqRefl (mkConst ``Bool.true)]
  pointTrace began "native equality check begins"
  let some equality ← checkCandidate began equation proposed `pointCoefficientEquality | return none
  pointTrace began "native equality checked"
  let predicate ← withLocalDeclD `coefficient (← inferType wanted) fun coefficient => do
    mkLambdaFVars #[coefficient] (← pointType agreement coefficient)
  let congruence ← mkAppM ``congrArg #[predicate, equality]
  let transported ← mkAppM ``Eq.mpr #[congruence, candidate]
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `basePointAgreement)
  pointTrace began "transported point check begins"
  let proof ← retainAt began name type transported
  pointTrace began "transported point checked"
  return some proof

syntax (name := originalBaseAgreement) "#original_base_agreement " num num : command
@[command_elab originalBaseAgreement]
unsafe def elaborate : CommandElab := fun stx => liftTermElabM <| withExporting (isExporting := false) do
  let some start := stx[1].isNatLit? | throwError "agreement start is not literal"
  let some limit := stx[2].isNatLit? | throwError "agreement limit is not literal"
  let began ← IO.getNumHeartbeats
  let all ← blocks began
  unless start < limit && limit ≤ all.size do throwError "invalid original support range"
  let agreement := mkConst ``GuardInventoryReplay.agreement
  let dataType ← inferType agreement
  let dataArgs := dataType.getAppArgs
  let domain := dataArgs[dataArgs.size-4]!
  let indexed ← GuardCoefficientIndex.prepare began agreement
  let codec ← mkAppM ``BaseContext.Element.codec #[mkConst ``FiniteBaseProbe.base]
  let encoder ← current began (← mkAppM ``SignDet.ValueCodec.encode #[codec])
  let wirePoints ← IO.mkRef ({} : PHashMap String Expr)
  let remembered := (← getEnv).checked.get.constants.fold (fun found name info =>
    if info.isTheorem && info.levelParams.isEmpty && info.type.getAppFn.isConstOf ``And &&
        info.type.getAppArgs[0]!.getAppFn == domain.getAppFn then
      found.insert info.type (mkConst name) else found) ({} : PHashMap Expr Expr)
  let points ← IO.mkRef remembered
  let mut pointCount : Nat := 0
  let mut reusedWirePoints : Nat := 0
  let mut positionProofs : Nat := 0
  let mut results : Array Expr := #[]
  for index in [start:limit] do
    let block := all[index]!
    let mut remaining := block
    let mut values : Array Expr := #[]
    for _ in [:10000] do
      let _ ← bounded began
      let literal ← withTransparency .all (whnf remaining)
      if literal.getAppFn.isConstOf ``List.nil then break
      unless literal.getAppFn.isConstOf ``List.cons do throwError "nonliteral original support block"
      let args := literal.getAppArgs
      values := values.push args[1]!
      remaining := args[2]!
    unless (← withTransparency .all (whnf remaining)).getAppFn.isConstOf ``List.nil do
      throwError "original support block exhausted its literal bound"
    let mut combined ← applyRule agreement ``Transport.Inventory.Agreement.nil
    for value in values.reverse do
      let required ← pointType agreement value
      let head ← if let some proof := (← points.get).find? required then pure proof else do
        let named ← current began (← expandValue began value)
        let program := mkApp encoder named
        let encoded ← evalExpr SignDet.Codec.Json (← inferType program) program (checkMeta := false)
        let key := reprStr encoded
        let candidate ← if let some candidate := (← wirePoints.get).find? key then
            reusePoint began agreement required candidate
          else pure none
        let proof ← if let some proof := candidate then do
            reusedWirePoints := reusedWirePoints + 1
            pure proof
          else do
            let some retained ← indexed (mkApp domain named) |
              throwError "original coefficient has no first-support position"
            let some name := retained.constName? | throwError "coefficient index returned an unnamed proof"
            let .thmInfo info ← getConstInfo name | throwError "coefficient index did not retain a theorem"
            unless info.value.getAppFn.isConstOf ``And.left do
              throwError "coefficient index no longer projects its complete agreement data"
            let full := info.value.getAppArgs.back!
            let name := mkPrivateName (← getEnv) (← mkFreshUserName `basePointAgreement)
            let proof ← retainAt began name required full
            positionProofs := positionProofs + 1
            pure proof
        unless ((← wirePoints.get).find? key).isSome do
          wirePoints.modify (·.insert key proof)
        points.modify (·.insert required proof)
        pointCount := pointCount + 1
        pure proof
      combined ← applyRule agreement ``Transport.Inventory.Agreement.cons
        #[(`x, value), (`head, head), (`tail, combined)]
    let required := mkAppN dataType.getAppFn (dataArgs.set! (dataArgs.size-1) block)
    let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardBaseAgreement ++
      Name.mkSimple s!"block{index}"
    let proof ← retainAt began name required combined
    results := results.push proof
    logInfo m!"original base agreement kernel checked: block={index} coefficients={values.size}"
  logInfo m!"original base agreement module export: start={start} limit={limit} blocks={results.size} pointProofs={pointCount} exactNativeCandidatesRechecked={reusedWirePoints} positionProofs={positionProofs} originalUniqueBlocks=2203 sameBaseInterpretation=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#original_base_agreement 0 16

end Hex.RealClosure.Algebraic.KernelReplay.GuardBaseAgreement
