/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealCoefficients.SectionBuild
import HexRCF.RealCoefficients.SectionQuote
import HexRCF.RealCoefficients.ScalarPacket
import HexRCF.SelectedRoot.RowCollect
import HexRCF.SelectedRoot.RowTools
import HexRCF.RealCoefficients.FieldRuntime
import HexRCF.ProofEvidence
import HexRCF.SectionReplayConformance

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
open Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper
open Lean Meta Elab Tactic
namespace Hex.RCF.RealCoefficients.SectionProduceConformance

def guardNat (n : Nat) : parent.Value :=
  @NatCast.natCast parent.Value
    (Algebraic.Element.cachedNatCast reduction reduction_eq []) n

theorem guardNat_value (n : Nat) : original.value (guardNat n) = (n : ℝ) := by
  unfold guardNat
  erw [Algebraic.Element.cachedNatCast_eq]
  exact original.nat n

meta section

private unsafe def evalPacketUnsafe (expression : Expr) : MetaM
    (Except SectionBuild.Error (Option SectionBuild.Packet)) := do
  evalExpr (Except SectionBuild.Error (Option SectionBuild.Packet))
    (← inferType expression) expression
@[implemented_by evalPacketUnsafe]
private opaque evalPacket (expression : Expr) : MetaM
    (Except SectionBuild.Error (Option SectionBuild.Packet))

private unsafe def evalJsonUnsafe (expression : Expr) : MetaM (Option Codec.Json) := do
  evalExpr (Option Codec.Json) (← inferType expression) expression
@[implemented_by evalJsonUnsafe]
private opaque evalJson (expression : Expr) : MetaM (Option Codec.Json)

mutual
private partial def jsonExpr : Codec.Json → Expr
  | .null => mkConst ``Codec.Json.Value.null
  | .bool value => mkApp (mkConst ``Codec.Json.Value.bool) (toExpr value)
  | .number value => mkApp (mkConst ``Codec.Json.Value.number) (toExpr value)
  | .string value => mkApp (mkConst ``Codec.Json.Value.string) (toExpr value)
  | .array values => mkApp (mkConst ``Codec.Json.Value.array) (arrayExpr values)
  | .object fields => mkApp (mkConst ``Codec.Json.Value.object) (fieldsExpr fields)
private partial def arrayExpr : Codec.Json.Values → Expr
  | .nil => mkConst ``Codec.Json.Values.nil
  | .cons value rest => mkAppN (mkConst ``Codec.Json.Values.cons) #[jsonExpr value, arrayExpr rest]
private partial def fieldsExpr : Codec.Json.Fields → Expr
  | .nil => mkConst ``Codec.Json.Fields.nil
  | .cons key value rest => mkAppN (mkConst ``Codec.Json.Fields.cons)
      #[toExpr key, jsonExpr value, fieldsExpr rest]
end

private def rules : MetaM Simp.Context := do
  let mut rules ← RowTools.rules
  for name in #[``SectionReplay.checkWith, ``SectionReplay.rowCodec,
      ``Algebraic.RootReplay.readContext, ``Algebraic.Context.changeOps, ``ScalarPacket.read] do
    rules ← rules.addDeclToUnfold name
  Simp.mkContext (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)

def producers : Array Name :=
  #[``SectionBuild.build, ``ScalarPacket.build, ``ScalarPacket.buildLiteral,
    ``Algebraic.Context.buildEvidence, ``Tower.Sample.family]

private def restoreProposal (scope : Name) (packet : Codec.Json) : MetaM Expr := do
  let context := mkConst ``native
  let value ← mkAppM ``Tower.Context.codec #[mkConst ``base]
  let .ok fields := packet.getArr? | throwError "scalar producer returned malformed fields"
  unless fields.size == 3 do throwError "scalar producer returned wrong field count"
  let .ok claimed := Codec.Json.decode (α := Int) fields[1]! | throwError "invalid scalar sign"
  let args := #[mkConst ``rational, value, context, jsonExpr fields[0]!,
    toExpr claimed, jsonExpr fields[2]!]
  let read ← mkAppM ``ScalarPacket.read args
  let predicate ← mkAppM ``Option.isSome #[read]
  let proposition ← mkEq predicate (mkConst ``Bool.true)
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let reflexivity ← mkEqRefl (mkConst ``Bool.true)
  let proof := mkAppN (mkConst ``of_decide_eq_true)
    #[proposition, dictionary, reflexivity]
  let name ← mkFreshUserName (scope ++ `sectionScalarAccepted)
  let _ ← Algebraic.KernelReplay.auditProof proof proposition
  KernelCheck.addChecked name proposition proof producers
  return ← mkAppM ``ScalarPacket.restore (args.push (mkConst name))

private def supply (scope : Name) (seen : IO.Ref (ExprMap Unit))
    (needed : Algebraic.KernelReplay.Request)
    (_inventory : Array Algebraic.KernelReplay.Inventory) : MetaM (Option Expr) := do
  unless needed.kind == .coefficient do return none
  unless ← isDefEq needed.context (mkConst ``native) do return none
  let context := mkConst ``native
  let value ← mkAppM ``Tower.Context.codec #[mkConst ``base]
  let key := mkApp (mkConst ``reduction) needed.polynomial
  let encoded ← mkAppM ``Codec.poly #[value, key]
  let encoded ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (reduce encoded)
  if (← seen.get).contains encoded then
    throwError "repeated reduced scalar request after checked supply"
  seen.modify (fun keys => keys.insert encoded ())
  let producer ← mkAppM ``ScalarPacket.buildLiteral #[context, value, encoded]
  let some packet ← evalJson producer | throwError "scalar production failed"
  let .ok fields := packet.getArr? | throwError "scalar producer returned malformed fields"
  unless fields.size == 3 do throwError "scalar producer returned wrong field count"
  unless ← isDefEq (jsonExpr fields[0]!) encoded do
    throwError "scalar producer changed the requested key"
  return some (← restoreProposal scope packet)

private def seed (scope : Name) (coefficients : List Codec.Json) : MetaM Expr := do
  let type ← whnf (← inferType (mkConst ``RowCollect.facts))
  let mut facts ← mkListLit type.getAppArgs.back! []
  let mut count := 0
  let value ← mkAppM ``Tower.Context.codec #[mkConst ``base]
  for coefficient in coefficients.eraseDups do
    let .ok fields := coefficient.getArr? | throwError "malformed predecessor coefficient hint"
    if fields.isEmpty then continue
    unless fields.size == 2 do throwError "malformed algebraic predecessor hint"
    let producer ← mkAppM ``ScalarPacket.buildLiteral
      #[mkConst ``native, value, jsonExpr fields[0]!]
    let some packet ← evalJson producer | throwError "initial scalar production failed"
    let fact ← restoreProposal scope packet
    facts ← mkAppM ``List.cons #[fact, facts]
    count := count + 1
  logInfo m!"checked scalar seeds={count}; pre-supplied fixture facts=0"
  let name ← mkFreshUserName (scope ++ `sectionSeed)
  let type ← inferType facts
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type, value := facts, hints := .regular 0, safety := .safe }
  let env ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true)
  setEnv env
  compileDecl declaration (logErrors := true)
  return mkConst name

private def trueResult (expression : Expr) : MetaM Expr := do
  let type ← whnf (← inferType expression)
  pure (mkAppN (mkConst ``Except.ok [.zero, .zero])
    (type.getAppArgs.push (mkConst ``Bool.true)))

private def requireRefusal (action : MetaM Expr) : MetaM Unit := do
  let constants := (← getEnv).constants.map₂.toList.length
  let before ← getMCtx
  let refused ← try
    let _ ← action
    pure false
  catch _ => pure true
  unless refused do throwError "source binding accepted an altered input"
  unless (← getEnv).constants.map₂.toList.length == constants do
    throwError "failed source quotation changed the environment"
  let after ← getMCtx
  unless after.mvarCounter == before.mvarCounter &&
      after.lmvarCounter == before.lmvarCounter &&
      after.depth == before.depth &&
      after.eAssignment.toList == before.eAssignment.toList &&
      after.lAssignment.toList == before.lAssignment.toList do
    throwError "failed source quotation changed the metavariable state"

private def proveCore (scope : Name) (target : Expr) (controls : Bool) : MetaM Expr := do
  let .ok source ← Reify.prepare target | throwError "source rejected"
  unless source.coefficients.size == 1 do
    throwError "this production probe expects one authenticated coefficient"
  let formula ← whnf source.formula
  unless formula.getAppFn.isConstOf ``RealFormula.Prenex.quant do throwError "expected quantifier"
  let quantifier := formula.getAppArgs[formula.getAppArgs.size - 2]!
  unless ← isDefEq quantifier (mkConst ``Hex.RealFormula.Quantifier.existsReal) do
    throwError "this production probe expects an existential source"
  let matrixFormula ← whnf formula.getAppArgs.back!
  unless matrixFormula.getAppFn.isConstOf ``RealFormula.Prenex.matrix do
    throwError "expected one matrix"
  let matrix := matrixFormula.getAppArgs.back!
  let guardType ← inferType (mkConst ``alpha)
  let mut guardValues := #[]
  let mut guardIdentities := #[]
  for divisor in source.divisors do
    let some (number, _) ← getOfNatValue? divisor ``Real
      | throwError "this probe only authenticates literal natural divisors"
    let guard ← mkAppM ``guardNat #[mkNatLit number]
    guardValues := guardValues.push guard
    guardIdentities := guardIdentities.push (← mkAppM ``guardNat_value #[mkNatLit number])
  let guards ← mkListLit guardType guardValues.toList
  let production ← mkAppM ``SectionBuild.build #[mkConst ``parent, mkConst ``values, guards, matrix]
  Core.checkInterrupted
  let packet ← match ← evalPacket production with
    | .ok (some packet) => pure packet
    | .ok none => throwError "no supported selected-section witness"
    | .error .divisor => throwError "original divisor preflight rejected"
    | .error .unresolved => throwError "selected-section row unresolved"
    | .error (.production error) => throwError "selected-section production failed: {reprStr error}"
  Core.checkInterrupted
  let value ← mkAppM ``Tower.Context.codec #[mkConst ``base]
  let factsType ← inferType (mkConst ``RowCollect.facts)
  let checkerWith ← withLocalDeclD `facts factsType fun facts => do
    let codec ← mkAppM ``Algebraic.Element.signCodec #[value, facts]
    let mut operations := #[]
    let mut equalities := #[]
    for (operation, equality) in #[
        (``Algebraic.Element.cachedOne, ``Algebraic.Element.cachedOne_eq),
        (``Algebraic.Element.cachedAdd, ``Algebraic.Element.cachedAdd_eq),
        (``Algebraic.Element.cachedNeg, ``Algebraic.Element.cachedNeg_eq),
        (``Algebraic.Element.cachedSub, ``Algebraic.Element.cachedSub_eq),
        (``Algebraic.Element.cachedMul, ``Algebraic.Element.cachedMul_eq),
        (``Algebraic.Element.cachedInv, ``Algebraic.Element.cachedInv_eq),
        (``Algebraic.Element.cachedDiv, ``Algebraic.Element.cachedDiv_eq),
        (``Algebraic.Element.cachedNatCast, ``Algebraic.Element.cachedNatCast_eq)] do
      let args := #[mkConst ``reduction, mkConst ``reduction_eq, facts]
      operations := operations.push (← mkAppM operation args)
      equalities := equalities.push (← mkAppM equality args)
    let args := #[mkConst ``original, codec, mkConst ``values, guards, matrix] ++
      operations ++ equalities ++ #[jsonExpr packet.subject, jsonExpr packet.graph, jsonExpr packet.row]
    mkLambdaFVars #[facts] (← mkAppM ``SectionReplay.checkWith args)
  let program ← withLocalDeclD `facts factsType fun facts => do
    let result := mkApp checkerWith facts
    let target ← trueResult result
    let equation ← mkEq result target
    let decision ← synthInstance (mkApp (mkConst ``Decidable) equation)
    mkLambdaFVars #[facts] (mkAppN (mkConst ``Decidable.decide) #[equation, decision])
  let initial ← seed scope packet.coefficients
  let seen ← IO.mkRef ({} : ExprMap Unit)
  let collected ← Algebraic.KernelReplay.collectMany 96 program
    #[⟨initial⟩] (← rules) (supply scope seen)
  let decisionProof ← match collected.outcome with
    | .checked true proof _ => pure proof
    | .checked false .. => throwError "frozen section replay rejected the proposed row"
    | .missing application => throwError "frozen section lacks a reached record: {application}"
  let some inventory := collected.inventories[0]? | throwError "missing scalar inventory"
  let facts := inventory.facts
  let checkWith := (mkApp checkerWith facts).headBeta
  let equationType ← trueResult checkWith
  let equationType ← mkEq checkWith equationType
  let accepted ← mkAppM ``of_decide_eq_true #[decisionProof]
  let acceptanceName ← mkFreshUserName (scope ++ `sectionAccepted)
  let _ ← Algebraic.KernelReplay.auditProof accepted equationType
  KernelCheck.addChecked acceptanceName equationType accepted producers
  let accepted := mkConst acceptanceName
  let args := checkWith.getAppArgs
  let equality ← mkAppM ``SectionReplay.checkWith_eq (args.extract (args.size-24) args.size)
  let checker := (← inferType equality).getAppArgs[2]!
  let accepted ← mkAppM ``Eq.mp #[← mkAppM ``congrArg
    #[← withLocalDeclD `result (← inferType checker) fun result => do
        mkLambdaFVars #[result] (← mkEq result (← trueResult result)),
      equality], accepted]
  let valuation ← withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit 1)) fun i => do
    mkLambdaFVars #[i] (← mkAppM ``Tower.Model.value
      #[mkConst ``original, mkApp (mkConst ``values) i])
  let identity ← mkFreshExprMVar (← mkEq valuation source.valuation)
  let remaining ← Lean.Elab.runTactic' identity.mvarId!
    (← `(tactic| funext i; fin_cases i; exact Data.alpha_value))
  unless remaining.isEmpty do throwError "source valuation not authenticated"
  logInfo m!"fresh section packet; reached scalar requests={collected.requests.size}"
  let identity ← instantiateMVars identity
  if !controls then
    return ← SectionQuote.finish target checker accepted identity guardIdentities
  if source.divisors != source.divisors.reverse then
    requireRefusal (SectionQuote.finish target checker accepted identity guardIdentities.reverse)
  if !guardIdentities.isEmpty then
    requireRefusal (SectionQuote.finish target checker accepted identity guardIdentities.pop)
  let existential ← whnf target
  unless existential.getAppFn.isConstOf ``Exists do throwError "expected source existential"
  let body := existential.getAppArgs.back!
  let wrongTarget ← withLocalDeclD `x (mkConst ``Real) fun x => do
    mkForallFVars #[x] ((mkApp body x).headBeta)
  let wrongMatrix ← withLocalDeclD `x (mkConst ``Real) fun x => do
    let reflexive ← mkEq x x
    let disjunction := mkApp2 (mkConst ``Or) ((mkApp body x).headBeta) reflexive
    mkAppM ``Exists #[← mkLambdaFVars #[x] disjunction]
  for candidate in #[wrongTarget, wrongMatrix] do
    let .ok recognized ← Reify.prepare candidate
      | throwError "binding control failed source recognition"
    unless recognized.divisors == source.divisors &&
        (← isDefEq recognized.valuation source.valuation) do
      throwError "binding control changed original divisors or coefficients"
    requireRefusal (SectionQuote.finish candidate checker accepted identity guardIdentities)
  SectionQuote.finish target checker accepted identity guardIdentities

private def prove (scope : Name) (target : Expr) (controls : Bool) : MetaM Expr := do
  let saved ← saveState
  let (proof, _) ← tryFinally' (proveCore scope target controls)
    (fun result => unless result.isSome do saved.restore)
  return proof

elab "produced_section" controls:("checked")? : tactic => do
  let goal ← getMainGoal
  let some scope ← Term.getDeclName? | throwError "expected a declaration context"
  let proof ← prove scope (← goal.getType) controls.isSome
  goal.assign proof
  replaceMainGoal []
end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem quoted : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by
  produced_section checked

#print axioms quoted

set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem negativeWitness : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ x < 0 := by
  produced_section checked

#print axioms negativeWitness

set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem guardedWitness : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧
    1 < x ∧ x / 2 < 1 ∧ x / 3 < 1 := by
  produced_section checked

#print axioms guardedWitness

def cancelledSentence : Prop :=
  ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 0 / (Real.sqrt 2 - Real.sqrt 2) = 0

run_meta do
  let candidate ← Lean.Meta.withTransparency .all
    (Lean.Meta.whnf (Lean.mkConst ``cancelledSentence))
  let .ok recognized ← Reify.prepare candidate
    | Lean.throwError "cancelled original divisor failed recognition"
  unless recognized.divisors.size == 1 do
    Lean.throwError "recognition discarded the cancelled original divisor"
  let proof := Lean.mkConst ``quoted
  let _ ← Hex.RCF.checkProof ``quoted (← Lean.Meta.inferType proof) proof
  for name in #[``quoted, ``negativeWitness, ``guardedWitness, ``ScalarPacket.fields] do
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "source quotation has an unexpected complete inventory"
  for name in #[``quoted, ``negativeWitness, ``guardedWitness] do
    for producer in producers do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf producer) then
        Lean.throwError "source quotation retains a producer"
    for law in #[``SectionReplay.check_sound, ``ScalarPacket.restore] do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
        Lean.throwError "source quotation omitted its actual replay law"

end Hex.RCF.RealCoefficients.SectionProduceConformance
