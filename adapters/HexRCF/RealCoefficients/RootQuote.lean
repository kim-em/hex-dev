/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootReplay
public import HexRealClosure.TowerContext
public meta import HexRCF.RealCoefficients.Reify
public meta import HexRCF.Tactic
public meta section

namespace Hex.RCF.RealCoefficients.RootQuote
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RealFormula.Reify

/-- Propose an ordinary equality for one demanded scalar decode. A missing
proposal leaves other literal rules available. Proposed equations are checked
against that exact decode before being used. -/
abbrev Decoder := Expr → MetaM (Option Expr)

/-- Reconstructed data and the checked equation from the original reader to
that data. Usage continues the caller's reflection request. -/
structure Result where
  value : Expr
  proof : Expr
  usage : Hex.Reflect.BudgetUsage

private def replayRules : Array (Name × Name × Bool) := #[
  (``SignTable.count, ``Replay.table_lookup, false),
  (``Dag.replay?, ``Dag.replay_eq, false),
  (``Dag.step, ``Dag.step_eq, false),
  (``Node.check, ``Node.check_eq, false),
  (``checkMoment, ``checkMoment_eq, false),
  (``TarskiCertificate.checkCached, ``TarskiCertificate.checkCached_eq, false),
  (``TarskiCertificate.check, ``TarskiCertificate.check_eq, false),
  (``Array.toList, ``Array.toList_range, false),
  (``Array.all, ``Array.all_toList, true),
  (``Array.foldlM, ``Array.foldlM_toList, true)]

private def numericHeads : Array Name := #[
  ``Nat.add,``Nat.sub,``Nat.mul,``Nat.div,``Nat.mod,``Nat.pow,``Nat.gcd,
  ``Nat.beq,``Nat.ble,``Nat.land,``Nat.lor,``Nat.xor,``Nat.shiftLeft,``Nat.shiftRight]

private partial def irreducible? (protectedNames : Array Name) (expression : Expr)
    : ReifyM (Option Name) := Core.withIncRecDepth do
  charge .proofNodes 1
  Core.checkSystem "literal reader reducibility boundary"
  let reduced ← withTransparency .default (whnf expression)
  if let some name := reduced.getAppFn.constName? then
    if protectedNames.contains name then return none
    if (← getReducibilityStatus name) == .irreducible then
      if let .defnInfo _ ← getConstInfo name then return some name
  match reduced with
  | .proj _ _ body => irreducible? protectedNames body
  | .mdata _ body => irreducible? protectedNames body
  | _ =>
    if let .proj _ _ body := reduced.getAppFn then
      return ← irreducible? protectedNames body
    if let some name := reduced.getAppFn.constName? then
      if numericHeads.contains name then
        for argument in reduced.getAppArgs do
          if let some stuck ← irreducible? protectedNames argument then return some stuck
    if let .const name _ := reduced.getAppFn then
      if let .recInfo recursor ← getConstInfo name then
        if let some major := reduced.getAppArgs[recursor.getMajorIdx]? then
          return ← irreducible? protectedNames major
    return none

private def replayWhnf (expression : Expr) : ReifyM Expr :=
  withoutModifyingEnv <| withFreshCache do
    let protectedNames := replayRules.filterMap fun rule =>
      if #[``Array.toList,``Array.all,``Array.foldlM].contains rule.1 then none else some rule.1
    for name in protectedNames do setReducibilityStatus name .irreducible
    while true do
      charge .proofNodes 1
      Core.checkSystem "literal reader reducibility budget"
      let reduced ← withOptions (fun options => smartUnfolding.set options false) do
        withTransparency .default (whnf expression)
      let some name ← irreducible? protectedNames reduced | return reduced
      setReducibilityStatus name .semireducible
      resetCache
    throwError "rcf: literal reducibility loop terminated unexpectedly"

private def replayProof? (expression : Expr) : ReifyM (Option Expr) := do
  if expression.hasLooseBVars || expression.hasMVar then return none
  let some head := expression.getAppFn.constName? | return none
  for (key,name,inverse) in replayRules do
    if head == key then
      let ruleConst ← mkConstWithFreshMVarLevels name
      let (parameters,_,_) ← forallMetaTelescopeReducing (← inferType ruleConst)
      let proof := mkAppN ruleConst parameters
      let proof ← if inverse then mkEqSymm proof else pure proof
      let type ← inferType proof
      unless type.isAppOfArity ``Eq 3 do throwError "public replay rule is not an equation"
      let lhs := type.getAppArgs[1]!
      if ← withTransparency .all <| isDefEq lhs expression then
        let proof ← instantiateMVars proof
        unless !proof.hasMVar do throwError "public replay rule left unresolved arguments"
        return some proof
  return none

private def codecProof? (decode : Decoder) (expression : Expr) : ReifyM (Option Expr) := do
  charge .proofNodes 1
  if expression.hasLooseBVars || expression.hasMVar then return none
  if let .proj ``ValueCodec 1 codec := expression.getAppFn then
    if codec.isAppOfArity ``Tower.contextCodec 1 && expression.getAppNumArgs == 1 then
      let proof ← mkAppM ``Tower.contextCodec_self #[codec.appArg!]
      let type ← inferType proof
      if ← withTransparency .all <| withNewMCtxDepth (isDefEq expression type.getAppArgs[1]!) then
        return some proof
  let saved ← (saveState : MetaM SavedState)
  let candidate ← try decode expression catch error =>
    saved.restore
    throw error
  let some proof := candidate | do
    saved.restore
    return none
  let proof ← instantiateMVars proof
  let type ← whnf (← inferType proof)
  unless type.isAppOfArity ``Eq 3 do throwError "rcf: literal codec proposal is not an equation"
  let statement ← mkEq expression type.getAppArgs[2]!
  let proof := mkExpectedPropHint proof statement
  accountProof proof
  return some (← Hex.RCF.checkProof `RootQuote.codec statement proof)

private def reflexiveProof? (expression : Expr) : ReifyM (Option Expr) := do
  unless expression.getAppFn.isConstOf ``withPtrEqDecEq do return none
  let type ← whnf (← inferType expression)
  unless type.isAppOfArity ``Decidable 1 do return none
  let proposition := type.appArg!
  unless proposition.isAppOfArity ``Eq 3 do return none
  let args := proposition.getAppArgs
  unless ← withTransparency .all <| withNewMCtxDepth (isDefEq args[1]! args[2]!) do return none
  let accepted := mkApp2 (mkConst ``Decidable.isTrue) proposition (← mkEqRefl args[1]!)
  return some (← mkAppM ``Subsingleton.elim #[expression,accepted])
private partial def demanded (decode : Decoder) (dependent : Expr → ReifyM Expr) (expression : Expr) :
    ReifyM (Option (Expr × Expr × Expr)) := Core.withIncRecDepth do
  charge .proofNodes 1
  Core.checkSystem "demanded literal-reader boundary"
  if let some proof ← replayProof? expression then return some (expression,expression,proof)
  if let some proof ← codecProof? decode expression then return some (expression,expression,proof)
  if let some proof ← reflexiveProof? expression then return some (expression,expression,proof)
  let reduced ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (replayWhnf expression)
  if let some proof ← replayProof? reduced then return some (reduced,reduced,proof)
  if let some proof ← codecProof? decode reduced then return some (reduced,reduced,proof)
  if let some proof ← reflexiveProof? reduced then return some (reduced,reduced,proof)
  match reduced with
  | .proj name index body =>
    let some (expanded,subject,proof) ← demanded decode dependent body | return none
    return some (.proj name index expanded,subject,proof)
  | .mdata metadata body =>
    let some (expanded,subject,proof) ← demanded decode dependent body | return none
    return some (.mdata metadata expanded,subject,proof)
  | _ =>
    if let .proj name index body := reduced.getAppFn then
      let some (expanded,subject,proof) ← demanded decode dependent body | return none
      return some (mkAppN (.proj name index expanded) reduced.getAppArgs,subject,proof)
    if let some name := reduced.getAppFn.constName? then
      if numericHeads.contains name then
        let args := reduced.getAppArgs
        for index in [:args.size] do
          if let some (expanded,subject,proof) ← demanded decode dependent args[index]! then
            return some (mkAppN reduced.getAppFn (args.set! index expanded),subject,proof)
    if let .const name _ := reduced.getAppFn then
      if let .recInfo recursor ← getConstInfo name then
        let args := reduced.getAppArgs
        if name == ``Bool.rec && args.size > recursor.getMajorIdx+1 then
          let proof ← dependent reduced
          return some (reduced,reduced,proof)
        if let some major := args[recursor.getMajorIdx]? then
          let some (expanded,subject,proof) ← demanded decode dependent major | return none
          return some (mkAppN reduced.getAppFn
            (args.set! recursor.getMajorIdx expanded),subject,proof)
    return none

private def checkedStep (current whole subject law : Expr) : ReifyM (Expr × Expr) := do
  let type ← inferType subject
  let lawType ← inferType law
  let rhs := lawType.getAppArgs[2]!
  let motive ← withLocalDeclD `boundary type fun boundary => do
    let body := whole.replace fun expression => if expression == subject then some boundary else none
    mkLambdaFVars #[boundary] body
  unless motive.bindingBody!.hasLooseBVars do
    throwError "demanded boundary does not occur in its reconstructed reader"
  let next := motive.bindingBody!.instantiate1 rhs
  if next == whole then throwError "demanded boundary made no change"
  let statement ← mkEq current next
  let candidate := mkExpectedPropHint (← mkAppM ``congrArg #[motive,law]) statement
  accountProof candidate
  let proof ← Hex.RCF.checkProof `RootQuote.step statement candidate
  return (next,proof)


private def checkedBool (decode : Decoder) (dependent : Expr → ReifyM Expr) (original : Expr) : ReifyM (Bool × Expr) := do
  let mut current := original
  let mut transport ← mkEqRefl original
  while true do
    charge .proofNodes 1
    let reduced ← withOptions (fun options => smartUnfolding.set options false) do
      withTransparency .all (replayWhnf current)
    if reduced.isConstOf ``Bool.true || reduced.isConstOf ``Bool.false then
      let value := reduced.isConstOf ``Bool.true
      let statement ← mkEq original (mkConst (if value then ``Bool.true else ``Bool.false))
      let candidate := mkExpectedPropHint transport statement
      accountProof candidate
      let proof ← Hex.RCF.checkProof `RootQuote.major statement candidate
      return (value,proof)
    let some (whole,subject,law) ← demanded decode dependent reduced
      | throwError "rcf: literal Boolean replay remains at {reduced.getAppFn.constName?}"
    let (next,proof) ← checkedStep current whole subject law
    current := next
    transport ← mkEqTrans transport proof
  throwError "rcf: literal Boolean loop terminated unexpectedly"

private partial def discharge (decode : Decoder) (node : Expr) : ReifyM Expr := Core.withIncRecDepth do
  Core.checkSystem "dependent decision discharge"
  unless node.isAppOfArity ``Bool.rec 5 do
    throwError "dependent sibling is not a single Boolean reflects_decide argument: {node.getAppFn.constName?}, arguments={node.getAppNumArgs}"
  let args := node.getAppArgs
  let witness := args[4]!
  let (condition,decision) ← do
    if witness.isAppOfArity ``Decidable.reflects_decide 2 then
      let fields := witness.getAppArgs
      pure (fields[0]!,fields[1]!)
    else if let .proj ``Decidable 1 decision := witness then
      let type ← inferType decision
      unless type.isAppOfArity ``Decidable 1 do throwError "invalid decision dictionary"
      pure (type.appArg!,decision)
    else throwError "dependent sibling is not reflects_decide"
  let (value,majorProof) ← checkedBool decode (discharge decode) args[3]!
  let decisionBool := mkApp2 (mkConst ``Decidable.decide) condition decision
  let literal := mkConst (if value then ``Bool.true else ``Bool.false)
  let decisionStatement ← mkEq decisionBool literal
  let candidate := mkExpectedPropHint majorProof decisionStatement
  accountProof candidate
  let decisionProof ← Hex.RCF.checkProof `RootQuote.decision decisionStatement candidate
  let branchProof := mkApp3
    (mkConst (if value then ``of_decide_eq_true else ``of_decide_eq_false))
    condition decision decisionProof
  let alpha ← inferType node
  let level ← getLevel alpha
  let branch := if value then args[2]! else args[1]!
  let proof := mkAppN
    (mkConst (if value then ``dite_eq_left else ``dite_eq_right) [level])
    #[condition,decision,branchProof,alpha,args[2]!,args[1]!]
  let statement ← mkEq node (mkApp branch branchProof)
  let candidate := mkExpectedPropHint proof statement
  accountProof candidate
  let proof ← Hex.RCF.checkProof `RootQuote.discharge statement candidate
  return proof

private partial def quoteCore (reader : Expr) (decode : Decoder) : ReifyM Result := do
  accountProof reader
  let reader ← Hex.RCF.checkExpr `RootQuote.reader reader
  let type ← whnf (← inferType reader)
  unless type.isAppOfArity ``Except 2 && type.getAppArgs[0]!.isConstOf ``String do
    throwError "rcf: expected a literal Except String reader"
  let original ← mkAppM ``Except.toOption #[reader]
  let mut current := original
  let mut transport ← mkEqRefl original
  while true do
    charge .proofNodes 1
    Core.checkSystem "literal root quotation"
    let reduced ← replayWhnf current
    if reduced.getAppFn.isConstOf ``Option.some then
      let value := reduced.getAppArgs.back!
      let conversion ← mkEq current reduced
      let conversion := mkExpectedPropHint (← mkEqRefl reduced) conversion
      let complete ← mkEqTrans transport conversion
      let statement ← mkEq original reduced
      let candidate := mkExpectedPropHint complete statement
      accountProof candidate
      let proof ← Hex.RCF.checkProof `RootQuote.accepted statement candidate
      return ⟨value,proof,(← get).budget.consumed⟩
    if reduced.getAppFn.isConstOf ``Option.none then
      abort (.providerFailure (.invalidProviderEvidence ⟨`Hex.RCF.RealCoefficients.RootQuote,0⟩
        "literal reader rejected its supplied input") #[])
    let some (whole,subject,law) ← demanded decode (discharge decode) reduced
      | throwError "rcf: literal root replay remains at {reduced.getAppFn.constName?}"
    let (next,proof) ← checkedStep current whole subject law
    current := next
    transport ← mkEqTrans transport proof
  throwError "rcf: literal quotation loop terminated unexpectedly"

/-- Quote a supplied literal replay reader with an ordinary-kernel equation
`Except.toOption reader = some value`. Public replay laws eliminate checked
caches, and core conditional laws retain dependent proof arguments. Every
step consumes the existing reflection budget. Success restores caller
metavariables and retains checked auxiliaries and accepted decoder callbacks'
environment effects; rejection or failure restores
the complete saved state. Source identities and real semantics compose with
this reader equation separately. No handler is registered here. -/
def quote (reader : Expr) (decode : Decoder := fun _ => pure none)
    (config : Hex.RealFormula.Reify.Config := {})
    (usage : Hex.Reflect.BudgetUsage := Hex.Reflect.Budget.zero) :
    MetaM (Except Hex.RealFormula.Reify.Error Result) := do
  let saved ← saveState
  let depthLimit := (← readThe Core.Context).maxRecDepth
  let auxName := mkPrivateName (← getEnv) (← mkFreshUserName `RootQuote)
  let action := ((quoteCore reader decode).run
    {config,budget := {initial := config.ring.budget,consumed := usage}}).run
  let (result,_) ← tryFinally' (withDeclNameForAuxNaming auxName <| withNewMCtxDepth <|
      Core.withIncRecDepth <| withOptions (fun options => maxRecDepth.set
        (debug.skipKernelTC.set (Elab.async.set options false) false) depthLimit) action)
    fun result => do
      match result with
      | some (.ok _) => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed,
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
      | _ => saved.restore
  return result.map (·.1)

end Hex.RCF.RealCoefficients.RootQuote
