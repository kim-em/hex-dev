/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.GeneratorWindowInputs
public meta import HexRCF.GeneratorWindowInputs
public meta import HexRCF.RealCoefficients.FieldCompile
public meta import HexRCF.RealCoefficients.FieldTransport
public meta import Lean.Elab.Command
public section
open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta Qq
open Hex.RCF.GeneratorWindowTests
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option debug.skipKernelTC false
set_option Elab.async false
run_meta do
  let pExpr := q(SquareTwo.polynomial)
  let rootExpr := q(root)
  let args := #[pExpr,q(SquareTwo.square),q(hw),q(hp)]
  let rep ← mkAppM ``Field.literalRep args
  let hrep ← mkAppM ``Field.literalRep_mk args
  let hreal ← mkAppM ``Field.literalRep_real (args.push q(real))
  let coordinate := q(theta)
  let scalar : Q(ℝ) ← mkAppM ``Field.value #[rep,coordinate]
  let leaf (source : Expr) : MetaM (Option (FieldCompile.Result SquareTwo.polynomial root)) := do
    if source == scalar then return some ⟨theta,coordinate,← mkEqRefl scalar⟩
    return none
  let count ← IO.mkRef (0 : Nat)
  let nonzero (denominator : FieldCompile.Result SquareTwo.polynomial root) : MetaM Expr := do
    count.modify (·+1)
    let some table := FieldBuild.buildTable SquareTwo.polynomial SquareTwo.square hw hp
        [denominator.value] | throwError "sign production failed"
    let some observed := table.lookup? denominator.value | throwError "missing denominator sign"
    if observed == 0 then throwError "original closed divisor is zero"
    let tableExpr ← FieldLiteral.signTableExpr pExpr rootExpr table
    let check ← mkAppM ``Field.checkSignTable (args.push tableExpr)
    let candidate ← mkFreshExprMVar (← mkEq check q(true))
    let lemmas ← FieldLiteral.evidenceLemmas
    let remaining ← Elab.runTactic' candidate.mvarId! (← `(tactic|
      (simp only [$lemmas,*, Bool.and_eq_true];
       repeat' (any_goals (apply And.intro)); all_goals decide +kernel)))
    unless remaining.isEmpty do throwError "denominator sign replay left goals"
    let checked ← instantiateMVars candidate
    let lookup ← mkAppM ``LiteralSign.Table.lookup? #[tableExpr,denominator.expression]
    let someSign ← mkAppM ``Option.some #[mkIntLit observed]
    let hit ← mkDecideProof (← mkEq lookup someSign)
    let hn ← mkDecideProof (← mkAppM ``Ne #[mkIntLit observed,mkIntLit 0])
    mkAppM ``FieldTransport.nonzero #[tableExpr,checked,denominator.expression,
      mkIntLit observed,hit,hn]
  let cases : Array (Name × Expr × Nat) := #[
    (`Hex.RCF.FiniteFieldCompile.division,q(1 / ($scalar+1)),1),
    (`Hex.RCF.FiniteFieldCompile.inverse,q(($scalar+1)⁻¹),1),
    (`Hex.RCF.FiniteFieldCompile.nested,q(1 / ((1 / ($scalar+1))+1)),2)]
  for (name,source,expectedCalls) in cases do
    count.set 0
    let result ← FieldCompile.compileGuarded pExpr rootExpr rep hrep hreal leaf nonzero source
    unless (← count.get) == expectedCalls do throwError "wrong guard count"
    let interpreted ← mkAppM ``Field.value #[rep,result.expression]
    let expected ← mkEq interpreted source
    let proof ← Hex.RCF.checkProof name expected result.proof
    addDecl (.thmDecl {name,levelParams:=[],type:=expected,value:=proof})
    logInfo m!"GUARDED_COMPILE {name}: checked, guards={expectedCalls}"
  for source in #[q((0 : ℝ) / ($scalar-$scalar)),q(0 * (1 / ($scalar-$scalar)))] do
    let saved ← saveState
    let rejected ← try
      let _ ← FieldCompile.compileGuarded pExpr rootExpr rep hrep hreal leaf nonzero source
      pure false
    catch e => pure (((← e.toMessageData.toString).splitOn "original closed divisor is zero").length > 1)
    saved.restore
    unless rejected do throwError "cancelled zero denominator accepted"
  let saved ← saveState
  let rejected ← try
    let _ ← FieldCompile.compileGuarded pExpr rootExpr rep hrep hreal leaf
      (fun _ => pure q(True.intro)) q(1 / ($scalar+1))
    pure false
  catch _ => pure true
  saved.restore
  unless rejected do throwError "proof of wrong guard accepted"
#print axioms Hex.RCF.FiniteFieldCompile.division
#print axioms Hex.RCF.FiniteFieldCompile.inverse
#print axioms Hex.RCF.FiniteFieldCompile.nested
