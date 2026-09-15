/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Translate
public import HexReflect.Session
public import Lean.Elab.Tactic.Config
public import Lean.Meta.Closure
public meta import HexKronecker
public meta import HexKroneckerMathlib.Translate

public section

namespace HexKroneckerMathlib

/-- The two independent preflight limits shared by both frontends. -/
structure Config extends Hex.Kronecker.Budget

end HexKroneckerMathlib

public meta section

namespace HexKroneckerMathlib

open Lean Meta Elab

deriving instance ToExpr for Hex.Kronecker.Expr
deriving instance ToExpr for Hex.Kronecker.Budget

declare_config_elab elabConfig Config

private def reflected (r : Hex.Reflect.ProviderOutcome α) : MetaM α := do
  match r with
  | .success a _ => return a
  | .notApplicable => throwUnsupportedSyntax
  | .declined (.unsupportedCarrier _) _
  | .declined (.unsupportedView ..) _
  | .declined (.unresolvedMetavariable _) _ => throwUnsupportedSyntax
  | .declined d _ => throwError "kronecker declined: {d.toMessageData}"
  | .failure f => throwError "kronecker failure: {f.toMessageData}"

private def requirement (n limit : Nat) : String :=
  if limit < n then s!"at least {limit + 1}" else toString n

/-- One shared reflection session and one synchronous kernel certificate check. -/
def prove (cfg : Config) (target : Lean.Expr) : MetaM Lean.Expr := do
  let target ← instantiateMVars target
  let some (carrier, lhs, rhs) := target.eq? | throwUnsupportedSyntax
  if carrier.hasMVar then throwUnsupportedSyntax
  let u ← getDecLevel carrier
  let some inst ← synthInstance? (mkApp (mkConst ``CommRing [u]) carrier)
    | throwUnsupportedSyntax
  let (k, le, re, ctx) ← Hex.Reflect.run do
    let l ← reflected (← Hex.Reflect.reifyCommRing lhs)
    let r ← reflected (← Hex.Reflect.reifyCommRing rhs)
    let s ← Hex.Reflect.sealAtoms
    let ctx ← Hex.Reflect.contextExpr (← Hex.Reflect.ringOf l) s
    return (s.n, l.expr, r.expr, ctx)
  let some l := fromGrind? k le | throwError "kronecker failure: variable outside sealed atoms"
  let some r := fromGrind? k re | throwError "kronecker failure: variable outside sealed atoms"
  let budget := cfg.toBudget
  let .ok size := Hex.Kronecker.sizeExprEq budget k l r
    | throwError "kronecker failure: ill-formed reflected tree"
  unless size.accepts budget do
    let degrees := if budget.maxDenseDigits < size.digits then
      s!"; per-atom degree bounds {size.degrees}" else ""
    throwError "kronecker declined: dense box requires {requirement size.digits budget.maxDenseDigits} digits and {requirement size.packedBits budget.maxPackedBits} packed bits (limits {budget.maxDenseDigits} digits, {budget.maxPackedBits} bits){degrees}"
  let valuation := mkApp2 (mkConst ``Lean.RArray.get [u]) carrier ctx
  let certificate := mkApp2 (mkConst ``Eq.refl [.succ .zero])
    (mkConst ``Bool) (mkConst ``Bool.true)
  let proof := mkAppN (mkConst ``Hex.Kronecker.checkExprEq_sound [u])
    #[toExpr budget, mkNatLit k, toExpr l, toExpr r, certificate, carrier, inst, valuation]
  let proof := mkAppN (mkConst ``denote_transport [u])
    #[carrier, inst, ctx, toExpr le, toExpr re, proof]
  let some (_, denotedL, denotedR) := (← inferType proof).eq?
    | throwError "kronecker failure: malformed soundness application"
  unless (← isDefEq denotedL lhs) && (← isDefEq denotedR rhs) do
    throwUnsupportedSyntax
  try
    withOptions (Elab.async.set · false) do
      mkAuxTheorem target proof (zetaDelta := true) (cache := false)
  catch ex =>
    -- Diagnose only after rejection; accepted certificates are never evaluated by Meta.
    if !Hex.Kronecker.checkExprEq budget k l r then
      throwError "kronecker: goal is not a polynomial identity in the sealed atoms"
    throwError "kronecker failure: kernel rejected certificate: {ex.toMessageData}"

syntax (name := kroneckerTac) &"kronecker" optConfig : tactic
syntax (name := kroneckerTerm) "kronecker%" "(" term ")" : term

@[tactic kroneckerTac, no_fallback]
def evalKronecker : Tactic.Tactic := fun stx => Tactic.withMainContext do
  let cfg ← elabConfig stx[1]
  let proof ← prove cfg (← Tactic.getMainTarget)
  Tactic.closeMainGoal `kronecker proof

@[term_elab kroneckerTerm, no_fallback]
def elabKronecker : Term.TermElab := fun stx _ => do
  let target ← Term.elabType stx[2]
  Term.synthesizeSyntheticMVarsNoPostponing
  prove {} target

end HexKroneckerMathlib
