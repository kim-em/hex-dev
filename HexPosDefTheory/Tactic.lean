/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Quote
public meta import HexPosDefTheory.Quote
public meta import HexPosDef.Producer

public meta section

/-! The `pos_def` tactic: closed exact matrix decisions with one kernel certificate check. -/

namespace Hex.PosDefTheory.Tactic

open Lean Meta Elab Tactic
open Hex.PosDef
open HexMatrixTheory.Literal

structure Config where
  method : Method := .triangular

declare_config_elab elabConfig Config

inductive Outcome (α : Type) where
  | notApplicable (message : MessageData)
  | declined (message : MessageData)
  | success (value : α)

def classify (target : Expr) : MetaM (Outcome (Expr × Bool × Recognized)) := do
  let negative := target.isAppOfArity ``Not 1
  let prop := if negative then target.appArg! else target
  unless prop.getAppFn.isConstOf ``Matrix.PosDef do
    return .notApplicable m!"expected `A.PosDef` or `¬ A.PosDef`"
  let A := prop.appArg!
  if A.hasFVar || A.hasMVar then return .notApplicable m!"the matrix must be closed"
  let some lit ← literal? A | return .notApplicable m!"unrecognized closed matrix literal"
  unless lit.n = lit.m do return .notApplicable m!"the matrix must be square"
  unless [``Int, ``Rat, ``Real, ``Complex].any lit.carrier.isConstOf do
    return .notApplicable m!"unsupported carrier {lit.carrier}"
  return .success (A, negative, lit)

def checked (proof : Expr) : MetaM Expr := do
  let target ← inferType proof
  try addClosedProof target proof
  catch e =>
    if e.isRuntime then throw e
    throwError "pos_def: kernel rejection of a supplied certificate (implementation failure): {e.toMessageData}"

def proveInt (cfg : Config) (A : Expr) (negative : Bool) (lit : Recognized) :
    MetaM (Outcome Expr) := do
  if negative && cfg.method == .positiveVector then
    return .declined m!"the positive-vector method accepts positive goals only"
  let input ← try Quote.integer lit A catch e =>
    if e.isRuntime then throw e
    return .declined m!"entry quotation: {e.toMessageData}"
  let B := Hex.Matrix.ofFn fun (i j : Fin lit.n) =>
    PosDef.Lists.get PosDef.Lists.intArithmetic input.rows i j
  let cert ← match PosDef.Int.certify B cfg.method with
    | .ok c => pure c
    | .error (.unsupported reason) => return .declined m!"{reason}"
    | .error .rejected => throwError "pos_def: producer self-validation failed (implementation failure)"
  let (isNegative, checkName, soundName, c) := match cert with
    | .positive c => (false, ``PosDef.Int.checkPositive, ``Int.positive_of_scaled, toExpr c)
    | .negative c => (true, ``PosDef.Int.checkNegative, ``Int.negative_of_scaled, toExpr c)
  let check ← mkEq (← mkAppM checkName #[mkNatLit lit.n, input.rowsExpr, c]) (mkConst ``Bool.true)
  let p ← mkAppM soundName #[lit.carrier, A, mkNatLit input.scale, input.rowsExpr, c,
    input.positiveScale, input.equation, ← decideProof check]
  let p ← checked p
  if isNegative != negative then
    match cert with
    | .positive _ => throwError "pos_def: the matrix has a checked positive certificate"
    | .negative c => throwError "pos_def: the matrix has a checked refutation: {repr c}"
  return .success p

def proveGaussian (A : Expr) (negative : Bool) (lit : Recognized) : MetaM (Outcome Expr) := do
  let input ← try Quote.gaussian lit A catch e =>
    if e.isRuntime then throw e
    return .declined m!"entry quotation: {e.toMessageData}"
  let B := Hex.Matrix.ofFn fun (i j : Fin lit.n) =>
    PosDef.Lists.get PosDef.Lists.gaussianArithmetic input.rows i j
  let cert ← match PosDef.Gaussian.certify B with
    | .ok c => pure c
    | .error (.unsupported reason) => return .declined m!"{reason}"
    | .error .rejected => throwError "pos_def: producer self-validation failed (implementation failure)"
  let (isNegative, checkName, soundName, c) := match cert with
    | .positive c => (false, ``PosDef.Gaussian.checkPositive, ``Gaussian.positive_of_scaled, toExpr c)
    | .negative c => (true, ``PosDef.Gaussian.checkNegative, ``Gaussian.negative_of_scaled, toExpr c)
  let check ← mkEq (← mkAppM checkName #[mkNatLit lit.n, input.rowsExpr, c]) (mkConst ``Bool.true)
  let p ← mkAppM soundName #[A, mkNatLit input.scale, input.rowsExpr, c,
    input.positiveScale, input.equation, ← decideProof check]
  let p ← checked p
  if isNegative != negative then
    match cert with
    | .positive _ => throwError "pos_def: the matrix has a checked positive certificate"
    | .negative c => throwError "pos_def: the matrix has a checked refutation: {repr c}"
  return .success p

def prove (cfg : Config) (target : Expr) : MetaM (Outcome Expr) := do
  match ← classify target with
  | .notApplicable msg => return .notApplicable msg
  | .declined msg => return .declined msg
  | .success (A, negative, lit) =>
    if lit.carrier.isConstOf ``Complex && cfg.method == .triangular then
      proveGaussian A negative lit
    else proveInt cfg A negative lit

/-- Decide exact positive definiteness of a supported closed matrix. -/
syntax (name := posDefTac) &"pos_def" optConfig : tactic

@[tactic posDefTac] def evalPosDef : Tactic := fun stx => withMainContext do
  let cfg ← elabConfig stx[1]
  let target ← instantiateMVars (← getMainTarget)
  match ← prove cfg target with
  | .notApplicable _ => throwUnsupportedSyntax
  | .declined msg => throwError "pos_def: declined: {msg}"
  | .success proof =>
    (← getMainGoal).assign proof
    replaceMainGoal []

end Hex.PosDefTheory.Tactic
