/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareissMathlib.Tactic
public import HexPolyDetMathlib.Small
public import HexPolyDetMathlib.RowFactor
public import HexPolyDetMathlib.RatFactor
public import HexPolyDetMathlib.Structural
public meta import HexBareissMathlib.Tactic
public meta import HexPolyDetMathlib.Small
public meta import HexPolyDetMathlib.RowFactor
public meta import HexPolyDetMathlib.RatFactor
public meta import HexPolyDetMathlib.Structural
public meta import Mathlib.Tactic.Ring
public meta import Lean

public meta section

namespace HexPolyDetMathlib

open Lean Meta Elab HexMatrixMathlib.Literal
open HexMatrixMathlib.DetPoly.Frontend (Outcome Result)

/-- Structural identities and closed forms precede polynomial reification. -/
def compute (A : Expr) (rhs? : Option Expr := none) : MetaM (Outcome Result) := do
  let mut recognized? := none
  if let some (n, m, _) ← shape? (← inferType A) then
    if n == m && n ≤ HexMatrixMathlib.DetPoly.Frontend.maxDimension then
      if let some lit ← literal? A (allowOpen := true) then
        if let some result ← Structural.direct? A lit then return .success result
        if let some result ← profileitM Exception "det.rowFactor" (← getOptions)
            (RowFactor.compute? A lit rhs?) then return .success result
        if let some result ← profileitM Exception "det.ratFactor" (← getOptions)
            (RatFactor.compute? A lit rhs?) then return .success result
        if n ≤ 3 then
          return .success (← profileitM Exception "det.small.formula" (← getOptions) (Small.formula A lit))
        if let some result ← Structural.sparse? A lit then return .success result
        recognized? := some lit
  trace[HexMatrix.certificate] "{(Json.mkObj [("route", toJson "certificate-attempt")]).compress}"
  return ← HexMatrixMathlib.DetPoly.Frontend.compute A rhs? recognized?

/-- Preserve the diagnostic if Mathlib cannot close the original goal. The
symbolic attempt is never repeated through a simproc. -/
def fallback (msg : MessageData) : Tactic.TacticM Unit := do
  trace[HexMatrix.certificate] "{(Json.mkObj [("route", toJson "fallback"),
    ("reason", toJson (← msg.toString))]).compress}"
  Tactic.evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [_root_.norm_det]))
  unless (← Tactic.getGoals).isEmpty do
    try Tactic.evalTactic (← `(tactic| all_goals ring)) catch _ => pure ()
  unless (← Tactic.getGoals).isEmpty do
    throwError "det: symbolic determinant declined: {msg}"

/-- Importing this companion opts into symbolic `det`. Numeric goals delegate
before any symbolic reification; Lean tries this later registration first. -/
@[tactic HexMatrixMathlib.Det.detTac, no_fallback]
def evalDet : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let target ← instantiateMVars (← Tactic.getMainTarget)
  let some (A, rhs, reverse) := HexMatrixMathlib.Det.detTarget? target | throwUnsupportedSyntax
  if let .success _ ← HexMatrixMathlib.Det.recognize A then throwUnsupportedSyntax
  match ← compute A rhs with
  | .notApplicable _ => throwUnsupportedSyntax
  | .declined msg => fallback msg
  | .success p =>
    if ← isDefEq p.value rhs then
      let proof ← if reverse then mkEqSymm p.proof else pure p.proof
      Tactic.closeMainGoal `det proof
    else
      -- Structural and small formulas leave ring normalization: the certificate path
      -- already checks agreement with the requested target in its one batch.
      let saved ← Tactic.saveState
      try
        let goal ← Tactic.getMainGoal
        let r ← goal.rewrite target p.proof
        let goal ← goal.replaceTargetEq r.eNew r.eqProof
        let reduced ← if reverse then mkEq rhs p.value else mkEq p.value rhs
        let goal ← goal.change reduced
        Tactic.setGoals [goal]
        profileitM Exception "det.structural.ring" (← getOptions) do
          Tactic.evalTactic (← `(tactic| ring))
        unless (← Tactic.getGoals).isEmpty do
          throwError "det: symbolic determinant declined: target is not a polynomial identity in the matrix entries: {← Tactic.getMainTarget}"
        if ← isTracingEnabledFor `HexMatrix.certificate then
          let proof ← instantiateMVars (mkMVar goal)
          trace[HexMatrix.certificate] "{(Json.mkObj [("route", toJson "closed-form-ring"),
            ("ring_proof_distinct_nodes", toJson (Hex.Reflect.proofNodeCount #[proof] 1000001))]).compress}"
      catch e =>
        saved.restore
        trace[HexMatrix.certificate] "structural target comparison declined: {e.toMessageData}"
        match ← HexMatrixMathlib.DetPoly.Frontend.compute A rhs with
        | .success p =>
          let proof ← if reverse then mkEqSymm p.proof else pure p.proof
          Tactic.closeMainGoal `det proof
        | .notApplicable _ | .declined _ =>
          fallback m!"structural formula did not close the target: {e.toMessageData}"

/-- The symbolic term form uses the existing syntax kind and result record. -/
@[term_elab HexMatrixMathlib.Det.detTerm]
def elabDet : Term.TermElab := fun stx expectedType? => do
  let saved ← saveState
  let A ← try Term.withoutErrToSorry (elabArgument stx[1]) catch _ => do
    saved.restore
    let A ← Term.elabTerm stx[1] none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars A
  if let .success _ ← HexMatrixMathlib.Det.recognize A then
    saved.restore
    throwUnsupportedSyntax
  match ← compute A with
  | .notApplicable msg => throwError "det: not applicable: {msg}"
  | .declined msg => throwError "det: symbolic determinant declined: {msg}"
  | .success p =>
    let lhs ← mkAppM ``Matrix.det #[A]
    let result ← mkAppOptM ``HexMatrixMathlib.Certified.mk
      #[none, none, some lhs.appFn!, some A, some p.value, some p.proof]
    Term.ensureHasType expectedType? result

end HexPolyDetMathlib

open Lean Meta in
/-- Opt-in symbolic determinant simplification. The published `Hex.norm_det`
keeps its numeric path and unmodified Mathlib fallback. -/
simproc_decl Hex.normPolyDet (Matrix.det _) := fun e => do
  if let .success _ ← HexMatrixMathlib.Det.recognize e.appArg! then
    return ← Hex.norm_det e
  match ← HexPolyDetMathlib.compute e.appArg! with
  | .success p => return .done { expr := p.value, proof? := some p.proof }
  | .notApplicable msg | .declined msg =>
    trace[HexMatrix.certificate] "{(Json.mkObj [("route", toJson "fallback"),
      ("reason", toJson (← msg.toString))]).compress}"
    _root_.norm_det e
