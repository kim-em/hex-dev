/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import HexRCF.RealCoefficients.Reify
public meta import HexRCF.RealCoefficients.Interpret
public meta import HexRCF.Reify

public meta section

/-! Evaluate checked source coefficients and shared formulas during search. -/

namespace Hex.RCF.RealCoefficients.FieldRuntime

open Lean Meta Qq

private meta unsafe def evalRealUnsafe (e : Expr) : MetaM RealAlgebraicNumber :=
  evalExpr RealAlgebraicNumber (mkConst ``RealAlgebraicNumber) e

@[implemented_by evalRealUnsafe]
meta opaque evalReal (e : Expr) : MetaM RealAlgebraicNumber

private meta unsafe def evalZPolyUnsafe (e : Expr) : MetaM ZPoly :=
  evalExpr ZPoly (mkConst ``ZPoly) e

@[implemented_by evalZPolyUnsafe]
meta opaque evalZPoly (e : Expr) : MetaM ZPoly

private meta unsafe def evalSquareUnsafe (e : Expr) : MetaM DyadicSquare :=
  evalExpr DyadicSquare (mkConst ``DyadicSquare) e

@[implemented_by evalSquareUnsafe]
meta opaque evalSquare (e : Expr) : MetaM DyadicSquare

private meta unsafe def evalRatPolyUnsafe (e : Expr) : MetaM (DensePoly Rat) := do
  let type ← inferType e
  evalExpr (DensePoly Rat) type e

@[implemented_by evalRatPolyUnsafe]
meta opaque evalRatPoly (e : Expr) : MetaM (DensePoly Rat)

private meta unsafe def evalFormulaUnsafe (n : Nat) (e : Expr) :
    MetaM (RealFormula.Prenex n) :=
  evalExpr (RealFormula.Prenex n)
    (mkApp (mkConst ``RealFormula.Prenex) (mkNatLit n)) e

@[implemented_by evalFormulaUnsafe]
meta opaque evalFormula (n : Nat) (e : Expr) : MetaM (RealFormula.Prenex n)

/-- Prove routine closed nonnegativity obligations of radical bases. -/
private meta def nonnegative (source : Expr) : MetaM (Option Expr) := do
  let x : Q(ℝ) := source
  let goal : Q(Prop) := q(0 ≤ $x)
  let candidate ← mkFreshExprMVar goal
  let saved ← saveState
  try
    let remaining ← Lean.Elab.runTactic' candidate.mvarId! (← `(tactic| norm_num))
    if remaining.isEmpty then return some (← instantiateMVars candidate)
  catch _ => pure ()
  saved.restore
  return none

/-- Interpret one source scalar through the existing algebraic-number API,
then run only that executable construction during certificate search. -/
meta def coefficient (source : Expr) : MetaM (Expr × Expr × RealAlgebraicNumber) := do
  let config : Hex.RealFormula.Reify.Config := {}
  let state : Hex.RealFormula.Reify.State :=
    { config, budget := .ofBudget config.ring.budget }
  let outcome ← ((Coefficients.interpret source nonnegative).run state).run
  let (.ok (prepared, _)) := outcome |
    match outcome with
    | .error error =>
        throwError "rcf: {Hex.RealFormula.Reify.Error.toMessageData error}"
    | .ok _ => unreachable!
  return (prepared.value, prepared.proof, ← evalReal prepared.value)

end Hex.RCF.RealCoefficients.FieldRuntime
