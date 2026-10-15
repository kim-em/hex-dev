/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.AlgebraicCells
public meta import HexRCF.RealCoefficients.AlgebraicCells
public meta import HexRCF.RealCoefficients.FieldRuntime
public meta section

/-! Prepare original algebraic inputs for the native packet producer without
constructing a primitive common field. Source identities are kernel proofs;
computed values are proposals. This does not quote a complete certificate or
install a tactic handler. In particular the producer's native context is not
a frozen source/history certificate. -/
namespace Hex.RCF.RealCoefficients.AlgebraicPreparation
open Hex Lean Meta

/-- A checked source interpretation and its executable proposal. The proof
identifies `expression.toReal` with the source, not with a quoted proposal. -/
structure Entry where
  expression : Expr
  identity : Expr
  proposal : RealAlgebraicNumber

/-- Shared source syntax and independently ordered coefficients and divisors.
Divisors remain present when absent from the normalized matrix. -/
structure Inputs where
  source : Reify.Source
  coefficients : Vector Entry source.coefficients.size
  divisors : Vector Entry source.divisors.size
  formula : RealFormula.QF (source.coefficients.size+1)
  quantifier : RealFormula.Quantifier
  usage : Hex.Reflect.BudgetUsage

/-- Keep coefficient coordinates first and every original divisor afterward.
No equality of independently computed algebraic representations is assumed. -/
def Inputs.inputs (environment : Inputs) :
    Fin (environment.source.coefficients.size + environment.source.divisors.size) → RealAlgebraicNumber :=
  Fin.addCases (fun i => environment.coefficients[i].proposal)
    (fun i => environment.divisors[i].proposal)

def Inputs.indices (environment : Inputs) : Fin environment.source.coefficients.size →
    Fin (environment.source.coefficients.size + environment.source.divisors.size) :=
  Fin.castAdd environment.source.divisors.size

def Inputs.guards (environment : Inputs) :
    List (Fin (environment.source.coefficients.size + environment.source.divisors.size)) :=
  (List.finRange environment.source.divisors.size).map (Fin.natAdd environment.source.coefficients.size)

/-- The original selected presentations and their complete native packet. -/
abbrev Inputs.Result (environment : Inputs) (registry : RealClosure.BaseContext.Registry) :=
  (sources : (i : Fin (environment.source.coefficients.size + environment.source.divisors.size)) →
    RealClosure.NumberField.Presentation (environment.inputs i) registry) ×
    AlgebraicCells.Packet sources environment.indices environment.guards environment.formula

/-- Raw native packet production on the proposals. No compiled result
authenticates a source expression or supplies an ordinary-kernel goal proof. -/
def Inputs.build (environment : Inputs) (registry : RealClosure.BaseContext.Registry) :=
  AlgebraicCells.build registry environment.inputs environment.indices environment.guards environment.formula

-- The strict argument to this non-inlined call is evaluated before its
-- cancellation check. Keeping the packet in an argument also avoids returning
-- its higher universe through MetaM/BaseIO, whose result lives in Type.
@[noinline, nospecialize] private def consumeBuilt (inputs : Inputs) (registry : RealClosure.BaseContext.Registry)
    (result : Except AlgebraicCells.Error (inputs.Result registry))
    (consume : Except AlgebraicCells.Error (inputs.Result registry) → MetaM α) : MetaM α := do
  Core.checkInterrupted
  consume result

/-- Observe cancellation before and after native production, then pass the
complete higher-universe packet to a meta consumer. The compiled call itself
has no internal interruption checkpoint. No failure starts a different solver. -/
def Inputs.buildWith (environment : Inputs) (registry : RealClosure.BaseContext.Registry)
    (consume : Except AlgebraicCells.Error (environment.Result registry) → MetaM α) : MetaM α := do
  Core.checkInterrupted
  consumeBuilt environment registry (environment.build registry) consume

private def entry (source : Expr) (prepared : Coefficients.Prepared) : MetaM Entry := do
  let expression ← instantiateMVars prepared.value
  let identity ← instantiateMVars prepared.proof
  unless !expression.hasFVar && !expression.hasMVar && !expression.hasLooseBVars do
    throwError "rcf: native algebraic input is not closed"
  let expression ← Hex.RCF.checkExpr `AlgebraicPreparation.input expression
  -- Interpretation's debug kernel check does not enforce this exact target
  -- or screen its axioms. Retain the checked, private source identity.
  let identity ← Hex.RCF.checkProof `AlgebraicPreparation.identity
    (← mkEq (← mkAppM ``RealAlgebraicNumber.toReal #[expression]) source) identity
  Core.checkInterrupted
  let proposal ← FieldRuntime.evalReal expression
  Core.checkInterrupted
  return ⟨expression,identity,proposal⟩

private def prepareCore (target : Expr) (nonnegative : Expr → MetaM (Option Expr))
    (config : Hex.RealFormula.Reify.Config) :
    MetaM (Except Hex.RealFormula.Reify.Error Inputs) := do
  let source ← match ← Reify.prepare target config with
    | .ok source => pure source
    | .error error => return .error error
  Core.checkInterrupted
  let .quant quantifier (.matrix formula) ← FieldRuntime.evalFormula source.coefficients.size source.formula
    | return .error (.unsupported target "expected exactly one real quantifier")
  Core.checkInterrupted
  let interpreted ← ((do
    let coefficients ← Vector.ofFnM fun i : Fin source.coefficients.size =>
      Coefficients.interpret source.coefficients[i] nonnegative
    let divisors ← Vector.ofFnM fun i : Fin source.divisors.size =>
      Coefficients.interpret source.divisors[i] nonnegative
    pure (coefficients,divisors)).run
      {config,budget := {initial := config.ring.budget,consumed := source.usage}}).run
  match interpreted with
  | .error error => return .error error
  | .ok ((coefficients,divisors),state) =>
    let coefficients ← Vector.ofFnM fun i => entry source.coefficients[i] coefficients[i]
    let divisors ← Vector.ofFnM fun i => entry source.divisors[i] divisors[i]
    return .ok {
      source := source
      formula := formula
      quantifier := quantifier
      usage := state.budget.consumed
      coefficients := coefficients
      divisors := divisors }

/-- Prepare closed algebraic coefficients directly for native selected
presentations. Reuse shared source lowering, all original divisor obligations
and aggregate reflection accounting. Unsupported syntax and resource failures
remain distinct; failed attempts restore the complete elaborator state.
Proposals require executable closed constructions. Native compilation failures
and exceptions from callbacks are terminal, rather than syntax declines. -/
def prepare (target : Expr) (nonnegative : Expr → MetaM (Option Expr) := FieldRuntime.nonnegative)
    (config : Hex.RealFormula.Reify.Config := {}) :
    MetaM (Except Hex.RealFormula.Reify.Error Inputs) := do
  let saved ← saveState
  let auxName := mkPrivateName (← getEnv) (← mkFreshUserName `AlgebraicPreparation)
  let (result,_) ← tryFinally' (withDeclNameForAuxNaming auxName <| withNewMCtxDepth <| withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false)
      (prepareCore target nonnegative config)) fun result => do
    match result with
    | some (.ok _) => modify fun state => {state with
        mctx := saved.meta.mctx, postponed := saved.meta.postponed,
        zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
    | _ => saved.restore
  return result
end Hex.RCF.RealCoefficients.AlgebraicPreparation
