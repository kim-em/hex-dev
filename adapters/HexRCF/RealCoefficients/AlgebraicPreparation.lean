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
open Hex Lean Meta Qq

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
  /-- Continue proof construction under the same reflection limits. -/
  config : Hex.RealFormula.Reify.Config

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
  List.ofFn (Fin.natAdd environment.source.coefficients.size)

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

private def entry (source : Expr) (prepared : Coefficients.Prepared) :
    Hex.RealFormula.Reify.ReifyM Entry := do
  let expression ← instantiateMVars prepared.value
  let identity ← instantiateMVars prepared.proof
  unless !expression.hasFVar && !expression.hasMVar && !expression.hasLooseBVars do
    throwError "rcf: native algebraic input is not closed"
  let expression ← Hex.RCF.checkExpr `AlgebraicPreparation.input expression
  -- Interpretation's debug kernel check does not enforce this exact target
  -- or screen its axioms. Retain the checked, private source identity.
  Hex.RealFormula.Reify.accountProof identity
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
  -- Reification checked the raw equivalence. Charge its additional private
  -- retention before the kernel check; later assembly checks only this constant.
  let retain : Hex.RealFormula.Reify.ReifyM Unit :=
    Hex.RealFormula.Reify.accountProof source.proof
  let retained ← (retain.run
    {config, budget := {initial := config.ring.budget, consumed := source.usage}}).run
  let usage ← match retained with
    | .error error => return .error error
    | .ok (_, state) => pure state.budget.consumed
  let sourceType ← mkAppM ``Iff
    #[← mkAppM ``RealFormula.Prenex.toProp #[source.formula, source.valuation], target]
  let equivalence ← Hex.RCF.checkProof `AlgebraicPreparation.equivalence sourceType source.proof
  let source := {source with proof := equivalence}
  let .quant quantifier (.matrix formula) ← FieldRuntime.evalFormula source.coefficients.size source.formula
    | return .error (.unsupported target "expected exactly one real quantifier")
  Core.checkInterrupted
  let interpreted ← ((do
    let coefficients ← Vector.ofFnM fun i : Fin source.coefficients.size =>
      Coefficients.interpret source.coefficients[i] nonnegative
    let divisors ← Vector.ofFnM fun i : Fin source.divisors.size =>
      Coefficients.interpret source.divisors[i] nonnegative
    let coefficients ← Vector.ofFnM fun i => entry source.coefficients[i] coefficients[i]
    let divisors ← Vector.ofFnM fun i => entry source.divisors[i] divisors[i]
    pure (coefficients,divisors)).run
      {config,budget := {initial := config.ring.budget,consumed := usage}}).run
  match interpreted with
  | .error error => return .error error
  | .ok ((coefficients,divisors),state) =>
    return .ok {
      source := source
      formula := formula
      quantifier := quantifier
      usage := state.budget.consumed
      config := config
      coefficients := coefficients
      divisors := divisors }

/-- Prepare closed algebraic coefficients directly for native selected
presentations. Reuse shared source lowering, all original divisor obligations
and aggregate reflection accounting. Unsupported syntax and resource failures
remain distinct; failed attempts restore the complete elaborator state.
The source equivalence consumes proof budget during reification and again
when retained as a checked private theorem for later composition.
Proposals require executable closed constructions. Native compilation failures
and exceptions from callbacks are terminal, rather than syntax declines. -/
def prepare (target : Expr) (nonnegative : Expr → MetaM (Option Expr) := FieldRuntime.nonnegative)
    (config : Hex.RealFormula.Reify.Config := {}) :
    MetaM (Except Hex.RealFormula.Reify.Error Inputs) := do
  let saved ← saveState
  let depthLimit := (← readThe Core.Context).maxRecDepth
  let auxName := mkPrivateName (← getEnv) (← mkFreshUserName `AlgebraicPreparation)
  let (result,_) ← tryFinally' (withDeclNameForAuxNaming auxName <| withNewMCtxDepth <| Core.withIncRecDepth <|
      withOptions (fun options => maxRecDepth.set
        (debug.skipKernelTC.set (Elab.async.set options false) false) depthLimit)
      (prepareCore target nonnegative config)) fun result => do
    match result with
    | some (.ok _) => modify fun state => {state with
        mctx := saved.meta.mctx, postponed := saved.meta.postponed,
        zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
    | _ => saved.restore
  return result

private def sourceFunction (entries : Array Entry) (sources : Array Expr)
    (expected : Expr) : Hex.RealFormula.Reify.ReifyM (Expr × Expr) := do
  unless entries.size == sources.size do throwError "source identity count differs from its source coordinates"
  let zero : Q(RealAlgebraicNumber) := q(RealAlgebraicNumber.ofRat 0)
  let mut values : Array Expr := #[]
  let mut proofs : Array Expr := #[]
  for (entry, source) in entries.zip sources do
    Core.checkInterrupted
    let value ← instantiateMVars entry.expression
    unless !value.hasFVar && !value.hasMVar && !value.hasLooseBVars do
      throwError "source acceptance requires closed algebraic expressions"
    let value ← Hex.RCF.checkExpr `sourceAcceptanceValue value
    let type ← mkEq (← mkAppM ``RealAlgebraicNumber.toReal #[value]) source
    Hex.RealFormula.Reify.accountProof entry.identity
    let proof ← Hex.RCF.checkProof `sourceAcceptanceIdentity type entry.identity
    Core.checkInterrupted
    values := values.push value
    proofs := proofs.push proof
  let function ← FieldLiteral.finiteExpr (mkConst ``RealAlgebraicNumber) values zero
  let domain := mkApp (mkConst ``Fin) (mkNatLit entries.size)
  let pointwise ← withLocalDeclD `i domain fun i => do
    let actual ← mkAppM ``RealAlgebraicNumber.toReal #[mkApp function i]
    mkForallFVars #[i] (← mkEq actual (mkApp expected i))
  let identity ← mkAppM ``funext #[← FieldLiteral.proveFinCases pointwise proofs]
  Core.checkInterrupted
  return (function, identity)

private def acceptanceCore (prepared : Inputs) (target registry : Expr) :
    Hex.RealFormula.Reify.ReifyM Expr := do
  Core.checkSystem "rcf source acceptance"
  let source := prepared.source
  let original ← instantiateMVars source.original
  let target ← instantiateMVars target
  unless original == target do throwError "source acceptance has a different original target"
  let divisors ← Reify.guardSources target
  let retained ← source.divisors.mapM instantiateMVars
  unless divisors == retained do
    throwError "source acceptance has a different original divisor inventory"
  let sourceType ← mkAppM ``Iff
    #[← mkAppM ``RealFormula.Prenex.toProp #[source.formula, source.valuation], original]
  Hex.RealFormula.Reify.accountProof source.proof
  let equivalence ← Hex.RCF.checkProof `sourceAcceptanceEquivalence sourceType source.proof
  let schema := (← whnf source.formula).consumeMData
  unless schema.isAppOfArity ``RealFormula.Prenex.quant 3 do
    throwError "source acceptance requires exactly one real quantifier"
  let args := schema.getAppArgs
  let quantifier := args[args.size-2]!
  let matrix := (← whnf args.back!).consumeMData
  unless matrix.isAppOfArity ``RealFormula.Prenex.matrix 2 do
    throwError "source acceptance requires a shared quantifier-free matrix"
  let formula := matrix.getAppArgs.back!
  let (values, coefficientEq) ← sourceFunction prepared.coefficients.toArray
    source.coefficients source.valuation
  let realZero : Q(ℝ) := q(0)
  let realDivisors ← FieldLiteral.finiteExpr (mkConst ``Real) source.divisors realZero
  let (divisors, divisorEq) ← sourceFunction prepared.divisors.toArray source.divisors realDivisors
  let registry ← Hex.RCF.checkExpr `sourceAcceptanceRegistry registry
  let proof ← mkAppM ``AlgebraicCells.accepts_source
    #[registry, values, divisors, source.valuation, realDivisors,
      formula, quantifier, coefficientEq, divisorEq, equivalence]
  Hex.RealFormula.Reify.accountProof proof
  let type ← inferType proof
  Hex.RCF.checkProof `sourceAcceptance type proof

/-- Connect mathematical producer acceptance at the retained kernel algebraic
expressions to the exact expected target and original divisors after checked
alias substitution. This returns an equivalence, not evidence of acceptance.
It does not authenticate runtime proposals or frozen source histories.

Each proof is charged before checking it. The returned usage continues the
preparation's aggregate budget, including a fresh original-divisor inventory
scan. Callers must thread it into later stages with `{prepared with usage}`.
Exhaustion, failure and interruption restore the complete saved state. -/
def Inputs.acceptanceIff (prepared : Inputs) (target registry : Expr) :
    MetaM (Except Hex.RealFormula.Reify.Error (Expr × Hex.Reflect.BudgetUsage)) := do
  let saved ← saveState
  let depthLimit := (← readThe Core.Context).maxRecDepth
  let auxName := mkPrivateName (← getEnv) (← mkFreshUserName `SourceAcceptance)
  let (result, _) ← tryFinally' (withDeclNameForAuxNaming auxName <| withNewMCtxDepth <| Core.withIncRecDepth <|
      withOptions (fun options => maxRecDepth.set
        (debug.skipKernelTC.set (Elab.async.set options false) false) depthLimit) do
    let action := acceptanceCore prepared target registry
    let state : Hex.RealFormula.Reify.State := {
      config := prepared.config
      budget := {initial := prepared.config.ring.budget, consumed := prepared.usage} }
    let accounted ← (action.run state).run
    match accounted with
    | .error error => return .error error
    | .ok (proof, state) => return .ok (proof, state.budget.consumed)) fun result => do
      match result with
      | some (.ok _) => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed,
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
      | _ => saved.restore
  return result

end Hex.RCF.RealCoefficients.AlgebraicPreparation
