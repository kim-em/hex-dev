/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexRealFormulaMathlib.Reify.Assemble

public meta section

/-! Shared polynomial-formula reification with a valuation-parametric equivalence. -/

namespace Hex.RealFormula.Reify

open Lean Meta Qq

/-- Source identities distinguish binders even when their user names coincide. -/
structure Binder where
  id : Nat
  name : Name

/-- A reification result contains closed syntax and proofs over arbitrary free
valuations. Binder metadata contains stable indices, never escaped local constants. -/
structure Result where
  parameters : Array Expr
  binders : Array Binder
  /-- Each entry names a source binder and its normalized kind. Its output
  coordinate is `parameters.size + index`, including copies from iff expansion. -/
  prefixMap : Array (Nat × Quantifier)
  /-- Ring-atom order mapped to parameters followed by source-binder identities. -/
  sealedMap : Array Nat
  scopedFormula : Expr
  formula : Expr
  /-- A function from `Fin parameters.size → ℝ` to the source proposition. -/
  source : Expr
  /-- `∀ ρ, Prenex.toProp formula ρ ↔ source ρ`. -/
  proof : Expr
  qf? : Option Expr
  /-- The same contract with QF semantics, available for quantifier-free inputs. -/
  qfProof? : Option Expr
  usage : Reflect.BudgetUsage

/-- Structured declines carry the caller's source location. -/
structure Diagnostic where
  reference : Syntax
  reason : Error

def Error.toMessageData : Error → MessageData
  | .unsupported source reason => m!"{reason}{indentExpr source}"
  | .budget reason => reason.toMessageData
  | .formulaBudget limit requested =>
      m!"formula-node budget exceeded: {requested} nodes, limit {limit}"
  | .providerDeclined reason _ _ => reason.toMessageData
  | .providerFailure reason _ => reason.toMessageData
  | .providerConditions cs => m!"ring provider returned {cs.size} undischarged conditions"
  | .internal reason => m!"proof reconstruction failed: {reason}"

private structure Universal where
  source : Expr
  proof : Expr
  qfProof? : Option Expr

private def universalAt (params : Array Expr) (source : Expr) (r : ScopedResult)
    (ρ : Expr) : ReifyM Universal := do
  let n := params.size
  let values ← (Array.range n).mapM fun i => do pure (mkApp ρ (← quoteFin n i))
  let sourceSchema ← mkLambdaFVars params source
  let proofSchema ← mkLambdaFVars params r.proof
  let valuationSchema ← mkLambdaFVars params (← valuation params)
  let sourceAt := mkAppN sourceSchema values
  let proofAt := mkAppN proofSchema values
  let valuationAt := mkAppN valuationSchema values
  let hv ← prove (← mkEq valuationAt ρ) (← `(tactic| funext i; fin_cases i <;> rfl))
  let h ← mkAppM ``Scoped.transport #[r.expr, valuationAt, ρ, sourceAt, hv, proofAt]
  let hn ← mkAppM ``Scoped.toPrenex_correct #[r.expr, ρ]
  let proof ← mkLambdaFVars #[ρ] (← mkAppM ``Iff.trans #[hn, h])
  let qfProof? ← r.qf?.mapM fun qf => do
    let target := mkApp2 (mkConst ``Iff) (← mkAppM ``QF.toProp #[qf, ρ]) sourceAt
    unless ← isDefEq (← inferType h) target do
      abort (.internal "quantifier-free proof disagrees with scoped semantics")
    mkLambdaFVars #[ρ] (← mkExpectedTypeHint h target)
  return ⟨← mkLambdaFVars #[ρ] sourceAt, proof, qfProof?⟩

private def universal (params : Array Expr) (source : Expr) (r : ScopedResult) : ReifyM Universal := do
  let state ← get
  let n : Q(ℕ) := toExpr params.size
  let outcome ← liftM <| withLocalDeclD `ρ q(Fin $n → ℝ) fun ρ =>
    ((universalAt params source r ρ).run state).run
  match outcome with
  | .error e => abort e
  | .ok (u, state) => set state; return u

private def finish (params : Array Expr) (source : Expr) (tree : Tree) : ReifyM Result := do
  formulaBudget tree.nodeCount
  let state ← get
  let allCoords := params ++ state.binders
  let budget := { state.budget.remaining with
    exponent := state.budget.initial.exponent
    coefficientBits := state.budget.initial.coefficientBits }
  let ringConfig := { state.config.ring with budget }
  let (outcome, conditions) ← Reflect.run (do
    let outcome ← Reflect.ringBatch state.inputs .lex ringConfig
    pure (outcome, ← Reflect.conditions)) ringConfig
  let batch ← match outcome with
    | .success b _ => pure b
    | .declined reason usage => abort (.providerDeclined reason usage conditions)
    | .failure reason => abort (.providerFailure reason conditions)
    | .notApplicable => abort (.unsupported source "no ring provider applies")
  unless conditions.isEmpty do abort (.providerConditions conditions)
  for dimension in [Reflect.BudgetDimension.sourceNodes, .atoms, .reflectedNodes,
      .exponent, .terms, .coefficientBits, .proofNodes] do
    charge dimension (batch.usage.get dimension)
  let sealedMap ← batch.sealed.atoms.mapM fun atom => do
    unless atom.isFVar do
      abort (.unsupported atom "opaque ring atoms are not declared real coordinates")
    match allCoords.toList.idxOf? atom with
    | some i => pure i
    | none => abort (.unsupported atom "ring atom belongs to a different binder scope")
  let r ← assemble batch tree
  if r.expr.hasFVar || r.expr.hasMVar then
    abort (.internal "reified syntax contains an escaped local constant or metavariable")
  let u ← universal params source r
  let u : Universal := { u with
    proof := ShareCommon.shareCommon u.proof
    qfProof? := u.qfProof?.map ShareCommon.shareCommon }
  if u.proof.hasFVar || u.source.hasFVar then
    abort (.unsupported source "equivalence depends on an undeclared parameter or local hypothesis")
  accountProof u.proof
  -- Check the complete generated proof, including every coordinate transport.
  checkWithKernel u.proof
  for h in u.qfProof? do checkWithKernel h
  let binders ← state.binders.mapIdxM fun id x => do
    pure { id, name := (← x.fvarId!.getDecl).userName : Binder }
  return {
    parameters := params, binders, prefixMap := tree.prefix false, sealedMap
    scopedFormula := r.expr, formula := ← mkAppM ``Scoped.toPrenex #[r.expr]
    source := u.source, proof := u.proof, qf? := r.qf?, qfProof? := u.qfProof?
    usage := (← get).budget.consumed }

/-- Reify a real proposition over the explicitly ordered real parameters.
Selected local hypotheses become visible antecedents; no other hypothesis is used.
All atom differences are reflected together after scope-aware collection. -/
def reify (source : Expr) (parameters : Array Expr := #[]) (assumptions : Array Expr := #[])
    (config : Config := {}) : MetaM (Except Diagnostic Result) := do
  let action : ReifyM Result := do
    let source ← instantiateMVars source
    if source.hasMVar then abort (.unsupported source "unresolved source metavariable")
    unless ← isProp source do abort (.unsupported source "expected a proposition")
    for i in [:parameters.size] do
      let p := parameters[i]!
      unless p.isFVar && !(parameters.extract 0 i).contains p do
        abort (.unsupported p "parameters must be distinct declared real local constants")
      if (← p.fvarId!.getDecl).isLet then
        abort (.unsupported p "parameters must be local constants, not local definitions")
      unless ← isDefEq (← inferType p) (mkConst ``Real) do
        abort (.unsupported p "parameters must have type Real")
    let mut proposition := source
    for h in assumptions.reverse do
      let type ← inferType h
      unless ← isProp type do abort (.unsupported h "selected assumption is not a proof")
      proposition ← mkArrow type proposition
    let cap := (← get).budget.remaining.sourceNodes
    charge .sourceNodes (Reflect.sourceNodeCount proposition (cap + 1))
    collect proposition parameters (finish parameters proposition)
  let outcome ← (action.run { config, budget := .ofBudget config.ring.budget }).run
  return match outcome with
    | .ok (result, _) => .ok result
    | .error reason => .error ⟨config.reference, reason⟩

/-- Elaborator-facing entry point, reporting a structured decline at the supplied source location. -/
def reify! (source : Expr) (parameters : Array Expr := #[]) (assumptions : Array Expr := #[])
    (config : Config := {}) : MetaM Result := do
  match ← reify source parameters assumptions config with
  | .ok result => return result
  | .error diagnostic =>
    throwErrorAt diagnostic.reference "real-formula: {diagnostic.reason.toMessageData}"

end Hex.RealFormula.Reify
