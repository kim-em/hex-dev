/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib.Provider
public meta import HexGenericRankMathlib.Provider
public meta import Lean

public meta section

namespace HexGenericRankMathlib

open Lean Meta Elab Hex.Reflect
open HexMatrixMathlib.Rank (Rel rankTarget?)

/-- Tactic syntax exposes the resource limits; programmatic callers may also
supply condition normalizers through the provider configuration. -/
structure RankConfig where
  reflection : Hex.Reflect.Config := {}
  matrixSize : Nat := 4096
  caseSplits : Nat := 0

declare_config_elab elabRankConfig RankConfig

/-- Read the provider outcome without changing any goals. -/
def result (A : Expr) (cfg : Provider.Config := {}) : MetaM Provider.Result := do
  match ← Provider.rank A cfg with
  | .success r _ => return r
  | .notApplicable => throwUnsupportedSyntax
  | .declined d _ => throwError "rank: declined: {d.toMessageData}"
  | .failure f => throwError "rank: failure: {f.toMessageData}"

/-- Reject a comparison the symbolic certificate does not establish. -/
def checkBound (result : Provider.Result) (other : Expr) (rel : Rel) : MetaM Unit := do
  let r := result.rank
  let some bound ← (Meta.evalNat other).run | throwUnsupportedSyntax
  let ok := match rel with
    | .eq => r == bound
    | .le => r ≤ bound
    | .ge => bound ≤ r
  unless ok do
    let reason : MessageData := match rel with
      | .eq => m!"the requested rank differs from the generic rank {r}"
      | .ge => m!"the unconditional bound `A.rank ≤ {r}` is provable"
      | .le => m!"the requested upper bound may hold after specialisation, but the generic certificate does not establish it"
    throwError "rank: declined: {reason}. Generic rank: {r}; certificate condition: {result.conditional.conditions[0]!.proposition}. Interpreted polynomial matrix: {result.interpretation}. Use rank_locus for the rank-drop set."

/-- Recognize a fraction-field scalar extension and retain its rank transport. -/
def baseMatrix (A : Expr) : MetaM (Expr × Option Expr) := do
  unless A.getAppFn.isConstOf ``Matrix.map do return (A, none)
  let args := A.getAppArgs
  if args.size < 2 then return (A, none)
  let B := args[args.size - 2]!
  let some (n, m, R) ← HexMatrixMathlib.Literal.shape? (← inferType B) | return (A, none)
  let some (_, _, K) ← HexMatrixMathlib.Literal.shape? (← inferType A) | return (A, none)
  try
    let proof ← mkAppOptM ``HexMatrixMathlib.rank_map_eq
      #[R, mkNatLit n, mkNatLit m, none, none, K, none, none, none, B]
    let some (_, lhs, _) := (← inferType proof).eq? | return (A, none)
    unless ← isDefEq lhs (← mkAppM ``Matrix.rank #[A]) do return (A, none)
    return (B, some proof)
  catch _ => return (A, none)

/-- Symbolic handler on the numeric library's syntax kind. -/
@[tactic HexMatrixMathlib.Rank.rankTac, no_fallback]
def evalSymbolicRank : Tactic.Tactic := fun stx => Tactic.withMainContext do
  let target ← instantiateMVars (← Tactic.getMainTarget)
  if let .ok _ ← HexMatrixMathlib.Rank.classify target then throwUnsupportedSyntax
  let some (A, other, rel, reverse) := rankTarget? target | throwUnsupportedSyntax
  if other.hasFVar || other.hasMVar then throwUnsupportedSyntax
  let syntaxCfg ← elabRankConfig stx[1]
  let (A, transport) ← baseMatrix A
  let cfg : Provider.Config := {
    reflection := syntaxCfg.reflection
    matrixSize := syntaxCfg.matrixSize
    caseSplits := syntaxCfg.caseSplits }
  let r ← result A cfg
  checkBound r other rel
  if let .le := rel then
    let bound ← Provider.checkedProof (← mkAppM ``LE.le #[mkNatLit r.rank, other])
    let proof ← mkAppM ``Nat.le_trans #[r.upperProof, bound]
    let proof ← match transport with
      | none => pure proof
      | some h => mkAppM ``Nat.le_trans #[← mkAppM ``Eq.le #[h], proof]
    Tactic.closeMainGoal `rank proof
  else
    let mut sideGoals := []
    let independent ← Provider.independent A r
    let eq ← match ← (if independent.isSome then pure independent else Provider.discharge r cfg) with
      | some p => pure p
      | none => do
        let goal ← mkFreshExprMVar r.conditional.conditions[0]!.proposition
        sideGoals := [goal.mvarId!]
        pure (mkApp r.conditional.proof goal)
    let eq ← match transport with
      | none => pure eq
      | some h => mkEqTrans h eq
    let (proof, _) ← HexMatrixMathlib.Rank.boundProof r.rank eq other rel reverse
    (← Tactic.getMainGoal).assign (← instantiateMVars proof)
    Tactic.replaceMainGoal sideGoals

/-- Return the polynomial matrix's rank and the interpretation of the source matrix. -/
syntax (name := genericRankTerm) "generic_rank% " term : term

/-- Return a specialised rank only when the certificate's condition is discharged. -/
syntax (name := rankTerm) "rank% " term : term

@[term_elab genericRankTerm]
def elabGenericRankTerm : Term.TermElab := fun stx _ => do
  let A ← Term.elabTerm stx[1] none
  Term.synthesizeSyntheticMVarsNoPostponing
  return (← result (← instantiateMVars A)).genericResult

@[term_elab rankTerm]
def elabRankTerm : Term.TermElab := fun stx _ => do
  let A ← Term.elabTerm stx[1] none
  Term.synthesizeSyntheticMVarsNoPostponing
  let A ← instantiateMVars A
  let (A, transport) ← baseMatrix A
  let r ← result A
  let independent ← Provider.independent A r
  let some proof ← (if independent.isSome then pure independent else Provider.discharge r) |
    throwError "rank%: declined: generic rank is {r.rank}; unresolved condition {r.conditional.conditions[0]!.proposition}. Interpreted polynomial matrix: {r.interpretation}. Use rank_locus for the rank-drop set."
  let proof ← match transport with
    | none => pure proof
    | some h => mkEqTrans h proof
  mkAppM ``RankResult.mk #[mkNatLit r.rank, proof]

end HexGenericRankMathlib
