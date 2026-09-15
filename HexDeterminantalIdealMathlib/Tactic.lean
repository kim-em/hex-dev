/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdealMathlib.Provider
public meta import HexDeterminantalIdealMathlib.Provider
public meta import Lean
public meta import HexReflect.Budget

public meta section

namespace HexDeterminantalIdealMathlib

open Lean Meta Elab Tactic

/-- Resource limits exposed by the tactic frontend. -/
structure LocusConfig where
  reflection : Hex.Reflect.Config := {}
  matrixSize : Nat := 4096
  minorWork : Nat := 50000

declare_config_elab elabLocusConfig LocusConfig

def LocusConfig.provider (cfg : LocusConfig) : Provider.Config := {
  reflection := cfg.reflection, matrixSize := cfg.matrixSize, minorWork := cfg.minorWork }

/-- The default-threshold syntax is open to the generic-rank companion. -/
syntax (name := rankLocusDefault) "rank_locus" optConfig ppSpace colGt term : tactic
syntax (name := rankLocusExplicit) "rank_locus" optConfig ppSpace colGt term:max ppSpace colGt term:max (" with " ident)? : tactic

@[tactic rankLocusExplicit]
def evalRankLocus : Tactic := fun stx => withMainContext do
  let cfg := (← elabLocusConfig stx[1]).provider
  let A ← Term.elabTerm stx[2] none
  let r ← Term.elabTerm stx[3] (some (mkConst ``Nat))
  Term.synthesizeSyntheticMVarsNoPostponing
  let r ← instantiateMVars r
  if r.hasFVar || r.hasMVar then throwError "rank_locus: the threshold must be a closed natural number"
  let some r ← (Meta.evalNat r).run
    | throwError "rank_locus: the threshold must be a closed natural number"
  let p ← Provider.reify (← instantiateMVars A) cfg
  let result ← Provider.locus p r cfg
  let name := if stx[4].isNone then `h else stx[4][1].getId
  let (_, goal) ← (← getMainGoal).note name result.iffProof (some (← result.proposition))
  replaceMainGoal [goal]

/-- Close one of the four rank comparisons using determinantal generators. -/
syntax (name := rankLocusClose) "rank_locus" optConfig : tactic

inductive Comparison where
  | lt | le | ge | eq

def target? (target : Expr) : Option (Expr × Expr × Comparison) :=
  let rank (e : Expr) := e.getAppFn.isConstOf ``Matrix.rank
  match target.getAppFnArgs with
  | (``Eq, #[_, a, b]) => if rank a then some (a.appArg!, b, .eq) else none
  | (``LT.lt, #[_, _, a, b]) => if rank a then some (a.appArg!, b, .lt) else none
  | (``LE.le, #[_, _, a, b]) =>
    if rank a then some (a.appArg!, b, .le)
    else if rank b then some (b.appArg!, a, .ge) else none
  | _ => none

/-- Assemble the displayed conjunction without a trailing `True`. -/
def conjunction : List Expr → MetaM Expr
  | [] => pure (mkConst ``True.intro)
  | [p] => pure p
  | p :: q :: ps => do mkAppM ``And.intro #[p, ← conjunction (q :: ps)]

/-- Return upper-bound proof data, creating only the unresolved conditions. -/
def upper (p : Provider.Reified) (r : Nat) (cfg : Provider.Config := {}) :
    MetaM (Expr × List MVarId) := do
  let result ← Provider.locus p r cfg
  let cs ← result.generators.mapM (fun g => Provider.condition p g false)
  let (resolved, _) ← Hex.Reflect.dischargeConditions cs (Provider.policy cfg)
  let mut proofs := []
  let mut goals := []
  for c in cs do
    match resolved.find? (fun a => a.1.proposition == c.proposition) with
    | some (_, h) => proofs := proofs ++ [h]
    | none =>
      let h ← mkFreshExprMVar c.proposition
      proofs := proofs ++ [h]
      goals := goals ++ [h.mvarId!]
  let proof ← mkAppM ``Iff.mpr #[result.iffProof, ← conjunction proofs]
  return (proof, goals)

/-- The lower-bound provider has already tried every automatic candidate. -/
def lower (p : Provider.Reified) (r : Nat) (cfg : Provider.Config := {}) :
    MetaM (Expr × List MVarId) := do
  let result ← Provider.lower p r cfg
  let (h, goals) ← match result.resolved with
    | some h => pure (h, [])
    | none => do
      let h ← mkFreshExprMVar result.condition.proposition
      pure (h, [h.mvarId!])
  logInfo m!"rank_locus: using minor {result.generator.display} at rows {result.rows}, columns {result.cols}"
  return (mkApp result.proof h, goals)

@[tactic rankLocusClose]
def evalRankLocusClose : Tactic := fun stx => withMainContext do
  let cfg := (← elabLocusConfig stx[1]).provider
  let some (A, bound, cmp) := target? (← instantiateMVars (← getMainTarget))
    | throwError "rank_locus: expected A.rank < r, A.rank ≤ r, r ≤ A.rank, or A.rank = r"
  if bound.hasFVar || bound.hasMVar then
    throwError "rank_locus: the threshold must be a closed natural number"
  let some r ← (Meta.evalNat bound).run | throwError "rank_locus: nonliteral threshold"
  let p ← Provider.reify A cfg
  let (proof, goals) ← match cmp with
    | .lt => upper p r cfg
    | .le => do
      let (h, gs) ← upper p (r + 1) cfg
      pure (← mkAppM ``Nat.le_of_lt_succ #[h], gs)
    | .ge => lower p r cfg
    | .eq => do
      let (hu, gu) ← upper p (r + 1) cfg
      let (hl, gl) ← lower p r cfg
      pure (← mkAppM ``Nat.le_antisymm #[← mkAppM ``Nat.le_of_lt_succ #[hu], hl], gu ++ gl)
  let _ ← Provider.checkProofBudget p #[proof] cfg
  (← getMainGoal).assign proof
  replaceMainGoal goals

/-- Return generators, their iff, the sealed polynomial data, and optional ideal data. -/
syntax (name := rankLocusTerm) "rank_locus% " term:max term:max : term

@[term_elab rankLocusTerm]
def elabRankLocusTerm : Term.TermElab := fun stx _ => do
  let A ← Term.elabTerm stx[1] none
  let r ← Term.elabTerm stx[2] (some (mkConst ``Nat))
  Term.synthesizeSyntheticMVarsNoPostponing
  let r ← instantiateMVars r
  if r.hasFVar || r.hasMVar then throwError "rank_locus%: expected a closed natural threshold"
  let some r ← (Meta.evalNat r).run | throwError "rank_locus%: expected a closed natural threshold"
  let p ← Provider.reify (← instantiateMVars A)
  Provider.result (← Provider.locus p r)

end HexDeterminantalIdealMathlib
