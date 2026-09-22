/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.Determinant.Bird.Cert
import HexPolyDetMathlib.Tactic

open Lean Meta Elab Tactic Qq
open Mathlib.Tactic Mathlib.Tactic.Ring Mathlib.Tactic.Determinant

namespace Determinant

variable {u : Level} {α : Q(Type u)} {rα : Q(CommRing $α)}

/-- Cache arithmetic subexpressions across the entire conjunction. This uses
only the arithmetic helpers, never the Bird determinant evaluator. -/
meta partial def cached (e : Q($α)) :
    StateT (ExprMap (Cert rα)) (CertM rα) (Cert rα) := do
  if let some c := (← get).get? e then return c
  let c ← match_expr e with
    | HAdd.hAdd _ _ _ _ a b =>
      liftM <| certAdd (← cached a) (← cached b)
    | HMul.hMul _ _ _ _ a b =>
      liftM <| certMul (← cached a) (← cached b)
    | Neg.neg _ _ a => liftM <| certNeg (← cached a)
    | _ => liftM <| certEval e
  modify (·.insert e c)
  return c

meta partial def prove (g : MVarId) :
    StateT (ExprMap (Cert rα)) (CertM rα) Unit := do
  let t ← instantiateMVars (← g.getType)
  if let some _ := t.and? then
    let gs ← g.apply (mkConst ``And.intro)
    for sub in gs do prove sub
  else if t.isConstOf ``True then
    g.assign (mkConst ``True.intro)
  else
    let some (_, a, b) := t.eq? | throwError "expected an arithmetic equality"
    have a : Q($α) := a
    have b : Q($α) := b
    let ca ← cached a
    let cb ← cached b
    let ctx ← read
    unless ca.val.eq rcℕ ctx.rc cb.val do throwError "unequal normal forms"
    have na : Q($α) := ca.norm
    have nb : Q($α) := cb.norm
    have : $na =Q $nb := ⟨⟩
    have pa : Q($a = $na) := ca.proof
    have pb : Q($b = $nb) := cb.proof
    g.assign q(Eq.trans $pa (Eq.symm $pb))

elab "cached_ring" : tactic => withMainContext do
  let g ← getMainGoal
  let mut first ← instantiateMVars (← g.getType)
  while first.and?.isSome do first := first.and?.get!.1
  let some (ty, _, _) := first.eq? | throwError "expected an equality"
  let .sort level ← whnf (← inferType ty) | throwError "expected a type"
  let some level := level.dec | throwError "expected a type universe"
  have α : Q(Type level) := ty
  let rα ← synthInstanceQ q(CommRing $α)
  let cα ← Common.mkCache (commSemiringOfCommRing rα)
  let ctx : Ctx rα := {
    cα
    rc := ringCompute cα
    dimension := 0
    dimensionLit := q(0)
    arrayExpr := q(#[] : Array $α)
    arrayEntries := #[] }
  AtomM.run .reducible <| ((prove (rα := rα) g).run' {}).run' {} |>.run ctx

meta partial def provePlain (g : MVarId) : MetaM Unit := do
  let t ← instantiateMVars (← g.getType)
  if let some _ := t.and? then
    for sub in ← g.apply (mkConst ``And.intro) do provePlain sub
  else if t.isConstOf ``True then
    g.assign (mkConst ``True.intro)
  else
    AtomM.run .reducible (Mathlib.Tactic.Ring.proveEq g)

elab "plain_ring" : tactic => withMainContext do
  provePlain (← getMainGoal)

elab "timed_proof" t:tacticSeq : tactic => do
  let start ← IO.monoNanosNow
  withOptions (fun o => o.setBool `profiler false) (evalTactic t)
  logInfo m!"CALL_NS {(← IO.monoNanosNow) - start}"

end Determinant
