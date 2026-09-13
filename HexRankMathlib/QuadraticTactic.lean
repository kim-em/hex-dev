/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Quadratic
public import HexRankMathlib.PolyExpr
public import HexRankMathlib.Tactic
public meta import HexRankMathlib.Quadratic
public meta import HexRankMathlib.PolyExpr
public meta import HexRank.PolyProduce

public meta section

namespace HexMatrixMathlib.Rank

open Lean Meta Elab
open HexMatrixMathlib.Literal (decideProof)

/-- Read a closed integer, including the constructor form returned by projection reduction. -/
def integerValue (e : Expr) : MetaM Int := do
  let e ← whnf e
  if e.isAppOfArity ``Int.negSucc 1 then
    if let some n ← (Meta.evalNat e.appArg!).run then return Int.negSucc n
  if e.isAppOfArity ``Int.ofNat 1 then
    if let some n ← (Meta.evalNat e.appArg!).run then return n
  if let some v ← getIntValue? e then return v
  let q ← HexMatrixMathlib.Literal.evalEntry e
  unless q.den = 1 do
    throwError "rank: declined: the entry is not an integer{indentExpr e}"
  return q.num

/-- Evaluate the two integer coordinates of a closed quadratic entry. -/
def quadraticEntry (e : Expr) : MetaM (List Int) := do
  let re ← integerValue (mkProj ``Zsqrtd 0 e)
  let im ← integerValue (mkProj ``Zsqrtd 1 e)
  return [re, im]

/-- Quadratic literals extend the owner's `rank` syntax. Other entry models
are left to the other handlers. -/
@[tactic rankTac, no_fallback]
def evalQuadraticRank : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let target ← instantiateMVars (← Tactic.getMainTarget)
  let some (A, other, rel, reverse) := rankTarget? target | throwUnsupportedSyntax
  let some (_, _, R) ← HexMatrixMathlib.Literal.shape? (← inferType A) | throwUnsupportedSyntax
  let carrier ← whnfR R
  let_expr Zsqrtd dE := carrier | throwUnsupportedSyntax
  let some lit ← HexMatrixMathlib.Literal.literal? A | throwUnsupportedSyntax
  if A.hasFVar || A.hasExprMVar || other.hasFVar || other.hasExprMVar then
    throwUnsupportedSyntax
  let .some _ ← trySynthInstance (← mkAppOptM ``IsDomain #[some carrier, none]) |
    throwError "rank: declined: no integral-domain instance is available for{indentExpr carrier}"
  let d ← integerValue dE
  let values ← lit.entries.mapM (·.mapM fun e => do return ← quadraticEntry e)
  let raw := values.toList.map (·.toList)
  let f := [-d, 0, 1]
  let w ← match Hex.Matrix.PolyWitness.produce lit.n lit.m f raw with
    | .ok w => pure w
    | .error e => throwError "rank: declined: the polynomial producer found no witness: {e}"
  let L := toExpr raw
  let c := toExpr w
  let check ← mkEq (← mkAppM ``Hex.Matrix.checkRankPoly
    #[mkNatLit lit.n, mkNatLit lit.m, toExpr f, L, c]) (mkConst ``Bool.true)
  let root ← mkAppOptM ``Zsqrtd.sqrtd #[some dE]
  let rows ← polynomialRows carrier root values
  let hA ← HexMatrixMathlib.Literal.identification lit A rows
  let eq ← mkAppM ``PolyWitness.rank_eq_quadratic' #[dE, A, L, c, hA, ← decideProof check]
  let (proof, bound) ← boundProof w.rank eq other rel reverse
  let ofL ← mkAppM ``PolyWitness.ofPolys #[root, mkNatLit lit.n, mkNatLit lit.m, L]
  let proof ← try
    withOptions (Lean.Elab.async.set · false) do mkAuxTheorem target proof
  catch e => throw (← diagnose bound check A ofL e)
  Tactic.closeMainGoal `rank proof

end HexMatrixMathlib.Rank
