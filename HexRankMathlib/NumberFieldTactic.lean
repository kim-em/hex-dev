/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.NumberField
public import HexRankMathlib
public import HexRankMathlib.PolyExpr
public meta import HexRankMathlib.NumberField
public meta import HexRankMathlib
public meta import HexRankMathlib.PolyExpr
public meta import HexRank.PolyProduce

public meta section

namespace HexMatrixMathlib.Rank

open Lean Meta Elab
open HexMatrixMathlib.Literal (decideProof)

private unsafe def evalCoeffsUnsafe (e : Expr) : MetaM (Except String (List Rat)) := do
  try return .ok (← evalExpr (List Rat) (mkApp (mkConst ``List [0]) (mkConst ``Rat)) e)
  catch ex => return .error (← ex.toMessageData.toString)

@[implemented_by evalCoeffsUnsafe]
private opaque evalCoeffs (e : Expr) : MetaM (Except String (List Rat))

private unsafe def evalPolynomialUnsafe (e : Expr) : MetaM (Except String Hex.ZPoly) := do
  try return .ok (← evalExpr Hex.ZPoly (mkConst ``Hex.ZPoly) e)
  catch ex => return .error (← ex.toMessageData.toString)

@[implemented_by evalPolynomialUnsafe]
private opaque evalPolynomial (e : Expr) : MetaM (Except String Hex.ZPoly)

/-- Check that the defining polynomial reduces to its quoted data before
handing it to the kernel. In particular, an irreducible root-search wrapper
must decline instead of starting a kernel search. -/
private def literalPolynomial (p : Expr) : MetaM Hex.ZPoly := do
  try
    withCurrHeartbeats <| withTheReader Core.Context
        (fun ctx => { ctx with maxHeartbeats :=
          if ctx.maxHeartbeats = 0 then 20000000 else min ctx.maxHeartbeats 20000000 }) do
      let p' ← whnf p
      unless p'.isAppOf ``Hex.DensePoly.mk do throwError "not a polynomial constructor"
      let .ok f ← evalPolynomial p' | throwError "cannot evaluate the polynomial"
      let quoted ← mkAppM ``Hex.DensePoly.ofList #[toExpr f.coeffs.toList]
      unless ← isDefEq p quoted do throwError "coefficients do not reduce"
      return f
  catch _ =>
    throwError "rank: declined: the defining polynomial is not kernel-reducible; use a literal presentation or AlgebraicNumber.ofNormalized"

/-- Read canonical rational coordinates. Projection reduction removes the
proof-bearing field instance before compiling the executable arithmetic. -/
private def fieldEntry (e : Expr) : MetaM (List Rat) := do
  let e ← Meta.transform e (pre := fun t => do
    if t.isAppOfArity ``HPow.hPow 6 then
      let args := t.getAppArgs
      let R ← whnfR args[0]!
      if R.isAppOfArity ``Hex.PolyQuot 2 || R.isAppOfArity ``Hex.QAdjoin 1 then
        if ← isDefEq args[1]! (mkConst ``Nat) then
          return .visit (← mkAppM ``Hex.PolyQuot.natPow #[args[4]!, args[5]!])
        if ← isDefEq args[1]! (mkConst ``Int) then
          return .visit (← mkAppM ``Hex.PolyQuot.intPow #[args[4]!, args[5]!])
    return .continue)
  let coeffs ← mkAppM ``Hex.PolyQuot.coeffs #[e]
  let arr ← mkAppM ``Hex.DensePoly.coeffs #[coeffs]
  let vals ← mkAppM ``Array.toList #[arr]
  match ← evalCoeffs vals with
  | .ok qs => return qs
  | .error _ =>
    match ← evalCoeffs (← reduce vals (explicitOnly := false)) with
    | .ok qs => return qs
    | .error msg => throwError "rank: declined: cannot evaluate number-field coordinates: {msg}"

/-- Optional handler for `QAdjoin` and explicit `PolyQuot` presentations. -/
@[tactic rankTac, no_fallback]
def evalNumberFieldRank : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let target ← instantiateMVars (← Tactic.getMainTarget)
  let some (A, other, rel, reverse) := rankTarget? target | throwUnsupportedSyntax
  let some (_, _, R) ← HexMatrixMathlib.Literal.shape? (← inferType A) | throwUnsupportedSyntax
  let carrier ← whnfR R
  let (p, x) ←
    if carrier.isAppOfArity ``Hex.PolyQuot 2 then
      pure (carrier.appFn!.appArg!, carrier.appArg!)
    else
      let_expr Hex.QAdjoin a := carrier | throwUnsupportedSyntax
      pure (← mkAppM ``Hex.AlgebraicNumber.p #[a], ← mkAppM ``Hex.AlgebraicNumber.x #[a])
  let some lit ← HexMatrixMathlib.Literal.literal? A | throwUnsupportedSyntax
  if A.hasFVar || A.hasExprMVar || other.hasFVar || other.hasExprMVar then
    throwUnsupportedSyntax
  let .some _ ← trySynthInstance (← mkAppM ``Hex.ZPoly.CheckedIrreducible #[p]) |
    throwError "rank: declined: the defining polynomial needs checked irreducibility"
  let f := (← literalPolynomial p).coeffs.toList
  let qs ← lit.entries.mapM (·.mapM fun e => do return ← fieldEntry e)
  let scales : Array Nat := qs.map fun row =>
    row.foldl (fun (d : Nat) q => q.foldl (fun (d : Nat) (r : Rat) => d.lcm r.den) d) 1
  let values := qs.mapIdx fun i row =>
    row.map fun q => q.map fun r => (r * (scales[i]! : Rat)).num
  let raw := values.toList.map (·.toList)
  let w ← match Hex.Matrix.PolyWitness.produce lit.n lit.m f raw with
    | .ok w => pure w
    | .error msg => throwError "rank: declined: the polynomial producer found no witness: {msg}"
  let L := toExpr raw
  let c := toExpr w
  let s := toExpr scales.toList
  let root ← mkAppM ``Hex.PolyQuot.Rank.generator #[p, x]
  let rows ← polynomialRows carrier root values
  let scaled ← withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit lit.n)) fun i =>
    withLocalDeclD `j (mkApp (mkConst ``Fin) (mkNatLit lit.m)) fun j => do
      let k ← mkAppM ``List.getD #[s, ← mkAppM ``Fin.val #[i], mkNatLit 1]
      let k ← mkAppOptM ``Nat.cast #[some carrier, none, some k]
      mkLambdaFVars #[i,j] (← mkAppM ``HMul.hMul #[k, mkApp2 A i j])
  let scaleCheck ← mkEq (← mkAppM ``entriesEq
    #[mkNatLit lit.n, mkNatLit lit.m, scaled, rows]) (mkConst ``Bool.true)
  let lenCheck ← mkEq (← mkAppM ``List.length #[s]) (mkNatLit lit.n)
  let pos ← withLocalDeclD `k (mkConst ``Nat) fun k => do
    mkLambdaFVars #[k] (← mkDecide (← mkAppM ``LT.lt #[mkNatLit 0, k]))
  let posCheck ← mkEq (← mkAppM ``List.all #[s, pos]) (mkConst ``Bool.true)
  let check ← mkEq (← mkAppM ``Hex.Matrix.checkRankPoly
    #[mkNatLit lit.n, mkNatLit lit.m, toExpr f, L, c]) (mkConst ``Bool.true)
  let eq ← mkAppM ``Hex.PolyQuot.Rank.rank_eq_scaled
    #[A, s, L, c, ← decideProof lenCheck, ← decideProof posCheck,
      ← decideProof scaleCheck, ← decideProof check]
  let (proof, _) ← boundProof w.rank eq other rel reverse
  let proof ← try
    withOptions (Lean.Elab.async.set · false) do mkAuxTheorem target proof
  catch e => throwError "rank: number-field kernel check failed: {e.toMessageData}"
  Tactic.closeMainGoal `rank proof

end HexMatrixMathlib.Rank
