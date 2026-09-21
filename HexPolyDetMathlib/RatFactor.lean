/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyDetMathlib.RowFactor
public meta import HexPolyDetMathlib.RowFactor
public meta import Mathlib.Tactic.Ring

public section
namespace HexPolyDetMathlib.RatFactor
open HexMatrixMathlib

@[expose] def matrix (n : Nat) (C : Matrix (Fin n) (Fin n) Rat)
    (f : List Rat) : Matrix (Fin n) (Fin n) Rat :=
  fun i j => C i j * vecOfList n f i

@[expose] def scalarOps (a b : Rat) : List Rat := [-a, a*b, a/b]

/-- The numeric matrix is arbitrary; row expressions are not normalized. -/
theorem det (n : Nat) (C : Matrix (Fin n) (Fin n) Rat) (f : List Rat)
    (d : Rat) (hlen : f.length = n) (hdet : C.det = d) :
    (matrix n C f).det = f.foldl (· * ·) d := by
  subst n
  have hm : matrix f.length C f =
      Matrix.of (fun i j => vecOfList f.length f i * C i j) := by
    ext i j
    exact mul_comm _ _
  have hp : (∏ i : Fin f.length, vecOfList f.length f i) = f.prod := by
    clear hm hdet C
    induction f with
    | nil => simp
    | cons a f ih => simpa [Fin.prod_univ_succ, vecOfList] using congrArg (a * ·) ih
  have : Std.Associative (fun a b : Rat => a * b) := ⟨mul_assoc⟩
  rw [hm, Matrix.det_mul_column, hdet, hp, mul_comm, List.prod_eq_foldl]
  simpa only [mul_one] using (List.foldl_assoc (op := (· * ·))
    (l := f) (a₁ := d) (a₂ := 1)).symm
end HexPolyDetMathlib.RatFactor

public meta section
namespace HexPolyDetMathlib.RatFactor
open Lean Meta HexMatrixMathlib HexMatrixMathlib.Literal
open HexMatrixMathlib.DetPoly.Frontend

/-- Prove only the scalar skeleton, before substituting potentially large factors. -/
def skeleton? (lhs rhs : Expr) (factors : Array Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    let rat := mkConst ``Rat
    withLocalDeclsD (factors.mapIdx fun i _ => (Name.mkSimple s!"factor{i}", fun _ => pure rat)) fun xs => do
      let abstract (e : Expr) := e.replace fun e => do
        let i ← factors.findIdx? (· == e)
        xs[i]?
      let lhs' := abstract lhs
      let rhs' := abstract rhs
      let g ← mkFreshExprMVar (← mkEq lhs' rhs')
      let goals ← Lean.Elab.runTactic' g.mvarId! (← `(tactic| ring))
      unless goals.isEmpty do saved.restore; return none
      let proof ← instantiateMVars g
      let proof ← mkLambdaFVars xs proof
      return some (mkAppN proof factors)
  catch _ => saved.restore; return none

/-- Evaluate only a bounded closed scalar, authenticating it later in the proof. -/
private def scalar? (e : Expr) : MetaM (Option Rat) := do
  match ← (HexMatrixMathlib.DetPoly.Normalize.scalarBound e).run with
  | .error _ | .ok none => return none
  | .ok (some _) => try return some (← evalEntry e) catch _ => return none

/-- One opaque factor surrounded by closed scalar operations. -/
private partial def split? (e : Expr) (fuel : Nat := 16) : MetaM (Option (Rat × Option Expr)) := do
  if fuel == 0 then return none
  if let some q ← scalar? e then return some (q, none)
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``Neg.neg, #[α, _, a]) =>
    unless ← withTransparency .reducible (isDefEq α (mkConst ``Rat)) do return none
    let some (q, f) ← split? a (fuel-1) | return none
    return some (-q, f)
  | (``HDiv.hDiv, #[α, β, γ, _, a, b]) =>
    unless ← withTransparency .reducible
        (isDefEq α (mkConst ``Rat) <&&> isDefEq β (mkConst ``Rat) <&&> isDefEq γ (mkConst ``Rat)) do return none
    if let some q ← scalar? b then
      let some (c, f) ← split? a (fuel-1) | return none
      return some (c/q, f)
  | (``HMul.hMul, #[α, β, γ, _, a, b]) =>
    unless ← withTransparency .reducible
        (isDefEq α (mkConst ``Rat) <&&> isDefEq β (mkConst ``Rat) <&&> isDefEq γ (mkConst ``Rat)) do return none
    if let some q ← scalar? a then
      let some (c, f) ← split? b (fuel-1) | return none
      return some (q*c, f)
    if let some q ← scalar? b then
      let some (c, f) ← split? a (fuel-1) | return none
      return some (q*c, f)
  | _ => pure ()
  return some (1, some e)

/-- A target is a scalar product of the retained factors, not their expansion. -/
private partial def targetShape (e : Expr) (fs : Array Expr) (fuel : Nat := 128) : MetaM Bool := do
  if fuel == 0 then return false
  if fs.contains e.consumeMData then return true
  if (← scalar? e).isSome then return true
  match e.getAppFnArgs with
  | (``Neg.neg, #[_, _, a]) => targetShape a fs (fuel-1)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    return (← targetShape a fs (fuel-1)) && (← targetShape b fs (fuel-1))
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
    return (← scalar? b).isSome && (← targetShape a fs (fuel-1))
  | _ => return false

/-- Rational row-factor recognition precedes small formulas in automatic mode. -/
def compute? (A : Expr) (lit : Recognized) (rhs? : Option Expr) : MetaM (Option Result) := do
  unless lit.carrier.isConstOf ``Rat do return none
  if A.hasExprMVar || rhs?.any (·.hasExprMVar) || lit.n == 0 || lit.n > maxDimension then return none
  if HexMatrixMathlib.DetPoly.Certificate.arm (← getOptions) != .automatic then return none
  if Hex.Reflect.proofNodeCount (#[A] ++ rhs?.toArray) 100001 > 100000 then return none
  let canonical ← withLocalDeclD `a lit.carrier fun a => withLocalDeclD `b lit.carrier fun b => do
    let actual ← mkListLit lit.carrier [← mkAppM ``Neg.neg #[a],
      ← mkAppM ``HMul.hMul #[a,b], ← mkAppM ``HDiv.hDiv #[a,b]]
    withTransparency .default (isDefEq actual (mkApp2 (mkConst ``scalarOps) a b))
  unless canonical do return none
  withLetDecl `detInput (← inferType A) A fun A => do
    let saved ← saveState
    let attempt : MetaM (Option Result) := do
      let mut rows : Array (Array Rat) := #[]
      let mut factors : Array Expr := #[]
      let mut sources : Array (Array Expr) := #[]
      for row in lit.entries do
        let mut coefficients := #[]
        let mut entries := #[]
        let mut factor? := none
        for source in row do
          let source ← reduceIndices source
          let some (q, f?) ← split? source | return none
          if q.num.natAbs.log2 + q.den.log2 > 4096 then return none
          if q != 0 then
            let some f := f? | return none
            match factor? with
            | none => factor? := some f
            | some g => if f != g then return none
          coefficients := coefficients.push q
          entries := entries.push source
        let factor := factor?.getD (← mkNumeral lit.carrier 1)
        rows := rows.push coefficients
        factors := factors.push factor
        sources := sources.push entries
      if let some rhs := rhs? then unless ← targetShape rhs factors do return none
      let L ← rowList lit.carrier (rows.map (·.map toExpr))
      let C ← mkAppM ``ofLists #[toExpr lit.n, toExpr lit.n, L]
      let numericLit : Recognized := {
        n := lit.n
        m := lit.n
        carrier := lit.carrier
        entries := rows.map (·.map toExpr)
        route := .chain }
      let scales := rows.map fun row => row.foldl (fun l q => Nat.lcm l q.den) 1
      let integers := rows.zipWith (fun row scale => row.map fun q => (q * (scale : Rat)).num) scales
      let bits := integers.flatten.foldl (fun b z => max b (integerBits z)) 1
      if 2 * lit.n * (bits + lit.n.log2 + 2) > Hex.Reflect.Budget.default.coefficientBits then return none
      let .success cert ← Det.certifyLiteral numericLit | return none
      let p ← Det.build {} C cert
      let mut value := p.value
      for f in factors do value ← mkAppM ``HMul.hMul #[value, f]
      let target := rhs?.getD value
      let some ht ← skeleton? value target factors | return none
      let mut hints := #[]
      for i in [:lit.n] do
        let mut row := #[]
        for j in [:lit.n] do
          let rhs ← mkAppM ``HMul.hMul #[toExpr (rows[i]!)[j]!, factors[i]!]
          let source := (sources[i]!)[j]!
          let some (_, original?) ← split? source | return none
          let abstracted := if let some f := original? then #[factors[i]!, f] else #[factors[i]!]
          let some h ← skeleton? source rhs abstracted | return none
          row := row.push h
        hints := hints.push row
      let fs ← mkListLit lit.carrier factors.toList
      let B := mkApp3 (mkConst ``matrix) (toExpr lit.n) C fs
      let hA ← applyEntryHints (← mkAppM ``DetPoly.Polynomial.identify #[A, B]) hints
      let hlen ← decideProof (← mkEq (← mkAppM ``List.length #[fs]) (toExpr lit.n))
      let hd := mkAppN (mkConst ``det) #[toExpr lit.n, C, fs, p.value, hlen, p.proof]
      let determinant := (← mkAppM ``Matrix.det #[A]).appFn!
      let proof ← mkEqTrans (← mkCongrArg determinant hA) (← mkEqTrans hd ht)
      let expected ← mkEq (← mkAppM ``Matrix.det #[A]) target
      let outcome ← Hex.Reflect.run <| Hex.Reflect.withOutcome do
        checkedBudgeted expected (mkExpectedPropHint proof expected)
      match outcome with
      | .success (proof, nodes) _ =>
        trace[HexMatrix.certificate] "{(Json.mkObj [("route", toJson "rational-row-factor"),
          ("dimension", toJson lit.n), ("proof_node_budget", toJson nodes)]).compress}"
        return some {value := target, proof}
      | .failure error => throwError error.toMessageData
      | _ => return none
    let result ← attempt
    if result.isNone then saved.restore
    return result

end HexPolyDetMathlib.RatFactor
