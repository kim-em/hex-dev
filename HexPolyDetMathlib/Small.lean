/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDetMathlib.Frontend
public meta import HexPolyDetMathlib.Frontend
public meta import HexPolyDetMathlib.Scaling
public meta import Lean

public meta section

namespace HexPolyDetMathlib.Small

open Lean Meta HexMatrixMathlib.Literal HexMatrixMathlib.DetPoly.Frontend

private def mul (a b : Expr) : MetaM Expr := mkAppM ``HMul.hMul #[a, b]
private def sub (a b : Expr) : MetaM Expr := mkAppM ``HSub.hSub #[a, b]
private def add (a b : Expr) : MetaM Expr := mkAppM ``HAdd.hAdd #[a, b]
private def triple (es : Array (Array Expr)) (i j a b c d : Nat) : MetaM Expr := do
  mul (← mul (es[i]!)[j]! (es[a]!)[b]!) (es[c]!)[d]!

/-- Closed formulas use entry expressions directly; this path never creates a
reflection batch or a polynomial certificate. -/
def formula (A : Expr) (lit : Recognized) : MetaM Result := do
  let es ← lit.entries.mapM (fun row => row.mapM reduceIndices)
  let result : Result ← match lit.n with
    | 0 => do
      let proof ← mkAppOptM ``Matrix.det_fin_zero #[some lit.carrier, none, some A]
      let value ← mkNumeral lit.carrier 1
      return ({ proof, value } : Result)
    | 1 => do return { proof := ← mkAppM ``Matrix.det_fin_one #[A], value := (es[0]!)[0]! }
    | 2 => do
      let proof ← if lit.route == .chain then
        mkAppM ``Matrix.det_fin_two_of #[(es[0]!)[0]!, (es[0]!)[1]!, (es[1]!)[0]!, (es[1]!)[1]!]
      else mkAppM ``Matrix.det_fin_two #[A]
      return { proof, value := ← sub (← mul (es[0]!)[0]! (es[1]!)[1]!) (← mul (es[0]!)[1]! (es[1]!)[0]!) }
    | 3 => do
      let v ← sub (← triple es 0 0 1 1 2 2) (← triple es 0 0 1 2 2 1)
      let v ← sub v (← triple es 0 1 1 0 2 2)
      let v ← add v (← triple es 0 1 1 2 2 0)
      let v ← add v (← triple es 0 2 1 0 2 1)
      return { proof := ← mkAppM ``Matrix.det_fin_three #[A], value := ← sub v (← triple es 0 2 1 1 2 0) }
    | _ => throwError "det: closed forms require dimension at most three"
  let target ← mkEq (← mkAppM ``Matrix.det #[A]) result.value
  if ← isTracingEnabledFor `HexMatrix.certificate then
    trace[HexMatrix.certificate] "{(Json.mkObj [("route", toJson "closed-form"),
      ("dimension", toJson lit.n), ("proof_nodes", toJson (Hex.Reflect.sourceNodeCount result.proof 1000001))]).compress}"
  return { result with proof := ← checked target (← mkExpectedTypeHint result.proof target) "det.small.kernel" }

end HexPolyDetMathlib.Small
