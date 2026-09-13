/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Polynomial
public meta import HexRankMathlib.Polynomial
public meta import Lean

public meta section

namespace HexMatrixMathlib.Rank

open Lean Meta

deriving instance ToExpr for Hex.Matrix.PolyWitness

/-- Quote polynomial rows at a selected generator for the shared literal
identification path. Only entry identification evaluates the carrier. -/
def polynomialRows (carrier root : Expr) (values : Array (Array (List Int))) : MetaM Expr := do
  let entries ← values.mapM (·.mapM fun p => mkAppM ``PolyWitness.eval #[root, toExpr p])
  HexMatrixMathlib.Literal.rowList carrier entries

/-- Insert a closed certificate directly through the shared kernel-only path.
Local instance dependencies retain the elaborator's proof-closing path. -/
def addProof (target proof : Expr) : MetaM Expr := do
  let target ← instantiateMVars target
  let proof ← instantiateMVars proof
  if target.hasFVar || target.hasMVar || proof.hasFVar || proof.hasMVar then
    withOptions (Lean.Elab.async.set · false) do mkAuxTheorem target proof
  else
    HexMatrixMathlib.Literal.addClosedProof target proof

end HexMatrixMathlib.Rank
