/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGraphIso.Cases
import HexGraphIso.SparseCases

open Lean Hex.GraphIsoCases

private def emit (c : Case) (discoveries : Option Nat := none) : IO Unit := do
  let j := Json.mkObj [("case", toJson c.name), ("n", toJson c.n),
    ("k", toJson c.k), ("colors", toJson c.colors), ("edges", toJson c.edges)]
  let answer ← IO.ofExcept (Hex.GraphIso.SparseProbe.evaluate j discoveries)
  IO.println answer.compress

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
    eachFixture emit
    eachAutos emit
    emit (← pruneRegression) (some 19)
  | ["campaign"] => eachCampaign emit
  | _ => throw (IO.userError "usage: hexgraphiso_emit_sparse [campaign]")
