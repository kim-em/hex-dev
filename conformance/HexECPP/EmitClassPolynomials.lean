/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPP.CM.Roots
import Lean.Data.Json

/-! Compiled table and bounded roots for the independent analytic oracle. -/

open Hex.ECPP Lean

def main : IO Unit := do
  for p in CM.classPolynomials do
    IO.println <| (Json.mkObj [("kind", toJson "polynomial"),
      ("d", toJson p.d), ("coefficients", toJson p.coefficients)]).compress
    for n in [9, 17, 25, 31, 35, 41, 49, 101, 113, 121] do
      let z := ((List.range n).find? fun z => CM.symbol z n == -1).getD 2
      IO.println <| (Json.mkObj [("kind", toJson "roots"), ("d", toJson p.d),
        ("n", toJson n), ("z", toJson z), ("roots", toJson (CM.roots? n z p))]).compress
