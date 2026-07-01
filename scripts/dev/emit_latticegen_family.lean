/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-
Dev tool: emit the Lean-generated lattice basis for a family at given
dimensions, one JSON object per line, for `validate_latticegen.py` to
cross-check against fplll's `latticegen`. Run with:

  lake env lean --run scripts/dev/emit_latticegen_family.lean ajtai 6 8 10 12
-/
import HexLLLBench.Inputs
open Hex.LLLBench

/-- The basis a family's `prepXInput` builds at parameter `d`, as a JSON matrix
string. Mirrors the bench prep conventions so the fixture is the real input. -/
def basisFor (family : String) (d : Nat) : Option (String) :=
  match family with
  | "ajtai"    => some (matrixHaskell (ajtaiBasis d))
  | "q-ary"    => some (matrixHaskell (qaryBasis d (d / 2) qaryBits))
  | "ntru"     => some (matrixHaskell (ntruBasis d))
  | "knapsack" => some (matrixHaskell (knapsackBasis d (knapsackBits d)))
  | _ => none

def main (args : List String) : IO Unit := do
  match args with
  | family :: dims =>
    for s in dims do
      let d := (s.toNat?).getD 0
      match basisFor family d with
      | some m => IO.println s!"\{\"family\":\"{family}\",\"d\":{d},\"basis\":{m}}"
      | none => throw (IO.userError s!"unknown family {family}")
  | _ => throw (IO.userError "usage: emit_latticegen_family <family> <d>...")
