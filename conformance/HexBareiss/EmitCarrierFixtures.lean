/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBareiss.Conformance
import Lean.Data.Json

/-! Canonical complete carrier records for the independent matrix oracle. -/
namespace Hex.BareissCarriers
open Lean (Json toJson)

def ratJson (q : Rat) : Json := toJson (#[toJson q.num, toJson q.den])
def modJson (q : Mod) : Json := toJson q.toNat
def denseJson {R : Type} [Zero R] [DecidableEq R] (encode : R → Json) (f : DensePoly R) : Json :=
  toJson (f.toArray.map encode)
def mvJson {n : Nat} {R : Type} [Zero R] (encode : R → Json) (f : Mv n R) : Json :=
  toJson (f.termsList.map fun (m, c) => toJson #[toJson m.toList, encode c])

def emitCases {R : Type} [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
    (carrier : String) (arity : Nat) (encode : R → Json)
    (cs : List (String × (n : Nat) × Matrix R n n)) : IO Unit := do
  for (id, ⟨n, m⟩) in cs do
    let record := Json.mkObj [
      ("kind", toJson "bareiss_carrier"), ("lib", toJson "HexBareiss"),
      ("carrier", toJson carrier),
      ("case", toJson s!"{carrier}/{arity}/{id}"), ("n", toJson n),
      ("arity", toJson arity), ("p", toJson (101 : Nat)),
      ("rows", toJson (m.rows.toArray.map fun row => toJson (row.toArray.map encode))),
      ("result", encode (Matrix.bareissWith Hex.exactDiv m))]
    let line := record.compress ++ "\n"
    if let some path ← IO.getEnv "HEX_FIXTURE_OUTPUT" then
      let h ← IO.FS.Handle.mk path .append
      h.putStr line
    else
      (← IO.getStdout).putStr line

end Hex.BareissCarriers

open Hex.BareissCarriers in
def main : IO Unit := do
    emitCases "rat" 0 ratJson ratCases
    emitCases "mod" 0 modJson (modCases ++ [("reduction", ⟨3, reduction⟩)])
    emitCases "dense_rat" 1 (denseJson ratJson) denseRatCases
    emitCases "dense_mod" 1 (denseJson modJson) denseModCases
    emitCases "zpoly" 1 (denseJson Lean.toJson) zpolyCases
    emitCases "mv_int" 2 (mvJson Lean.toJson) (mvIntCases 2 (by decide))
    emitCases "mv_int" 3 (mvJson Lean.toJson) (mvIntCases 3 (by decide))
    emitCases "mv_rat" 2 (mvJson ratJson) (mvRatCases 2 (by decide))
    emitCases "mv_rat" 3 (mvJson ratJson) (mvRatCases 3 (by decide))
