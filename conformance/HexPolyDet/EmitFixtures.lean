/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDet.Conformance
import Lean.Data.Json

namespace Hex.PolyDetFixtures
open Lean (Json toJson)
open Hex.BareissCarriers

def polyJson {k : Nat} {C : Type} [Zero C] (encode : C → Json) (p : Mv k C) : Json :=
  toJson (p.termsList.map fun (m, c) => toJson #[toJson m.toList, encode c])

def emit {k : Nat} {C : Type} [Lean.Grind.CommRing C]
    [DecidableEq C] [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C] [LawfulGcdOps C]
    (carrier : String) (encode : C → Json)
    (cs : List (String × (n : Nat) × Matrix (Mv k C) n n)) : IO Unit := do
  for (id, ⟨n, A⟩) in cs do
    let w ← match PolyDet.polyDetWitness A with
      | .ok w => pure w
      | .error msg => throw (IO.userError msg)
    let record := Json.mkObj [
      ("kind", toJson "poly_det"), ("lib", toJson "HexPolyDet"),
      ("case", toJson s!"{carrier}/{k}/{id}"), ("carrier", toJson carrier),
      ("arity", toJson k), ("n", toJson n), ("p", toJson (101 : Nat)),
      ("checked", toJson (PolyDet.check n (A.rows.toList.map (·.toList)) w)),
      ("entry_support", toJson (A.rows.toList.map fun row => row.toList.map MvPoly.termCount)),
      ("rows", toJson (A.rows.toList.map fun row => row.toList.map (polyJson encode))),
      ("result", polyJson encode w.value)]
    let line := record.compress ++ "\n"
    if let some path ← IO.getEnv "HEX_FIXTURE_OUTPUT" then
      let handle ← IO.FS.Handle.mk path .append
      handle.putStr line
    else (← IO.getStdout).putStr line

end Hex.PolyDetFixtures

open Hex.PolyDetFixtures Hex.BareissCarriers in
def main : IO Unit := do
  emit "mv_int" Lean.toJson (intCases 2 (by decide))
  emit "mv_int" Lean.toJson (intCases 3 (by decide))
  emit "mv_rat" (fun q => Lean.toJson #[Lean.toJson q.num, Lean.toJson q.den]) (Hex.PolyDetFixtures.ratCases 2 (by decide))
  emit "mv_rat" (fun q => Lean.toJson #[Lean.toJson q.num, Lean.toJson q.den]) (Hex.PolyDetFixtures.ratCases 3 (by decide))
  emit "mv_mod" (fun q => Lean.toJson q.toNat) (Hex.PolyDetFixtures.modCases 2 (by decide))
  emit "mv_mod" (fun q => Lean.toJson q.toNat) (Hex.PolyDetFixtures.modCases 3 (by decide))
