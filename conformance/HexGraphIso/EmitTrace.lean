/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso.Cases
import Lean.Data.Json

open Lean Hex.GraphIso Hex.GraphIso.Nauty Hex.GraphIsoCases

private def emitTrace (corpus : String) (c : Case) : IO Unit := do
  let some G := coloredOf? c.n c.k c.colors c.edges
    | throw (IO.userError s!"trace: invalid graph {corpus}/{c.name}")
  let (lab, ends) := initialPartition G
  let (exit, st) := runState c.n (rowsOf G) lab ends
  let tr := finish { g := rowsOf G } st
  let r := tr.result
  let output := Json.mkObj [
    ("canonlab", toJson r.canonlab),
    ("canong", toJson (r.canong.map fun row =>
      (Array.range c.n).filter fun v => row.mem v)),
    ("numnodes", toJson r.numnodes), ("numorbits", toJson r.numorbits),
    ("numgenerators", toJson r.numgenerators), ("numbadleaves", toJson r.numbadleaves),
    ("maxlevel", toJson r.maxlevel), ("tctotal", toJson r.tctotal),
    ("canupdates", toJson r.canupdates), ("autos", toJson tr.autos),
    ("bestCodes", toJson tr.bestCodes), ("orbits", toJson st.orbits),
    ("exit", match exit with
      | .done => Json.mkObj [("kind", toJson "done")]
      | .fuel => Json.mkObj [("kind", toJson "fuel")]
      | .unwind level short => Json.mkObj [("kind", toJson "unwind"),
          ("level", toJson level), ("short", toJson short)])]
  IO.println (Json.mkObj [("corpus", toJson corpus), ("name", toJson c.name),
    ("input", Json.mkObj [("n", toJson c.n), ("k", toJson c.k),
      ("colors", toJson c.colors), ("edges", toJson c.edges)]),
    ("output", output)]).compress

private def parseInput (text : String) : Except String Case := do
  let j ← Json.parse text
  return ⟨"mixed-cfi-120", ← j.getObjValAs? Nat "n", ← j.getObjValAs? Nat "k",
    ← j.getObjValAs? (Array Nat) "colors", ← j.getObjValAs? (List (Nat × Nat)) "edges"⟩

def main (args : List String) : IO Unit := do
  unless args.isEmpty do
    throw (IO.userError "trace: no arguments expected")
  eachFixture (emitTrace "fixtures")
  eachAutos (emitTrace "autos")
  eachCampaign (emitTrace "campaign")
  let c ← IO.ofExcept (parseInput (← IO.FS.readFile "conformance-fixtures/HexGraphIso/prune.json"))
  emitTrace "regression" c
