/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso.Cases

/-!
Twin conformance for the second canonical search: `hexgraphiso_engine_twin`
runs `Nauty.runColoredTraced` and `Cases.engine` on every case of the
committed fixture corpus, of its automorphism records and of the
extended campaign, and compares the
whole traversal rather than only its answer: `canonlab`, `canong`, the
seven statistics of `Nauty.RunResult`, the accepted automorphisms in
discovery order, and the best path's refinement codes.

The first case on which the two disagree is printed with the differing
fields, the vertex count, the colour vector and the edge list, and the
run exits non-zero. With no argument every corpus runs; `fixtures`,
`autos` and `campaign` select one.

`Nauty.RunResult` does not carry the final `orbits` array, so the twin
compares `numorbits` rather than the orbit partition itself.
-/

namespace Hex.GraphIsoTwin

open Hex.GraphIso.Nauty
open Hex.GraphIsoCases

/-- The fields on which two traced runs differ, named as in
`Nauty.RunResult` and `Nauty.TraceRun`. -/
private def diffs {n : Nat} (a b : TraceRun n) : List String :=
  let r := a.result
  let s := b.result
  let field (name : String) (agree : Bool) : List String :=
    if agree then [] else [name]
  field "canonlab" (r.canonlab == s.canonlab)
    ++ field "canong" (r.canong == s.canong)
    ++ field "numnodes" (r.numnodes == s.numnodes)
    ++ field "numorbits" (r.numorbits == s.numorbits)
    ++ field "numgenerators" (r.numgenerators == s.numgenerators)
    ++ field "numbadleaves" (r.numbadleaves == s.numbadleaves)
    ++ field "maxlevel" (r.maxlevel == s.maxlevel)
    ++ field "tctotal" (r.tctotal == s.tctotal)
    ++ field "canupdates" (r.canupdates == s.canupdates)
    ++ field "autos" (a.autos == b.autos)
    ++ field "bestCodes" (a.bestCodes == b.bestCodes)

/-- Run both searches on one case, counting it and reporting the first
disagreement as an error. -/
private def check (seen : IO.Ref Nat) (case : Case) : IO Unit := do
  let some G := coloredOf? case.n case.k case.colors case.edges
    | throw (IO.userError s!"twin: case {case.name} rejected by the builders")
  match diffs (runColoredTraced G) (engine G) with
  | [] => seen.modify (· + 1)
  | ds =>
    throw <| IO.userError <|
      s!"twin: mismatch on {case.name}" ++
      "\n  fields: " ++ String.intercalate ", " ds ++
      s!"\n  n = {case.n}, k = {case.k}" ++
      s!"\n  colors = {case.colors.toList}" ++
      s!"\n  edges = {case.edges}"

private def run (corpus : String) : IO Unit := do
  let seen ← IO.mkRef 0
  match corpus with
  | "fixtures" => eachFixture (check seen)
  | "autos" => eachAutos (check seen)
  | "campaign" => eachCampaign (check seen)
  | other => throw (IO.userError s!"twin: unknown corpus {other}")
  IO.println s!"twin: {corpus} agree over {← seen.get} cases"

def main (args : List String) : IO Unit := do
  let corpora := if args.isEmpty then ["fixtures", "autos", "campaign"] else args
  try
    for corpus in corpora do
      run corpus
  catch e =>
    IO.eprintln e.toString
    IO.Process.exit 1

end Hex.GraphIsoTwin

def main (args : List String) : IO Unit := Hex.GraphIsoTwin.main args
