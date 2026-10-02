/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGraphIso.Sparse.Run
import HexGraphIso.Sparse.Autos
import HexGraphIso.Nauty.Sparse.Cert.Records
import Lean.Data.Json

/-! Native sparse timing driver for the six-way comparison. The shared
adjacency-text corpus is decoded before timing. Native JSON edge input is
also supported for larger graphs. Every timed repetition is emitted. An
optional iteration count runs one stage repeatedly for CPU profiling;
parsing and preparation remain outside that loop. -/

open Lean Hex.GraphIso

namespace Hex.GraphIsoSparseBench

initialize sink : IO.Ref Nat ← IO.mkRef 0

@[noinline] private def blackBox (v : Nat) : IO Unit := sink.modify (· ^^^ v)

private def time (act : Unit → IO Nat) : IO (Nat × Array Nat) := do
  let t0 ← IO.monoNanosNow
  blackBox (← act ())
  let warmup := (← IO.monoNanosNow) - t0
  let reps := if warmup > 1000000000 then 1 else 5
  let mut samples := #[]
  for _ in [0:reps] do
    let start ← IO.monoNanosNow
    blackBox (← act ())
    samples := samples.push ((← IO.monoNanosNow) - start)
  return (warmup, samples)

private def read (path : System.FilePath) : IO (String × String × Nat × List (Nat × Nat)) := do
  let h ← IO.FS.Handle.mk path .read
  let header := (← h.getLine).trimAscii.toString
  if header.startsWith "{" then
    let j ← IO.ofExcept (Json.parse header)
    return (← IO.ofExcept (j.getObjValAs? String "name"),
      ← IO.ofExcept (j.getObjValAs? String "family"),
      ← IO.ofExcept (j.getObjValAs? Nat "n"),
      ← IO.ofExcept (j.getObjValAs? (List (Nat × Nat)) "edges"))
  let ["G", name, family, ns] := header.splitOn " "
    | throw (IO.userError "invalid corpus header")
  let some n := ns.toNat? | throw (IO.userError "invalid vertex count")
  let mut edges := []
  for i in [0:n] do
    let row := (← h.getLine).trimAscii.toString.toUTF8
    unless row.size == n do throw (IO.userError "invalid adjacency row size")
    for j in [0:n] do
      unless row[j]! == 48 || row[j]! == 49 do throw (IO.userError "invalid adjacency bit")
      if i < j && row[j]! == 49 then edges := (i, j) :: edges
  return (name, family, n, edges.reverse)

@[noinline] private def graphDigest (g : Hex.SparseGraph n) : Nat :=
  g.offsets.foldl (· + ·) 0 + g.neighbors.foldl (fun a v => a + v.val) 0

@[noinline] private def searchDigest (G : Sparse.Colored n 1) : Nat :=
  let r := Nauty.Sparse.runColored G
  r.canonlab.foldl (· + ·) 0 + r.canong.neighbors.foldl (· + ·) 0 + r.numnodes

@[noinline] private def canonDigest (G : Sparse.Colored n 1) : IO Nat := do
  let some r := Nauty.Sparse.searchResult? G | throw (IO.userError "invalid sparse label")
  return graphDigest r.form.graph + r.label.perm.vec.toArray.foldl (fun a v => a + v.val) 0

@[noinline] private def autosDigest (G : Sparse.Colored n 1) : Nat :=
  let a := Sparse.autos G
  a.order + a.numOrbits + a.orbits.foldl (· + ·) 0 +
    a.gens.foldl (fun total p => total + p.vec.toArray.foldl (fun s v => s + v.val) 0) 0

@[noinline] private def certDigest (G : Sparse.Colored n 1) : IO Nat := do
  let some c := Nauty.Sparse.Compact.produceCand G
    | throw (IO.userError "sparse certificate production failed")
  return c.tree.stats.records + graphDigest c.key.graph + c.lab.foldl (· + ·) 0

@[noinline] private def replayDigest (G : Sparse.Colored n 1)
    (c : Nauty.Sparse.CertCandidate n) : IO Nat := do
  unless Nauty.Sparse.Compact.checkKey G c.tree c.key do
    throw (IO.userError "sparse certificate replay failed")
  return 1

def run (path : System.FilePath) (mode : String) (iters : Nat := 0) : IO Unit := do
  let (name, family, n, edges) ← read path
  unless ["canon", "run", "build", "output", "label", "autos", "cert-produce", "cert-replay"].contains mode do
    throw (IO.userError "expected canon, run, build, output, label, autos, cert-produce, or cert-replay")
  if hn : 0 < n then
    let some graph := Hex.SparseGraph.ofEdges? n edges | throw (IO.userError "invalid edges")
    let G : Sparse.Colored n 1 := ⟨graph, Coloring.trivial n hn⟩
    let action : Unit → IO Nat ←
      if mode == "canon" then pure fun _ => canonDigest G
      else if mode == "run" then pure fun _ => pure (searchDigest G)
      else if mode == "autos" then pure fun _ => pure (autosDigest G)
      else if mode == "cert-produce" then pure fun _ => certDigest G
      else if mode == "cert-replay" then do
        let some c := Nauty.Sparse.Compact.produceCand G
          | throw (IO.userError "sparse certificate preparation failed")
        pure fun _ => replayDigest G c
      else if mode == "build" then pure fun _ => do
        let some g := Hex.SparseGraph.ofEdges? n edges | throw (IO.userError "invalid edges")
        pure (graphDigest g)
      else do
        let r := Nauty.Sparse.runColored G
        if mode == "label" then
          pure fun _ => do
            let some l := Label.ofArray? n r.canonlab | throw (IO.userError "invalid label")
            pure (l.perm.vec.toArray.foldl (fun a v => a + v.val) 0)
        else do
          let some l := Label.ofArray? n r.canonlab | throw (IO.userError "invalid label")
          pure fun _ => pure (graphDigest (graph.relabel l.perm))
    if iters > 0 then
      let start ← IO.monoNanosNow
      for _ in [0:iters] do blackBox (← action ())
      let elapsed := (← IO.monoNanosNow) - start
      IO.println (Json.mkObj [("name", toJson name), ("mode", toJson mode),
        ("iterations", toJson iters), ("elapsed_ns", toJson elapsed),
        ("ns_per_iteration", toJson (elapsed / iters)), ("sink", toJson (← sink.get))]).compress
      return
    let (warmup, samples) ← time action
    let key := if mode == "canon" then "hex_sparse_ns"
      else if mode == "run" then "hex_sparse_search_ns"
      else if mode == "build" then "hex_sparse_build_ns"
      else if mode == "label" then "hex_sparse_label_ns"
      else if mode == "autos" then "hex_sparse_autos_ns"
      else if mode == "cert-produce" then "hex_sparse_cert_produce_ns"
      else if mode == "cert-replay" then "hex_sparse_cert_replay_ns"
      else "hex_sparse_output_ns"
    let fields := [("name", toJson name), ("family", toJson family), ("n", toJson n),
      (key, toJson (samples.foldl min samples[0]!)),
      ("samples_ns", toJson samples), ("warmup_ns", toJson warmup),
      ("offset_entries", toJson graph.offsets.size),
      ("neighbor_entries", toJson graph.neighbors.size)]
    let fields := if mode == "canon" || mode == "run" then
      ("hex_sparse_nodes", toJson (Nauty.Sparse.runColored G).numnodes) :: fields else fields
    IO.println (Json.mkObj fields).compress
  else throw (IO.userError "benchmark corpus must be nonempty")

end Hex.GraphIsoSparseBench

def main (args : List String) : IO Unit := do
  match args with
  | [path, mode] => Hex.GraphIsoSparseBench.run path mode
  | [path, mode, iters] =>
    let some count := iters.toNat? | throw (IO.userError "invalid iteration count")
    unless count > 0 do throw (IO.userError "iteration count must be positive")
    Hex.GraphIsoSparseBench.run path mode count
  | _ => throw (IO.userError "usage: hexgraphiso_sparse_bench FILE MODE [PROFILE_ITERATIONS]")
