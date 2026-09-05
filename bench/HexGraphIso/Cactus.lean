/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso
import Hex.BenchOracle.Nauty

/-!
Per-instance timing sweep over the deterministic graph families for the
hex-graph-iso cactus plots: the public `canonicalize` and the pinned
nauty 2.9.3 FFI comparator on the same instances.

Emits one JSON line per instance:

```
{"family": "...", "name": "...", "n": N, "fast_ns": ...,
 "nauty_ns": ..., "nodes": ...}
```

Timing is the minimum of several repetitions after one warmup call.
The driver is for local and scheduled sweeps
(`scripts/plots/hexgraphiso-cactus.py` renders the plots); it is not
part of merge CI.
-/

namespace Hex.GraphIsoCactus

open Hex.GraphIso

private def reps : Nat := 5

/-- One instance: family label, instance name, and the coloured graph. -/
private structure Inst where
  family : String
  name : String
  packed : (n : Nat) × Colored n 1

private def inst (family name : String) {n : Nat} (G : Graph n)
    (h : 0 < n) : Inst :=
  { family, name, packed := ⟨n, Graph.singleColor G h⟩ }

/-- A cheap digest forcing full evaluation of a canonical result. -/
private def digest {n k : Nat} (res : CanonResult n k) : Nat :=
  (Nauty.rowsOf res.form).foldl (· + ·) 0 +
    (List.finRange n).foldl (fun a i => a + (res.label.get i).val) 0

private def adjStrings {n : Nat} (G : Colored n 1) : List String :=
  (List.finRange n).map fun i => String.ofList <|
    (List.finRange n).map fun j => if G.graph.adj i j then '1' else '0'

/-- Route every measured result through an opaque IO sink so the
compiler cannot hoist or elide the timed computation (LeanBench's
`blackBox` idiom). -/
initialize sinkRef : IO.Ref Nat ← IO.mkRef 0

@[noinline] def blackBox (a : Nat) : IO Unit :=
  sinkRef.modify (· ^^^ a)

private def timeMinNs (act : Unit → IO Nat) : IO Nat := do
  let w0 ← IO.monoNanosNow
  blackBox (← act ())  -- warmup
  let w1 ← IO.monoNanosNow
  -- one timed repetition suffices once a single call costs a second
  let effReps := if w1 - w0 > 1000000000 then 1 else reps
  let mut best : Nat := 0
  for _ in [0 : effReps] do
    let t0 ← IO.monoNanosNow
    blackBox (← act ())
    let t1 ← IO.monoNanosNow
    if best == 0 || t1 - t0 < best then
      best := t1 - t0
  -- scaling self-check: a doubled batch must cost about double, or the
  -- measurement is an artifact (hoisting, memoization) — warn loudly
  if effReps > 1 && best > 20000 then
    let t0 ← IO.monoNanosNow
    blackBox (← act ())
    blackBox (← act ())
    let t1 ← IO.monoNanosNow
    let two := t1 - t0
    if two < best || two > 8 * best then
      IO.eprintln s!"cactus: WARNING scaling self-check failed \
        (1x best {best}ns, 2x batch {two}ns) — measurement suspect"
  return best

private def runInst (i : Inst) : IO Unit := do
  let ⟨n, G⟩ := i.packed
  let fastNs ← timeMinNs fun _ => pure (digest (canonicalize G))
  let colors := List.replicate n 0
  let adj := adjStrings G
  let nautyNs ← timeMinNs fun _ => do
    let r ← Hex.BenchOracle.Nauty.canon n 1 colors adj
    pure (r.lab.foldl (· + ·) 0)
  let nodes := (Nauty.runColored G).numnodes
  IO.println <| "{\"family\": \"" ++ i.family ++ "\", \"name\": \"" ++
    i.name ++ s!"\", \"n\": {n}, \"fast_ns\": {fastNs}" ++
    s!", \"nauty_ns\": {nautyNs}, \"nodes\": {nodes}}" ++ ""
  (← IO.getStdout).flush

private def instances : List Inst := Id.run do
  let mut out : List Inst := []
  for n in [8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 64, 96, 128, 160,
      192, 224, 255] do
    if h : 0 < n then
      out := inst "circulant-12" s!"circulant{n}-1-2"
        (Families.circulant n [1, 2]) h :: out
  for n in [17, 25, 33, 41, 49, 57, 65, 97, 129, 161, 193, 225] do
    if h : 0 < n then
      out := inst "circulant-1248" s!"circulant{n}-1-2-4-8"
        (Families.circulant n [1, 2, 4, 8]) h :: out
  for a in [3, 4, 5, 6, 7, 8, 10, 12, 14, 15] do
    if h : 0 < a * a then
      out := inst "grid" s!"grid{a}x{a}" (Families.grid a a) h :: out
  for d in [3, 4, 5, 6, 7] do
    if h : 0 < 2 ^ d then
      out := inst "hypercube" s!"q{d}" (Families.hypercube d) h :: out
  for m in [5, 6, 7, 8, 9, 12, 15, 17, 20, 22] do
    if h : 0 < Families.choose m 2 then
      out := inst "kneser" s!"kneser{m}-2" (Families.kneser m 2) h :: out
    if h : 0 < Families.choose m 2 then
      out := inst "johnson" s!"johnson{m}-2" (Families.johnson m 2) h :: out
  for q in [13, 17, 29, 37, 41, 53, 61, 73, 89, 113, 149, 181, 229] do
    if h : 0 < q then
      out := inst "paley" s!"paley{q}" (Families.paley q) h :: out
  for m in [5, 9, 13] do
    if h : 0 < m * m then
      out := inst "latin" s!"latin{m}" (Families.latinSquare m) h :: out
  let mut g : Random.Gen := ⟨Random.seed1⟩
  for n in [10, 14, 18, 22, 26, 30, 36, 42, 48, 56, 64, 80, 96, 128,
      160, 192, 224, 255] do
    let (mask, g') := Random.gnpMask g n
    g := g'
    if h : 0 < n then
      -- the campaign's mask convention: bit `t` is the `t`-th pair
      -- `(i, j)`, `i < j`, in lexicographic order
      out := inst "random" s!"gnp{n}-seed1"
        (Graph.ofRel fun i j =>
          decide (i.val < j.val) &&
            mask.testBit (i.val * (n - 1) - i.val * (i.val - 1) / 2 +
              (j.val - i.val - 1)))
        h :: out
  return out.reverse

/-! # Pair problems

Isomorphism decisions for the proof-obligation cactus: each problem is
a pair with a known polarity. The `exprA`/`exprB` fields are the Lean
source of the two sides, consumed by the tactic harness in
`scripts/plots/hexgraphiso-cactus.py` to generate `graph_iso` proof
files, so the compiled and tactic tiers run the same problems.
Polarity is revalidated at runtime before timing. -/

private def rotExpr (n : Nat) : String :=
  s!"A.relabel ((Perm.ofVector? (Vector.ofFn fun i => i + 1)).getD " ++
    s!"(Perm.id {n})).toLabel"

private structure PairInst where
  family : String
  name : String
  iso : Bool
  exprA : String
  exprB : String
  packed : (m : Nat) × Colored m 1 × Colored m 1

private def rotate {n : Nat} (G : Colored n 1) (h : 0 < n) : Colored n 1 :=
  G.relabel ((Perm.ofVector? (Vector.ofFn fun i =>
    ⟨(i.val + 1) % n, Nat.mod_lt _ h⟩)).getD (Perm.id n)).toLabel

private def posPair (family name : String) {n : Nat} (G : Graph n)
    (h : 0 < n) (exprA : String) : PairInst :=
  let A := Graph.singleColor G h
  { family, name, iso := true, exprA, exprB := rotExpr n,
    packed := ⟨n, A, rotate A h⟩ }

private def negPair (family name : String) {n : Nat} (G H : Graph n)
    (h : 0 < n) (exprA exprB : String) : PairInst :=
  { family, name, iso := false, exprA, exprB,
    packed := ⟨n, Graph.singleColor G h, Graph.singleColor H h⟩ }

private def pairInstances : List PairInst := Id.run do
  let mut out : List PairInst := []
  for n in [8, 12, 16, 20, 24, 32] do
    if h : 0 < n then
      out := posPair "circulant-12" s!"pos-circulant{n}"
        (Families.circulant n [1, 2]) h
        s!"Graph.singleColor (Families.circulant {n} [1, 2])" :: out
  for a in [3, 4, 5] do
    if h : 0 < a * a then
      out := posPair "grid" s!"pos-grid{a}x{a}" (Families.grid a a) h
        s!"Graph.singleColor (Families.grid {a} {a})" :: out
  for d in [3, 4] do
    if h : 0 < 2 ^ d then
      out := posPair "hypercube" s!"pos-q{d}" (Families.hypercube d) h
        s!"Graph.singleColor (Families.hypercube {d})" :: out
  if h : 0 < Families.choose 5 2 then
    out := posPair "kneser" "pos-kneser5-2" (Families.kneser 5 2) h
      "Graph.singleColor (Families.kneser 5 2)" :: out
  -- C(2m) versus two copies of C(m): 2-regular, never isomorphic
  for m in [3, 4, 5, 6, 7, 8] do
    if h : 0 < 2 * m then
      out := negPair "cycles" s!"neg-c{2*m}-vs-2c{m}"
        (Families.cycle (2 * m)) (Families.copies 2 (Families.cycle m)) h
        s!"Graph.singleColor (Families.cycle {2 * m})"
        s!"Graph.singleColor (Families.copies 2 (Families.cycle {m}))" :: out
  -- cubic non-isomorphic pair on ten vertices
  if h : 0 < (10 : Nat) then
    out := negPair "named" "neg-circulant10-2-5-vs-1-5"
      (Families.circulant 10 [2, 5]) (Families.circulant 10 [1, 5]) h
      "Graph.singleColor (Families.circulant 10 [2, 5])"
      "Graph.singleColor (Families.circulant 10 [1, 5])" :: out
  -- 10-regular non-isomorphic pair on 21 vertices
  if h : 0 < Families.choose 7 2 then
    out := negPair "named" "neg-kneser72-vs-johnson72"
      (Families.kneser 7 2) (Families.johnson 7 2) h
      "Graph.singleColor (Families.kneser 7 2)"
      "Graph.singleColor (Families.johnson 7 2)" :: out
  -- irregular negatives (added as a documented series break): distinct
  -- degree multisets at matched size, so the root refinement separates
  -- them and the tiered negative route's cheapest tier is exercised
  if h : 0 < 3 * 4 then
    out := negPair "irregular" "neg-grid3x4-vs-circulant12"
      (Families.grid 3 4) (Families.circulant 12 [1, 2]) h
      "Graph.singleColor (Families.grid 3 4)"
      "Graph.singleColor (Families.circulant 12 [1, 2])" :: out
  if h : 0 < 4 * 4 then
    out := negPair "irregular" "neg-grid4x4-vs-q4"
      (Families.grid 4 4) (Families.hypercube 4) h
      "Graph.singleColor (Families.grid 4 4)"
      "Graph.singleColor (Families.hypercube 4)" :: out
  if h : 0 < 4 * 5 then
    out := negPair "irregular" "neg-grid4x5-vs-k8-12"
      (Families.grid 4 5) (Families.completeBipartite 8 12) h
      "Graph.singleColor (Families.grid 4 5)"
      "Graph.singleColor (Families.completeBipartite 8 12)" :: out
  if h : 0 < 4 * 6 then
    out := negPair "irregular" "neg-grid4x6-vs-2grid3x4"
      (Families.grid 4 6) (Families.copies 2 (Families.grid 3 4)) h
      "Graph.singleColor (Families.grid 4 6)"
      "Graph.singleColor (Families.copies 2 (Families.grid 3 4))" :: out
  -- larger positives (corpus extension, series break 2)
  for n in [64, 128] do
    if h : 0 < n then
      out := posPair "circulant-12" s!"pos-circulant{n}"
        (Families.circulant n [1, 2]) h
        s!"Graph.singleColor (Families.circulant {n} [1, 2])" :: out
  for d in [5, 6] do
    if h : 0 < 2 ^ d then
      out := posPair "hypercube" s!"pos-q{d}" (Families.hypercube d) h
        s!"Graph.singleColor (Families.hypercube {d})" :: out
  if h : 0 < Families.choose 10 2 then
    out := posPair "kneser" "pos-kneser10-2" (Families.kneser 10 2) h
      "Graph.singleColor (Families.kneser 10 2)" :: out
  if h : 0 < (61 : Nat) then
    out := posPair "paley" "pos-paley61" (Families.paley 61) h
      "Graph.singleColor (Families.paley 61)" :: out
  -- strongly regular negative: same parameters (25, 12, 5, 6), never
  -- isomorphic — vertex partitions stay uniform until deep in the search
  if h : 0 < (25 : Nat) then
    out := negPair "srg" "neg-paley25-vs-latin5"
      (Families.paley 25) (Families.latinSquare 5) h
      "Graph.singleColor (Families.paley 25)"
      "Graph.singleColor (Families.latinSquare 5)" :: out
  -- same-degree regular negatives at scale: connected circulant versus
  -- two disjoint copies, both 4-regular, refinement-uniform at the root
  for m in [24, 48] do
    if h : 0 < 2 * m then
      out := negPair "cycles-dense" s!"neg-circ{2*m}-vs-2circ{m}"
        (Families.circulant (2 * m) [1, 2])
        (Families.copies 2 (Families.circulant m [1, 2])) h
        s!"Graph.singleColor (Families.circulant {2 * m} [1, 2])"
        s!"Graph.singleColor (Families.copies 2 (Families.circulant {m} [1, 2]))"
        :: out
  -- 30-regular vertex-transitive negative: the Paley graph on 61
  -- vertices against a circulant of equal degree whose connection set
  -- mixes residues and non-residues (so no multiplier carries one to
  -- the other, and by Turner's theorem for prime order they are not
  -- isomorphic)
  if h : 0 < (61 : Nat) then
    out := negPair "srg" "neg-paley61-vs-circulant61"
      (Families.paley 61)
      (Families.circulant 61 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
        13, 14, 15]) h
      "Graph.singleColor (Families.paley 61)"
      ("Graph.singleColor (Families.circulant 61 [1, 2, 3, 4, 5, 6, 7, " ++
        "8, 9, 10, 11, 12, 13, 14, 15])") :: out
  return out.reverse

private def escape (s : String) : String :=
  s.foldl (fun a c => if c == '"' then a ++ "\\\"" else a.push c) ""

private def runPair (p : PairInst) : IO Unit := do
  let ⟨n, A, B⟩ := p.packed
  unless isIso A B == p.iso do
    throw <| IO.userError s!"pair {p.name}: polarity mismatch"
  let fastNs ← timeMinNs fun _ =>
    pure (if isIso A B then 1 else 0)
  let colors := List.replicate n 0
  let adjA := adjStrings A
  let adjB := adjStrings B
  let nautyNs ← timeMinNs fun _ => do
    let ra ← Hex.BenchOracle.Nauty.canon n 1 colors adjA
    let rb ← Hex.BenchOracle.Nauty.canon n 1 colors adjB
    pure (if ra.tri == rb.tri then 1 else 0)
  IO.println <| "{\"family\": \"" ++ p.family ++ "\", \"name\": \"" ++
    p.name ++ s!"\", \"n\": {n}, \"iso\": {p.iso}" ++
    s!", \"fast_ns\": {fastNs}" ++
    s!", \"nauty_ns\": {nautyNs}" ++
    ", \"exprA\": \"" ++ escape p.exprA ++
    "\", \"exprB\": \"" ++ escape p.exprB ++ "\"}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  match args with
  | ["pairs"] => for p in pairInstances do runPair p
  | _ => for i in instances do runInst i

end Hex.GraphIsoCactus

def main (args : List String) : IO Unit := Hex.GraphIsoCactus.main args
