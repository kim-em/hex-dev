/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-
The IsoGraph side of the HexGraphIso / IsoGraph comparison.

Not part of this project's build: drop this file into a checkout of
https://github.com/Timeroot/IsoGraph as `testing/HexCompare.lean` and
add

```toml
[[lean_exe]]
name = "hexcompare"
root = "testing.HexCompare"
```

to its `lakefile.toml`. It is kept here so the comparison in
`reports/graphiso-comparison.md` can be rerun; IsoGraph is a
separate repository and nothing here is published into it.

Measured against IsoGraph 7cfa2370 (2026-09-02), Lean v4.34.0-rc2.
-/

import IsoGraph.Canon.Algorithm
import Lean.Data.Json

/-!
Head-to-head timing driver: `IsoGraph.Canon.canonical` on exactly the
instances `hexgraphiso_cactus dump` emits, read as JSON lines of the form

```
{"family": "...", "name": "...", "n": N, "rows": ["0101...", ...]}
```

and re-emitted as

```
{"name": "...", "iso_ns": ..., "iso_nodes": ..., "build_ns": ...}
```

Timing mirrors the hex driver: one warmup call, then the minimum of
several repetitions, with every measured result routed through an
opaque `IO.Ref` sink so the compiler cannot hoist or elide the timed
computation, and a doubled-batch self-check that flags a measurement
whose cost does not scale with the number of calls.

    lake exe hexcompare instances.jsonl > isograph.jsonl
-/

open IsoGraph.Canon
open Lean

namespace HexCompare

def reps : Nat := 5

initialize sinkRef : IO.Ref Nat ← IO.mkRef 0

@[noinline] def blackBox (a : Nat) : IO Unit :=
  sinkRef.modify (· ^^^ a)

/-- A cheap digest forcing full evaluation of a canonical result. -/
def digest (r : Result) : Nat :=
  r.cert.foldl (fun a w => a + w.toNat) 0 + r.lab.foldl (· + ·) 0 + r.nodes

def timeMinNs (act : Unit → IO Nat) : IO Nat := do
  let w0 ← IO.monoNanosNow
  blackBox (← act ())  -- warmup
  let w1 ← IO.monoNanosNow
  let effReps := if w1 - w0 > 1000000000 then 1 else reps
  let mut best : Nat := 0
  for _ in [0 : effReps] do
    let t0 ← IO.monoNanosNow
    blackBox (← act ())
    let t1 ← IO.monoNanosNow
    if best == 0 || t1 - t0 < best then
      best := t1 - t0
  if effReps > 1 && best > 20000 then
    let t0 ← IO.monoNanosNow
    blackBox (← act ())
    blackBox (← act ())
    let t1 ← IO.monoNanosNow
    let two := t1 - t0
    if two < best || two > 8 * best then
      IO.eprintln s!"hexcompare: WARNING scaling self-check failed \
        (1x best {best}ns, 2x batch {two}ns) — measurement suspect"
  return best

structure Inst where
  family : String
  name : String
  n : Nat
  bits : Array (Array Bool)

def chomp (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r')).reverse

/-- Read one corpus block from `h`, or `none` at end of file. The format
is the one `hexgraphiso_cactus dump` writes: a header `G <name> <family>
<n>` followed by `n` rows of `n` `0`/`1` characters. Instances are
streamed, not materialized all at once. -/
def readBlock (h : IO.FS.Handle) : IO (Option Inst) := do
  let mut header := ""
  repeat
    let line ← h.getLine
    if line.isEmpty then return none
    let line := chomp line
    if !line.isEmpty then
      header := line
      break
  match header.splitOn " " with
  | ["G", name, family, nStr] =>
    let some n := nStr.toNat? | throw <| IO.userError s!"corpus: bad n {nStr}"
    let mut bits : Array (Array Bool) := Array.emptyWithCapacity n
    for _ in [0:n] do
      let row := chomp (← h.getLine)
      unless row.length == n do
        throw <| IO.userError s!"corpus: {name} row length {row.length} ≠ {n}"
      bits := bits.push (row.toList.map (· == '1')).toArray
    return some { family, name, n, bits }
  | _ => throw <| IO.userError s!"corpus: bad header {header}"

/-- Which column to measure. A sweep under a per-instance time budget
runs one process per column, so an instance's budget is spent on the one
measurement it is being judged on. -/
inductive Column where
  /-- `canonical` on an already-built graph. -/
  | canon
  /-- `canonical` charged the dense-to-native conversion too, which is
  what the hex column pays inside its own timer through `rowsOf`. -/
  | whole
  /-- Both, plus the graph construction on its own. -/
  | all
  deriving BEq

def Column.ofString? : String → Option Column
  | "canon" => some .canon
  | "whole" => some .whole
  | "all" => some .all
  | _ => none

def run (col : Column) (i : Inst) : IO Unit := do
  let bits := i.bits
  let mut fields : List String := []
  if col == .all then
    -- the adjacency is materialized outside the timed region, as it is on
    -- the hex side: what is timed is the canonical search, not the family
    -- generator
    let buildNs ← timeMinNs fun _ => do
      let G := Graph.ofOracle i.n fun v w => (bits[v]!)[w]!
      pure (G.adj.size + G.nbr.size)
    fields := s!"\"iso_build_ns\": {buildNs}" :: fields
  if col == .whole || col == .all then
    -- the same search charged the dense-to-native conversion, which is what
    -- the hex column pays inside its own timed region (`rowsOf`)
    let wholeNs ← timeMinNs fun _ =>
      pure (digest (canonical (Graph.ofOracle i.n fun v w => (bits[v]!)[w]!)))
    fields := s!"\"iso_whole_ns\": {wholeNs}" :: fields
  if col == .canon || col == .all then
    let G := Graph.ofOracle i.n fun v w => (bits[v]!)[w]!
    blackBox (G.adj.size + G.nbr.size)
    let isoNs ← timeMinNs fun _ => pure (digest (canonical G))
    fields := s!"\"iso_nodes\": {(canonical G).nodes}" :: fields
    fields := s!"\"iso_ns\": {isoNs}" :: fields
  IO.println <| "{\"name\": \"" ++ i.name ++ s!"\", \"n\": {i.n}, " ++
    String.intercalate ", " fields.reverse ++ "}"
  (← IO.getStdout).flush

end HexCompare

namespace HexCompare

/-- xorshift64*, so the relabelling check does not depend on anything
outside this file. -/
def nextRand (s : UInt64) : UInt64 :=
  let x := s ^^^ (s <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  x

/-- A pseudo-random permutation of `{0, …, n-1}` (Fisher-Yates). -/
def randPerm (n : Nat) (seed : UInt64) : Array Nat := Id.run do
  let mut a := Array.range n
  let mut s := seed ^^^ 88172645463325252
  let mut i := n
  while i > 1 do
    i := i - 1
    s := nextRand s
    let j := ((s * 2685821657736338717) >>> 11).toNat % (i + 1)
    let ai := a[i]!
    a := a.set! i a[j]!
    a := a.set! j ai
  return a

/-- `G` relabelled by `π`: new vertex `π[v]` plays the role of old `v`. -/
def relabel (bits : Array (Array Bool)) (n : Nat) (π : Array Nat) :
    Array (Array Bool) := Id.run do
  let mut inv := Array.replicate n 0
  for v in [0:n] do
    inv := inv.set! π[v]! v
  return Array.ofFn (n := n) fun a =>
    Array.ofFn (n := n) fun b => (bits[inv[a.1]!]!)[inv[b.1]!]!

def graphOf (n : Nat) (bits : Array (Array Bool)) : Graph :=
  Graph.ofOracle n fun v w => (bits[v]!)[w]!

/-- Canonicalise the instance and three pseudo-random relabellings of it;
every certificate must agree, and the reported labelling must be a
permutation whose certificate is the one reported. -/
def checkInvariance (i : Inst) : IO Bool := do
  let G := graphOf i.n i.bits
  let res := canonical G
  let mut ok := true
  if !isPermArray i.n res.lab then
    IO.eprintln s!"{i.name}: labelling is not a permutation"
    ok := false
  if lexCmpU64 (certOf G res.lab) res.cert != .eq then
    IO.eprintln s!"{i.name}: certificate disagrees with certOf"
    ok := false
  for t in [1:4] do
    let π := randPerm i.n (UInt64.ofNat (t * 7919 + i.n))
    let H := graphOf i.n (relabel i.bits i.n π)
    if lexCmpU64 (canonical H).cert res.cert != .eq then
      IO.eprintln s!"{i.name}: canonical form is NOT isomorphism-invariant"
      ok := false
  return ok

structure Pair where
  name : String
  n : Nat
  iso : Bool
  a : Array (Array Bool)
  b : Array (Array Bool)

def parsePair (line : String) : Except String Pair := do
  let j ← Json.parse line
  let name ← j.getObjValAs? String "name"
  let n ← j.getObjValAs? Nat "n"
  let iso ← j.getObjValAs? Bool "iso"
  let ra ← j.getObjValAs? (Array String) "rowsA"
  let rb ← j.getObjValAs? (Array String) "rowsB"
  let dec := fun (rs : Array String) => rs.map fun r => (r.toList.map (· == '1')).toArray
  return { name, n, iso, a := dec ra, b := dec rb }

/-- Does IsoGraph's certificate settle this pair the way hex does? -/
def checkPair (p : Pair) : IO Bool := do
  let got := lexCmpU64 (canonical (graphOf p.n p.a)).cert
    (canonical (graphOf p.n p.b)).cert == .eq
  if got != p.iso then
    IO.eprintln s!"{p.name}: IsoGraph says iso = {got}, hex says {p.iso}"
  return got == p.iso

end HexCompare

def runFile (path : String) (c : HexCompare.Column) : IO Unit := do
  let h ← IO.FS.Handle.mk path .read
  repeat
    match ← HexCompare.readBlock h with
    | none => break
    | some i => HexCompare.run c i

def main (args : List String) : IO Unit := do
  match args with
  | ["--check", path] =>
    let h ← IO.FS.Handle.mk path .read
    let mut ok := true
    let mut count := 0
    repeat
      match ← HexCompare.readBlock h with
      | none => break
      | some i =>
        count := count + 1
        unless (← HexCompare.checkInvariance i) do ok := false
    IO.println s!"invariance: {count} instances, {if ok then "all OK" else "FAILURES"}"
  | ["--pairs", path] =>
    let mut ok := true
    let mut count := 0
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if line.startsWith "{" then
        count := count + 1
        unless (← HexCompare.checkPair (← IO.ofExcept (HexCompare.parsePair line))) do
          ok := false
    IO.println s!"pairs: {count} decisions, {if ok then "all agree with hex" else "DISAGREEMENTS"}"
  | [path] => runFile path .all
  | [path, col] =>
    let some c := HexCompare.Column.ofString? col
      | throw <| IO.userError s!"unknown column {col}"
    runFile path c
  | _ =>
    throw <| IO.userError
      "usage: hexcompare [--check|--pairs] <file> | <corpus> [canon|whole|all]"
