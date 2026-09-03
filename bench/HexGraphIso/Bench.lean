/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso
import Hex.BenchOracle.Nauty
import LeanBench

/-!
Benchmark registrations for `hex-graph-iso`.

This first slice measures the polynomially modelled building blocks and
the factorially modelled reference canonical form on deterministic
family inputs; input construction is hoisted into `prep` so each model
tracks the timed operation.

Scientific registrations:

* `runDenseConvert`: dense bitset-row conversion of a coloured graph,
  quadratic in the vertex count.
* `runRefine`: one full equitable refinement of the colour partition by
  the nauty-compatible `refine`, declared with the SPEC's conservative
  cubic model.
* `runRelabel`: relabelling a coloured graph along a rotation,
  quadratic bit-matrix work.
* `runReferenceCanon`: the reference canonical form, dominated by the
  `n^n` candidate enumeration with quadratic per-candidate work; capped
  at the small sizes where the factorial-style enumeration is practical.

The nauty-compatible search declares no polynomial model in `n`
(HexGraphIso/SPEC/hex-graph-iso.md § Benchmarks); the public operations
backed by it, the certificate pipeline, and the pinned nauty
comparator register as fixed benchmarks on committed circulant sizes:

* `runHexCanon{8,12,16}` versus `runNautyCanon{8,12,16}`: the public
  fast `canon` (the transcription surface; before the API flip this
  series measured the certificate-checked pipeline — series break
  noted) against the pinned nauty 2.9.3 comparator (in-process FFI
  against the vendored source, via `Hex.BenchOracle.Nauty`), joined
  on the canonical upper-triangle bits.
* `runHexCanonChecked{8,12,16}`: the certificate-checked
  `canonChecked` on the same instances — the explicit price of the
  validated certificate.
* `runIsIso12`, `runFindIso12`: the public fast isomorphism
  decisions; `runIsIsoChecked12` the certificate-checked decision.
* `runCertify12`, `runCertReplay12`: unbounded certificate generation
  and the generation-plus-replay pipeline (`Nauty.certifyKey?` and
  `Nauty.certifyCanon?`; the limit-gated public wrappers are covered
  by conformance).
* `runCanonAgree16`: the agreement check joining the two comparator
  columns — `verify` fails if the public canonical bits ever diverge
  from pinned nauty's.
-/

namespace Hex.GraphIsoBench

open Hex.GraphIso

/-- Flattened benchmark input: a deterministic coloured circulant. -/
structure GraphInput where
  n : Nat
  deriving Repr, BEq, Hashable

/-- The benchmark family: the circulant on `{1, 2}` offsets with the
one-cell colouring, plus a fallback for `n = 0`. -/
def prepGraph (n : Nat) : GraphInput :=
  { n := n }

/-- Rebuild the typed coloured graph of an input. -/
def graphOf (input : GraphInput) : Option ((n : Nat) × Colored n 1) :=
  if h : 0 < input.n then
    some ⟨input.n, Families.plain (Families.circulant input.n [1, 2]) h⟩
  else
    none

/-- Benchmark target: dense bitset-row conversion. -/
def runDenseConvert (input : GraphInput) : Nat :=
  match graphOf input with
  | some ⟨_, G⟩ => (Nauty.rowsOf G).foldl (· + ·) 0
  | none => 0

/- Cost model: the conversion reads one adjacency bit for each of the
n × n vertex pairs, so it is quadratic in n. -/
setup_benchmark runDenseConvert n => n ^ 2
  with prep := prepGraph
  where {
    paramFloor := 8
    paramCeiling := 256
    maxSecondsPerCall := 1.0
  }

/-- Benchmark target: one full equitable refinement of the colour
partition. -/
def runRefine (input : GraphInput) : Nat :=
  match graphOf input with
  | some ⟨n, G⟩ =>
    let ctx : Nauty.Ctx := { n := n, g := Nauty.rowsOf G }
    let (lab0, ends) := Nauty.initialPartition G
    let st := Nauty.refine ctx 1 lab0
      ((Array.replicate n (n + 2)).set! (n - 1) 0)
      (Nauty.insert 0 0) ends.length
    st.numcells + st.longcode
  | none => 0

/- Cost model: one equitable refinement performs at most n splitting
passes (each split creates a cell, and there are at most n), and each
pass counts neighbours of up to n vertices against n-bit rows, so the
worst case is cubic in n. -/
setup_benchmark runRefine n => n ^ 3
  with prep := prepGraph
  where {
    paramFloor := 8
    paramCeiling := 128
    maxSecondsPerCall := 1.0
  }

/-- Benchmark target: relabel a coloured graph along the rotation
labelling. -/
def runRelabel (input : GraphInput) : Nat :=
  match graphOf input with
  | some ⟨n, G⟩ =>
    let l := (Perm.ofNatArray? n
      (.ofFn fun i : Fin n => (i.val + 1) % n)).getD (Perm.id n) |>.toLabel
    (G.relabel l).graph.degree ⟨0, by
      have := G.coloring.onto 0
      rcases this with ⟨v, _⟩
      exact v.pos⟩
  | none => 0

/- Cost model: relabelling rebuilds the n × n adjacency relation one
entry at a time, so it is quadratic in n. -/
setup_benchmark runRelabel n => n ^ 2
  with prep := prepGraph
  where {
    paramFloor := 8
    paramCeiling := 256
    maxSecondsPerCall := 1.0
  }

/-- Benchmark target: the reference canonical form, factorially
expensive by design. -/
def runReferenceCanon (input : GraphInput) : Nat :=
  match graphOf input with
  | some ⟨_, G⟩ => (Reference.canonicalize G).label.perm.vec.toList.foldl
      (fun a v => a + v.val) 0
  | none => 0

/- Cost model: the reference form enumerates all cell-respecting
labellings — at most n! ≤ n ^ n — and serializes an n × n adjacency
matrix for each comparison, so the declared model is n ^ n · n². -/
setup_benchmark runReferenceCanon n => n ^ n * n ^ 2
  with prep := prepGraph
  where {
    paramFloor := 2
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 5, 6]
    maxSecondsPerCall := 5.0
  }

/-! # Fixed benchmarks: public operations and the nauty comparator -/

private def triBitsOf {n k : Nat} (K : Colored n k) : String :=
  String.ofList <| (List.range n).flatMap fun i =>
    ((List.range n).filter (fun j => i < j)).map fun j =>
      if h : i < n ∧ j < n then
        (if K.graph.adj ⟨i, h.1⟩ ⟨j, h.2⟩ then '1' else '0')
      else '0'

private def adjStrings {n k : Nat} (G : Colored n k) : List String :=
  (List.range n).map fun i => String.ofList <| (List.range n).map fun j =>
    if h : i < n ∧ j < n then
      (if G.graph.adj ⟨i, h.1⟩ ⟨j, h.2⟩ then '1' else '0')
    else '0'

private def runHexCanonAt (m : Nat) (_ : Unit) : IO String :=
  match graphOf { n := m } with
  | some ⟨_, G⟩ => return triBitsOf (canon G)
  | none => return ""

private def runNautyCanonAt (m : Nat) (_ : Unit) : IO String := do
  match graphOf { n := m } with
  | some ⟨m', G⟩ =>
    let result ← Hex.BenchOracle.Nauty.canon m' 1
      (List.replicate m' 0) (adjStrings G)
    return result.tri
  | none => return ""

private def runHexCanonCheckedAt (m : Nat) (_ : Unit) : IO String :=
  match graphOf { n := m } with
  | some ⟨_, G⟩ => return triBitsOf (canonChecked G)
  | none => return ""

def runHexCanon8 : Unit → IO String := runHexCanonAt 8
def runHexCanonChecked8 : Unit → IO String := runHexCanonCheckedAt 8
def runHexCanonChecked12 : Unit → IO String := runHexCanonCheckedAt 12
def runHexCanonChecked16 : Unit → IO String := runHexCanonCheckedAt 16
def runNautyCanon8 : Unit → IO String := runNautyCanonAt 8
def runHexCanon12 : Unit → IO String := runHexCanonAt 12
def runNautyCanon12 : Unit → IO String := runNautyCanonAt 12
def runHexCanon16 : Unit → IO String := runHexCanonAt 16
def runNautyCanon16 : Unit → IO String := runNautyCanonAt 16

/-- The unpruned specification key on a factorially feasible size. -/
def runSpecKey6 : Unit → IO Nat := fun _ =>
  match graphOf { n := 6 } with
  | some ⟨_, G⟩ =>
    return (Nauty.canonSpecKey G).codes.foldl (· + ·) 0
  | none => return 0

def runIsIso12 : Unit → IO Bool := fun _ =>
  match graphOf { n := 12 } with
  | some ⟨_, G⟩ => return isIso G G
  | none => return false

def runIsIsoChecked12 : Unit → IO Bool := fun _ =>
  match graphOf { n := 12 } with
  | some ⟨_, G⟩ => return isIsoChecked G G
  | none => return false

def runFindIso12 : Unit → IO Bool := fun _ =>
  match graphOf { n := 12 } with
  | some ⟨_, G⟩ => return (findIso G G).isSome
  | none => return false

def runCertify12 : Unit → IO Bool := fun _ =>
  match graphOf { n := 12 } with
  | some ⟨_, G⟩ => return (Nauty.certifyKey? G).isSome
  | none => return false

def runCertReplay12 : Unit → IO String := fun _ =>
  match graphOf { n := 12 } with
  | some ⟨_, G⟩ =>
    match Nauty.certifyCanon? G with
    | some res => return triBitsOf res.form
    | none => return "certify-failed"
  | none => return ""

/-- The comparator agreement check: `verify` fails if the public
canonical bits ever diverge from pinned nauty's. -/
def runCanonAgree16 : Unit → IO String := fun _ => do
  match graphOf { n := 16 } with
  | some ⟨m, G⟩ =>
    let hexTri := triBitsOf (canon G)
    let result ← Hex.BenchOracle.Nauty.canon m 1
      (List.replicate m 0) (adjStrings G)
    unless hexTri == result.tri do
      throw (IO.userError
        s!"canonical bits diverge from nauty: {hexTri} vs {result.tri}")
    return hexTri
  | none => return ""

private def hexComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 8.0

private def externalComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 8.0
  warmupFirstIter := true

setup_fixed_benchmark runHexCanon8 where hexComparisonConfig
setup_fixed_benchmark runNautyCanon8 where externalComparisonConfig
setup_fixed_benchmark runHexCanon12 where hexComparisonConfig
setup_fixed_benchmark runNautyCanon12 where externalComparisonConfig
setup_fixed_benchmark runHexCanon16 where hexComparisonConfig
setup_fixed_benchmark runHexCanonChecked8 where hexComparisonConfig
setup_fixed_benchmark runHexCanonChecked12 where hexComparisonConfig
setup_fixed_benchmark runHexCanonChecked16 where hexComparisonConfig
setup_fixed_benchmark runNautyCanon16 where externalComparisonConfig
setup_fixed_benchmark runSpecKey6 where hexComparisonConfig
setup_fixed_benchmark runIsIso12 where hexComparisonConfig
setup_fixed_benchmark runIsIsoChecked12 where hexComparisonConfig
setup_fixed_benchmark runFindIso12 where hexComparisonConfig
setup_fixed_benchmark runCertify12 where hexComparisonConfig
setup_fixed_benchmark runCertReplay12 where hexComparisonConfig
setup_fixed_benchmark runCanonAgree16 where externalComparisonConfig

end Hex.GraphIsoBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
