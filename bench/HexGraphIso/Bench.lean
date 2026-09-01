/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso
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

The nauty-compatible search itself declares no polynomial model in `n`
(SPEC/Libraries/hex-graph-iso.md § Benchmarks); its node-count-based
registrations and the external nauty comparator shim belong to the
scheduled performance stage, not this merge slice.
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

setup_benchmark runDenseConvert n => n * n
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

setup_benchmark runRefine n => n * n * n
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
    let l := (permOfNatArray? n
      (.ofFn fun i : Fin n => (i.val + 1) % n)).getD (Perm.id n) |>.toLabel
    (G.relabel l).graph.degree ⟨0, by
      have := G.coloring.onto 0
      rcases this with ⟨v, _⟩
      exact v.pos⟩
  | none => 0

setup_benchmark runRelabel n => n * n
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

setup_benchmark runReferenceCanon n => n ^ n * n * n
  with prep := prepGraph
  where {
    paramFloor := 2
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 5, 6]
    maxSecondsPerCall := 5.0
  }

end Hex.GraphIsoBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
