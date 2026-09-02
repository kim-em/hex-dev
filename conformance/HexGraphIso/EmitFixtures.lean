/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexGraphIso

/-!
Deterministic JSONL fixtures for the `HexGraphIso` external nauty oracle.

The stream contains the SPEC's merge fixture: all 1,100 labelled
uncoloured graphs for `0 ≤ n ≤ 5`, all 4,912 graph and
ordered-surjective-partition pairs for `0 ≤ n ≤ 4`, deterministic
relabellings and colourings of named larger examples, positive and
negative isomorphism pairs, and graphs whose automorphism groups are
trivial, small, and large. Graphs are enumerated by an adjacency bitmask
over the lexicographic `i < j` pair order; colour vectors are enumerated
as base-`k` numerals with vertex `0` most significant. Pseudo-random
cases use the SPEC's SplitMix64 corpus seeds.

Each record carries the *public* answer: the canonical label and
canonical upper-triangle bits are read off `canonicalize` (the
certificate-checked production pipeline behind `canon` and `label`),
with the coloured graph built through the public checked constructors.
The search-node count comes from the transcribed search
(`Nauty.runColored`). The oracle recomputes all of them with the pinned
external nauty, so the campaign pins the public surface, not only the
transcription.
-/

namespace Hex.GraphIsoEmit

open Hex.Conformance.Emit
open Hex.GraphIso
open Hex.GraphIso.Nauty

private def lib : String := "HexGraphIso"

/-- The vertex pairs `(i, j)`, `i < j`, in lexicographic order. -/
private def pairList (n : Nat) : List (Nat × Nat) := Id.run do
  let mut out := []
  for i in [0 : n] do
    for j in [i + 1 : n] do
      out := (i, j) :: out
  return out.reverse

private def edgesOfMask (n mask : Nat) : List (Nat × Nat) :=
  ((pairList n).zipIdx.filter fun (_, t) => mask.testBit t).map (·.1)

/-- Build the coloured graph through the public checked constructors. -/
private def coloredOf? (n k : Nat) (colors : Array Nat)
    (edges : List (Nat × Nat)) : Option (Colored n k) := do
  let g ← Graph.ofEdges? n edges
  if h : colors.size = n ∧ ∀ v ∈ colors, v < k then
    let c ← Coloring.ofVector?
      ⟨colors.attach.map fun v => (⟨v.val, h.2 v.val v.property⟩ : Fin k),
        by simp [h.1]⟩
    some { graph := g, coloring := c }
  else
    none

/-- The upper-triangle adjacency bits of a coloured graph in row-major
order. -/
private def triBits {n k : Nat} (G : Colored n k) : String :=
  String.ofList <| (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => decide (i.val < j.val)).map fun j =>
      if G.graph.adj i j then '1' else '0'

/-- Canonicalize through the public API and emit one fixture record: the
label and upper-triangle bits are read off public `canonicalize`, the
node count off the transcribed search. -/
private def emitCase (case : String) (n k : Nat) (colors : Array Nat)
    (edges : List (Nat × Nat)) : IO Unit := do
  let some G := coloredOf? n k colors edges
    | throw (IO.userError s!"emit: case {case} rejected by the builders")
  let res := canonicalize G
  -- release-gate cross-checks: the fast tier never falls back and
  -- agrees with the certificate-checked tier on every emitted case
  unless (Hex.GraphIso.canonicalize? G).isSome do
    throw (IO.userError s!"emit: fast fallback observed on {case}")
  unless res == canonicalizeChecked G do
    throw (IO.userError s!"emit: fast/checked disagreement on {case}")
  let r := Nauty.runColored G
  let mut sizes : Array Nat := .replicate k 0
  for v in [0 : n] do
    let c := colors[v]!
    sizes := sizes.set! c (sizes[c]! + 1)
  emitGraphIsoFixture lib case n k
    (colors.toList.map Int.ofNat)
    (edges.map fun (a, b) =>
      (Int.ofNat (Nat.min a b), Int.ofNat (Nat.max a b)))
    ((List.finRange n).map fun i => Int.ofNat (res.label.get i).val)
    (triBits res.form)
    (sizes.toList.map Int.ofNat)
    r.numnodes

/-- All base-`k` colour vectors of length `n`, vertex `0` most
significant, in ascending numeral order. -/
private def colorVectors (k : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | m + 1 => (List.range k).flatMap fun d => (colorVectors k m).map (d :: ·)

private def isOnto (k : Nat) (v : List Nat) : Bool :=
  (List.range k).all fun c => v.contains c

/-! # Named examples -/

private def petersen : List (Nat × Nat) :=
  (List.range 5).map (fun i => (i, (i + 1) % 5))
    ++ (List.range 5).map (fun i => (5 + i, 5 + ((i + 2) % 5)))
    ++ (List.range 5).map (fun i => (i, 5 + i))

/-- The Kneser presentation `K(5, 2)`: the two-element subsets of `Fin 5`
in lexicographic order, joined when disjoint. -/
private def kneser52 : List (Nat × Nat) := Id.run do
  let subsets := pairList 5
  let mut out := []
  for (s, i) in subsets.zipIdx do
    for (t, j) in subsets.zipIdx do
      if i < j then
        if s.1 ≠ t.1 ∧ s.1 ≠ t.2 ∧ s.2 ≠ t.1 ∧ s.2 ≠ t.2 then
          out := (i, j) :: out
  return out.reverse

private def prism5 : List (Nat × Nat) :=
  (List.range 5).map (fun i => (i, (i + 1) % 5))
    ++ (List.range 5).map (fun i => (5 + i, 5 + ((i + 1) % 5)))
    ++ (List.range 5).map (fun i => (i, 5 + i))

private def hypercube (d : Nat) : List (Nat × Nat) := Id.run do
  let n := 2 ^ d
  let mut out := []
  for x in [0 : n] do
    for b in [0 : d] do
      let y := x ^^^ (1 <<< b)
      if x < y then
        out := (x, y) :: out
  return out.reverse

private def completeBipartite (a b : Nat) : List (Nat × Nat) := Id.run do
  let mut out := []
  for i in [0 : a] do
    for j in [0 : b] do
      out := (i, a + j) :: out
  return out.reverse

private def triangles (t : Nat) : List (Nat × Nat) := Id.run do
  let mut out := []
  for i in [0 : t] do
    out := (3*i, 3*i+1) :: (3*i+1, 3*i+2) :: (3*i, 3*i+2) :: out
  return out.reverse

private def paley13 : List (Nat × Nat) := Id.run do
  let q := 13
  let qr := (List.range q).filterMap fun x =>
    if x > 0 then some ((x * x) % q) else none
  let mut out := []
  for i in [0 : q] do
    for j in [i + 1 : q] do
      if qr.contains ((j - i) % q) ∨ qr.contains ((q + i - j) % q) then
        out := (i, j) :: out
  return out.reverse

private def complete (n : Nat) : List (Nat × Nat) := pairList n

/-- Apply a vertex permutation to an edge list, renormalizing to `i < j`
pairs in lexicographic order. -/
private def relabelEdges (perm : Array Nat) (edges : List (Nat × Nat)) :
    List (Nat × Nat) :=
  (edges.map fun (a, b) =>
    let a := perm[a]!
    let b := perm[b]!
    (Nat.min a b, Nat.max a b)).mergeSort fun x y =>
      x.1 < y.1 ∨ (x.1 == y.1 ∧ x.2 ≤ y.2)

def main : IO Unit := do
  -- all labelled uncoloured graphs, 0 ≤ n ≤ 5
  for n in [0 : 6] do
    let pcount := n * (n - 1) / 2
    for mask in [0 : 2 ^ pcount] do
      let k := if n == 0 then 0 else 1
      emitCase s!"u/n{n}/m{mask}" n k (.replicate n 0) (edgesOfMask n mask)
  -- all graph and ordered-surjective-partition pairs, 0 ≤ n ≤ 4
  for n in [0 : 5] do
    let pcount := n * (n - 1) / 2
    for mask in [0 : 2 ^ pcount] do
      let edges := edgesOfMask n mask
      if n == 0 then
        emitCase s!"c/n0/m0/k0/" 0 0 #[] []
      else
        for k in [1 : n + 1] do
          for v in colorVectors k n do
            if isOnto k v then
              let digits := String.join (v.map toString)
              emitCase s!"c/n{n}/m{mask}/k{k}/{digits}" n k v.toArray edges
  -- named examples: positive and negative pairs, and automorphism-group
  -- extremes (trivial for the random graphs, small for paley13, large for
  -- empty/complete/triangles)
  emitCase "named/petersen" 10 1 (.replicate 10 0) petersen
  emitCase "named/kneser52" 10 1 (.replicate 10 0) kneser52
  emitCase "named/prism5" 10 1 (.replicate 10 0) prism5
  emitCase "named/q3" 8 1 (.replicate 8 0) (hypercube 3)
  emitCase "named/q4" 16 1 (.replicate 16 0) (hypercube 4)
  emitCase "named/k33" 6 1 (.replicate 6 0) (completeBipartite 3 3)
  emitCase "named/triangles4" 12 1 (.replicate 12 0) (triangles 4)
  emitCase "named/paley13" 13 1 (.replicate 13 0) paley13
  emitCase "named/empty8" 8 1 (.replicate 8 0) []
  emitCase "named/complete8" 8 1 (.replicate 8 0) (complete 8)
  -- parity two-colouring of the 4-cube: deterministic, onto, symmetric
  emitCase "named/q4-parity2" 16 2
    (.ofFn (n := 16) fun i => (Nauty.popCount i.val) % 2) (hypercube 4)
  -- SplitMix64 corpus cases
  let g0 : Random.Gen := ⟨Random.seed1⟩
  let (perm10, g1) := Random.shuffle g0 (.ofFn (n := 10) (·.val))
  emitCase "rand/petersen-relabel-seed1" 10 1 (.replicate 10 0)
    (relabelEdges perm10 petersen)
  let (mask12a, g2) := Random.gnpMask g1 12
  emitCase "rand/g12-seed1" 12 1 (.replicate 12 0) (edgesOfMask 12 mask12a)
  let (col12, _) := Random.ontoColoring g2 12 3
  emitCase "rand/g12-col3-seed1" 12 3 col12 (edgesOfMask 12 mask12a)
  let h0 : Random.Gen := ⟨Random.seed2⟩
  let (mask12b, h1) := Random.gnpMask h0 12
  emitCase "rand/g12-seed2" 12 1 (.replicate 12 0) (edgesOfMask 12 mask12b)
  let (col10, _) := Random.ontoColoring h1 10 2
  emitCase "rand/petersen-col2-seed2" 10 2 col10 petersen

end Hex.GraphIsoEmit

def main : IO Unit := Hex.GraphIsoEmit.main
