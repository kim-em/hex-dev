/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexGraphIso

/-!
The extended graph-isomorphism conformance campaign, streamed to the
external nauty oracle rather than committed: all 32,768 labelled graphs
at `n = 6`, larger deterministic pseudo-random cases from the SplitMix64
corpus seeds, and the deterministic hard families. Run locally or on the
scheduled profile as

```
lake exe hexgraphiso_emit_campaign | python3 scripts/oracle/graphiso_nauty.py
```

Records carry the public `canonicalize` answer (label and canonical
upper-triangle bits) with the node count from the transcribed search,
as in `HexGraphIso.EmitFixtures`, so the campaign pins the public
surface against real nauty. Only failures are retained as replay
records (the oracle reports the failing case identifier).
-/

namespace Hex.GraphIsoCampaign

open Hex.Conformance.Emit
open Hex.GraphIso
open Hex.GraphIso.Nauty

private def lib : String := "HexGraphIso"

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

/-- Canonicalize through the public API and emit one campaign record:
the label and upper-triangle bits are read off public `canonicalize`,
the node count off the transcribed search. -/
private def emitCase (case : String) (n k : Nat) (colors : Array Nat)
    (edges : List (Nat × Nat)) : IO Unit := do
  let some G := coloredOf? n k colors edges
    | throw (IO.userError s!"emit: case {case} rejected by the builders")
  let res := canonicalize G
  let r := Nauty.runColored G
  let mut sizes : Array Nat := .replicate k 0
  for v in [0 : n] do
    sizes := sizes.set! colors[v]! (sizes[colors[v]!]! + 1)
  emitGraphIsoFixture lib case n k
    (colors.toList.map Int.ofNat)
    (edges.map fun (a, b) =>
      (Int.ofNat (Nat.min a b), Int.ofNat (Nat.max a b)))
    ((List.finRange n).map fun i => Int.ofNat (res.label.get i).val)
    (triBits res.form)
    (sizes.toList.map Int.ofNat)
    r.numnodes

private def emitGraph (case : String) {n : Nat} (G : Hex.Graph n) : IO Unit := do
  let mut edges : List (Nat × Nat) := []
  for i in [0 : n] do
    for j in [i + 1 : n] do
      if h : i < n ∧ j < n then
        if G.adj ⟨i, h.1⟩ ⟨j, h.2⟩ then
          edges := (i, j) :: edges
  emitCase case n (if n == 0 then 0 else 1) (.replicate n 0) edges.reverse

def main : IO Unit := do
  -- every labelled graph on six vertices
  for mask in [0 : 2 ^ 15] do
    emitCase s!"campaign/n6/m{mask}" 6 1 (.replicate 6 0) (edgesOfMask 6 mask)
  -- deterministic hard families
  emitGraph "campaign/paley13" (Families.paley 13)
  emitGraph "campaign/paley17" (Families.paley 17)
  emitGraph "campaign/hypercube4" (Families.hypercube 4)
  emitGraph "campaign/hypercube5" (Families.hypercube 5)
  emitGraph "campaign/grid6" (Families.grid 6 6)
  emitGraph "campaign/johnson72" (Families.johnson 7 2)
  emitGraph "campaign/kneser72" (Families.kneser 7 2)
  emitGraph "campaign/triangular8" (Families.triangular 8)
  emitGraph "campaign/multipartite" (Families.completeMultipartite [3, 4, 5])
  emitGraph "campaign/copies5c5" (Families.copies 5 (Families.cycle 5))
  emitGraph "campaign/circulant17" (Families.circulant 17 [1, 2, 4, 8])
  -- pseudo-random corpus: G(n, 1/2) for both seeds at growing sizes
  let mut g : Random.Gen := ⟨Random.seed1⟩
  for n in [12, 14, 16] do
    let (mask, g') := Random.gnpMask g n
    g := g'
    emitCase s!"campaign/g{n}-seed1" n 1 (.replicate n 0) (edgesOfMask n mask)
    let (cols, g'') := Random.ontoColoring g n 3
    g := g''
    emitCase s!"campaign/g{n}-col3-seed1" n 3 cols (edgesOfMask n mask)
  let mut h : Random.Gen := ⟨Random.seed2⟩
  for n in [12, 14, 16] do
    let (mask, h') := Random.gnpMask h n
    h := h'
    emitCase s!"campaign/g{n}-seed2" n 1 (.replicate n 0) (edgesOfMask n mask)

end Hex.GraphIsoCampaign

def main : IO Unit := Hex.GraphIsoCampaign.main
