/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso
import HexGraphIso.TestGraphs

/-!
Shared inputs for the `graph_iso` fresh-module probes
(SPEC/hex-graph-iso § Benchmarks, "the tactic has fresh-module
probes"). Each probe case imports this module and nothing else beyond
it, so a fresh build of one probe measures reification, compiled
search, literal elaboration, and kernel replay for exactly one goal
against the `Baseline` module's matched import cost.

The random instances are the recorded corpus pair of
`HexGraphIso.TestGraphs`, shared with the `graph_iso` regression
tests: the `G(12, 1/2)` graph of the first SplitMix64 corpus seed, its
image under the recorded Fisher-Yates relabelling, and the
`G(12, 1/2)` graph of the second seed.

The coloured pair is the Petersen graph with an adjacent, respectively
non-adjacent, vertex pair marked with colour zero, at `n = 10`.

The CFI pair is probe-local: the Cai-Fürer-Immerman construction over
`K4`, untwisted against twisted, on `4 * (4 + 6) = 40` vertices. Each
degree-3 base vertex becomes a gadget with four middle vertices (the
even-parity subsets of its three edge ports) and an `a`/`b` port pair
per incident base edge; ports join middle vertices containing them,
`a`–`a` and `b`–`b` across each base edge, and the twist crosses
exactly one base edge. The two graphs agree on every refinement
invariant and differ globally, the classical hard negative for
individualization-refinement.
-/

namespace Hex.GraphIso.ProofProbe

open Hex Hex.GraphIso

/-! # The recorded corpus pair, shared with the `graph_iso` regression
tests -/

export Hex.GraphIso.TestGraphs (g12 g12relabelled g12b)

def petersen : Colored 10 1 :=
  { graph := Graph.ofEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
       (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]
    coloring := Coloring.trivial 10 }

def markPair (a b : Fin 10) : Coloring 10 2 :=
  (Coloring.ofVector? (Hex.Vector.ofFn' fun i =>
    if i = a ∨ i = b then 0 else 1)).getD (Coloring.mod 10 2)

def edgeMarkA : Colored 10 2 := ⟨petersen.graph, markPair 0 1⟩
def edgeMarkB : Colored 10 2 := ⟨petersen.graph, markPair 2 3⟩
def nonedgeMark : Colored 10 2 := ⟨petersen.graph, markPair 0 2⟩

/-! # The CFI pair over `K4`

Vertex numbering: base vertex `v ∈ [0, 4)` owns the block
`[10v, 10v + 10)`. Within a block, positions `0..3` are the four
even-parity middle vertices (subsets of the vertex's three incident
base edges, indexed by the two low bits of the subset's rank), and
positions `4 + 2e` and `4 + 2e + 1` are the `a` and `b` ports of the
vertex's `e`-th incident base edge, `e ∈ [0, 3)`, incident edges in
lexicographic base-edge order. -/

/-- The six edges of `K4` in lexicographic order. -/
def k4Edges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The index of base edge `(u, v)` in the incident-edge list of `u`. -/
def portIdx (u other : Nat) : Nat :=
  ((k4Edges.filter fun e => e.1 == u || e.2 == u).findIdx
    fun e => (e.1 == u && e.2 == other) || (e.1 == other && e.2 == u))

/-- The `k`-th even-parity subset of three ports: rank `k ∈ [0, 4)`
maps to the subset with low bits chosen by `k` and top bit fixing the
parity. -/
def middleMask (k : Nat) : Nat :=
  (k % 2) + 2 * ((k / 2) % 2) + 4 * (((k % 2) + ((k / 2) % 2)) % 2)

/-- The adjacency of the (possibly twisted) CFI graph over `K4` on an
ordered pair `x < y`: the twist crosses the `a`/`b` connection of the
lexicographically first base edge `(0, 1)`. The public adjacency wraps
this in an explicit diagonal guard and min/max normalization, so
symmetry and looplessness are by construction. -/
def cfiAdjCore (twist : Bool) (x y : Nat) : Bool := Id.run do
  let vx := x / 10; let px := x % 10
  let vy := y / 10; let py := y % 10
  if vx == vy then
    -- middle-to-port inside one gadget: port `e` sits in middle `k`
    -- iff bit `e` of the middle's subset mask is set; the `a` port for
    -- a set bit, the `b` port for a clear bit.
    let (m, p) := if px < 4 then (px, py) else (py, px)
    if m < 4 && 4 ≤ p then
      let e := (p - 4) / 2
      let isA := (p - 4) % 2 == 0
      return (middleMask m).testBit e == isA
    return false
  -- across a base edge: `a`–`a` and `b`–`b`, crossed on the twisted edge
  if px < 4 || py < 4 then return false
  let lo := Nat.min vx vy; let hi := Nat.max vx vy
  unless k4Edges.contains (lo, hi) do return false
  let ex := portIdx vx (if vx == lo then hi else lo)
  let ey := portIdx vy (if vy == lo then hi else lo)
  unless (px - 4) / 2 == ex && (py - 4) / 2 == ey do return false
  let sameKind := (px - 4) % 2 == (py - 4) % 2
  if twist && lo == 0 && hi == 1 then return !sameKind
  return sameKind

def cfi (twist : Bool) : Colored 40 1 :=
  { graph := Graph.ofAdj
      (fun i j => if i == j then false else
        cfiAdjCore twist (Nat.min i.val j.val) (Nat.max i.val j.val))
      (fun i j => by rcases Decidable.em (i = j) with h | h <;>
        simp [h, Nat.min_comm, Nat.max_comm, BEq.comm])
      (fun i => by simp)
    coloring := Coloring.trivial 40 }

end Hex.GraphIso.ProofProbe
