/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Tactic
public import HexGraphIso.Random
public meta import HexGraphIso.Tactic
public meta import HexGraphIso.Random

/-!
Regression tests for the Mathlib-free `graph_iso` tactic: positive and
negative goals, coloured goals, the limit syntax, and the promised
diagnostics. The kernel replays every closing proof; every failure case
asserts its message and leaves the goal unchanged.
-/

namespace Hex.GraphIso.TacticTests

open Hex Hex.GraphIso

def p3 : Colored 3 1 :=
  { graph := Graph.ofEdges [(0, 1), (1, 2)]
    coloring := Coloring.trivial 3 }

def p3' : Colored 3 1 :=
  { graph := Graph.ofEdges [(0, 1), (0, 2)]
    coloring := Coloring.trivial 3 }

def k3 : Colored 3 1 :=
  { graph := Graph.ofEdges [(0, 1), (1, 2), (0, 2)]
    coloring := Coloring.trivial 3 }

example : Isomorphic p3 p3' := by graph_iso
example : ¬ Isomorphic p3 k3 := by graph_iso
example : Isomorphic p3 p3' := by
  graph_iso (maxNodes := 200000) (maxCheckerSteps := 10000000)
example : Isomorphic p3 p3' := by
  graph_iso (maxCheckerSteps := 10000000) (maxCertNodes := 200000)

/-- error: graph_iso: the graphs are not isomorphic; the positive goal is not provable -/
#guard_msgs in
example : Isomorphic p3 k3 := by graph_iso

/-- error: graph_iso: the graphs are isomorphic; the negative goal is not provable -/
#guard_msgs in
example : ¬ Isomorphic p3 p3' := by graph_iso

/-- error: graph_iso: search exhausted: visited 6 nodes but maxNodes := 0 -/
#guard_msgs in
example : Isomorphic p3 p3' := by graph_iso (maxNodes := 0)

/-- error: graph_iso: replay exhausted: checking the transporter takes 12 steps but maxCheckerSteps := 0 -/
#guard_msgs in
example : Isomorphic p3 p3' := by graph_iso (maxCheckerSteps := 0)

/-- error: graph_iso: duplicate limit `maxNodes` -/
#guard_msgs in
example : Isomorphic p3 p3' := by graph_iso (maxNodes := 1) (maxNodes := 2)

/-- error: graph_iso: unknown limit `maxFoo` -/
#guard_msgs in
example : Isomorphic p3 p3' := by graph_iso (maxFoo := 1)

/-!
The Petersen pair at `n = 10`: two genuinely different presentations of
the same graph, and a cubic ten-vertex non-example.
-/

def petersen : Colored 10 1 :=
  { graph := Graph.ofEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
       (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]
    coloring := Coloring.trivial 10 }

def kneser52 : Colored 10 1 :=
  { graph := Graph.ofEdges
      [(0, 7), (0, 8), (0, 9), (1, 5), (1, 6), (1, 9), (2, 4), (2, 6), (2, 8),
       (3, 4), (3, 5), (3, 7), (4, 9), (5, 8), (6, 7)]
    coloring := Coloring.trivial 10 }

example : Isomorphic petersen kneser52 := by graph_iso

/-- The pentagonal prism: also cubic on ten vertices, so degree
refinement alone cannot separate it from the Petersen graph; the
negative goal replays the verified pairwise decision in the kernel. -/
def prism5 : Colored 10 1 :=
  { graph := Graph.ofEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
       (5, 6), (6, 7), (7, 8), (8, 9), (5, 9),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]
    coloring := Coloring.trivial 10 }

set_option maxRecDepth 100000 in
example : ¬ Isomorphic petersen prism5 := by graph_iso

/-!
Coloured goals at `n = 6`: ordered colours constrain isomorphisms.
Colour `0` marks an adjacent pair of the six-cycle in the first two
colourings and a non-adjacent pair in the third.
-/

def c6 : Graph 6 :=
  Graph.ofEdges [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]

def modFallback : Coloring 6 2 := Coloring.mod 6 2

def edgeMarkA : Colored 6 2 :=
  ⟨c6, (Coloring.ofVector? #v[(0 : Fin 2), 0, 1, 1, 1, 1]).getD modFallback⟩

def edgeMarkB : Colored 6 2 :=
  ⟨c6, (Coloring.ofVector? #v[(1 : Fin 2), 1, 1, 0, 0, 1]).getD modFallback⟩

def nonedgeMark : Colored 6 2 :=
  ⟨c6, (Coloring.ofVector? #v[(0 : Fin 2), 1, 1, 0, 1, 1]).getD modFallback⟩

example : Isomorphic edgeMarkA edgeMarkB := by graph_iso
example : ¬ Isomorphic edgeMarkA nonedgeMark := by graph_iso

/-!
The positive random `n = 12` pair related by a recorded relabelling: the
`G(12, 1/2)` graph of the first corpus seed against its image under the
Fisher-Yates relabelling drawn from the continuation of the same stream.
-/

def pairIdx (i j : Nat) : Nat :=
  -- lexicographic pair index of `(i, j)`, `i < j`, over 12 vertices
  i * 12 - i * (i + 1) / 2 + (j - i - 1)

/-- The recorded pair bitmask of `Random.gnpMask ⟨Random.seed1⟩ 12`, kept
literal so the kernel replay does not evaluate the UInt64 stream; the
`#guard` below ties it to the generator. -/
def mask12 : Nat := 48283412393242304007

/-- The recorded Fisher-Yates relabelling drawn from the continuation of
the same stream. -/
def perm12 : Array Nat := #[11, 10, 1, 7, 3, 5, 4, 2, 9, 6, 8, 0]

#guard mask12 == (Random.gnpMask ⟨Random.seed1⟩ 12).1
#guard perm12 ==
  (Random.shuffle (Random.gnpMask ⟨Random.seed1⟩ 12).2
    (.ofFn (n := 12) (·.val))).1

def g12 : Colored 12 1 :=
  { graph := Graph.ofAdj
      (fun i j => if i == j then false else
        mask12.testBit (pairIdx (Nat.min i.val j.val) (Nat.max i.val j.val)))
      (fun i j => by rcases Decidable.em (i = j) with h | h <;>
        simp [h, Nat.min_comm, Nat.max_comm, BEq.comm])
      (fun i => by simp)
    coloring := Coloring.trivial 12 }

def g12relabelled : Colored 12 1 :=
  { graph := Graph.ofAdj
      (fun i j => if i == j then false else
        mask12.testBit (pairIdx
          (Nat.min perm12[i.val]! perm12[j.val]!)
          (Nat.max perm12[i.val]! perm12[j.val]!)))
      (fun i j => by rcases Decidable.em (i = j) with h | h <;>
        simp [h, Nat.min_comm, Nat.max_comm, BEq.comm])
      (fun i => by simp)
    coloring := Coloring.trivial 12 }

example : Isomorphic g12 g12relabelled := by graph_iso

/-- The recorded pair bitmask of the second corpus seed, giving the
negative pair from the two recorded `G(12, 1/2)` seeds. -/
def mask12b : Nat := 61032603037995048816

#guard mask12b == (Random.gnpMask ⟨Random.seed2⟩ 12).1

def g12b : Colored 12 1 :=
  { graph := Graph.ofAdj
      (fun i j => if i == j then false else
        mask12b.testBit (pairIdx (Nat.min i.val j.val) (Nat.max i.val j.val)))
      (fun i j => by rcases Decidable.em (i = j) with h | h <;>
        simp [h, Nat.min_comm, Nat.max_comm, BEq.comm])
      (fun i => by simp)
    coloring := Coloring.trivial 12 }

set_option maxRecDepth 400000 in
example : ¬ Isomorphic g12 g12b := by graph_iso

end Hex.GraphIso.TacticTests
