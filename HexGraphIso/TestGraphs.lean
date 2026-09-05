/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Random
public meta import HexGraphIso.Random

@[expose] public section

/-!
The recorded random `G(12, 1/2)` corpus pair shared by the `graph_iso`
regression tests and the fresh-module probes: the graph of the first
SplitMix64 corpus seed, its image under the recorded Fisher-Yates
relabelling, and the graph of the second seed. The masks and the
relabelling are kept literal so a kernel replay does not evaluate the
`UInt64` stream. The `#guard`s check the literals against the
generators.
-/

namespace Hex.GraphIso.TestGraphs

open Hex Hex.GraphIso

/-- Lexicographic pair index of `(i, j)`, `i < j`, over 12 vertices. -/
def pairIdx (i j : Nat) : Nat :=
  i * 12 - i * (i + 1) / 2 + (j - i - 1)

/-- The recorded pair bitmask of `Random.gnpMask ⟨Random.seed1⟩ 12`. -/
def mask12 : Nat := 48283412393242304007

/-- The recorded Fisher-Yates relabelling drawn from the continuation
of the first seed's stream. -/
def perm12 : Array Nat := #[11, 10, 1, 7, 3, 5, 4, 2, 9, 6, 8, 0]

/-- The recorded pair bitmask of `Random.gnpMask ⟨Random.seed2⟩ 12`. -/
def mask12b : Nat := 61032603037995048816

#guard mask12 == (Random.gnpMask ⟨Random.seed1⟩ 12).1
#guard perm12 ==
  (Random.shuffle (Random.gnpMask ⟨Random.seed1⟩ 12).2
    (.ofFn (n := 12) (·.val))).1
#guard mask12b == (Random.gnpMask ⟨Random.seed2⟩ 12).1

/-- The `G(12, 1/2)` graph of the first corpus seed. -/
def g12 : Colored 12 1 :=
  { graph := Graph.ofAdj
      (fun i j => if i == j then false else
        mask12.testBit (pairIdx (Nat.min i.val j.val) (Nat.max i.val j.val)))
      (fun i j => by rcases Decidable.em (i = j) with h | h <;>
        simp [h, Nat.min_comm, Nat.max_comm, BEq.comm])
      (fun i => by simp)
    coloring := Coloring.trivial 12 }

/-- The image of `g12` under the recorded relabelling. -/
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

/-- The `G(12, 1/2)` graph of the second corpus seed. -/
def g12b : Colored 12 1 :=
  { graph := Graph.ofAdj
      (fun i j => if i == j then false else
        mask12b.testBit (pairIdx (Nat.min i.val j.val) (Nat.max i.val j.val)))
      (fun i j => by rcases Decidable.em (i = j) with h | h <;>
        simp [h, Nat.min_comm, Nat.max_comm, BEq.comm])
      (fun i => by simp)
    coloring := Coloring.trivial 12 }

end Hex.GraphIso.TestGraphs
