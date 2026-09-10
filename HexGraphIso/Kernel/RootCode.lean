/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Kernel.CheckKey
public import HexGraphIso.Nauty.Spec.SpecIso

public section

/-!
The root separator: the head code of the specification key, computed
by a single refinement of the initial partition and no tree search.
Isomorphic graphs have equal specification keys, so a difference in
that one code refutes isomorphism at the cost of one refinement per
graph, far below the cost of a certificate replay.

`Kernel.rootCode` runs the refinement over the packed state of
`HexGraphIso.Kernel.CheckKey`, on the adjacency rows packed as one
number. `Kernel.rootCode_eq` identifies it with the head of
`Nauty.canonSpecKey` through the list and `Array` layers, and
`Kernel.not_isomorphic_of_rootCode` is the theorem the tactic applies.
-/

namespace Hex.GraphIso

open Nauty

variable {n k : Nat}

/-- The root refinement code over the packed-set state of the
specification. -/
def rootCodeA (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : Nat :=
  (refine { g := g } 1 lab0 (initPtn n (n + 2) cellEnds)
    (initActive n cellEnds) cellEnds.length).longcode

/-- Above one vertex the specification key's head code is the code of
the root refinement. -/
private theorem rootCodeA_eq (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) (h2 : 2 ≤ n) :
    (canonSpec n g lab0 cellEnds).codes.head? =
      some (rootCodeA n g lab0 cellEnds) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [canonSpec, show ((m + 2) == 0) = false by simp]
  simp only [Bool.false_eq_true, ite_false]
  obtain ⟨rest, hrest⟩ := specNode_codes_head { g := g } 100 (m + 1) 1 lab0
    (initPtn (m + 2) (m + 2 + 2) cellEnds) (initActive (m + 2) cellEnds)
    cellEnds.length
  rw [hrest, List.head?_cons, rootCodeA]

/-- The root refinement code over list state. -/
private def rootCodeL (n : Nat) (g lab0 : List Nat) (cellEnds : List Nat) : Nat :=
  (refineL ⟨n, g⟩ 1 lab0 (initPtn n (n + 2) cellEnds).toList
    (initActive n cellEnds).toNat cellEnds.length).longcode

private theorem rootCodeL_eq (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) :
    rootCodeL n (g.toList.map VSet.toNat) lab0.toList cellEnds =
      rootCodeA n g lab0 cellEnds :=
  congrArg RefineStL.longcode (refineL_eq { g := g } 1 lab0 _ _ _)

namespace Kernel

/-- The specification key's head code of a coloured graph whose
adjacency rows are packed as the one number `rows`: a single
refinement of the initial partition. -/
@[expose] def rootCode (G : Colored n k) (rows : Nat) : Nat :=
  (refineP (initCtx n rows) 1 (initLabP G) (initPtnP G)
    (initActive n (initialPartition G).2).toNat
    (initialPartition G).2.length).longcode

private theorem rootCode_eq_L (G : Colored n k) (flat : List Bool) (hn : 2 ≤ n) :
    rootCode G (packRows n flat) =
      rootCodeL n (flatRows n flat).toList (initialPartition G).1.toList
        (initialPartition G).2 := by
  rw [rootCodeL, rootCode, packRows_eq]
  obtain ⟨hctx, hlab, hptn⟩ := initRep G flat (by omega)
  have hrs := refineP_eq hctx (level := 1)
    (by show (1 : Nat) < 2 ^ initW n; have := initW_lt n; omega) hlab hptn
    (initActive n (initialPartition G).2).toNat (initialPartition G).2.length
  rw [hrs.longcode]

/-- Above one vertex the root code is the head of the specification
key. -/
theorem rootCode_eq (G : Colored n k) (hn : 2 ≤ n) :
    (canonSpecKey G).codes.head? =
      some (rootCode G (packRows n G.graph.adjMatrix.data.toList)) := by
  rw [rootCode_eq_L G _ hn, canonSpecKey, ← rowsOfFlat_eq_rowsOf G,
    ← toNat_rowsOfFlat, rootCodeL_eq, rootCodeA_eq _ _ _ _ hn]

/-- The compiled-side root-code test: whether the root route separates
this pair. Evaluated at elaboration time over the `Array` rows, so the
route decision costs one refinement per graph and no kernel work. -/
def rootSeparates (G H : Colored n k) : Bool :=
  decide (2 ≤ n) &&
  !Nat.beq (rootCodeA n (rowsOf G) (initialPartition G).1 (initialPartition G).2)
    (rootCodeA n (rowsOf H) (initialPartition H).1 (initialPartition H).2)

/-- The root codes of two coloured graphs disagree: the cheapest
kernel check of the negative route, one refinement per graph. -/
@[expose] def rootDiff (G H : Colored n k) (NA NB : Nat) : Bool :=
  decide (2 ≤ n) && !Nat.beq (rootCode G NA) (rootCode H NB)

/-- Equalities identifying each graph's packed rows, plus a root-code
disagreement, prove non-isomorphism. -/
theorem not_isomorphic_of_rootCode {G H : Colored n k} {NA NB : Nat}
    (hA : packRows n G.graph.adjMatrix.data.toList = NA)
    (hB : packRows n H.graph.adjMatrix.data.toList = NB)
    (h : rootDiff G H NA NB = true) : ¬Isomorphic G H := by
  subst hA hB
  rw [rootDiff, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, h⟩ := h
  rw [Bool.not_eq_true', beq_eq_beq, beq_eq_false_iff_ne] at h
  intro hiso
  refine h (Option.some.inj ((rootCode_eq G hn).symm.trans ?_))
  rw [canonSpecKey_eq_of_isomorphic hiso, rootCode_eq H hn]

end Kernel

end Hex.GraphIso
