/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Achieved
public import HexGraphIso.Nauty.CanonForm

public section

/-!
Transcription labelling invariants for the verified search refinement
programme (layer-two bridge `isPerm_of_trace` and the
`colorSortedCheck` residual of `certifyCanon?_isSome`).

The single simulation-relation clause on the imperative search state
is that the labelling stays cell-content-reachable from the initial
labelling relative to the initial partition: `CellsReach G lab` below.
`breakout` individualizes a vertex to the front of its cell and
`refine` splits cells into finer cells, and both are permutations
within the initial colour classes, so every leaf the search reaches
— in particular `canonlab` — satisfies it. From that one clause the
two transcription-side residuals follow immediately through the
existing achievement lemmas: `achieved_perm_range` turns it into
permutation-ness (`canonlab` is a bijection of `Fin n`, the label
well-formedness `isPerm_of_trace` consumes) and
`achieved_position_colors` turns it into `colorSortedCheck`.

This file proves those two reductions in full; the remaining work is
the quartet induction establishing the clause for the transcribed
`canonlab` (`canonlab_cellsReach`), which is the shared B2 simulation
clause of the layer-three programme.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The simulation-relation clause: `lab` is cell-content-reachable
from the initial labelling relative to the initial partition. Every
labelling the search visits satisfies this (individualization and
refinement permute within the initial colour classes). -/
@[expose] def CellsReach (G : Colored n k) (lab : Array Nat) : Prop :=
  cellsPerm (initPtn n (n + 2) (initialPartition G).2) 1
    (initialPartition G).1 lab

/-- The initial labelling reaches itself. -/
theorem cellsReach_initial (G : Colored n k) :
    CellsReach G (initialPartition G).1 := by
  intro a len _
  exact List.Perm.refl _

/-- A reached labelling of full size is a permutation of `[0, n)`: the
permutation-ness `isPerm_of_trace` needs for label well-formedness. -/
theorem isPerm_of_cellsReach {G : Colored n k} {lab : Array Nat}
    (hsz : lab.size = n) (hn0 : 0 < n) (h : CellsReach G lab) :
    lab.toList.Perm (List.range n) :=
  achieved_perm_range hsz hn0 h

/-- Every entry of a reached labelling is a valid vertex. -/
theorem cellsReach_lt {G : Colored n k} {lab : Array Nat}
    (h : CellsReach G lab) (i : Nat) (hi : i < n) : lab[i]! < n :=
  (achieved_position_colors (G := G) (llab := lab) h i hi).choose

/-- A reached labelling passes `colorSortedCheck`: the transcription
output's colours are nondecreasing, the `certifyCanon?_isSome`
residual. The colour at each position matches `sortedColorSeq`
(`achieved_position_colors`), which is sorted
(`pairwise_sortedColorSeq`). -/
theorem colorSortedCheck_of_cellsReach {G : Colored n k}
    {lab : Array Nat} (hsz : lab.size = n) (h : CellsReach G lab) :
    colorSortedCheck G lab = true := by
  have hcols := achieved_position_colors (G := G) (llab := lab) h
  rw [colorSortedCheck, List.all_eq_true]
  intro i hi
  have hin := List.mem_range.mp hi
  refine (Bool.or_eq_true_iff).mpr ?_
  rcases Decidable.em (i + 1 = n) with he | he
  · exact Or.inl (by simpa using he)
  · right
    refine decide_eq_true ?_
    obtain ⟨hv1, hc1⟩ := hcols i hin
    obtain ⟨hv2, hc2⟩ := hcols (i + 1) (by omega)
    have hl1 : labColor G lab i = (sortedColorSeq G)[i]! := by
      rw [labColor, dite_eq_left ⟨by omega, hv1⟩] <;> try (rw [hsz])
      exact hc1
    have hl2 : labColor G lab (i + 1) = (sortedColorSeq G)[i + 1]! := by
      rw [labColor, dite_eq_left ⟨by omega, hv2⟩] <;> try (rw [hsz])
      exact hc2
    rw [hl1, hl2]
    have hp := pairwise_sortedColorSeq G
    rw [List.pairwise_iff_getElem] at hp
    have hlen := length_sortedColorSeq G
    have := hp i (i + 1) (by omega) (by omega) (by omega)
    rw [getElem!_pos _ _ (by omega), getElem!_pos _ _ (by omega)]
    exact this

end Hex.GraphIso.Nauty
