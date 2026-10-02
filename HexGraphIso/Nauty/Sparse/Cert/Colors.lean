/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Canonical

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Read a colour without requiring an inhabitant of the empty colour type. -/
@[expose] def rawColor (G : GraphIso.Sparse.Colored n k) (v : Nat) : Nat :=
  if h : v < n then (G.coloring.cells[(⟨v, h⟩ : Fin n)]).val else 0

/-- Expected canonical colours, in the actual stable bucket order.
Construction takes one native colour-bucket pass and a label scan. -/
@[expose] def colorSeq (G : GraphIso.Sparse.Colored n k) : List Nat :=
  (initialPartitionWith n k G.coloring.cells.toArray Fin.val).1.toList.map (rawColor G)

/-- The colours of a checked label in its position-to-vertex convention. -/
@[expose] def labelColors (G : GraphIso.Sparse.Colored n k) (l : Label n) : List Nat :=
  List.ofFn fun i => (G.coloring.cells[l.get i]).val

theorem colorSeq_length (G : GraphIso.Sparse.Colored n k) : (colorSeq G).length = n := by
  simp only [colorSeq, List.length_map, Array.length_toList, initialPartition_size]

/-- The executed initializer's colour sequence has the proved canonical
colour at every position. The dense projection appears only in this proof. -/
theorem colorSeq_get (G : GraphIso.Sparse.Colored n k) (i : Fin n) :
    (colorSeq G)[i.val]! = ((GraphIso.Sparse.canon G).coloring.cells[i]).val := by
  have hpos := achieved_position_colors (cellsReach_initial G.toDense) i.val i.isLt
  rw [← initialPartition_eq G] at hpos
  obtain ⟨hv, he⟩ := hpos
  rw [GraphIso.Sparse.canon_colors]
  have hi : i.val < (colorSeq G).length := by rw [colorSeq_length]; exact i.isLt
  rw [getElem!_pos (colorSeq G) i.val hi]
  simp only [colorSeq, List.getElem_map, Array.getElem_toList]
  rw [← getElem!_pos (initialPartitionWith n k G.coloring.cells.toArray Fin.val).1
    i.val (by rw [initialPartition_size]; exact i.isLt)]
  rw [rawColor, dite_eq_left hv]
  exact he

theorem labelColors_get (G : GraphIso.Sparse.Colored n k) (l : Label n) (i : Fin n) :
    (labelColors G l)[i.val]! = ((G.relabel l).coloring.cells[i]).val := by
  rw [getElem!_pos _ _ (by simp [labelColors])]
  simp only [labelColors, List.getElem_ofFn]
  simp [GraphIso.Sparse.Colored.relabel]

/-- The actual production label passes the canonical-colour check. -/
theorem labelColors_eq (G : GraphIso.Sparse.Colored n k) :
    labelColors G (GraphIso.Sparse.label G) = colorSeq G := by
  apply List.ext_getElem
  · simp [labelColors, colorSeq_length]
  · intro i hi hj
    have hin : i < n := by simpa [labelColors] using hi
    have he : (labelColors G (GraphIso.Sparse.label G))[i]! = (colorSeq G)[i]! := by
      rw [labelColors_get G _ ⟨i, hin⟩, colorSeq_get G ⟨i, hin⟩,
        GraphIso.Sparse.relabel_label]
    simpa only [getElem!_pos (labelColors G (GraphIso.Sparse.label G)) i hi,
      getElem!_pos (colorSeq G) i hj] using he

end Hex.GraphIso.Nauty.Sparse
