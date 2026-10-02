/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Result
public import HexGraphIso.Sparse.Iso

public section

namespace Hex.GraphIso.Sparse

variable {n k : Nat}

/-- The native sparse search result, extracted using unconditional parser
success. The proof is erased; execution retains the optimized search. -/
@[expose] def canonicalize (G : Colored n k) : CanonResult n k :=
  (Nauty.Sparse.searchResult? G).get (Nauty.Sparse.searchResult?_isSome G)

@[expose] def canon (G : Colored n k) : Colored n k := (canonicalize G).form

@[expose] def label (G : Colored n k) : Label n := (canonicalize G).label

/-- The diagnostic and total entrypoints return exactly the same result. -/
theorem searchResult?_eq (G : Colored n k) :
    Nauty.Sparse.searchResult? G = some (canonicalize G) :=
  (Option.some_get (Nauty.Sparse.searchResult?_isSome G)).symm

theorem relabel_label (G : Colored n k) : G.relabel (label G) = canon G :=
  (Nauty.Sparse.searchResult?_relabel (searchResult?_eq G)).symm

/-- The public label is parsed from the literal production output array. -/
theorem label_parse (G : Colored n k) :
    Label.ofArray? n (Nauty.Sparse.runColored G).canonlab = some (label G) := by
  have h := searchResult?_eq G
  unfold Nauty.Sparse.searchResult? at h
  cases he : Label.ofArray? n (Nauty.Sparse.runColored G).canonlab with
  | none => simp [he] at h
  | some l =>
    have heq : (⟨G.relabel l, l⟩ : CanonResult n k) = canonicalize G := by simpa [he] using h
    exact congrArg (fun r : CanonResult n k => some r.label) heq

theorem label_toArray (G : Colored n k) :
    (label G).toArray = (Nauty.Sparse.runColored G).canonlab :=
  Label.ofArray?_toArray (label_parse G)

theorem canon_iso (G : Colored n k) : Isomorphic G (canon G) := by
  rw [← relabel_label]
  exact isomorphic_relabel G (label G)

/-- The actual canonical output has the original sorted colour sequence. -/
theorem canon_colors (G : Colored n k) (i : Fin n) :
    ((canon G).coloring.cells[i]).val = (Nauty.sortedColorSeq G.toDense)[i.val]! := by
  obtain ⟨hb, he⟩ := Nauty.achieved_position_colors (Nauty.Sparse.canonlab_cellsReach G) i.val i.isLt
  have hv : (⟨(Nauty.Sparse.runColored G).canonlab[i.val]!, hb⟩ : Fin n) = (label G).get i :=
    Fin.ext (Label.ofArray?_get (label_parse G) i.val i.isLt).symm
  change (G.toDense.coloring.cells.get ⟨(Nauty.Sparse.runColored G).canonlab[i.val]!, hb⟩).val = _ at he
  rw [hv] at he
  rw [← relabel_label]
  simpa [Colored.relabel, Colored.toDense, Hex.Vector.get_eq_getElem] using he

/-- The original ordered colour classes occupy consecutive vertices. -/
@[expose] def ColorSorted (G : Colored n k) : Prop :=
  ∀ i j : Fin n, i ≤ j → G.coloring.cells[i] ≤ G.coloring.cells[j]

theorem colorSorted_canon (G : Colored n k) : ColorSorted (canon G) := by
  intro i j hij
  rw [Fin.le_def, canon_colors, canon_colors]
  rcases Nat.eq_or_lt_of_le (Fin.le_def.mp hij) with he | hlt
  · rw [he]
    exact Nat.le_refl _
  · have hp := Nauty.pairwise_sortedColorSeq G.toDense
    rw [List.pairwise_iff_getElem] at hp
    have hs := Nauty.length_sortedColorSeq G.toDense
    have hi : i.val < (Nauty.sortedColorSeq G.toDense).length := by omega
    have hj : j.val < (Nauty.sortedColorSeq G.toDense).length := by omega
    rw [getElem!_pos (Nauty.sortedColorSeq G.toDense) i.val hi,
      getElem!_pos (Nauty.sortedColorSeq G.toDense) j.val hj]
    exact hp i.val j.val hi hj hlt

/-- Compose the native canonical labels when the two output forms agree. -/
@[expose] def findIso (G H : Colored n k) : Option (Perm n) :=
  if canon G = canon H then
    some (((label H).toPerm.inv).comp ((label G).toPerm))
  else none

@[expose] def isIso (G H : Colored n k) : Bool := (findIso G H).isSome

theorem findIso_sound {G H : Colored n k} {p : Perm n}
    (h : findIso G H = some p) : IsIso G H p := by
  rw [findIso] at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    have h1 : IsIso G (canon G) (label G).toPerm := by
      rw [← relabel_label G]
      exact isIso_relabel ..
    have h2 : IsIso H (canon G) (label H).toPerm := by
      rw [hc, ← relabel_label H]
      exact isIso_relabel ..
    exact h1.trans h2.symm
  · simp at h

end Hex.GraphIso.Sparse
