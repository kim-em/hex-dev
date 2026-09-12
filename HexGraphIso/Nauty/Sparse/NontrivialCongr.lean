/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountPassCongr
public import HexGraphIso.Nauty.Sparse.NontrivialEquiv
public import HexGraphIso.Nauty.Sparse.RefineState
import all HexGraphIso.Nauty.Spec.SpecIso

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Admissible scratch reuse cannot change the literal label array of the
complete native nontrivial splitter, including first-touch clearing and
the ordered touched-cell fold. -/
theorem splitNontrivial_lab (G : Hex.SparseGraph n) (level split len : Nat)
    (s t : RefineSt n) (hs : s.Valid level) (ht : t.Valid level)
    (hl : t.lab = s.lab) (he : t.ptn = s.ptn)
    (hc : IsCell s.ptn level split len) (hb : split + len ≤ n) :
    (splitNontrivial (.ofGraph G) level split s).lab =
      (splitNontrivial (.ofGraph G) level split t).lab := by
  have hlen := hc.1
  have hi := ht.index
  rw [he] at hi
  have hse : s.cellend[split]! + 1 = split + len := by
    have := hs.index.ends_eq split len hc hb (by omega)
    omega
  have hte : t.cellend[split]! + 1 = split + len := by
    have := hi.ends_eq split len hc hb (by omega)
    omega
  have hid : (renamingOf (Perm.id n)).toFun = id := by
    funext v
    simp [renamingOf]
  have hp : cellsPerm s.ptn level t.lab (s.lab.map (renamingOf (Perm.id n)).toFun) := by
    rw [hid, Array.map_id, hl]
    exact cellsPerm_refl _ _ _
  have hleft := splitNontrivial_trace G level split len s hs.lab hs.size hs.closed hs.index hc hb
    ⟨hs.scratch.marks_size, hs.scratch.marks_le⟩ hs.scratch.hits_size
  have hright := splitNontrivial_trace G level split len t ht.lab ht.size ht.closed ht.index
    (he ▸ hc) hb ⟨ht.scratch.marks_size, ht.scratch.marks_le⟩ ht.scratch.hits_size
  have hscan := count_neighbors_map G G (Perm.id n) (by intro u v; simp)
    s t s.ptn level split len hs.index hi hs.lab ht.lab hs.size hs.closed hc hb hp
    ⟨hs.scratch.marks_size, hs.scratch.marks_le⟩ hs.scratch.hits_size
    ⟨ht.scratch.marks_size, ht.scratch.marks_le⟩ ht.scratch.hits_size
  dsimp only at hleft hright hscan
  rw [hl] at hright hscan
  rw [hse] at hleft
  rw [hte, ← hscan.1] at hright
  apply hleft.lab_eq hright hs.lab hs.size rfl he hs.index
  simpa only [RefineSt.hash, hl] using ht.index

end Hex.GraphIso.Nauty.Sparse
