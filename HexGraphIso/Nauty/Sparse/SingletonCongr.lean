/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SingletonTrace
public import HexGraphIso.Nauty.Sparse.PassCongr
public import HexGraphIso.Nauty.Sparse.RefineState
import all HexGraphIso.Nauty.Spec.SpecIso

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Reusing admissible scratch cannot change the literal label array of
the executed singleton splitter. The retained marks and generations may
differ; the observed predicate is fixed by the native graph row. -/
theorem splitSingleton_lab (G : Hex.SparseGraph n) (level split : Nat)
    (s t : RefineSt n) (hs : s.Valid level) (ht : t.Valid level)
    (hl : t.lab = s.lab) (he : t.ptn = s.ptn) (hb : split < n) :
    (splitSingleton (.ofGraph G) level split s).lab =
      (splitSingleton (.ofGraph G) level split t).lab := by
  have hroot := perm_bound hs.lab hb
  have hid : (renamingOf (Perm.id n)).toFun = id := by
    funext v
    simp [renamingOf]
  have hp : cellsPerm s.ptn level t.lab (s.lab.map (renamingOf (Perm.id n)).toFun) := by
    rw [hid, Array.map_id, hl]
    exact cellsPerm_refl _ _ _
  have hi := ht.index
  rw [he] at hi
  have hleft := splitSingleton_trace G level split s hs.lab hs.size hs.closed hb hs.index
    ⟨hs.scratch.marks_size, hs.scratch.marks_le⟩
    ⟨hs.scratch.vmarks_size, hs.scratch.vmarks_le⟩
  have hright := splitSingleton_trace G level split t ht.lab ht.size ht.closed hb ht.index
    ⟨ht.scratch.marks_size, ht.scratch.marks_le⟩
    ⟨ht.scratch.vmarks_size, ht.scratch.vmarks_le⟩
  have hmark := mark_neighbors_map G G (Perm.id n) (by intro u v; simp)
    ⟨s.lab[split]!, hroot⟩ s t s.ptn level hs.index hi hs.lab ht.lab hs.size hs.closed hp
    ⟨hs.scratch.marks_size, hs.scratch.marks_le⟩
    ⟨hs.scratch.vmarks_size, hs.scratch.vmarks_le⟩
    ⟨ht.scratch.marks_size, ht.scratch.marks_le⟩
    ⟨ht.scratch.vmarks_size, ht.scratch.vmarks_le⟩
  dsimp only at hleft hright hmark
  simp only [Perm.get_id] at hmark
  have hvertex : t.lab[split]! = s.lab[split]! := by rw [hl]
  rw [hvertex, ← hmark.1] at hright
  apply hleft.lab_eq hright hs.lab hs.size hl he hs.index ht.index
  intro v hv
  simpa only [RefineSt.hash] using hmark.2 ⟨v, hv⟩

end Hex.GraphIso.Nauty.Sparse
