/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Classify
public import HexGraphIso.Nauty.Sparse.CompareKey
public import HexGraphIso.Nauty.Sparse.Update

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A canonical tie uses equal native graphs and emits the forward map
from the incumbent label to the current label. -/
theorem canonVerdict_canon (G : Hex.SparseGraph n) {level : Nat} {st out : State n}
    {l c : Label n} (hauto : canonVerdict (.ofGraph G) level st = (.autoCanon, out))
    (hw : st.workperm.size = n) (hl : Label.ofArray? n st.lab = some l)
    (hc : Label.ofArray? n st.canonlab = some c)
    (hR : st.canong.toRows.Prefix (G.relabel c.perm) st.samerows) :
    G.relabel l.perm = G.relabel c.perm ∧
      ∀ v : Fin n, out.workperm[v.val]! = ((l.perm.comp c.perm.inv).get v).val := by
  by_cases hcomp : st.compCanon = 0
  · by_cases hlevel : level < st.canonlevel
    · simp [canonVerdict, hcomp, hlevel] at hauto
    · have hrows := testcanlab_eq_zero G (G.relabel c.perm)
        (updatecan (.ofGraph G) st.canong.toRows st.canonlab st.samerows) st.lab l hl
        (updatecan_relabel G st.canong.toRows st.canonlab c st.samerows hc hR)
      simp only [canonVerdict, hcomp, beq_self_eq_true, ite_true, hlevel, ite_false] at hauto
      split at hauto
      · rename_i htie
        refine ⟨hrows.mp (by simpa only [Storage.update, beq_iff_eq] using htie), ?_⟩
        have hout := (Prod.mk.inj hauto).2
        rw [← hout]
        intro v
        simpa only [scatter_eq] using scatter_perm hw hc hl v
      · split at hauto <;> cases hauto
  · simp only [canonVerdict, beq_eq_false_iff_ne.mpr hcomp, Bool.false_eq_true, ite_false] at hauto
    split at hauto <;> cases hauto

/-- Every native canonical-automorphism verdict has these semantics,
including the path that first tried a scatter against the first leaf. -/
theorem classify_canon (G : Hex.SparseGraph n) {level numcells : Nat} {st out : State n}
    {l c : Label n} (hauto : classify (.ofGraph G) level numcells st = (.autoCanon, out))
    (hw : st.workperm.size = n) (hl : Label.ofArray? n st.lab = some l)
    (hc : Label.ofArray? n st.canonlab = some c)
    (hR : st.canong.toRows.Prefix (G.relabel c.perm) st.samerows) :
    G.relabel l.perm = G.relabel c.perm ∧
      ∀ v : Fin n, out.workperm[v.val]! = ((l.perm.comp c.perm.inv).get v).val := by
  rw [classify_eq] at hauto
  split at hauto
  · cases hauto
  · split at hauto
    · cases hauto
    · split at hauto
      · dsimp only at hauto
        split at hauto
        · cases hauto
        · apply canonVerdict_canon G hauto
          · exact (scatter_size st.firstlab st).trans hw
          · simpa only [scatter_eq] using hl
          · simpa only [scatter_eq] using hc
          · simpa only [scatter_eq] using hR
      · exact canonVerdict_canon G hauto hw hl hc hR

/-- Equality established by the canonical row scan implies adjacency
preservation by the exact emitted permutation. -/
theorem classify_canon_adj (G : Hex.SparseGraph n) {level numcells : Nat} {st out : State n}
    {l c : Label n} (hauto : classify (.ofGraph G) level numcells st = (.autoCanon, out))
    (hw : st.workperm.size = n) (hl : Label.ofArray? n st.lab = some l)
    (hc : Label.ofArray? n st.canonlab = some c)
    (hR : st.canong.toRows.Prefix (G.relabel c.perm) st.samerows) :
    ∀ i j, G.adj ((l.perm.comp c.perm.inv).get i) ((l.perm.comp c.perm.inv).get j) = G.adj i j := by
  have he := (classify_canon G hauto hw hl hc hR).1
  intro i j
  have ha := congrArg (fun H : Hex.SparseGraph n => H.adj (c.perm.inv.get i) (c.perm.inv.get j)) he
  simpa only [Hex.SparseGraph.adj_relabel, Perm.get_inv_get, Perm.get_comp] using ha

end Hex.GraphIso.Nauty.Sparse
