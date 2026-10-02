/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonAutom
public import HexGraphIso.Nauty.Sparse.LabelColors

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The canonical-row admission emits a colour-preserving automorphism.
The statement identifies every entry of the actual emitted workspace. -/
theorem classify_canon_iso (G : GraphIso.Sparse.Colored n k)
    {level numcells : Nat} {st out : State n} {l c : Label n}
    (hauto : classify (.ofGraph G.graph) level numcells st = (.autoCanon, out))
    (hw : st.workperm.size = n) (hl : Label.ofArray? n st.lab = some l)
    (hc : Label.ofArray? n st.canonlab = some c)
    (hrl : CellsReach G.toDense st.lab) (hrc : CellsReach G.toDense st.canonlab)
    (hR : st.canong.toRows.Prefix (G.graph.relabel c.perm) st.samerows) :
    GraphIso.Sparse.IsIso G G (l.perm.comp c.perm.inv) ∧
      ∀ v : Fin n, out.workperm[v.val]! = ((l.perm.comp c.perm.inv).get v).val := by
  obtain ⟨he, hp⟩ := classify_canon G.graph hauto hw hl hc hR
  exact ⟨label_pair_iso G hl hc hrl hrc he, hp⟩

/-- When the cheap boundary is unavailable, first-reference admission
executes the native scan. Its exact scatter is a coloured automorphism. -/
theorem classify_first_scan (G : GraphIso.Sparse.Colored n k)
    {level numcells : Nat} {st out : State n} {l f : Label n}
    (hauto : classify (.ofGraph G.graph) level numcells st = (.autoFirst, out))
    (hnc : st.gcaFirst < st.noncheaplevel)
    (hw : st.workperm.size = n) (hl : Label.ofArray? n st.lab = some l)
    (hf : Label.ofArray? n st.firstlab = some f)
    (hrl : CellsReach G.toDense st.lab) (hrf : CellsReach G.toDense st.firstlab) :
    GraphIso.Sparse.IsIso G G (l.perm.comp f.perm.inv) ∧
      ∀ v : Fin n, out.workperm[v.val]! = ((l.perm.comp f.perm.inv).get v).val := by
  obtain ⟨_, _, hout, hguard⟩ := classify_first hauto
  have hs : isautom (.ofGraph G.graph) out.workperm = true :=
    hguard.resolve_left (by omega)
  rw [hout] at hs ⊢
  exact ⟨GraphIso.Sparse.IsIso.mk (label_pair_colors G hl hf hrl hrf)
    (scatter_isautom G.graph hw hf hl hs),
    scatter_perm hw hf hl⟩

end Hex.GraphIso.Nauty.Sparse
