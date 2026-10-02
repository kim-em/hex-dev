/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FollowsPerm

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A current history modulo within-cell order still identifies the saved
first graph and depth at a discrete endpoint. -/
theorem FirstRef.leaf_follows {G : Hex.SparseGraph n} {tcLevel base level : Nat}
    {root current : RefineSt n} {st : State n} {f l : Label n}
    (h : FirstRef G tcLevel base root st) (hdepth : level ≤ h.last)
    (hr : RefineSt.Ready G base root) (hc : RefineSt.Ready G level current)
    (hshape : NodeShape n base root.ptn)
    (hp : FollowsPerm G st.firsttc base root level current)
    (hd : discreteAt current.ptn level n = true)
    (hf : Label.ofArray? n st.firstlab = some f) (hl : Label.ofArray? n current.lab = some l) :
    level = h.last ∧ G.relabel l.perm = G.relabel f.perm := by
  obtain ⟨leaf, path, hpath, ht, hlabel, hptn⟩ := hp.leaf hr hc hd
  exact h.leaf_eq hdepth hr hshape hpath ht (by rw [hptn]; exact hd) hf
    (by rw [hlabel]; exact hl)

/-- The literal native first-reference verdict emits a coloured
automorphism when the retained cheap history allows sibling cell reordering.
Production use requires these histories at every admission. -/
theorem classify_first_follows {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {root current : RefineSt n} {st out : State n} {cs fs : List Nat} {f l : Label n}
    (hauto : classify (.ofGraph G.graph) level numcells st = (.autoFirst, out))
    (h : FirstRef G.graph tcLevel st.gcaFirst root st)
    (hcodes : FirstCodeInv n cs fs st.firstcode st.eqlevFirst)
    (hr : RefineSt.Ready G.graph st.gcaFirst root) (hc : RefineSt.Ready G.graph level current)
    (hshape : NodeShape n st.gcaFirst root.ptn)
    (hp : FollowsPerm G.graph st.firsttc st.gcaFirst root level current)
    (hd : discreteAt current.ptn level n = true) (hcurrent : current.lab = st.lab)
    (hw : st.workperm.size = n) (hf : Label.ofArray? n st.firstlab = some f)
    (hl : Label.ofArray? n st.lab = some l)
    (hrf : CellsReach G.toDense st.firstlab) (hrl : CellsReach G.toDense st.lab) :
    GraphIso.Sparse.IsIso G G (l.perm.comp f.perm.inv) ∧
      ∀ v : Fin n, out.workperm[v.val]! = ((l.perm.comp f.perm.inv).get v).val := by
  obtain ⟨leaf, path, hpath, ht, hlabel, hptn⟩ := hp.leaf hr hc hd
  exact classify_first_cheap hauto h hcodes hr hshape hpath ht
    (by rw [hptn]; exact hd) (hlabel.trans hcurrent) hw hf hl hrf hrl

end Hex.GraphIso.Nauty.Sparse
