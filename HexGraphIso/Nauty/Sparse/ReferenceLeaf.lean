/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstRef
public import HexGraphIso.Nauty.Sparse.Depth
public import HexGraphIso.Nauty.Sparse.CheapPrefix
public import HexGraphIso.Nauty.Sparse.LeafAutom
import all HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Policy.Selection

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Live code agreement cannot pass the saved native leaf's sentinel. -/
theorem FirstRef.depth {G : Hex.SparseGraph n} {tcLevel base : Nat} {root : RefineSt n}
    {st : State n} (h : FirstRef G tcLevel base root st) {cs fs : List Nat}
    (hc : FirstCodeInv n cs fs st.firstcode st.eqlevFirst) : st.eqlevFirst ≤ h.last := by
  have hb := hc.sentinel_bound (by omega) h.sentinel
  have := hc.elev_fs
  omega

/-- The code comparison and the saved actual descent read identical real
codes at every position represented by both histories. -/
theorem FirstRef.code_eq {G : Hex.SparseGraph n} {tcLevel base i : Nat} {root : RefineSt n}
    {st : State n} (h : FirstRef G tcLevel base root st) {cs fs : List Nat}
    (hc : FirstCodeInv n cs fs st.firstcode st.eqlevFirst) (hbase : 1 ≤ base)
    (hi : i < h.codes.length) (hf : base + i ≤ fs.length) :
    h.codes[i]! = fs[base + i - 1]! :=
  (h.stored i hi).symm.trans (hc.fcontent (base + i) (by omega) hf)

/-- At a cheap ancestor, a discrete current descent following the saved
targets has exactly the saved first leaf's depth and native graph. -/
theorem FirstRef.leaf_eq {G : Hex.SparseGraph n} {tcLevel base level : Nat}
    {root current : RefineSt n} {st : State n} {xs : List (Nat × Nat)} {f l : Label n}
    (h : FirstRef G tcLevel base root st) (hdepth : level ≤ h.last)
    (hr : RefineSt.Ready G base root) (hshape : NodeShape n base root.ptn)
    (hp : DescPath G base root xs level current)
    (ht : Targets st.firsttc base (xs.map Prod.fst))
    (hd : discreteAt current.ptn level n = true)
    (hf : Label.ofArray? n st.firstlab = some f) (hl : Label.ofArray? n current.lab = some l) :
    level = h.last ∧ G.relabel l.perm = G.relabel f.perm := by
  have hprefix : xs.map Prod.fst <+: h.path.map Prod.fst := by
    apply ht.prefix h.targets
    have := hp.length
    have := h.trace.descent.length
    simp only [List.length_map]
    omega
  exact DescPath.leaf_prefix hr hshape h.trace.descent h.discrete
    (by rw [h.lab]; exact hf) hp hprefix hd hl

/-- The saved and current native histories justify the literal first
scatter as a coloured automorphism, without an adjacency scan. -/
theorem FirstRef.scatter {G : GraphIso.Sparse.Colored n k} {tcLevel level : Nat}
    {root current : RefineSt n} {st : State n} {xs : List (Nat × Nat)} {f l : Label n}
    (h : FirstRef G.graph tcLevel st.gcaFirst root st) (hdepth : level ≤ h.last)
    (hr : RefineSt.Ready G.graph st.gcaFirst root) (hshape : NodeShape n st.gcaFirst root.ptn)
    (hp : DescPath G.graph st.gcaFirst root xs level current)
    (ht : Targets st.firsttc st.gcaFirst (xs.map Prod.fst))
    (hd : discreteAt current.ptn level n = true) (hcurrent : current.lab = st.lab)
    (hw : st.workperm.size = n) (hf : Label.ofArray? n st.firstlab = some f)
    (hl : Label.ofArray? n st.lab = some l)
    (hrf : CellsReach G.toDense st.firstlab) (hrl : CellsReach G.toDense st.lab) :
    GraphIso.Sparse.IsIso G G (l.perm.comp f.perm.inv) ∧
      ∀ v : Fin n, (scatter st.firstlab st).workperm[v.val]! = ((l.perm.comp f.perm.inv).get v).val := by
  have he := (h.leaf_eq hdepth hr hshape hp ht hd hf (by rw [hcurrent]; exact hl)).2
  exact ⟨label_pair_iso G hl hf hrl hrf he, scatter_perm hw hf hl⟩

/-- The actual first-reference classification is sound when the frozen
cheap ancestor and current saved-target descent have been retained. -/
theorem classify_first_cheap {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {root current : RefineSt n} {st out : State n} {xs : List (Nat × Nat)}
    {cs fs : List Nat} {f l : Label n}
    (hauto : classify (.ofGraph G.graph) level numcells st = (.autoFirst, out))
    (h : FirstRef G.graph tcLevel st.gcaFirst root st)
    (hc : FirstCodeInv n cs fs st.firstcode st.eqlevFirst)
    (hr : RefineSt.Ready G.graph st.gcaFirst root) (hshape : NodeShape n st.gcaFirst root.ptn)
    (hp : DescPath G.graph st.gcaFirst root xs level current)
    (ht : Targets st.firsttc st.gcaFirst (xs.map Prod.fst))
    (hd : discreteAt current.ptn level n = true) (hcurrent : current.lab = st.lab)
    (hw : st.workperm.size = n) (hf : Label.ofArray? n st.firstlab = some f)
    (hl : Label.ofArray? n st.lab = some l)
    (hrf : CellsReach G.toDense st.firstlab) (hrl : CellsReach G.toDense st.lab) :
    GraphIso.Sparse.IsIso G G (l.perm.comp f.perm.inv) ∧
      ∀ v : Fin n, out.workperm[v.val]! = ((l.perm.comp f.perm.inv).get v).val := by
  obtain ⟨_, heq, hout, _⟩ := classify_first hauto
  have hdepth : level ≤ h.last := by rw [← heq]; exact h.depth hc
  rw [hout]
  exact h.scatter hdepth hr hshape hp ht hd hcurrent hw hf hl hrf hrl

end Hex.GraphIso.Nauty.Sparse
