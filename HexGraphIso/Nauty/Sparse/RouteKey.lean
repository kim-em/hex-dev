/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RouteAt
public import HexGraphIso.Nauty.Sparse.Canonical
public import HexGraphIso.Nauty.Sparse.TraceState
import all HexGraphIso.Sparse.Iso

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The forward permutation between two parsed labels maps their literal
arrays pointwise, independently of any graph or automorphism claim. -/
theorem labels_map {ref lab : Array Nat} {f l : Label n}
    (hf : Label.ofArray? n ref = some f) (hl : Label.ofArray? n lab = some l) :
    ref.map (renamingOf (l.perm.comp f.perm.inv)).toFun = lab := by
  rw [← Label.ofArray?_toArray hf, ← Label.ofArray?_toArray hl]
  apply Array.ext (by simp)
  intro i hi hj
  simp only [Label.toArray, Array.getElem_map, Array.getElem_ofFn]
  rw [renamingOf_lt _ (f.get _).isLt]
  simp only [Label.get, Perm.get_comp, Fin.eta, Perm.inv_get_get]

/-- Every first-reference admission has the complete saved key when its
actual guided history is available. Cheap and scanned admissions use the
proved native automorphism; the guided path establishes the sentinel. -/
theorem RouteAt.autoFirst_key {G : GraphIso.Sparse.Colored n k} {tcLevel base : Nat}
    {root : RefineSt n} {cs fs : List Nat} {st out : State n} {f l : Label n}
    (h : RouteAt G.graph tcLevel st.firsttc base root cs.length n st)
    (href : FirstRef G.graph tcLevel base root st) (hr : RefineSt.Ready G.graph base root)
    (hh : CheapHistory G.graph tcLevel cs.length cs.length n st)
    (hcodes : FirstCodeInv n cs fs st.firstcode st.eqlevFirst)
    (hauto : classify (.ofGraph G.graph) cs.length n st = (.autoFirst, out))
    (hw : st.workperm.size = n) (hf : Label.ofArray? n st.firstlab = some f)
    (hl : Label.ofArray? n st.lab = some l)
    (hrf : CellsReach G.toDense st.firstlab) (hrl : CellsReach G.toDense st.lab) :
    (⟨cs ++ [codeSentinel], G.graph.relabel l.perm⟩ : Key n) =
      ⟨fs ++ [codeSentinel], G.graph.relabel f.perm⟩ := by
  have ha := (hh.first_iso hauto hw hl hf hrl hrf).1
  obtain ⟨hsent, hgraph⟩ := h.first_leaf href hr hf hl (l.perm.comp f.perm.inv) ha.2 (labels_map hf hl)
  have heq := (classify_first hauto).2.1
  have hc := firstCodeInv_eq_of_live (heq ▸ hcodes) hsent
  simp only [hc, hgraph]

/-- At a valid prepared native leaf with retained guided history, the
executed leaf action computes the exact incumbent maximum. The first-key
bound is derived from that history, not supplied as a classification oracle. -/
theorem TraceReady.leaf_max {G : GraphIso.Sparse.Colored n k} {tcLevel base : Nat}
    {root : RefineSt n} {cs bs fs : List Nat} {st : State n}
    (h : TraceReady G tcLevel cs.length n st) (hn : 0 < n)
    (route : RouteAt G.graph tcLevel st.firsttc base root cs.length n st)
    (href : FirstRef G.graph tcLevel base root st) (hr : RefineSt.Ready G.graph base root)
    (hc : Comparison G.graph cs bs fs st) :
    let verdict := classify (.ofGraph G.graph) cs.length n st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ∃ l c bs' d, Label.ofArray? n st.lab = some l ∧ Label.ofArray? n st.canonlab = some c ∧
      Label.ofArray? n out.canonlab = some d ∧
      (⟨bs' ++ [codeSentinel], G.graph.relabel d.perm⟩ : Key n) =
        Key.max ⟨bs ++ [codeSentinel], G.graph.relabel c.perm⟩
          ⟨cs ++ [codeSentinel], G.graph.relabel l.perm⟩ ∧ Settled cs bs' out := by
  obtain ⟨l, hl⟩ := h.ready.parse hn
  obtain ⟨f, c, hf, hcan, hbound⟩ := hc.lower
  obtain ⟨c', hcan', hprefix⟩ := h.saved.store
  have he : c' = c := Option.some.inj (hcan'.symm.trans hcan)
  subst c'
  have hlen : cs.length ≤ n := by
    have hb := h.ready.ok.bc
    have hn := bcount_le st.ptn cs.length n
    exact Nat.le_trans hb hn
  obtain ⟨bs', d, hd, hmax, hsettled⟩ := Sparse.leaf_max hc.canonical hlen hl hcan hprefix (by
    intro ha
    rw [route.autoFirst_key href hr h.history hc.first (Prod.ext ha rfl)
      h.saved.work hf hl h.saved.first.2 h.ready.ok.reach]
    exact hbound)
  exact ⟨l, c, bs', d, hl, hcan, hd, hmax, hsettled⟩

end Hex.GraphIso.Nauty.Sparse
