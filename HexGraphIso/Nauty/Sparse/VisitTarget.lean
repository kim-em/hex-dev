/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.VisitKey
public import HexGraphIso.Nauty.Sparse.TargetInvariant
public import HexGraphIso.Nauty.Sparse.TargetDispatch
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Recovering an equitable parent preserves every field of its fresh
target dispatch, for any fixed hint and depth cutoff. -/
theorem FrameOut.target_eq {G : GraphIso.Sparse.Colored n k}
    {level numcells : Nat} {st out : State n}
    (h : FrameOut G level level st out) (hs : Ready G level numcells st)
    (ho : Ready G level numcells out) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : numcells < n) (tcLevel : Nat) (hint : Int) :
    maketargetcell (.ofGraph G.graph) st.lab st.ptn level tcLevel hint =
      maketargetcell (.ofGraph G.graph) out.lab out.ptn level tcLevel hint := by
  have hp : out.ptn = st.ptn := h.effect.ptnEq hs.ok ho.ok
  have hslabel := isPerm_of_cellsReach hs.ok.labSize hn hs.ok.reach
  have holabel := isPerm_of_cellsReach ho.ok.labSize hn ho.ok.reach
  have hsize : st.ptn.size = n := hs.ok.ptnSize
  have hcount : numcells = bcount st.ptn level n := hs.ok.count
  have hend : st.ptn[n - 1]! ≤ level := by
    have he := searchOk_end hn hs.ok hl
    change st.ptn[st.ptn.size - 1]! ≤ level at he
    rwa [hsize] at he
  obtain ⟨a, ha⟩ := Index.exists_valid hslabel hs.ok.ptnSize hend
  obtain ⟨b, hb⟩ := Index.exists_valid holabel hs.ok.ptnSize hend
  rw [hp]
  exact maketargetcell_perm G.graph st.lab out.lab st.ptn level tcLevel hint a b
    hslabel holabel hs.ok.ptnSize hend ha hb hs.equitable h.effect.perm
    (by rw [← hcount]; exact hc)

/-- The cached target following an actual visit has the specification's
fresh position, vertex set and size. The two visits may order labels
differently within their cells. -/
theorem NodeInv.visit_target {G : GraphIso.Sparse.Colored n k}
    {level numcells : Nat} {st : State n} (h : NodeInv G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) (tcLevel : Nat) (hint : Int) :
    let r := visit (.ofGraph G.graph) level numcells st
    let f := refine (.ofGraph G.graph) level st.lab st.ptn st.active numcells
    r.1 < n →
      let t := maketargetCached (.ofGraph G.graph) r.2.2.lab r.2.2.ptn level tcLevel hint
        r.2.2.canong.scratch
      (t.1, t.2.1, t.2.2.1) = maketargetcell (.ofGraph G.graph) f.lab f.ptn level tcLevel hint := by
  intro r f hc
  obtain ⟨hcount, _, _, hframe, hf, hr⟩ := h.visit_equiv hn hl
  have hc' : (visit (.ofGraph G.graph) level numcells
      { st with canong := { st.canong with scratch := .fresh n } }).1 < n := by
    rw [hcount]
    exact hc
  have hready : Ready G level
      (visit (.ofGraph G.graph) level numcells
        { st with canong := { st.canong with scratch := .fresh n } }).1 r.2.2 := by
    rw [hcount]
    exact hr
  have ht := hframe.target_eq hf hready hn hl hc' tcLevel hint
  have hsize : r.2.2.ptn.size = n := hr.ok.ptnSize
  have hrCount : r.1 = bcount r.2.2.ptn level n := hr.ok.count
  have hend : r.2.2.ptn[n - 1]! ≤ level := by
    have he := searchOk_end hn hr.ok hl
    change r.2.2.ptn[r.2.2.ptn.size - 1]! ≤ level at he
    rwa [hsize] at he
  obtain ⟨label, hlabel⟩ := Label.ofArray?_exists (isPerm_of_cellsReach hr.ok.labSize hn hr.ok.reach)
  have he := maketargetCached_eq G.graph r.2.2.lab r.2.2.ptn level tcLevel hint
    r.2.2.canong.scratch label hlabel hr.ok.ptnSize hend hr.scratch
    (Target.nonempty hr.ok.ptnSize hend (by rw [← hrCount]; exact hc))
  exact he.trans ht.symm

end Hex.GraphIso.Nauty.Sparse
