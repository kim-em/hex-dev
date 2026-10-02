/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Matching
public import HexGraphIso.Nauty.Sparse.ReferenceCode
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A stored target equal to the unhinted native rule survives both
cached dispatch arms, including a changed scratch result. -/
theorem Ready.match_target {G : GraphIso.Sparse.Colored n k}
    {tcLevel level numcells : Nat} {st : State n}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : numcells < n) (heq : st.eqlevFirst = level)
    (hslot : st.firsttc[level]! =
      Int.ofNat (targetcell (.ofGraph G.graph) st.lab st.ptn level tcLevel (-1))) :
    (chooseTarget false (.ofGraph G.graph) tcLevel level numcells st).1 = st.firsttc[level]! := by
  have hp := isPerm_of_cellsReach h.ok.labSize hn h.ok.reach
  obtain ⟨label, hparse⟩ := Label.ofArray?_exists hp
  have hsize : st.ptn.size = n := h.ok.ptnSize
  have hend : st.ptn[n - 1]! ≤ level := by
    simpa only [hsize] using (h.partition hn hl).ptnEnd
  have hcount : bcount st.ptn level n < n := by
    have he : numcells = bcount st.ptn level n := h.ok.count
    rw [← he]
    exact hc
  rw [chooseTarget_pos hc heq]
  have ht := maketargetCached_eq G.graph st.lab st.ptn level tcLevel
    (if st.compCanon < 0 then st.firsttc[level]! else -1) st.canong.scratch label hparse
    h.ok.ptnSize hend h.scratch (Target.nonempty h.ok.ptnSize hend hcount)
  rw [(Prod.mk.inj ht).1]
  change Int.ofNat (targetcell (.ofGraph G.graph) st.lab st.ptn level tcLevel
    (if st.compCanon < 0 then st.firsttc[level]! else -1)) = _
  split
  · rw [hslot, targetcell_hint]
  · exact hslot.symm

end Hex.GraphIso.Nauty.Sparse
