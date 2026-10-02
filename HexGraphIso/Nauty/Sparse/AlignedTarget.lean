/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Alignment
public import HexGraphIso.Nauty.Sparse.TargetHint
import all HexGraphIso.Nauty.Sparse.DescentAt
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- First-code agreement at an open node executes the cached target call
with precisely the production hint, and returns its natural position. -/
theorem chooseTarget_pos {g : Graph n} {tcLevel level numcells : Nat} {st : State n}
    (hnc : numcells < n) (he : st.eqlevFirst = level) :
    (chooseTarget false g tcLevel level numcells st).1 =
      Int.ofNat (maketargetCached g st.lab st.ptn level tcLevel
        (if st.compCanon < 0 then st.firsttc[level]! else -1) st.canong.scratch).1 := by
  by_cases hn : st.compCanon < 0 <;>
    simp [chooseTarget, hnc, he, hn, apply_ite Id.run, apply_ite Prod.fst]

theorem chooseTarget_cast {g : Graph n} {tcLevel level numcells : Nat} {st : State n}
    (hnc : numcells < n) (he : st.eqlevFirst = level) :
    Int.ofNat (chooseTarget false g tcLevel level numcells st).1.toNat =
      (chooseTarget false g tcLevel level numcells st).1 := by
  rw [chooseTarget_pos hnc he]
  rfl

/-- The native frozen descent identifies the actual target with its saved
slot, through both the hinted and ordinary cached dispatch arms. -/
theorem DescentAt.target {G : Hex.SparseGraph n} {tcLevel base level numcells : Nat}
    {root : RefineSt n} {st : State n}
    (h : DescentAt G st.firsttc base root level numcells st)
    (href : FirstRef G tcLevel base root st) (hd : Depth href.last st)
    (he : st.eqlevFirst = level) (hnc : numcells < n)
    (hr : RefineSt.Ready G base root) (hshape : NodeShape n base root.ptn)
    (hs : Scratch.Valid n st.lab st.ptn level st.canong.scratch) :
    (chooseTarget false (.ofGraph G) tcLevel level numcells st).1 = st.firsttc[level]! := by
  obtain ⟨current, hc, hp, hl, hptn, hcount⟩ := h
  have hopen : discreteAt current.ptn level n ≠ true := by
    intro hdisc
    have hb := (discreteAt_iff_bcount hc.spec.node.ptnSize.symm hc.spec.node.ptnEnd).mp hdisc
    have hbc := hc.spec.count
    omega
  have hh := href.target (by have hb := hd.1; omega) hr hc hshape hp hopen
  rw [hl, hptn] at hh
  obtain ⟨l, hlabel⟩ := Label.ofArray?_exists hc.spec.label
  rw [hl] at hlabel
  have hsize : st.ptn.size = n := by rw [← hptn]; exact hc.spec.node.ptnSize
  have hend : st.ptn[n - 1]! ≤ level := by
    rw [← hptn]
    simpa only [hc.spec.node.ptnSize] using hc.spec.node.ptnEnd
  have hb : bcount st.ptn level n < n := by
    rw [← hptn, ← hc.spec.count, hcount]
    exact hnc
  rw [chooseTarget_pos hnc he]
  have ht := maketargetCached_eq G st.lab st.ptn level tcLevel
    (if st.compCanon < 0 then st.firsttc[level]! else -1) st.canong.scratch l hlabel
    hsize hend hs (Target.nonempty hsize hend hb)
  rw [(Prod.mk.inj ht).1]
  change Int.ofNat (targetcell (.ofGraph G) st.lab st.ptn level tcLevel
    (if st.compCanon < 0 then st.firsttc[level]! else -1)) = _
  split
  · rw [← hh, targetcell_hint]
  · exact hh

/-- A surviving first-target comparison agrees with the saved target.
All descent and cache premises concern the actual native partition. -/
theorem Aligned.target_eq {G : Hex.SparseGraph n} {tcLevel base level numcells : Nat}
    {root : RefineSt n} {st : State n}
    (h : Aligned G base root level level numcells st)
    (href : FirstRef G tcLevel base root st) (hd : Depth href.last st)
    (hkeep : (chooseTarget false (.ofGraph G) tcLevel level numcells st).2.2.2.eqlevFirst = level)
    (hnc : numcells < n) (hr : RefineSt.Ready G base root)
    (hshape : NodeShape n base root.ptn) (hs : Scratch.Valid n st.lab st.ptn level st.canong.scratch) :
    (chooseTarget false (.ofGraph G) tcLevel level numcells st).1 = st.firsttc[level]! := by
  have he : st.eqlevFirst = level := by
    have := chooseTarget_le (.ofGraph G) tcLevel level numcells st
    have := h.bound
    omega
  exact (h.descent he).target href hd he hnc hr hshape hs

end Hex.GraphIso.Nauty.Sparse
