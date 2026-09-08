/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Domination
public import HexGraphIso.Nauty.SmallCell.Transitive

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Under the search invariant, the transcription's refined cell-count
guard agrees with the specification's discreteness guard. -/
theorem refine_discrete_iff {G : Colored n k} {ctx : Ctx n}
    (hn0 : 0 < n) {level numcells : Nat}
    {st : SearchSt n} (hok : SearchOk G level numcells st)
    (hlevel : 1 ≤ level) :
    (refine ctx level st.lab st.ptn st.active numcells).numcells =
        n ↔
      discreteAt (refine ctx level st.lab st.ptn st.active
        numcells).ptn level n = true := by
  have hend := searchOk_end hn0 hok hlevel
  have hnn : n = st.ptn.size := by rw [hok.ptnSize]
  have hls : st.lab.size = st.ptn.size := by
    rw [hok.labSize, hok.ptnSize]
  have hnc := hok.count
  have hR := refine_refInv (ctx := ctx) (level := level)
    (lab := st.lab) (ptn := st.ptn) (active := st.active)
    (numcells := numcells) (Nat.le_of_eq hnn) hls hend
  have hRend : (refine ctx level st.lab st.ptn st.active
      numcells).ptn[(refine ctx level st.lab st.ptn st.active
        numcells).ptn.size - 1]! ≤ level := by
    rw [hR.ptnSize, refine_frozen hnn hls hend hend]
    exact hend
  have hcount := refine_bcount (ctx := ctx) (level := level)
    (lab := st.lab) (ptn := st.ptn) (active := st.active)
    (numcells := numcells) hnn hls hend
  have haccurate : (refine ctx level st.lab st.ptn st.active
      numcells).numcells =
      bcount (refine ctx level st.lab st.ptn st.active
        numcells).ptn level n := by omega
  rw [haccurate]
  exact (discreteAt_iff_bcount (by rw [hR.ptnSize, ← hnn]) hRend).symm

/-- The subtree facts ignore the refinement bookkeeping fields. -/
theorem SubtreeOk.ofFrames {ctx : Ctx n} {level : Nat} {r r' : RefineSt n}
    (h : SubtreeOk ctx level r) (hlab : r'.lab = r.lab)
    (hptn : r'.ptn = r.ptn)
    (hcells : r'.numcells = r.numcells) :
    SubtreeOk ctx level r' := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, h.it.lvl⟩, ?_, ?_, ?_⟩
  · rw [hlab]; exact h.it.ok.labSize
  · rw [hlab]; exact h.it.ok.labOk
  · rw [hptn]; exact h.it.ok.ptnSize
  · rw [hptn]; exact h.it.ok.ptnEnd
  · rw [hlab]; exact h.it.inj
  · rw [hptn]; exact h.it.vals
  · rw [hlab, hptn]; exact h.eqt
  · rw [hptn, hcells]; exact h.acc
  · rw [hptn]; exact h.shape

end Hex.GraphIso.Nauty
