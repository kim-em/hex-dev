/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstKey
public import HexGraphIso.Nauty.Policy.PathFrame
import all HexGraphIso.Nauty.Policy.HistoryState
import all HexGraphIso.Nauty.Policy.RouteHistory
import all HexGraphIso.Nauty.Policy.Tracking
import all HexGraphIso.Nauty.Policy.RouteState
import all HexGraphIso.Nauty.Policy.Route
import all HexGraphIso.Nauty.Policy.FirstRef
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Policy.State

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- A checked scatter between the actual leaves identifies the saved
sentinel and all adjacency rows along a live guided history. -/
theorem RouteHistory.first_leaf {G : Colored n k} {ctx : Ctx n} {tcLevel level : Nat}
    {st : Search n} (h : RouteHistory ctx tcLevel level level n st)
    (hok : SearchOk G level n st.view) (heq : st.eqlevFirst = level)
    (hgsz : ctx.g.size = n) (hcheck : checkAutom ctx.g (scatter st.firstlab st).workperm = true)
    (hwork : st.workperm.size = n) (hfirst : st.firstlab.size = n)
    (hperm : st.firstlab.toList.Perm (List.range n)) :
    st.firstcode[level + 1]! = codeSentinel ∧ leafRows ctx st.lab = leafRows ctx st.firstlab := by
  obtain ⟨root, href, hi, _, _, ha⟩ := h
  obtain ⟨current, hg, hl, hp, _⟩ := ha.descent heq
  have hdisc : ∀ i, i < n → current.ptn[i]! ≤ level := by
    have hcount := hok.count
    change n = bcount st.ptn level n at hcount
    have hall : (List.range n).countP (fun i => decide (st.ptn[i]! ≤ level)) =
        (List.range n).length := by
      simpa only [bcount, List.length_range] using hcount.symm
    intro i hi
    rw [hp]
    exact of_decide_eq_true (List.countP_eq_length.mp hall i (List.mem_range.mpr hi))
  obtain ⟨leaf, path, hd, hguided, hll, hlp⟩ := hg.leaf hi hdisc
  have hmap : ∀ i, i < n → (scatter st.firstlab st).workperm[href.leaf.lab[i]!]! = leaf.lab[i]! := by
    rw [href.lab, hll, hl]
    exact scatter_map hwork hfirst hperm
  obtain ⟨hlevel, hrows⟩ := Guided.leaf_checked href.descent hi href.selects href.targets
    hd hguided href.discrete (fun i hi => by rw [hlp]; exact hdisc i hi) hgsz hcheck hmap
  exact ⟨by rw [hlevel]; exact href.sentinel, by rwa [hll, hl, href.lab] at hrows⟩

/-- Every first-reference admission has the complete saved key. The
retained histories justify its depth even when admission uses a scan. -/
theorem History.autoFirst_key {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {cs fs : List Nat} {st out : Search n}
    (h : History ctx tcLevel cs.length cs.length n st)
    (hinv : RunInv G ctx st) (hn0 : 0 < n) (hok : SearchOk G cs.length n st.view)
    (hcodes : FirstCodeInv n cs fs st.firstcode st.eqlevFirst)
    (hauto : Engine.classify ctx cs.length n st = (.autoFirst, out)) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    pathLeafKey ctx cs st.lab = incKey ctx fs st.firstlab := by
  obtain ⟨_, heq, hout, _⟩ := classify_first hauto
  have hcheck := h.first_checked hinv hn0 hok hauto hgsz hsymm hloop
  rw [hout] at hcheck
  obtain ⟨hsent, hrows⟩ := h.route.first_leaf hok heq hgsz hcheck hinv.scratch hinv.firstSize hinv.first
  have hc : cs = fs := firstCodeInv_eq_of_live (heq ▸ hcodes) hsent
  simp only [pathLeafKey, incKey, hc, hrows]

end Hex.GraphIso.Nauty.Engine
