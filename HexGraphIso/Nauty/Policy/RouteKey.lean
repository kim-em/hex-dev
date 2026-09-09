/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.First.Key
public import HexGraphIso.Nauty.Policy.PathFrame
import all HexGraphIso.Nauty.Policy.HistoryState
import all HexGraphIso.Nauty.Policy.RouteHistory
import all HexGraphIso.Nauty.Policy.Tracking
import all HexGraphIso.Nauty.Policy.RouteState
import all HexGraphIso.Nauty.Policy.Route
import all HexGraphIso.Nauty.Policy.First.Ref
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Policy.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A checked scatter between the actual leaves identifies the saved
sentinel and all adjacency rows along a live guided history. -/
theorem RouteHistory.first_leaf {G : Colored n k} {ctx : Ctx n} {tcLevel level : Nat}
    {st : Search n} (h : RouteHistory ctx tcLevel level level n st)
    (hok : SearchOk G level n st) (heq : st.eqlevFirst = level)
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
    (hinv : RunInv G ctx st) (hn0 : 0 < n) (hok : SearchOk G cs.length n st)
    (hcodes : FirstCodeInv n cs fs st.firstcode st.eqlevFirst)
    (hauto : Nauty.classify ctx cs.length n st = (.autoFirst, out)) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    pathLeafKey ctx cs st.lab = incKey ctx fs st.firstlab := by
  obtain ⟨_, heq, hout, _⟩ := classify_first hauto
  have hcheck := h.first_checked hinv hn0 hok hauto hgsz hsymm hloop
  rw [hout] at hcheck
  obtain ⟨hsent, hrows⟩ := h.route.first_leaf hok heq hgsz hcheck hinv.scratch hinv.firstSize hinv.first
  have hc : cs = fs := firstCodeInv_eq_of_live (heq ▸ hcodes) hsent
  simp only [pathLeafKey, incKey, hc, hrows]

/-- At every discrete node with live histories, the leaf action computes
exactly the maximum of its incoming incumbent and its current leaf key.
The saved first key is already bounded by the incoming incumbent. -/
theorem History.leaf_max {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {cs bs fs : List Nat} {st : Search n}
    (h : History ctx tcLevel cs.length cs.length n st)
    (hinv : RunInv G ctx st) (hn0 : 0 < n) (hlevel : 1 ≤ cs.length)
    (hok : SearchOk G cs.length n st)
    (hcanon : Codes cs bs st)
    (hfirst : FirstCodeInv n cs fs st.firstcode st.eqlevFirst)
    (hbs : bs ≠ [])
    (hle : keyLe (incKey ctx fs st.firstlab) (incKey ctx bs st.canonlab))
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let verdict := Nauty.classify ctx cs.length n st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ∃ bs', Settled cs bs' out ∧ out.key ctx bs' =
      some (incMax (st.key ctx bs) (pathLeafKey ctx cs st.lab)) := by
  have hlen : cs.length ≤ n := by
    have hb := hok.bc
    have hc := hok.count
    change cs.length ≤ bcount st.ptn cs.length n at hb
    change n = bcount st.ptn cs.length n at hc
    omega
  apply Nauty.leaf_max hcanon hlen (by intro he; simp [he] at hlevel) hbs hinv.cache
  intro ha
  have hpair : Nauty.classify ctx cs.length n st =
      (.autoFirst, (Nauty.classify ctx cs.length n st).2) := by
    exact Prod.ext ha rfl
  rw [h.autoFirst_key hinv hn0 hok hfirst hpair hgsz hsymm hloop]
  exact hle

/-- The completed leaf action exposes that maximum through the executable
code store, even if the incoming store was in the overwrite window. -/
theorem History.leaf_best {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {cs bs fs : List Nat} {st : Search n}
    (h : History ctx tcLevel cs.length cs.length n st)
    (hinv : RunInv G ctx st) (hn0 : 0 < n) (hlevel : 1 ≤ cs.length)
    (hok : SearchOk G cs.length n st)
    (hcanon : Codes cs bs st)
    (hfirst : FirstCodeInv n cs fs st.firstcode st.eqlevFirst)
    (hbs : bs ≠ [])
    (hle : keyLe (incKey ctx fs st.firstlab) (incKey ctx bs st.canonlab))
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let verdict := Nauty.classify ctx cs.length n st
    (leafExit verdict.1 cs.length verdict.2).2.best ctx =
      some (incMax (st.key ctx bs) (pathLeafKey ctx cs st.lab)) := by
  obtain ⟨bs', hm, hk⟩ := h.leaf_max hinv hn0 hlevel hok hcanon hfirst hbs hle hgsz hsymm hloop
  exact hm.read.trans hk

end Hex.GraphIso.Nauty
