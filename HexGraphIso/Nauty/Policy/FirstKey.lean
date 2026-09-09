/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.HistoryState
public import HexGraphIso.Nauty.Policy.Canonical
import all HexGraphIso.Nauty.Policy.HistoryState
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Recovery
import all HexGraphIso.Nauty.Policy.FirstRef
import all HexGraphIso.Nauty.Policy.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A discrete aligned endpoint reaches the first depth. Its sentinel is
therefore the saved sentinel, even though the engine does not test it. -/
theorem Aligned.first_leaf {G : Colored n k} {ctx : Ctx n} {tcLevel level : Nat}
    {root : RefineSt n} {st : Search n}
    (h : Aligned ctx st.gcaFirst root level level n st)
    (href : FirstRef ctx tcLevel st.gcaFirst root st) (hdepth : Depth href.last st)
    (hsmall : SubtreeOk ctx st.gcaFirst root) (hok : SearchOk G level n st)
    (heq : st.eqlevFirst = level) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    st.firstcode[level + 1]! = codeSentinel ∧
      leafRows ctx st.lab = leafRows ctx st.firstlab := by
  obtain ⟨current, hh, hl, hp, _⟩ := h.descent heq
  have hbound : level ≤ href.last := by rw [← heq]; exact hdepth.1
  have hdisc : ∀ i, i < n → current.ptn[i]! ≤ level := by
    have hcount := hok.count
    change n = bcount st.ptn level n at hcount
    have hall : (List.range n).countP (fun i => decide (st.ptn[i]! ≤ level)) =
        (List.range n).length := by
      simpa only [bcount, List.length_range] using hcount.symm
    intro i hi
    rw [hp]
    exact of_decide_eq_true (List.countP_eq_length.mp hall i (List.mem_range.mpr hi))
  obtain ⟨hlevel, hrows⟩ := href.leaf_eq hbound hgsz hsymm hloop hsmall hh hdisc
  exact ⟨by rw [hlevel]; exact href.sentinel, by rw [← hl]; exact hrows⟩

/-- Below a cheap first ancestor, live code agreement and the retained
histories identify the entire current leaf key with the saved first key. -/
theorem History.first_key {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {cs fs : List Nat} {st : Search n}
    (h : History ctx tcLevel cs.length cs.length n st)
    (hcheap : st.noncheaplevel ≤ st.gcaFirst)
    (hok : SearchOk G cs.length n st)
    (hcodes : FirstCodeInv n cs fs st.firstcode st.eqlevFirst)
    (heq : st.eqlevFirst = cs.length) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    pathLeafKey ctx cs st.lab = incKey ctx fs st.firstlab := by
  obtain ⟨root, href, hd, hs, ha⟩ := h.cheapHistory hcheap
  obtain ⟨hsent, hrows⟩ := ha.first_leaf href hd hs hok heq hgsz hsymm hloop
  have hc : cs = fs := firstCodeInv_eq_of_live (heq ▸ hcodes) hsent
  simp only [pathLeafKey, incKey, hc, hrows]

/-- The canonical code machine alone bounds every downward-frozen leaf,
including leaves admitted against the first reference. -/
theorem Codes.leaf_le {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hc : st.compCanon < 0) :
    keyLe (pathLeafKey ctx cs st.lab) (incKey ctx bs st.canonlab) := by
  have heq : st.compCanon = -1 := by
    rcases h.tri with ⟨he, _⟩ | ⟨_, _, _, _, _, _, hd⟩
    · omega
    · rcases hd with ⟨he, _⟩ | ⟨he, _, _⟩ <;> omega
  have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon (-1) := heq ▸ h
  rw [keyLe, frozen_lt_keyCmp hm]
  decide

end Hex.GraphIso.Nauty
