/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FollowsPerm
public import HexGraphIso.Nauty.Sparse.CheapTarget
import all HexGraphIso.Nauty.Sparse.FollowsPerm
import all HexGraphIso.Nauty.Policy.History

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A live stored-target descent below a cheap ancestor chooses the exact
saved next target, even after sibling searches reorder the current cells. -/
theorem FirstRef.target {G : Hex.SparseGraph n} {tcLevel base level : Nat}
    {root current : RefineSt n} {st : State n}
    (h : FirstRef G tcLevel base root st) (hdepth : level ≤ h.last)
    (hr : RefineSt.Ready G base root) (hc : RefineSt.Ready G level current)
    (hshape : NodeShape n base root.ptn)
    (hp : FollowsPerm G st.firsttc base root level current)
    (hopen : discreteAt current.ptn level n ≠ true) :
    Int.ofNat (targetcell (.ofGraph G) current.lab current.ptn level tcLevel (-1)) = st.firsttc[level]! := by
  obtain ⟨leaf, path, hd, ht, hptn, he⟩ := hp
  have hl := hd.ready hr
  have hprefix : path.map Prod.fst <+: h.path.map Prod.fst := by
    apply ht.prefix h.targets
    have := hd.length
    have := h.trace.descent.length
    simp only [List.length_map]
    omega
  obtain ⟨hshort, htarget⟩ := h.trace.target_prefix hr hshape h.selects h.discrete hd hprefix
    (by rw [← hptn]; exact hopen)
  have hslot : st.firsttc[level]! = Int.ofNat (h.path.map Prod.fst)[path.length]! := by
    have hs := h.targets path.length (by simpa only [List.length_map] using hshort)
    simpa only [← hd.length] using hs
  have hend : leaf.ptn[n - 1]! ≤ level := by
    simpa only [hl.spec.node.ptnSize] using hl.spec.node.ptnEnd
  obtain ⟨s, hs⟩ := Index.exists_valid hc.spec.label hl.spec.node.ptnSize hend
  obtain ⟨t, ht⟩ := Index.exists_valid hl.spec.label hl.spec.node.ptnSize hend
  have hcurrent : Equitable (Graph.context G) level current.lab leaf.ptn := by
    rw [← hptn]
    exact hc.equitable
  have htarget' : targetcell (.ofGraph G) current.lab current.ptn level tcLevel (-1) =
      targetcell (.ofGraph G) leaf.lab leaf.ptn level tcLevel (-1) := by
    rw [hptn]
    exact targetcell_perm G current.lab leaf.lab leaf.ptn level tcLevel (-1) s t
      hc.spec.label hl.spec.label hl.spec.node.ptnSize hend hs ht hcurrent he
  exact (congrArg Int.ofNat (htarget'.trans htarget)).trans hslot.symm

end Hex.GraphIso.Nauty.Sparse
