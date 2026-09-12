/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CodePrefix
public import HexGraphIso.Nauty.Sparse.FollowsPerm
public import HexGraphIso.Nauty.Sparse.AlignedTarget
import all HexGraphIso.Nauty.Sparse.FollowsPerm
import all HexGraphIso.Nauty.Sparse.DescentAt
import all HexGraphIso.Nauty.Policy.History
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- An open node following the saved cheap descent is strictly above
its terminal depth, even after reordering inside recovered cells. -/
theorem FirstRef.next_depth {G : Hex.SparseGraph n} {tcLevel base level : Nat}
    {root current : RefineSt n} {st : State n}
    (h : FirstRef G tcLevel base root st) (hdepth : level ≤ h.last)
    (hr : RefineSt.Ready G base root) (hshape : NodeShape n base root.ptn)
    (hp : FollowsPerm G st.firsttc base root level current)
    (hopen : discreteAt current.ptn level n ≠ true) : level < h.last := by
  obtain ⟨leaf, path, hd, ht, hptn, _⟩ := hp
  have hprefix : path.map Prod.fst <+: h.path.map Prod.fst := by
    apply ht.prefix h.targets
    have := hd.length
    have := h.trace.descent.length
    simp only [List.length_map]
    omega
  have hlt := (h.trace.target_prefix hr hshape h.selects h.discrete hd hprefix
    (by rw [← hptn]; exact hopen)).1
  have := hd.length
  have := h.trace.descent.length
  omega

open Std.Do
set_option mvcgen.warning false

/-- Matching the saved target prevents the native target dispatch from
demoting first-code agreement. This includes its scratch detachment. -/
theorem chooseTarget_match (g : Graph n) (tcLevel level numcells : Nat) (st : State n)
    (heq : st.eqlevFirst = level) :
    let out := chooseTarget false g tcLevel level numcells st
    out.1 = st.firsttc[level]! → out.2.2.2.eqlevFirst = level := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.1 = st.firsttc[level]! → out.2.2.2.eqlevFirst = level)
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals rcases ‹st.compCanon < 0 ∧ _› with ⟨hneg, hne⟩; simp_all

/-- Every actual cached child at a stored target has the next saved code
below a cheap ancestor. The parent may have been reordered by completed
sibling searches; only its cell contents and saved descent are needed. -/
theorem FirstRef.child_code {G : Hex.SparseGraph n} {tcLevel base level : Nat}
    {root current : RefineSt n} {st : State n}
    (h : FirstRef G tcLevel base root st) (hdepth : level + 1 ≤ h.last)
    (hr : RefineSt.Ready G base root) (hc : RefineSt.Ready G level current)
    (hshape : NodeShape n base root.ptn)
    (hp : FollowsPerm G st.firsttc base root level current)
    {tc len o : Nat} (hcell : IsCell current.ptn level tc len)
    (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (htc : st.firsttc[level]! = Int.ofNat tc)
    (scratch : Scratch) (hs : Scratch.Bounded n scratch) :
    (current.child (.ofGraph G) level tc current.lab[tc + o]! scratch).longcode =
      st.firstcode[level + 1]! := by
  obtain ⟨leaf, path, hd, ht, hptn, he⟩ := hp
  have hl := hd.ready hr
  have hcount : leaf.numcells = current.numcells := by rw [hl.spec.count, hc.spec.count, hptn]
  have hperm : cellsPerm current.ptn level leaf.lab (current.lab.map (renamingOf (Perm.id n)).toFun) := by
    rw [FollowsPerm.map_id, hptn]
    exact cellsPerm_symm he
  let fresh := Scratch.fresh n
  have hf : Scratch.Bounded n fresh := (Scratch.fresh_valid n leaf.lab leaf.ptn (level + 1)).toBounded
  obtain ⟨j, hj, _, hchild⟩ := child_match G G (Perm.id n) (by simp) hc hl hptn.symm hcount hperm
    hcell hb hn ho scratch fresh hs hf
  have hcell' : IsCell leaf.ptn level tc len := by rw [← hptn]; exact hcell
  let next := leaf.child (.ofGraph G) level tc leaf.lab[tc + j]! fresh
  have hstep : DescPath G level leaf [(tc, j)] (level + 1) next :=
    .step tc len j fresh hcell' hb hn hj hf (.refl _ _)
  have htargets : Targets st.firsttc base ((path ++ [(tc, j)]).map Prod.fst) := by
    simp only [List.map_append, List.map_cons, List.map_nil]
    apply ht.append
    simpa only [List.length_map, ← hd.length] using htc
  exact hchild.code.trans (h.code hdepth hr hshape (hd.append hstep) htargets)

/-- Native child entry, scratch invalidation and refinement retain the
saved-target history and read the next saved code after sibling recovery. -/
theorem FirstRef.child_visit {G : Hex.SparseGraph n} {tcLevel base level numcells : Nat}
    {root : RefineSt n} {st : State n} (h : FirstRef G tcLevel base root st)
    (hdepth : level + 1 ≤ h.last) (hr : RefineSt.Ready G base root)
    (hshape : NodeShape n base root.ptn)
    (hd : DescentAt G st.firsttc base root level numcells st)
    (first : Bool) {tc len o : Nat} (hc : IsCell st.ptn level tc len)
    (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (htc : st.firsttc[level]! = Int.ofNat tc) (hs : Scratch.Bounded n st.canong.scratch) :
    let next := (policy (n := n)).child first level tc st.lab[tc + o]! st
    let r := State.refined (.ofGraph G) (level + 1) (numcells + 1) next
    FollowsPerm G st.firsttc base root (level + 1) r ∧ r.longcode = st.firstcode[level + 1]! := by
  obtain ⟨current, hready, hh, hl, hp, hcount⟩ := hd
  let next := (policy (n := n)).child first level tc st.lab[tc + o]! st
  have hscratch : Scratch.Bounded n next.canong.scratch :=
    (child_valid first level tc st.lab[tc + o]! st hs).toBounded
  have hcell : IsCell current.ptn level tc len := by rw [hp]; exact hc
  have hfollow := hh.child hr hready hcell hb hn ho htc next.canong.scratch hscratch
  have hcode := h.child_code hdepth hr hready hshape hh hcell hb hn ho htc next.canong.scratch hscratch
  have he : State.refined (.ofGraph G) (level + 1) (numcells + 1) next =
      current.child (.ofGraph G) level tc current.lab[tc + o]! next.canong.scratch := by
    unfold State.refined RefineSt.child
    rw [hl, hp, hcount]
    cases first <;> rfl
  dsimp only
  rw [he]
  exact ⟨hfollow, hcode⟩

end Hex.GraphIso.Nauty.Sparse
