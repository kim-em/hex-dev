/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstCheap
import all HexGraphIso.Nauty.Sparse.CheapHistory
import all HexGraphIso.Nauty.Sparse.DescentAt
import all HexGraphIso.Nauty.Sparse.FirstRef
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Completion of the actual first child installs its native saved history
at the recovered parent. The parent witness, cheap shape and current descent
are derived from entry invariants and the executed first path. -/
theorem firstChild_history {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tv last : Nat} {st leaf : State n}
    (hn : 0 < n) (hl : 1 ≤ level) (hok : NodeInv G level numcells st)
    (hshape : FirstShape G.graph level numcells st)
    (htsize : n < st.firsttc.size) (hcsize : n + 1 < st.firstcode.size)
    (hopen : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).1 ≠ n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true level
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.2.2).orbits[tv]! = tv)
    (hpath : let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel (level + 1) (r.1 + 1)
        ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) last leaf) :
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1)
      ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))).2
    let result := (policy (n := n)).recover (n + 2) level
      ((policy (n := n)).leaveChild tv (afterChildFirst level tv out))
    CheapHistory G.graph tcLevel level level r.1 result := by
  let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
  let R := State.refined (.ofGraph G.graph) level numcells st
  let ready := cheapCheck true level r.2.2.2.2
  let ch := (policy (n := n)).child true level r.2.1.toNat tv ready
  let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch).2
  let left := (policy (n := n)).leaveChild tv (afterChildFirst level tv out)
  let result := (policy (n := n)).recover (n + 2) level left
  have hp : Generic.FirstPath (.ofGraph G.graph) tcLevel (fuel + 1) level numcells st last leaf :=
    .step hopen htv horbit hpath
  obtain ⟨href, hlast⟩ := firstRef_of_path (inf := n + 2) hn hp hl hok htsize hcsize
  have hrout : out.reference =
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel (fuel + 1) level numcells st).2.reference :=
    (firstPath_reference hpath).trans (firstPath_reference hp).symm
  have hr : result.reference =
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel (fuel + 1) level numcells st).2.reference :=
    ((referencePolicy (.ofGraph G.graph) (n + 2) tcLevel).recover level left).trans hrout
  have hg : result.gcaFirst = level := (gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover level left
  have hbound : level ≤ last := by
    have hlen := href.trace.descent.length
    rw [hlast] at hlen
    omega
  obtain ⟨hprep, htarg⟩ := hok.prepare (tcLevel := tcLevel) hn hl
  have hready := hprep.cheap true
  have htarget := htarg.of_out hready.frame.effect
  have hmem := VSet.nextElem_mem htv
  have hch := hready.ready.child hn hl true htarget hmem
  have ho := node_frame G hn true tcLevel fuel (level + 1) (r.1 + 1) ch (by omega) hch
  have hframe : FrameOut G level level ready out := hready.ready.child_frame hn hl true htarget hmem
    (by simpa only [Nat.add_sub_cancel] using ho)
  have hleft : FrameOut G level level ready left := (hframe.afterChild level tv).leave tv
  have cheap_parent : result.noncheaplevel ≤ level → ready.noncheaplevel ≤ level := by
    intro hc
    have hcheapout : out.noncheaplevel ≤ level := by
      have he := recover_noncheap (n + 2) level left
      change result.noncheaplevel = if level < out.noncheaplevel then level + 1 else out.noncheaplevel at he
      rw [he] at hc
      split at hc <;> omega
    by_cases hb : ready.noncheaplevel ≤ level
    · exact hb
    · have hchcheap : level < ch.noncheaplevel := Nat.lt_of_not_ge hb
      have hret := firstPath_noncheap (inf := n + 2) hpath (Nat.lt_succ_self level) hchcheap
      change level < out.noncheaplevel at hret
      omega
  change CheapHistory G.graph tcLevel level level r.1 result
  intro hc
  rw [hg] at hc ⊢
  have hsmall := hshape.prepare hok (cheap_parent hc)
  let href' := href.congr hr
  refine ⟨R, href', ?_, hok.refined, hsmall, ?_⟩
  · refine ⟨?_, href'.sentinel⟩
    change result.eqlevFirst ≤ href.last
    rw [hlast]
    have he := recover_eqlev (n + 2) level left
    change result.eqlevFirst = min left.eqlevFirst level at he
    omega
  · refine ⟨?_, fun _ => ?_⟩
    · rw [recover_eqlev]; omega
    · have hd : DescentAt G.graph result.firsttc level R level r.1 ready := by
        have hp := prepareFirst_partition (.ofGraph G.graph) tcLevel level numcells st
        refine ⟨R, hok.refined, FollowsPerm.refl _ _ _ _, ?_, ?_, hp.2.2.symm⟩
        · unfold ready cheapCheck
          split <;> exact hp.1.symm
        · unfold ready cheapCheck
          split <;> exact hp.2.1.symm
      exact hd.recover hready.ready.ok hleft

/-- The first child's saved target survives its terminal sentinel write,
all later siblings, and the actual parent recovery. -/
theorem firstChild_target {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tv last : Nat} {st leaf : State n}
    (hn : 0 < n) (hl : 1 ≤ level) (hok : NodeInv G level numcells st)
    (htsize : n < st.firsttc.size)
    (hopen : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).1 ≠ n)
    (hpath : let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel (level + 1) (r.1 + 1)
        ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) last leaf) :
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1)
      ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))).2
    let result := (policy (n := n)).recover (n + 2) level
      ((policy (n := n)).leaveChild tv (afterChildFirst level tv out))
    result.firsttc[level]! = Int.ofNat r.2.1.toNat := by
  let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
  let ch := (policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)
  let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch).2
  let left := (policy (n := n)).leaveChild tv (afterChildFirst level tv out)
  let result := (policy (n := n)).recover (n + 2) level left
  have hdepth : level + 1 ≤ last := by
    have hgen : ∀ {fuel depth count last : Nat} {st leaf : State n},
        Generic.FirstPath (.ofGraph G.graph) tcLevel fuel depth count st last leaf → depth ≤ last := by
      intro fuel depth count last st leaf hp
      induction hp with
      | leaf => exact Nat.le_refl _
      | step _ _ _ _ ih => omega
    exact hgen hpath
  have hr := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
    ((referencePolicy (.ofGraph G.graph) (n + 2) tcLevel).recover level left)
  change result.firsttc = out.firsttc at hr
  have htc := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
    (firstPath_reference (inf := n + 2) hpath)
  change out.firsttc = leaf.firsttc.set! (last + 1) (-1) at htc
  change result.firsttc[level]! = Int.ofNat r.2.1.toNat
  rw [hr, htc, Array.getElem!_set!_ne _ _ _ _ (by omega)]
  rw [(Prod.mk.inj (firstPath_before hpath (by omega))).2]
  have hstore := (prepareFirst_store (.ofGraph G.graph) tcLevel level numcells st).2
  have hch : ch.firsttc = st.firsttc.set! level r.2.1 := by
    change (cheapCheck true level r.2.2.2.2).firsttc = _
    unfold cheapCheck
    split <;> exact hstore
  change ch.firsttc[level]! = Int.ofNat r.2.1.toNat
  have hlevel : level ≤ n := Nat.le_trans hok.spec.depth
    (by rw [hok.spec.count]; exact bcount_le _ _ _)
  rw [hch, Array.getElem!_set!_self _ _ _ (by omega), prepareFirst_choice hok hn hl hopen]
  rfl

end Hex.GraphIso.Nauty.Sparse
