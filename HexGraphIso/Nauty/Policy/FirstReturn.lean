/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstEntry
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.FirstEntry
import all HexGraphIso.Nauty.Policy.FirstRef
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Leftmost
import all HexGraphIso.Nauty.Policy.Safety
import all HexGraphIso.Nauty.Policy.RouteHistory
import all HexGraphIso.Nauty.Policy.Tracking
import all HexGraphIso.Nauty.Policy.RouteState
import all HexGraphIso.Nauty.Policy.Route
import all HexGraphIso.Nauty.Policy.CheapHistory
import all HexGraphIso.Nauty.Policy.HistoryState
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Recovery
import all HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Policy.Descent
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}


/-- The first child installs the reference at its parent and supplies the
recovered frame from which all later siblings use the off-path contract. -/
theorem firstChild_ready {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tv last : Nat} {st leaf : Search n}
    (hin : FirstPre G ctx level numcells st) (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hopen : (Generic.prepareFirst ctx tcLevel level numcells st).1 ≠ n)
    (htv : (Generic.prepareFirst ctx tcLevel level numcells st).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true level
      (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).orbits[tv]! = tv)
    (hpath : let r := Generic.prepareFirst ctx tcLevel level numcells st
      Generic.FirstPath ctx tcLevel fuel (level + 1) (r.1 + 1)
        (child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) last leaf)
    (hchild : let r := Generic.prepareFirst ctx tcLevel level numcells st
      RunInv G ctx (node true ctx (n + 2) tcLevel fuel (level + 1) (r.1 + 1)
        (child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))).2)
    (hgsz : ctx.g.size = n)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    let out := (node true ctx (n + 2) tcLevel fuel (level + 1) (r.1 + 1)
      (child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))).2
    let left := { afterChildFirst level tv out with fixedpts := out.fixedpts.erase tv }
    SweepPre G ctx tcLevel true level r.1 r.2.1.toNat tv none r.2.2.1
      (recoverLevels level (recoverPtn (n + 2) level left)) := by
  let r := Generic.prepareFirst ctx tcLevel level numcells st
  let R := st.refined ctx level numcells
  let ready := cheapCheck true level r.2.2.2.2
  let ch := child true level r.2.1.toNat tv ready
  let out := (node true ctx (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch).2
  let left := { afterChildFirst level tv out with fixedpts := out.fixedpts.erase tv }
  let result := recoverLevels level (recoverPtn (n + 2) level left)
  have hp : Generic.FirstPath ctx tcLevel (fuel + 1) level numcells st last leaf :=
    .step hopen htv horbit hpath
  obtain ⟨href, hlast⟩ := firstRef_of_path (inf := n + 2) hn0 hsymm hp hin.positive hin.partition
    hin.equitable hin.targets hin.codes
  have hrout : out.reference = (node true ctx (n + 2) tcLevel (fuel + 1) level numcells st).2.reference :=
    (firstPath_reference hpath).trans (firstPath_reference hp).symm
  have hr : result.reference = (node true ctx (n + 2) tcLevel (fuel + 1) level numcells st).2.reference :=
    ((referencePolicy ctx (n + 2) tcLevel).recover level left).trans hrout
  have hgr : result.gcaFirst = level := (gcaPolicy ctx (n + 2) tcLevel).recover level left
  have hbound : level ≤ last := by
    have hl := href.descent.length
    rw [hlast] at hl
    omega
  obtain ⟨hprep, htarg⟩ := prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 hin.positive hin.partition
  have hcheap := (reachPolicy G ctx tcLevel hn0).cheap true level r.1 r.2.2.2.2 hprep
  have hreadyTarget := htarg.of_out hcheap.effect
  have hcell : r.2.2.1.mem tv = true := VSet.nextElem_mem htv
  have hch := (reachPolicy G ctx tcLevel hn0).child true level r.1 r.2.1.toNat tv r.2.2.1 ready
    hin.positive hcheap.ok hreadyTarget hcell
  have hentry := hin.child hn0 hsymm htv hgsz hloop
  have hpathReady := (hin.prepare_path hn0 hgsz tcLevel).cheap true
  have hfixout := node_fixed (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) true hn0
    (by have := hin.positive; omega) hentry.partition hentry.path.fixed
  have hfresh := (fixed_child true hn0 hcheap.ok hpathReady.fixed hreadyTarget hcell).1
  have hrestore : left.fixedpts = ready.fixedpts := by
    apply fixed_restore (base := ready) (out := out) _ hfresh
    exact hfixout
  have hbout := hentry.boundary.firstPath hn0 (by have := hin.positive; omega) hentry.partition hpath
  have hbleft : Boundary G ctx (level + 1) left := hbout.congr rfl rfl rfl
  have ho := node_out (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) true hn0 (by omega) hch.1
  have hframe : SearchOut G level level ready.view out.view := hch.2 _
    (by simpa only [Nat.add_sub_cancel, policy, Generic.Policy.child] using ho)
  have hleftFrame : SearchOut G level level ready.view left.view := hframe.congr rfl rfl rfl rfl
  have hrec := (reachPolicy G ctx tcLevel hn0).recover level r.1 ready left hin.positive hcheap.ok hleftFrame
  have hstored : RunInv G ctx result :=
    (hchild.congr (out := left) rfl rfl hchild.cache rfl rfl rfl rfl rfl).recover (n + 2) level
  have hcheapHist : CheapHistory ctx tcLevel level level r.1 result := by
    intro hc
    rw [hgr] at hc ⊢
    have houtcheap : out.noncheaplevel ≤ level := by
      have he := recover_noncheap (n + 2) level left
      change result.noncheaplevel = if level < out.noncheaplevel then level + 1 else out.noncheaplevel at he
      rw [he] at hc
      split at hc <;> omega
    have hreadycheap : ready.noncheaplevel ≤ level := by
      by_cases hle : ready.noncheaplevel ≤ level
      · exact hle
      · have hchcheap : level < ch.noncheaplevel := Nat.lt_of_not_ge hle
        have hret := firstPath_noncheap (inf := n + 2) hpath (Nat.lt_succ_self level) hchcheap
        change level < out.noncheaplevel at hret
        omega
    have hs := firstCheap_small hn0 hin.positive hin.partition hin.equitable hin.small hreadycheap
    let href' := href.congr hr
    refine ⟨R, href', ?_, hs, ?_⟩
    · refine ⟨?_, href'.sentinel⟩
      change result.eqlevFirst ≤ href.last
      rw [hlast]
      have he := recover_eqlev (n + 2) level left
      change result.eqlevFirst = min left.eqlevFirst level at he
      omega
    · refine ⟨?_, fun _ => ?_⟩
      · rw [recover_eqlev]
        omega
      · have hd : DescentAt ctx result.firsttc level R level r.1 ready := by
          refine ⟨R, (Follows.refl _ _ _ _).perm, ?_, ?_, rfl⟩
          · have hl := (prepareFirst_fields ctx tcLevel level numcells st).1
            change R.lab = ready.lab
            unfold ready cheapCheck
            split <;> exact hl.symm
          · have hp := (prepareFirst_fields ctx tcLevel level numcells st).2.1
            change R.ptn = ready.ptn
            unfold ready cheapCheck
            split <;> exact hp.symm
        exact hd.recover hcheap.ok hleftFrame
  have hsaved : result.firsttc[level]! = Int.ofNat r.2.1.toNat := by
    have hrleft := (referencePolicy ctx (n + 2) tcLevel).recover level left
    have htleft := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) hrleft
    change result.firsttc = out.firsttc at htleft
    rw [htleft]
    have htout := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      (firstPath_reference (inf := n + 2) hpath)
    change out.firsttc = leaf.firsttc.set! (last + 1) (-1) at htout
    rw [htout, Array.getElem!_set!_ne _ _ _ _ (by omega), firstPath_before hpath (by omega)]
    change ready.firsttc[level]! = Int.ofNat r.2.1.toNat
    have hstore := (prepareFirst_fields ctx tcLevel level numcells st).2.2
    have hlevel : level < st.firsttc.size := by
      have hl := (refined_iter (ctx := ctx) hn0 hin.positive hin.partition).lvl
      have ht := hin.targets
      omega
    have hchoice := prepareFirst_choice hopen (refined_iter hn0 hin.positive hin.partition) hin.equitable
    have hcast : Int.ofNat r.2.1.toNat = r.2.1 := by rw [hchoice]; rfl
    rw [hcast]
    unfold ready cheapCheck
    split <;> change r.2.2.2.2.firsttc[level]! = r.2.1
    all_goals rw [hstore, Array.getElem!_set!_self _ _ _ hlevel]
  have hroute : RouteHistory ctx tcLevel level level r.1 result := by
    unfold RouteHistory
    rw [hgr]
    have hl : R.lab = ready.lab := by
      have hl := (prepareFirst_fields ctx tcLevel level numcells st).1
      unfold ready cheapCheck
      split <;> exact hl.symm
    have hp : R.ptn = ready.ptn := by
      have hp := (prepareFirst_fields ctx tcLevel level numcells st).2.1
      unfold ready cheapCheck
      split <;> exact hp.symm
    refine ⟨R, href.congr hr, refined_iter hn0 hin.positive hin.partition, hin.equitable, ?_, ?_⟩
    · have hc := hcheap.ok.count
      change r.1 = bcount ready.ptn level n at hc
      rw [hp]
      exact hc.symm
    · refine ⟨?_, fun _ => ?_⟩
      · rw [recover_eqlev]
        omega
      · have hd : GuidedAt ctx tcLevel result.firsttc level R level r.1 ready :=
          ⟨R, GuidedPerm.refl _ _ _ _ _, hl, hp, rfl⟩
        exact hd.recover hcheap.ok hleftFrame
  have hhist : History ctx tcLevel level level r.1 result := ⟨hcheapHist, hroute⟩
  have hrecord : Recorded ctx tcLevel level r.2.1.toNat result :=
    ⟨fun _ _ => hsaved, fun _ => Or.inr hsaved⟩
  have heq : Equitable ctx level ready.lab ready.ptn := by
    have hl := (prepareFirst_fields ctx tcLevel level numcells st).1
    have hp := (prepareFirst_fields ctx tcLevel level numcells st).2.1
    unfold ready cheapCheck
    split <;> change Equitable ctx level r.2.2.2.2.lab r.2.2.2.2.ptn
    all_goals rw [hl, hp]; exact hin.equitable
  exact ⟨(by intro _ v hv; cases hv), hin.positive, hrec.ok, hreadyTarget.of_out hrec.effect,
    (by intro v hv; cases hv), hstored, Nat.le_of_eq hgr, recover_canon_le level _, hhist, hrecord,
    recover_equitable hn0 hin.positive hcheap.ok heq hleftFrame,
    hbleft.recover_child hin.positive (by have := Nat.le_trans hcheap.ok.bc (bcount_le _ _ _); omega),
    recover_bound level left, hpathReady.recover hn0 hin.positive hcheap.ok hleftFrame hrestore⟩

end Hex.GraphIso.Nauty.Engine
