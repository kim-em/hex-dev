/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonPair
public import HexGraphIso.Nauty.Sparse.ReturnOrigin
public import HexGraphIso.Nauty.Sparse.ExitBound
public import HexGraphIso.Nauty.Sparse.Capacity
public import HexGraphIso.Nauty.Sparse.PairsNode
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Policy.Generic.Short
import all HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- An implicit pair frozen below the receiving parent fixes every vertex
of that parent's path, before the returned partition is recovered. -/
theorem short_implicit_fix {G : GraphIso.Sparse.Colored n k} {level numcells : Nat}
    {base out : State n} (hn : 0 < n) (hl : 1 ≤ level) (h : Ready G level numcells base)
    (hfixed : FixedCells level base.frame) (hframe : FrameOut G level level base out)
    (hf : out.fixedpts = base.fixedpts) (hsaved : level ≤ out.noncheaplevel) :
    out.fixedpts.subset (fmptn out.lab out.ptn out.noncheaplevel n).1 = true := by
  have hs : out.ptn.size = n := hframe.effect.ptnSize.trans h.ok.ptnSize
  have hend := searchOk_end hn h.ok hl
  have hlow := hframe.effect.low (base.ptn.size - 1) (Or.inl hend)
  have hsize : out.ptn.size = base.ptn.size := hframe.effect.ptnSize
  change out.ptn[base.ptn.size - 1]! = base.ptn[base.ptn.size - 1]! at hlow
  have heout : out.ptn[out.ptn.size - 1]! ≤ level := by
    rw [hsize, hlow]
    exact hend
  exact (hfixed.ofEffect hf hframe.effect).fmptn hs heout hsaved

/-- Every pair read by the native short filter is valid at its receiving
parent. Canonical scatters use the retained parent reference; implicit pairs
use the exactly restored fixed set and established root-pair validity. -/
theorem return_pair {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc tv target : Nat} {first childFirst : Bool}
    {cell : VSet n} {st : State n} {key : Nat → Key n} {best : Option (Key n)}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hpath : PathInv G level st) (ht : Generic.Target State.frame level tc cell st)
    (hv : cell.mem tv = true) (hbound : target < level + 1)
    (he : (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).1 =
        .unwind target true)
    (hreceive : level ≤ target) (hguide : CanonGuide level tc st key best st)
    (hcap : 0 < st.wsCap) :
    let raw := (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    let out := (policy (n := n)).leaveChild tv raw
    Saved G raw → TraceOk G raw → PairsOk G raw →
      ∀ pair, out.autos.back? = some pair →
        PairOk (Graph.context G.graph).g st.ptn st.lab level pair.1 pair.2 := by
  intro raw out hs htrace hpairs pair hpair
  have htarg : target = level := by omega
  have horigin : LeafReturn target out := shortPolicy.leave tv target raw
    (node_origin childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st) he)
  have hcapacity : 0 < out.wsCap := by
    change 0 < raw.wsCap
    dsimp only [raw]
    rw [node_capacity]
    cases first <;> exact hcap
  rcases horigin.admission hcapacity with ⟨hb, hg, hmem, hmap⟩ | ⟨hb, hcheap⟩
  · have hp : pair = fmperm out.workperm n := Option.some.inj (hpair.symm.trans hb)
    subst pair
    apply child_canon_pair h hn hl first childFirst ht hv h
      ⟨SearchOut.refl _ _ _ h.ok.reach, h.scratch.toBounded⟩ hguide
      (hg.symm.trans htarg) hs.canonical.1 (htrace _ hmem)
    exact hmap hs.work hs.canonical.1 (isPerm_of_cellsReach hs.canonical.1 hn hs.canonical.2)
  · have hp : pair = fmptn out.lab out.ptn out.noncheaplevel n :=
      Option.some.inj (hpair.symm.trans hb)
    have hi := h.child hn hl first ht hv
    have hfixed := fixed_child first hn h hpath.fixed ht hv
    have hx := node_frame G hn childFirst tcLevel fuel (level + 1) (numcells + 1) _ (by omega) hi
    have hf := node_fixed hn childFirst tcLevel fuel (level + 1) (numcells + 1) _ (by omega) hi hfixed.2
    have hfout : out.fixedpts = st.fixedpts := by
      apply fixed_restore (st := st)
      · exact hf.trans (by cases first <;> rfl)
      · exact hfixed.1
    have hout : FrameOut G level level st out := (h.child_frame hn hl first ht hv hx).leave tv
    have hfix := short_implicit_fix (out := out) hn hl h hpath.fixed hout hfout (by omega)
    have hm : pair ∈ raw.autos := by
      change pair ∈ out.autos
      exact Array.mem_of_back? hpair
    have hmframe : pair ∈ raw.frame.autos.toList := by
      change pair ∈ raw.autos.toList
      exact Array.mem_toList_iff.mpr hm
    intro v hv hmcr
    obtain ⟨gamma, hc, hfixed, hroot, hlt⟩ := hpairs pair hmframe v hv hmcr
    refine ⟨gamma, hc, hfixed, ?_, hlt⟩
    apply hpath.stab gamma hc hroot
    intro u hu hmem
    apply hfixed u hu
    rw [hp]
    apply VSet.subset_iff.mp hfix
    change out.fixedpts.mem u = true
    rw [hfout]
    exact hmem

/-- A later sibling derives receiver validity from its reached native
invariants. Complete child calls supply trace, pair and label soundness;
the ancestor and cheap bounds determine the exact receiving level. -/
theorem PairsReady.return_pair {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc tv target : Nat} {first : Bool}
    {cell : VSet n} {st : State n} {key : Nat → Key n} {best : Option (Key n)}
    (h : PairsReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hrecord : CheapRecorded level tc st) (hc : st.gcaCanon ≤ level) (hcap : 0 < st.wsCap)
    (he : (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).1 =
        .unwind target true)
    (hreceive : level ≤ target) (hguide : CanonGuide level tc st key best st) :
    let raw := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    let out := (policy (n := n)).leaveChild tv raw
    ∀ pair, out.autos.back? = some pair →
      PairOk (Graph.context G.graph).g st.ptn st.lab level pair.1 pair.2 := by
  have hi := h.child hn hl first ht hv hrecord
  have htarget := child_target h.ancestor hc h.bound he hreceive
  apply Sparse.return_pair h.ready hn hl h.path ht hv (by omega) he hreceive hguide hcap
  · exact hi.saved.node hn tcLevel fuel (level + 1) (numcells + 1) (by omega) hi.node
  · exact node_trace G hn tcLevel fuel (level + 1) (numcells + 1) _ (by omega) hi.toTraceEntry
  · exact node_pairs G hn tcLevel fuel (level + 1) (numcells + 1) _ (by omega) hi

/-- A vertex removed by the actual received short filter has a strictly
smaller representative under a checked automorphism of the parent cells.
The witness comes from that child's emitted pair, including implicit pairs. -/
theorem PairsReady.short_drop {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tc tv target : Nat} {first : Bool}
    {cell : VSet n} {st : State n} {key : Nat → Key n} {best : Option (Key n)}
    (h : PairsReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hrecord : CheapRecorded level tc st) (hc : st.gcaCanon ≤ level) (hcap : 0 < st.wsCap)
    (he : (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).1 =
        .unwind target true)
    (hreceive : level ≤ target) (hguide : CanonGuide level tc st key best st) :
    let raw := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    let out := (policy (n := n)).leaveChild tv raw
    ∀ v, v < n → cell.mem v = true → ((policy (n := n)).shortprune cell out).mem v = false →
      ∃ gamma, checkAutom (Graph.context G.graph).g gamma = true ∧
        CellStab st.ptn level st.lab gamma ∧ gamma[v]! < v := by
  intro raw out v hvi hm hd
  apply shortprune_drop (st := out.frame) hvi hm
  · exact hd
  · intro fix mcr hp
    exact h.return_pair hn hl ht hv hrecord hc hcap he hreceive hguide (fix, mcr) hp

end Hex.GraphIso.Nauty.Sparse
