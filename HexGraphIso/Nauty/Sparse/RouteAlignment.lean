/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RouteAt
public import HexGraphIso.Nauty.Sparse.Alignment
public import HexGraphIso.Nauty.Sparse.Divergence
public import HexGraphIso.Nauty.Sparse.Reach
import all HexGraphIso.Nauty.Policy.Effect
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Agreement with the saved first codes retains the complete guided
native history for the current partition. Before comparison, `agreed` is the preceding level. -/
structure RouteAligned (G : Hex.SparseGraph n) (tcLevel base : Nat) (root : RefineSt n)
    (level agreed numcells : Nat) (st : State n) : Prop where
  bound : st.eqlevFirst ≤ agreed
  descent : st.eqlevFirst = agreed →
    RouteAt G tcLevel st.firsttc base root level numcells st

namespace RouteAligned

variable {G : Hex.SparseGraph n} {tcLevel base level agreed numcells : Nat}
  {root : RefineSt n} {st out : State n}

theorem mono (h : RouteAligned G tcLevel base root level agreed numcells st)
    (he : out.eqlevFirst ≤ st.eqlevFirst) (ht : out.firsttc = st.firsttc)
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn) :
    RouteAligned G tcLevel base root level agreed numcells out := by
  refine ⟨Nat.le_trans he h.bound, ?_⟩
  intro hmatch
  have hold : st.eqlevFirst = agreed := by have := h.bound; omega
  rw [ht]
  exact (h.descent hold).congr hl hp

theorem compare (h : RouteAligned G tcLevel base root level (level - 1) numcells st)
    (hl : 0 < level) (code : Nat) :
    RouteAligned G tcLevel base root level level numcells (compareCodes level code st) := by
  have he := compareCodes_eqlev level code st
  have ht := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
    ((referencePolicy (.ofGraph G) 0 0).compare level code st)
  change (compareCodes level code st).firsttc = st.firsttc at ht
  obtain ⟨hlab, hptn, _, _⟩ := compareCodes_frame level code st
  constructor
  · rw [he]
    split <;> have := h.bound <;> omega
  · intro hmatch
    have hold : st.eqlevFirst = level - 1 := by
      rw [he] at hmatch
      split at hmatch
      · exact ‹st.eqlevFirst = level - 1 ∧ code = st.firstcode[level]!›.1
      · have := h.bound; omega
    rw [ht]
    exact (h.descent hold).congr hlab hptn

theorem target (h : RouteAligned G tcLevel base root level level numcells st) :
    RouteAligned G tcLevel base root level level numcells
      (chooseTarget false (.ofGraph G) tcLevel level numcells st).2.2.2 := by
  obtain ⟨hl, hp, _, _⟩ := chooseTarget_frame false (.ofGraph G) tcLevel level numcells st
  exact h.mono (chooseTarget_le (.ofGraph G) tcLevel level numcells st)
    (congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      (chooseTarget_reference (.ofGraph G) tcLevel level numcells st)) hl hp

theorem classify (h : RouteAligned G tcLevel base root level level numcells st) :
    RouteAligned G tcLevel base root level level numcells (Sparse.classify (.ofGraph G) level numcells st).2 := by
  obtain ⟨hl, hp, _, _⟩ := classify_frame (.ofGraph G) level numcells st
  exact h.mono (Nat.le_of_eq (classify_eqlev (.ofGraph G) level numcells st))
    (congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      (classify_reference (.ofGraph G) level numcells st)) hl hp

theorem leaf (h : RouteAligned G tcLevel base root level level numcells st) (leaf : Leaf) :
    RouteAligned G tcLevel base root level level numcells (leafExit leaf level st).2 := by
  obtain ⟨hl, hp, _, _⟩ := leafExit_frame leaf level st
  exact h.mono (Nat.le_of_eq (leafExit_eqlev leaf level st))
    (congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      (leafExit_reference leaf level st)) hl hp

theorem cheap (h : RouteAligned G tcLevel base root level level numcells st) (first : Bool) :
    RouteAligned G tcLevel base root level level numcells (cheapCheck first level st) := by
  unfold cheapCheck
  split
  · exact h.mono (Nat.le_refl _) rfl rfl rfl
  · exact h

end RouteAligned

namespace RouteAligned

variable {G : GraphIso.Sparse.Colored n k} {tcLevel base level numcells : Nat}
  {root : RefineSt n} {st out : State n}

/-- Individualization and the real cached visit extend the guided history
from a canonical or saved target and the parent's equitable witness. -/
theorem child (h : RouteAligned G.graph tcLevel base root level level numcells st)
    (first : Bool) (hr : RefineSt.Ready G.graph base root)
    (hok : Ready G level numcells st) {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hrecord : st.eqlevFirst = level →
      tc = targetcell (.ofGraph G.graph) st.lab st.ptn level tcLevel (-1) ∨
        st.firsttc[level]! = Int.ofNat tc) :
    let next := (policy (n := n)).child first level tc tv st
    let r := visit (.ofGraph G.graph) (level + 1) (numcells + 1) next
    RouteAligned G.graph tcLevel base root (level + 1) level r.1 r.2.2 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · cases first <;> exact h.bound
  · intro heq
    have hold : st.eqlevFirst = level := by cases first <;> exact heq
    obtain ⟨len, hc, hm⟩ := ht
    obtain ⟨hc, hlen, hb⟩ := hc (mem_ne_empty hv)
    obtain ⟨o, ho, he⟩ := mem_segN_iff.mp (hm tv hv)
    change st.lab[tc + o]! = tv at he
    have hh := (h.descent hold).child hr first hc hb (by omega) ho (hrecord hold) hok.scratch.toBounded
    rw [he] at hh
    cases first <;> exact hh

/-- A return that cannot repair an earlier divergence preserves the
ancestor's frozen descent through actual partition and cache recovery. -/
theorem recover (h : RouteAligned G.graph tcLevel base root level level numcells st)
    (hok : SearchOk G.toDense level numcells st.frame) (hout : FrameOut G level level st out)
    (ht : out.firsttc = st.firsttc)
    (hdiv : st.eqlevFirst < level → out.eqlevFirst < level) :
    RouteAligned G.graph tcLevel base root level level numcells ((policy (n := n)).recover (n + 2) level out) := by
  constructor
  · rw [recover_eqlev]; omega
  · intro hmatch
    have hold : st.eqlevFirst = level := by
      by_cases he : st.eqlevFirst = level
      · exact he
      · have hb := h.bound
        have hd := hdiv (by omega)
        rw [recover_eqlev] at hmatch
        omega
    have hs : ((policy (n := n)).recover (n + 2) level out).firsttc = st.firsttc := by
      exact (congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
        ((referencePolicy (.ofGraph G.graph) (n + 2) 0).recover level out)).trans ht
    rw [hs]
    exact (h.descent hold).recover hok hout

/-- Every actual off-path child call has the frame and divergence effects
needed to recover its parent's alignment, for arbitrary recursion fuel. -/
theorem child_return (h : RouteAligned G.graph tcLevel base root level level numcells st)
    (first : Bool) (fuel : Nat) (hl : 1 ≤ level) (hok : Ready G level numcells st)
    {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st)).2
    RouteAligned G.graph tcLevel base root level level numcells
      ((policy (n := n)).recover (n + 2) level ((policy (n := n)).leaveChild tv out)) := by
  let ch := (policy (n := n)).child first level tc tv st
  let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).2
  have hn : 0 < n := by have := VSet.mem_lt hv; omega
  have hch := hok.child hn hl first ht hv
  have hresult := node_frame G hn false tcLevel fuel (level + 1) (numcells + 1) ch (by omega) hch
  have hout : FrameOut G level level st out := hok.child_frame hn hl first ht hv
    (by simpa only [Nat.add_sub_cancel] using hresult)
  have htc : out.firsttc = st.firsttc := by
    have hr := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      (node_reference (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch)
    change out.firsttc = ch.firsttc at hr
    cases first <;> exact hr
  apply h.recover hok.ok (hout.leave tv) htc
  intro hlow
  change out.eqlevFirst < level
  apply node_diverged (by omega)
  cases first <;> exact hlow

end RouteAligned
end Hex.GraphIso.Nauty.Sparse
