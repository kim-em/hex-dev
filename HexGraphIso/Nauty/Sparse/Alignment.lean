/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.DescentAt
public import HexGraphIso.Nauty.Sparse.Divergence
public import HexGraphIso.Nauty.Sparse.Reach
import all HexGraphIso.Nauty.Policy.Effect
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Agreement with the saved first codes retains a native descent for the
current partition. Before comparison, `agreed` is the preceding level. -/
structure Aligned (G : Hex.SparseGraph n) (base : Nat) (root : RefineSt n)
    (level agreed numcells : Nat) (st : State n) : Prop where
  bound : st.eqlevFirst ≤ agreed
  descent : st.eqlevFirst = agreed →
    DescentAt G st.firsttc base root level numcells st

namespace Aligned

variable {G : Hex.SparseGraph n} {base level agreed numcells : Nat}
  {root : RefineSt n} {st out : State n}

theorem mono (h : Aligned G base root level agreed numcells st)
    (he : out.eqlevFirst ≤ st.eqlevFirst) (ht : out.firsttc = st.firsttc)
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn) :
    Aligned G base root level agreed numcells out := by
  refine ⟨Nat.le_trans he h.bound, ?_⟩
  intro hmatch
  have hold : st.eqlevFirst = agreed := by have := h.bound; omega
  rw [ht]
  exact (h.descent hold).congr hl hp

theorem compare (h : Aligned G base root level (level - 1) numcells st)
    (hl : 0 < level) (code : Nat) :
    Aligned G base root level level numcells (compareCodes level code st) := by
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

theorem target (h : Aligned G base root level level numcells st) (tcLevel : Nat) :
    Aligned G base root level level numcells
      (chooseTarget false (.ofGraph G) tcLevel level numcells st).2.2.2 := by
  obtain ⟨hl, hp, _, _⟩ := chooseTarget_frame false (.ofGraph G) tcLevel level numcells st
  exact h.mono (chooseTarget_le (.ofGraph G) tcLevel level numcells st)
    (congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      (chooseTarget_reference (.ofGraph G) tcLevel level numcells st)) hl hp

theorem classify (h : Aligned G base root level level numcells st) :
    Aligned G base root level level numcells (Sparse.classify (.ofGraph G) level numcells st).2 := by
  obtain ⟨hl, hp, _, _⟩ := classify_frame (.ofGraph G) level numcells st
  exact h.mono (Nat.le_of_eq (classify_eqlev (.ofGraph G) level numcells st))
    (congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      (classify_reference (.ofGraph G) level numcells st)) hl hp

theorem leaf (h : Aligned G base root level level numcells st) (leaf : Leaf) :
    Aligned G base root level level numcells (leafExit leaf level st).2 := by
  obtain ⟨hl, hp, _, _⟩ := leafExit_frame leaf level st
  exact h.mono (Nat.le_of_eq (leafExit_eqlev leaf level st))
    (congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      (leafExit_reference leaf level st)) hl hp

theorem cheap (h : Aligned G base root level level numcells st) (first : Bool) :
    Aligned G base root level level numcells (cheapCheck first level st) := by
  unfold cheapCheck
  split
  · exact h.mono (Nat.le_refl _) rfl rfl rfl
  · exact h

end Aligned

/-- The actual native recovery caps first agreement at the receiving level. -/
theorem recover_eqlev (inf level : Nat) (st : State n) :
    ((policy (n := n)).recover inf level st).eqlevFirst = min st.eqlevFirst level := by
  change (recoverLevels level (recoverPtn inf level st)).eqlevFirst = _
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.eqlevFirst, ite_self]
  split <;> omega

namespace Aligned

variable {G : GraphIso.Sparse.Colored n k} {base level numcells : Nat}
  {root : RefineSt n} {st out : State n}

/-- Individualization and the real cached visit prepare the next pending
history from a recorded target and the parent's equitable witness. -/
theorem child (h : Aligned G.graph base root level level numcells st)
    (first : Bool) (hr : RefineSt.Ready G.graph base root)
    (hok : Ready G level numcells st) {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hrecord : st.eqlevFirst = level → st.firsttc[level]! = Int.ofNat tc) :
    let next := (policy (n := n)).child first level tc tv st
    let r := visit (.ofGraph G.graph) (level + 1) (numcells + 1) next
    Aligned G.graph base root (level + 1) level r.1 r.2.2 := by
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
theorem recover (h : Aligned G.graph base root level level numcells st)
    (hok : SearchOk G.toDense level numcells st.frame) (hout : FrameOut G level level st out)
    (ht : out.firsttc = st.firsttc)
    (hdiv : st.eqlevFirst < level → out.eqlevFirst < level) :
    Aligned G.graph base root level level numcells ((policy (n := n)).recover (n + 2) level out) := by
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
theorem child_return (h : Aligned G.graph base root level level numcells st)
    (first : Bool) (tcLevel fuel : Nat) (hl : 1 ≤ level) (hok : Ready G level numcells st)
    {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st)).2
    Aligned G.graph base root level level numcells
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

end Aligned
end Hex.GraphIso.Nauty.Sparse
