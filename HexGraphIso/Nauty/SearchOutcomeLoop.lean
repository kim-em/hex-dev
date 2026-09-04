/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeFirst
public import HexGraphIso.Nauty.SearchOutcomeLocatedProof

public section

/-!
The stable frame carried by a mutable child sweep.

The executable recovers the parent after every recursive child and may
permute its target cell.  Consequently the loop cannot identify a child
by the current array offset.  `LoopInv` freezes the refined frame used by
the specification and relates every later loop state to it by vertex
membership.  Coverage and generator anchors are likewise stated over
the frozen offsets.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- First and canonical controls that point at the current loop level are
backed by children already absorbed into the semantic incumbent. -/
structure FrameRefs (ctx : Ctx) (tcLevel specFuel level : Nat)
    (codes : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (st : SearchSt) (best : Option Key) : Prop where
  first : st.gcaFirst = level →
    ∃ o, o < len ∧
      ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells best o ∧
      st.firstlab[tc]! = rsLab[tc + o]! ∧
      cellsPerm rsPtn level rsLab st.firstlab
  canon : st.gcaCanon = level →
    ∃ o, o < len ∧
      ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
        numcells best o ∧
      st.canonlab[tc]! = rsLab[tc + o]! ∧
      cellsPerm rsPtn level rsLab st.canonlab

/-- Frame references survive an incumbent increase. -/
theorem FrameRefs.grow {ctx : Ctx} {tcLevel specFuel level : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {st : SearchSt} {best best' : Option Key}
    (h : FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells st best)
    (hinc : IncGrows best best') :
    FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells st best' := by
  constructor
  · intro heq
    obtain ⟨o, ho, hdone, hat, hperm⟩ := h.first heq
    exact ⟨o, ho, hdone.mono hinc, hat, hperm⟩
  · intro heq
    obtain ⟨o, ho, hdone, hat, hperm⟩ := h.canon heq
    exact ⟨o, ho, hdone.mono hinc, hat, hperm⟩

/-- Invariant of one imperative child loop.  `base` is the refined state
whose labelling and partition were frozen for `specNode`; `st` is the
current recovered state after zero or more children and pruning steps. -/
structure LoopInv (G : Colored n k) (ctx : Ctx)
    (tcLevel specFuel level : Nat) (codes bs fs : List Nat)
    (numcells : Nat) (rsLab rsPtn : Array Nat) (tc len tcell : Nat)
    (cursor : Option Nat) (base st : SearchSt) (best : Option Key)
    (trail : FrameTrail) : Prop where
  nodeCount : ctx.n = n
  nonempty : 0 < n
  positive : 1 ≤ level
  baseOk : SearchOk G level numcells base
  run : RunInv G ctx tcLevel level codes bs fs numcells st best trail
  effect : SearchOut G level level base st
  baseLab : base.lab = rsLab
  basePtn : base.ptn = rsPtn
  equitable : Equitable ctx level rsLab rsPtn
  cell : IsCell rsPtn level tc len
  lenTwo : 2 ≤ len
  range : tc + len ≤ ctx.n
  values : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = ctx.n + 2
  members : ∀ v, elem tcell v = true → v ∈ segN rsLab tc len
  cover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
    numcells tcell cursor best
  refs : FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len
    numcells st best
  fuelBound : level + 1 + specFuel ≤ ctx.n + 1

namespace LoopInv

/-- A fresh sweep freezes the current equitable target-cell frame.  The
strict guide bounds make current-level frame references vacuous before
the first child is explored. -/
theorem start {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len : Nat}
    {codes bs fs : List Nat} {st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (h : RunInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hfirst : st.gcaFirst < level) (hcanon : st.gcaCanon < level)
    (heq : Equitable ctx level st.lab st.ptn)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ ctx.n)
    (hvals : ∀ q : Nat, st.ptn[q]! ≤ level ∨
      st.ptn[q]! = ctx.n + 2)
    (hfuel : level + 1 + specFuel ≤ ctx.n + 1) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      st.lab st.ptn tc len (windowSet st.lab tc len) none st st best
      trail := by
  refine ⟨hn, hn0, hlevel, h.searchOk, h,
    SearchOut.refl G level level h.searchOk.reach, rfl, rfl, heq, hcell,
    hlen, hrange, hvals, ?_, sweepCover_init ctx tcLevel specFuel level
      codes st.lab st.ptn tc len numcells best, ?_, hfuel⟩
  · intro v hv
    exact elem_windowSet.mp hv
  · constructor
    · intro he
      exact (Nat.ne_of_lt hfirst he).elim
    · intro he
      exact (Nat.ne_of_lt hcanon he).elim

theorem frozenLabSize {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    rsLab.size = ctx.n := by
  rw [← h.baseLab, h.baseOk.labSize, ← h.nodeCount]

theorem frozenPtnSize {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    rsPtn.size = ctx.n := by
  rw [← h.basePtn, h.baseOk.ptnSize, ← h.nodeCount]

theorem frozenLabOk {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    LabOk rsLab ctx.n := by
  rw [← h.baseLab, h.nodeCount]
  exact labOk_of_reach h.baseOk.labSize h.baseOk.reach

theorem frozenEnd {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    rsPtn[rsPtn.size - 1]! ≤ level := by
  rw [← h.basePtn]
  exact searchOk_end h.nonempty h.baseOk h.positive

theorem frozenVals {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = ctx.n + 2 := by
  exact h.values

/-- The current recovered partition is exactly the frozen partition. -/
theorem ptnEq {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    st.ptn = rsPtn := by
  rw [← h.basePtn]
  exact h.effect.ptnEq h.baseOk h.run.searchOk

/-- Recovery may reorder a cell, but cannot change its vertex set. -/
theorem labPerm {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    cellsPerm rsPtn level rsLab st.lab := by
  rw [← h.basePtn, ← h.baseLab]
  exact h.effect.perm

theorem currentEquitable {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    Equitable ctx level st.lab st.ptn := by
  rw [h.ptnEq]
  exact h.equitable.ofCellsPerm h.labPerm h.frozenPtnSize h.frozenEnd

theorem currentCell {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    IsCell st.ptn level tc len := by
  rw [h.ptnEq]
  exact h.cell

/-- A vertex selected from the mutable bitset has both its frozen
specification offset and its current executable offset. -/
theorem nextOffsets {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell tv : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hnext : nextElem tcell cursor = some tv) :
    ∃ offset currentOffset, offset < len ∧ currentOffset < len ∧
      rsLab[tc + offset]! = tv ∧ st.lab[tc + currentOffset]! = tv := by
  have hmemBit : elem tcell tv = true := by
    simpa only [elem] using nextElem_mem hnext
  have hmemFrozen := h.members tv hmemBit
  obtain ⟨offset, hoffset, hatFrozen⟩ := mem_segN_iff.mp hmemFrozen
  have hmemCurrent : tv ∈ segN st.lab tc len :=
    (h.labPerm tc len h.cell).mem_iff.mp hmemFrozen
  obtain ⟨currentOffset, hcurrent, hatCurrent⟩ :=
    mem_segN_iff.mp hmemCurrent
  exact ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen,
    hatCurrent⟩

/-- The next mutable-loop selection enters a valid recursive node while
recording the corresponding frozen specification offset in the trail. -/
theorem child {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell tv coset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hnext : nextElem tcell cursor = some tv)
    (hcheap : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) (level + 1) st) :
    ∃ offset currentOffset, offset < len ∧ currentOffset < len ∧
      rsLab[tc + offset]! = tv ∧ st.lab[tc + currentOffset]! = tv ∧
      NodeInv G ctx tcLevel (level + 1) codes bs fs (numcells + 1)
        { st with
          lab := (breakout st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).1
          ptn := (breakout st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).2.1
          active := (breakout st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).2.2
          fixedpts := insert st.fixedpts st.lab[tc + currentOffset]!
          cosetindex := coset }
        best
        (trail.push level
          ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) := by
  obtain ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen,
      hatCurrent⟩ := h.nextOffsets hnext
  let child : SearchSt := { st with
    lab := (breakout st.lab st.ptn (level + 1) tc
      st.lab[tc + currentOffset]!).1
    ptn := (breakout st.lab st.ptn (level + 1) tc
      st.lab[tc + currentOffset]!).2.1
    active := (breakout st.lab st.ptn (level + 1) tc
      st.lab[tc + currentOffset]!).2.2
    fixedpts := insert st.fixedpts st.lab[tc + currentOffset]!
    cosetindex := coset }
  let childTrail := trail.push level
    ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
  have hfirstSize : st.firstlab.size = ctx.n := by
    rw [h.nodeCount]
    exact h.run.leafRefs.firstSize
  have hcanonSize : st.canonlab.size = ctx.n := by
    rw [h.nodeCount]
    exact h.run.leafRefs.canonSize
  have hguides : GuideStore ctx tcLevel (level + 1) child best
      childTrail := by
    apply GuideStore.stateEq
      (h.run.guides.pushSweep h.positive h.frozenLabSize h.frozenLabOk
        h.frozenPtnSize h.frozenEnd h.frozenVals h.cell h.range
        h.fuelBound hfirstSize hcanonSize
        h.refs.first h.refs.canon)
    all_goals rfl
  have hls : st.lab.size = ctx.n := by
    rw [h.nodeCount]
    exact h.run.searchOk.labSize
  have hps : st.ptn.size = ctx.n := by
    rw [h.nodeCount]
    exact h.run.searchOk.ptnSize
  have hinj : LabInj st.lab st.lab.size := by
    rw [h.run.searchOk.labSize]
    exact labInj_of_reach h.run.searchOk.labSize h.nonempty
      h.run.searchOk.reach
  have htrail : TrailOk ctx (level + 1) child childTrail := by
    apply h.run.trailOk.pushFrame hls hps hinj
      (searchOk_end h.nonempty h.run.searchOk h.positive)
      h.frozenLabSize h.frozenPtnSize h.frozenEnd h.labPerm h.ptnEq
      h.cell h.currentCell h.lenTwo h.range hoffset hcurrent
    · exact hatCurrent.trans hatFrozen.symm
    · rfl
    · exact breakout_ptn st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!
  have hnode : NodeInv G ctx tcLevel (level + 1) codes bs fs
      (numcells + 1) child best childTrail := by
    apply h.run.child h.nodeCount h.nonempty h.positive h.currentEquitable
      h.currentCell h.lenTwo h.range hcurrent hcheap hguides htrail
  exact ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen, hatCurrent,
    hnode⟩

end LoopInv

end Hex.GraphIso.Nauty
