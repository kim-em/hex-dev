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

/-- The target-cell representation used by `maketargetcell` is the same
bitset as the length-indexed window representation used by sweep
coverage. -/
theorem worksetOf_eq_windowSet (lab : Array Nat) (tc len : Nat)
    (hlen : 1 ≤ len) :
    worksetOf lab tc (tc + len - 1) = windowSet lab tc len := by
  unfold worksetOf windowSet segN
  rw [show tc + len - 1 + 1 - tc = len by omega]
  rw [List.foldl_map]

/-- Charging target-cell statistics changes no logical search field. -/
theorem RunPrep.setTctotal {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells value : Nat} {codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (h : RunPrep G ctx tcLevel level codes bs fs numcells st best trail) :
    RunPrep G ctx tcLevel level codes bs fs numcells
      { st with tctotal := value } best trail := by
  let st' : SearchSt := { st with tctotal := value }
  have hok : SearchOk G level numcells st' := by
    refine ⟨h.searchOk.labSize, h.searchOk.ptnSize, h.searchOk.reach,
      h.searchOk.init1, h.searchOk.vals, h.searchOk.count, h.searchOk.bc,
      h.searchOk.canon⟩
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  refine ⟨hok, h.codeInv, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-- Parking the cheap-automorphism boundary changes only the `CheapOk`
component of the stable invariant. -/
theorem RunInv.park {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (h : RunInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hcheap : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) level
      { st with noncheaplevel := level + 1 }) :
    RunInv G ctx tcLevel level codes bs fs numcells
      { st with noncheaplevel := level + 1 } best trail := by
  let st' : SearchSt := { st with noncheaplevel := level + 1 }
  have hok : SearchOk G level numcells st' := by
    refine ⟨h.searchOk.labSize, h.searchOk.ptnSize, h.searchOk.reach,
      h.searchOk.init1, h.searchOk.vals, h.searchOk.count, h.searchOk.bc,
      h.searchOk.canon⟩
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  refine ⟨hok, h.codeInv, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, hcheap, hrefs,
    h.guides.stateEq rfl rfl rfl rfl,
    h.trailOk.stateEq rfl rfl, h.firstPositive, h.canonPositive,
    h.firstBound, h.canonBound, h.bestCodes, h.incumbent⟩

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

/-- Recovering a state related to a valid loop entry restores the full
parent invariant as well as the composable parent-level effect. -/
theorem SearchOut.recoverOk {G : Colored n k} {ctx : Ctx}
    {level numcells inf : Nat} {base out : SearchSt}
    (hn : ctx.n = n) (hinf : inf = n + 2)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells base)
    (hout : SearchOut G level level base out) :
    SearchOut G level level base (Nauty.recover ctx.n inf level out) ∧
      SearchOk G level numcells (Nauty.recover ctx.n inf level out) := by
  subst inf
  have hrec : SearchOut G level level out
      (Nauty.recover ctx.n (n + 2) level out) := by
    rw [hn]
    have hle : level ≤ n := Nat.le_trans hok.bc
      (bcount_le base.ptn level n)
    exact recover_out (by omega) hout.reach
  have heffect := hout.trans hrec
  refine ⟨heffect, searchOk_of_out hok hlevel heffect ?_⟩
  intro q hq
  rw [hn, recover_ptn]
  rcases Decidable.em (q < n ∧ out.ptn[q]! > level) with hc | hc
  · rw [ite_eq_left hc]
    exact Or.inr rfl
  · rw [ite_eq_right hc]
    left
    rcases Nat.lt_or_ge level out.ptn[q]! with hgt | hle
    · exact absurd ⟨hq, hgt⟩ hc
    · exact hle

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
  shortClear : st.needshortprune = false
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
    (hshort : st.needshortprune = false)
    (hfuel : level + 1 + specFuel ≤ ctx.n + 1) :
    LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      st.lab st.ptn tc len (windowSet st.lab tc len) none st st best
      trail := by
  refine ⟨hn, hn0, hlevel, h.searchOk, h,
    SearchOut.refl G level level h.searchOk.reach, rfl, rfl, heq, hcell,
    hlen, hrange, hvals, ?_, sweepCover_init ctx tcLevel specFuel level
      codes st.lab st.ptn tc len numcells best, ?_, hshort, hfuel⟩
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

/-- A recursive child effect, followed by temporary fixed-point cleanup
and `recover`, composes back into the frozen parent frame. -/
theorem recoverChild {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell currentOffset inf : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hinf : inf = n + 2) (hcurrent : currentOffset < len)
    (hout : SearchOut G level (level + 1)
      { st with
        lab := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := insert st.fixedpts st.lab[tc + currentOffset]! }
      out) :
    let cleaned : SearchSt :=
      { out with fixedpts := erase out.fixedpts st.lab[tc + currentOffset]! }
    let recovered := Nauty.recover ctx.n inf level cleaned
    SearchOut G level level base recovered ∧
      SearchOk G level numcells recovered := by
  dsimp only
  let cleaned : SearchSt :=
    { out with fixedpts := erase out.fixedpts st.lab[tc + currentOffset]! }
  have hchild : SearchOut G level level st out := by
    apply breakout_child_out hinv.nonempty hinv.run.searchOk hinv.positive
      hinv.currentCell hinv.lenTwo
      (by rw [← hinv.nodeCount]; exact hinv.range) hcurrent
    · exact hout
    · rfl
    · exact breakout_ptn st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!
    · rfl
    · rfl
  have hclean : SearchOut G level level st cleaned := by
    exact hchild.congr rfl rfl rfl rfl
  have hbase : SearchOut G level level base cleaned :=
    hinv.effect.trans hclean
  simpa only [cleaned] using hbase.recoverOk hinv.nodeCount hinf
    hinv.positive hinv.baseOk

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

/-- Every vertex returned by a verified sibling sweep lies in the graph
vertex range.  This is the cursor bound threaded by the fuel induction;
it is intentionally derived from the frozen target-cell membership rather
than from the mutable bitset alone. -/
theorem nextLt {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells tc len tcell tv : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt} {best : Option Key}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hnext : nextElem tcell cursor = some tv) :
    tv < ctx.n := by
  obtain ⟨offset, _, hoffset, _, hatFrozen, _⟩ := h.nextOffsets hnext
  rw [← hatFrozen]
  apply h.frozenLabOk (tc + offset)
  rw [h.frozenLabSize]
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoffset tc) h.range

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
      h.currentCell h.lenTwo h.range hcurrent h.shortClear hcheap hguides
      htrail
  exact ⟨offset, currentOffset, hoffset, hcurrent, hatFrozen, hatCurrent,
    hnode⟩

/-- An internal off-path node reaches a fresh verified child sweep after
the executable refinement, comparison, target-accounting, and cheap-rule
bookkeeping.  The returned target is simultaneously the executable and
specification target, so the accompanying equality exposes the whole
node key as this sweep's bound. -/
theorem NodeInv.otherSweep {G : Colored n k} {ctx : Ctx}
    {tcLevel specFuel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n) (hg : ctx.g = rowsOf G) (hn0 : 0 < n)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (h : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ ctx.n)
    (hnonneg : (otherLeafSt ctx level numcells st).compCanon ≥ 0)
    (hfuel : level + 1 + specFuel ≤ ctx.n + 1) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    let full := codes ++ [r.longcode]
    let pre := otherLeafSt ctx level numcells st
    ∃ tc len,
      let tcell := worksetOf r.lab tc (tc + len - 1)
      let base : SearchSt := { pre with tctotal := pre.tctotal + len }
      let start := if cheapautom base.ptn level ctx.n then base
        else { base with noncheaplevel := level + 1 }
      maketargetcell ctx r.lab r.ptn level tcLevel (-1) =
          (tc, tcell, len) ∧
        processnode ctx level r.numcells base = (Int.ofNat level, base) ∧
        nodeKey ctx tcLevel (specFuel + 1) level codes st numcells =
          keysMax
            (sweepKey ctx tcLevel specFuel level full r.lab r.ptn tc
              r.numcells 0)
            ((List.range (len - 1)).map fun o =>
              sweepKey ctx tcLevel specFuel level full r.lab r.ptn tc
                r.numcells (o + 1)) ∧
        LoopInv G ctx tcLevel specFuel level full bs fs r.numcells
          r.lab r.ptn tc len tcell none start start best trail := by
  dsimp only
  let r := refine ctx level st.lab st.ptn st.active numcells
  let full := codes ++ [r.longcode]
  let pre := otherLeafSt ctx level numcells st
  have href := h.refined hn hg hn0 hlevel
  obtain ⟨tc, len, hmk, hspec, hcell, hlen, hrange⟩ :=
    h.target hn hg hn0 hlevel hnum
  refine ⟨tc, len, ?_⟩
  let tcell := worksetOf r.lab tc (tc + len - 1)
  let base : SearchSt := { pre with tctotal := pre.tctotal + len }
  let start := if cheapautom base.ptn level ctx.n then base
    else { base with noncheaplevel := level + 1 }
  have hdisc : discreteAt r.ptn level ctx.n = false := by
    rw [← Bool.not_eq_true, ← refine_discrete_iff hn hn0
      h.run.searchOk hlevel]
    exact hnum
  have hchildren := h.children (specFuel := specFuel) hdisc hspec hlen
  have hprep : RunPrep G ctx tcLevel level full bs fs r.numcells pre
      best trail := by
    simpa only [r, full, pre] using
      h.run.otherLeaf hn hn0 hlevel hpath
  have hbase : RunPrep G ctx tcLevel level full bs fs r.numcells base
      best trail := by
    exact hprep.setTctotal
  have hpreNonneg : pre.compCanon ≥ 0 := by
    simpa only [pre] using hnonneg
  have hprocess : processnode ctx level r.numcells base =
      (Int.ofNat level, base) := by
    apply processnode_internal
    · intro hgate
      have hcomp : base.compCanon = pre.compCanon := rfl
      rw [hcomp] at hgate
      omega
    · intro heq
      exact hnum (beq_iff_eq.mp heq)
  have hrun : RunInv G ctx tcLevel level full bs fs r.numcells start
      best trail := by
    rcases hc : cheapautom base.ptn level ctx.n with _ | _
    · have hp : CheapOk ctx (initialPartition G).1
          (initPtn n (n + 2) (initialPartition G).2) level
          { base with noncheaplevel := level + 1 } :=
        hbase.cheap.park (by omega) (by omega)
      simpa only [start, hc, Bool.false_eq_true, ite_false] using
        hbase.run.park hp
    · simpa only [start, hc, ite_true] using hbase.run
  have hpreFirst : pre.gcaFirst = st.gcaFirst := by
    dsimp only [pre, otherLeafSt, r]
    exact (otherNodePrep_frames level
      (refine ctx level st.lab st.ptn st.active numcells).longcode
      { st with
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
        active := (refine ctx level st.lab st.ptn st.active numcells).active
        numnodes := st.numnodes + 1 }).2.2.2.2.2.2.1
  have hpreCanon : pre.gcaCanon = st.gcaCanon := by
    dsimp only [pre, otherLeafSt, r]
    exact (otherNodePrep_frames level
      (refine ctx level st.lab st.ptn st.active numcells).longcode
      { st with
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
        active := (refine ctx level st.lab st.ptn st.active numcells).active
        numnodes := st.numnodes + 1 }).2.2.2.2.2.2.2.1
  have hpreShort : pre.needshortprune = st.needshortprune := by
    dsimp only [pre, otherLeafSt, r]
    rw [otherNodePrep]
    simp only [Id.run_pure, apply_ite Id.run,
      apply_ite SearchSt.needshortprune, ite_self]
  have hstartFirst : start.gcaFirst = st.gcaFirst := by
    unfold start base
    split <;> exact hpreFirst
  have hstartCanon : start.gcaCanon = st.gcaCanon := by
    unfold start base
    split <;> exact hpreCanon
  have hstartShort : start.needshortprune = false := by
    unfold start base
    split <;> simpa only [hpreShort] using h.shortClear
  have hstartLab : start.lab = r.lab := by
    unfold start base pre otherLeafSt
    split <;>
      simpa only [r] using
        (otherNodePrep_frames level r.longcode
          { st with
            lab := r.lab
            ptn := r.ptn
            active := r.active
            numnodes := st.numnodes + 1 }).2.2.2.2.2.2.2.2.2.2.2.1
  have hstartPtn : start.ptn = r.ptn := by
    unfold start base pre otherLeafSt
    split <;>
      simpa only [r] using
        (otherNodePrep_frames level r.longcode
          { st with
            lab := r.lab
            ptn := r.ptn
            active := r.active
            numnodes := st.numnodes + 1 }).2.2.2.2.2.2.2.2.2.2.2.2
  have hvals : ∀ q : Nat, r.ptn[q]! ≤ level ∨
      r.ptn[q]! = ctx.n + 2 := by
    intro q
    rcases Nat.lt_or_ge q ctx.n with hq | hq
    · exact href.1.vals q hq
    · left
      rw [getElem!_neg _ _ (by rw [href.1.ok.ptnSize]; omega)]
      exact Nat.zero_le _
  have hloop := LoopInv.start hn hn0 hlevel hrun
    (by rw [hstartFirst]; exact h.firstBelow)
    (by rw [hstartCanon]; exact h.canonBelow)
    (by rw [hstartLab, hstartPtn]; exact href.2.1)
    (by rw [hstartPtn]; exact hcell) hlen hrange
    (by rw [hstartPtn]; exact hvals) hstartShort hfuel
  refine ⟨?_, hprocess, hchildren, ?_⟩
  · simpa only [r, tcell] using hmk
  · rw [worksetOf_eq_windowSet r.lab tc len (by omega)]
    simpa only [hstartLab, hstartPtn] using hloop

set_option maxHeartbeats 800000 in
/-- The nonnegative internal branch with a failed cheap-automorphism test
parks the boundary before entering its child loop. -/
theorem otherNode_park_state (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells < ctx.n)
    (hnonneg : let r := refine ctx level st.lab st.ptn st.active numcells
      let pre := otherNodePrep level r.longcode { st with
        lab := r.lab, ptn := r.ptn, active := r.active
        numnodes := st.numnodes + 1 }
      pre.compCanon ≥ 0)
    (hshort : let r := refine ctx level st.lab st.ptn st.active numcells
      let pre := otherNodePrep level r.longcode { st with
        lab := r.lab, ptn := r.ptn, active := r.active
        numnodes := st.numnodes + 1 }
      let mt := maketargetcell ctx pre.lab pre.ptn level tcLevel (-1)
      let base := { pre with tctotal := pre.tctotal + mt.2.2 }
      (processnode ctx level r.numcells base).2.needshortprune = false)
    (hcheap : let r := refine ctx level st.lab st.ptn st.active numcells
      let pre := otherNodePrep level r.longcode { st with
        lab := r.lab, ptn := r.ptn, active := r.active
        numnodes := st.numnodes + 1 }
      let mt := maketargetcell ctx pre.lab pre.ptn level tcLevel (-1)
      let base := { pre with tctotal := pre.tctotal + mt.2.2 }
      cheapautom (processnode ctx level r.numcells base).2.ptn
        level ctx.n = false) :
    let r := refine ctx level st.lab st.ptn st.active numcells
    let pre := otherNodePrep level r.longcode { st with
      lab := r.lab, ptn := r.ptn, active := r.active
      numnodes := st.numnodes + 1 }
    let mt := maketargetcell ctx pre.lab pre.ptn level tcLevel (-1)
    let base := { pre with tctotal := pre.tctotal + mt.2.2 }
    let pr := processnode ctx level r.numcells base
    let parked := { pr.2 with noncheaplevel := level + 1 }
    let L := otherChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
      r.numcells mt.1 ((nextElem mt.2.1 none).getD 0)
      (nextElem mt.2.1 none) mt.2.1 parked
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      if pr.1 < Int.ofNat level then pr
      else match L.1 with
        | some rtn => (rtn, L.2)
        | none => (Int.ofNat level - 1, L.2) := by
  dsimp only at hnonneg hshort hcheap ⊢
  rw [otherNode]
  simp only [hnum, true_and, ne_eq, ite_eq_left (Or.inr hnonneg),
    ite_eq_right (by omega : ¬((otherNodePrep level
      (refine ctx level st.lab st.ptn st.active numcells).longcode
      { st with
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
        active := (refine ctx level st.lab st.ptn st.active numcells).active
        numnodes := st.numnodes + 1 }).compCanon < 0)),
    hshort, Bool.false_eq_true, ite_false, hcheap,
    Int.ofNat_eq_natCast, Int.toNat_natCast]
  generalize hL : (otherChildLoop ctx inf tcLevel fuel (ctx.n + 1)
    level _ _ _ _ _ _) = L
  rcases L with ⟨r, out⟩
  cases r <;> simp only [Id.run_pure, apply_ite Id.run] <;> rfl

end LoopInv

end Hex.GraphIso.Nauty
