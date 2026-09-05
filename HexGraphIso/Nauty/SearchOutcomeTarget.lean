/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcome

public section

/-!
Consumption rules for search unwinds at their target child loop.

The executable state does not retain a parent loop's refined labelling:
`recover` reopens the partition but deliberately leaves the descendant
labelling in `SearchSt`.  A direct unwind therefore needs an explicit
relation between its stored anchor and the frozen loop frame.  Orbit
unwinds instead resolve through the receiving loop's evolving coverage.
-/

namespace Hex.GraphIso.Nauty

/-- The immutable specification data of one active child-loop frame. -/
structure SweepFrame where
  specFuel : Nat
  codes : List Nat
  rsLab : Array Nat
  rsPtn : Array Nat
  tc : Nat
  numcells : Nat

/-- Package the immutable parameters of a concrete child-loop call. -/
@[expose] def sweepFrame (specFuel : Nat) (codes : List Nat)
    (rsLab rsPtn : Array Nat) (tc numcells : Nat) : SweepFrame :=
  ⟨specFuel, codes, rsLab, rsPtn, tc, numcells⟩

/-- The frame stored by a direct unwind anchor. -/
@[expose] def Anchor.frame {ctx : Ctx} {tcLevel level : Nat}
    {best : Option Key} (a : Anchor ctx tcLevel level best) : SweepFrame :=
  ⟨a.specFuel, a.codes, a.rsLab, a.rsPtn, a.tc, a.numcells⟩

/-- The immutable frame named by a generator guide. -/
@[expose] def Guide.frame {ctx : Ctx} {tcLevel level : Nat}
    {best : Option Key} (g : Guide ctx tcLevel level best) : SweepFrame :=
  ⟨g.specFuel, g.codes, g.rsLab, g.rsPtn, g.tc, g.numcells⟩

/-- One active ancestor frame together with the child offset followed by
the current descent. -/
structure TrailEntry where
  frame : SweepFrame
  offset : Nat

/-- Active ancestor children, keyed by their parent search level. -/
abbrev FrameTrail := Nat → Option TrailEntry

/-- The empty active-frame trail. -/
@[expose] def FrameTrail.empty : FrameTrail := fun _ => none

/-- Every active ancestor frame reaches the current labelling, and its
closed boundaries remain frozen in the current partition. -/
structure TrailOk (ctx : Ctx) (level : Nat) (st : SearchSt)
    (trail : FrameTrail) : Prop where
  reach : ∀ target entry, target < level → trail target = some entry →
    cellsPerm entry.frame.rsPtn target entry.frame.rsLab st.lab
  ptnSize : ∀ target entry, target < level → trail target = some entry →
    entry.frame.rsPtn.size = ctx.n
  endClosed : ∀ target entry, target < level →
    trail target = some entry →
    entry.frame.rsPtn[entry.frame.rsPtn.size - 1]! ≤ target
  frozen : ∀ target entry, target < level →
    trail target = some entry → ∀ q : Nat,
    entry.frame.rsPtn[q]! ≤ target →
    st.ptn[q]! = entry.frame.rsPtn[q]!
  picked : ∀ target entry, target < level →
    trail target = some entry →
    ∃ len, IsCell entry.frame.rsPtn target entry.frame.tc len ∧
      entry.offset < len ∧
      st.ptn[entry.frame.tc]! = target + 1 ∧
      IsCell st.ptn level entry.frame.tc 1 ∧
      st.lab[entry.frame.tc]! =
        entry.frame.rsLab[entry.frame.tc + entry.offset]!

/-- No ancestor frame is present in the empty trail. -/
theorem TrailOk.empty (ctx : Ctx) (level : Nat) (st : SearchSt) :
    TrailOk ctx level st FrameTrail.empty := by
  constructor <;> intro target entry _ hentry
  all_goals simp [FrameTrail.empty] at hentry

/-- Record the active child of one parent level. -/
@[expose] def FrameTrail.push (trail : FrameTrail) (level : Nat)
    (entry : TrailEntry) : FrameTrail :=
  fun q => if q = level then some entry else trail q

@[simp] theorem FrameTrail.push_self (trail : FrameTrail) (level : Nat)
    (entry : TrailEntry) : trail.push level entry level = some entry := by
  simp [FrameTrail.push]

theorem FrameTrail.push_of_ne (trail : FrameTrail) {level q : Nat}
    (entry : TrailEntry) (hne : q ≠ level) :
    trail.push level entry q = trail q := by
  simp [FrameTrail.push, hne]

/-- A direct anchor was created from the active frame at its target. -/
@[expose] def Anchor.Located {ctx : Ctx} {tcLevel level : Nat}
    {best : Option Key} (trail : FrameTrail)
    (a : Anchor ctx tcLevel level best) : Prop :=
  trail level = some ⟨a.frame, a.offset⟩

/-- A guide names the active frame at its target. -/
@[expose] def Guide.Located {ctx : Ctx} {tcLevel level : Nat}
    {best : Option Key} (trail : FrameTrail)
    (g : Guide ctx tcLevel level best) : Prop :=
  ∃ entry, trail level = some entry ∧ entry.frame = g.frame

/-- Adding a different, deeper active child preserves an older anchor's
location. -/
theorem Anchor.Located.push {ctx : Ctx} {tcLevel target level : Nat}
    {best : Option Key} {trail : FrameTrail}
    {a : Anchor ctx tcLevel target best} {entry : TrailEntry}
    (h : a.Located trail) (hne : target ≠ level) :
    a.Located (trail.push level entry) := by
  change trail.push level entry target = some ⟨a.frame, a.offset⟩
  rw [FrameTrail.push_of_ne _ entry hne]
  exact h

/-- Adding a different, deeper active child preserves a guide's frame
location. -/
theorem Guide.Located.push {ctx : Ctx} {tcLevel target level : Nat}
    {best : Option Key} {trail : FrameTrail}
    {g : Guide ctx tcLevel target best} {entry : TrailEntry}
    (h : g.Located trail) (hne : target ≠ level) :
    g.Located (trail.push level entry) := by
  obtain ⟨old, hold, hframe⟩ := h
  exact ⟨old, by rw [FrameTrail.push_of_ne _ entry hne]; exact hold,
    hframe⟩

/-- A guide for the newly pushed frame is located there immediately;
the active descent offset need not be the guide's own explored offset. -/
theorem Guide.Located.pushSelf {ctx : Ctx} {tcLevel level : Nat}
    {best : Option Key} (trail : FrameTrail)
    (g : Guide ctx tcLevel level best) (offset : Nat) :
    g.Located (trail.push level ⟨g.frame, offset⟩) := by
  exact ⟨⟨g.frame, offset⟩, FrameTrail.push_self _ _ _, rfl⟩

/-- A located guide's ancestor frame reaches the current labelling. -/
theorem Guide.reachAt {ctx : Ctx} {tcLevel target level : Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (g : Guide ctx tcLevel target best) (hloc : g.Located trail)
    (hok : TrailOk ctx level st trail) (hlt : target < level) :
    cellsPerm g.rsPtn target g.rsLab st.lab := by
  obtain ⟨entry, hentry, hframe⟩ := hloc
  have hreach := hok.reach target entry hlt hentry
  rw [hframe] at hreach
  exact hreach

/-- A located guide identifies the exact active ancestor child followed
by the current descent. -/
theorem Guide.active {ctx : Ctx} {tcLevel target level : Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (g : Guide ctx tcLevel target best) (hloc : g.Located trail)
    (hok : TrailOk ctx level st trail) (hlt : target < level) :
    ∃ o, trail target = some ⟨g.frame, o⟩ ∧ o < g.len ∧
      st.lab[g.tc]! = g.rsLab[g.tc + o]! := by
  obtain ⟨entry, hentry, hframe⟩ := hloc
  obtain ⟨len, hcell, hoff, _, _, hat⟩ :=
    hok.picked target entry hlt hentry
  rw [hframe] at hcell hat
  change IsCell g.rsPtn target g.tc len at hcell
  change st.lab[g.tc]! = g.rsLab[g.tc + entry.offset]! at hat
  have hlen : len = g.len := by
    rcases isCell_disjoint_or_eq hcell g.cell with hleft | hright | heq
    · have := g.cell.1
      omega
    · have := hcell.1
      omega
    · exact heq.2
  subst len
  refine ⟨entry.offset, ?_, hoff, hat⟩
  calc
    trail target = some entry := hentry
    _ = some ⟨g.frame, entry.offset⟩ := by
      congr 1
      cases entry with
      | mk frame offset =>
          simp only at hframe ⊢
          subst frame
          rfl

/-- Location evidence follows a guide when a checked carrier turns it
into an unwind anchor. -/
theorem Guide.locateAnchor {ctx : Ctx} {tcLevel level : Nat}
    {before best : Option Key} (trail : FrameTrail)
    (g : Guide ctx tcLevel level before)
    {oCur : Nat} (hentry : trail level = some ⟨g.frame, oCur⟩)
    (hgsz : ctx.g.size = ctx.n) (hinc : IncGrows before best)
    {cur : Array Nat} {store : Array (Array Nat)}
    (hcarrier : LabelCarrier ctx g.ref cur store)
    (hstab : ∀ γ ∈ store, CellStab g.rsPtn level g.rsLab γ)
    (hcur : oCur < g.len)
    (hatCur : cur[g.tc]! = g.rsLab[g.tc + oCur]!) :
    (g.anchor hgsz hinc hcarrier hstab hcur hatCur).Located trail := by
  change trail level = some
    ⟨(g.anchor hgsz hinc hcarrier hstab hcur hatCur).frame,
      (g.anchor hgsz hinc hcarrier hstab hcur hatCur).offset⟩
  rw [hentry]
  congr

/-- Location evidence follows a witness-local carrier into its direct
unwind anchor. -/
theorem Guide.locateAnchorCell {ctx : Ctx} {tcLevel level : Nat}
    {before best : Option Key} (trail : FrameTrail)
    (g : Guide ctx tcLevel level before)
    {oCur : Nat} (hentry : trail level = some ⟨g.frame, oCur⟩)
    (hgsz : ctx.g.size = ctx.n) (hinc : IncGrows before best)
    {cur : Array Nat} {store : Array (Array Nat)}
    (hcarrier : CellCarrier ctx g.rsPtn level g.rsLab g.ref cur store)
    (hcur : oCur < g.len)
    (hatCur : cur[g.tc]! = g.rsLab[g.tc + oCur]!) :
    (g.anchorCell hgsz hinc hcarrier hcur hatCur).Located trail := by
  change trail level = some
    ⟨(g.anchorCell hgsz hinc hcarrier hcur hatCur).frame,
      (g.anchorCell hgsz hinc hcarrier hcur hatCur).offset⟩
  rw [hentry]
  congr

/-- Location evidence attached to each direct unwind constructor.  Orbit
unwinds use only the target loop's own frame and need no stored frame. -/
inductive Unwind.Located (trail : FrameTrail) {ctx : Ctx} {tcLevel target : Nat}
    {out : SearchSt} {best : Option Key} :
    Unwind ctx tcLevel target out best → Prop where
  | first (anchor : Anchor ctx tcLevel target best)
      (carrier : LabelCarrier ctx out.firstlab out.lab out.genTrace)
      (located : anchor.Located trail) :
      Unwind.Located trail (.first anchor carrier)
  | canon (anchor : Anchor ctx tcLevel target best)
      (carrier : LabelCarrier ctx out.canonlab out.lab out.genTrace)
      (located : anchor.Located trail) :
      Unwind.Located trail (.canon anchor carrier)
  | orbit (payload : OrbitUnwind ctx target out) :
      Unwind.Located trail (.orbit payload)

/-- The frame-local condition needed to consume an unwind.  Direct
unwinds already carry a checked cell carrier in their anchor, while the
orbit-pointer arm relies on every admitted generator stabilizing the
receiving cell. -/
inductive Unwind.FrameStable {ctx : Ctx} {tcLevel target : Nat}
    {out : SearchSt} {best : Option Key}
    (rsPtn : Array Nat) (level : Nat) (rsLab : Array Nat) :
    Unwind ctx tcLevel target out best → Prop where
  | first (anchor : Anchor ctx tcLevel target best)
      (carrier : LabelCarrier ctx out.firstlab out.lab out.genTrace) :
      Unwind.FrameStable rsPtn level rsLab (.first anchor carrier)
  | canon (anchor : Anchor ctx tcLevel target best)
      (carrier : LabelCarrier ctx out.canonlab out.lab out.genTrace) :
      Unwind.FrameStable rsPtn level rsLab (.canon anchor carrier)
  | orbit (payload : OrbitUnwind ctx target out)
      (stable : ∀ γ ∈ out.genTrace.toList,
        CellStab rsPtn level rsLab γ) :
      Unwind.FrameStable rsPtn level rsLab (.orbit payload)

/-- Extending the trail at a different, deeper level preserves the source
location of a transported unwind. -/
theorem Unwind.Located.push {ctx : Ctx} {tcLevel target level : Nat}
    {out : SearchSt} {best : Option Key} {trail : FrameTrail}
    {payload : Unwind ctx tcLevel target out best} {entry : TrailEntry}
    (h : payload.Located trail) (hne : target ≠ level) :
    payload.Located (trail.push level entry) := by
  cases h with
  | first anchor carrier located =>
      exact .first anchor carrier (located.push hne)
  | canon anchor carrier located =>
      exact .canon anchor carrier (located.push hne)
  | orbit payload => exact .orbit payload

/-- An unwind anchor belongs to the indicated frozen child-loop frame. -/
structure Anchor.At {ctx : Ctx} {tcLevel level : Nat}
    {best : Option Key} (a : Anchor ctx tcLevel level best)
    (specFuel : Nat) (codes : List Nat) (rsLab rsPtn : Array Nat)
    (tc numcells : Nat) : Prop where
  fuel : a.specFuel = specFuel
  codePath : a.codes = codes
  lab : a.rsLab = rsLab
  ptn : a.rsPtn = rsPtn
  cell : a.tc = tc
  cells : a.numcells = numcells

/-- Looking up the same active frame as a located anchor identifies all
of the frozen loop parameters required to consume it. -/
theorem Anchor.at_of_loc {ctx : Ctx} {tcLevel level specFuel tc numcells : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {best : Option Key}
    {trail : FrameTrail} {offset : Nat}
    (a : Anchor ctx tcLevel level best)
    (hloc : a.Located trail)
    (hframe : trail level = some
      ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) :
    a.At specFuel codes rsLab rsPtn tc numcells := by
  change trail level = some ⟨a.frame, a.offset⟩ at hloc
  have heq : a.frame = sweepFrame specFuel codes rsLab rsPtn tc numcells :=
    congrArg TrailEntry.frame (Option.some.inj (hloc.symm.trans hframe))
  constructor
  · simpa only [Anchor.frame, sweepFrame] using
      congrArg SweepFrame.specFuel heq
  · simpa only [Anchor.frame, sweepFrame] using
      congrArg SweepFrame.codes heq
  · simpa only [Anchor.frame, sweepFrame] using
      congrArg SweepFrame.rsLab heq
  · simpa only [Anchor.frame, sweepFrame] using
      congrArg SweepFrame.rsPtn heq
  · simpa only [Anchor.frame, sweepFrame] using
      congrArg SweepFrame.tc heq
  · simpa only [Anchor.frame, sweepFrame] using
      congrArg SweepFrame.numcells heq

/-- A located anchor follows the child offset recorded by the active
descent at its target. -/
theorem Anchor.offset_of_loc {ctx : Ctx} {tcLevel level : Nat}
    {best : Option Key} {trail : FrameTrail} {frame : SweepFrame}
    {offset : Nat} (a : Anchor ctx tcLevel level best)
    (hloc : a.Located trail)
    (hframe : trail level = some ⟨frame, offset⟩) :
    a.offset = offset := by
  change trail level = some ⟨a.frame, a.offset⟩ at hloc
  exact congrArg TrailEntry.offset
    (Option.some.inj (hloc.symm.trans hframe))

/-- A located anchor supplies coverage of its stored child offset in the
receiving loop's frame. -/
theorem Anchor.doneAt {ctx : Ctx} {tcLevel level specFuel tc numcells : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {best : Option Key}
    (a : Anchor ctx tcLevel level best)
    (h : a.At specFuel codes rsLab rsPtn tc numcells) :
    ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc numcells
      best a.offset := by
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact a.done

/-- A direct generator anchor addressed to this loop advances coverage
past the current child. -/
theorem SweepCover.anchor {ctx : Ctx}
    {tcLevel specFuel level tc len numcells tcell tv : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option Key}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : nextElem tcell cursor = some tv)
    (a : Anchor ctx tcLevel level best)
    (hat : a.At specFuel codes rsLab rsPtn tc numcells)
    (htv : rsLab[tc + a.offset]! = tv)
    (hinj : LabInj rsLab rsLab.size)
    (hrange : tc + len ≤ rsLab.size)
    (hoff : tc + a.offset < rsLab.size) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) best := by
  have hgrown := h.grow hinc
  apply hgrown.advance hnext
  · intro o ho heq
    have hidx : tc + o = tc + a.offset := hinj.eq
      (by omega) hoff (heq.trans htv.symm)
    have : o = a.offset := by omega
    subst o
    exact a.doneAt hat
  · intro _ hdone
    exact hdone

/-- A located direct anchor consumes the active child named by the target
trail entry. -/
theorem SweepCover.locatedAnchor {ctx : Ctx}
    {tcLevel specFuel level tc len numcells tcell tv offset : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option Key}
    {trail : FrameTrail}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : nextElem tcell cursor = some tv)
    (a : Anchor ctx tcLevel level best) (hloc : a.Located trail)
    (hframe : trail level = some
      ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
    (htv : rsLab[tc + offset]! = tv)
    (hinj : LabInj rsLab rsLab.size)
    (hrange : tc + len ≤ rsLab.size)
    (hoff : tc + offset < rsLab.size) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) best := by
  have hoffset := a.offset_of_loc hloc hframe
  apply h.anchor hinc hnext a (a.at_of_loc hloc hframe)
  · rwa [hoffset]
  · exact hinj
  · exact hrange
  · rwa [hoffset]

/-- An orbit unwind addressed to this loop advances coverage through its
strictly smaller, sound pointer. -/
theorem SweepCover.orbitUnwind {ctx : Ctx}
    {tcLevel specFuel level tc len numcells tcell tv o : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option Key} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : nextElem tcell cursor = some tv)
    (ho : o < len) (htv : rsLab[tc + o]! = tv)
    (payload : OrbitUnwind ctx level out)
    (hcoset : out.cosetindex = tv)
    (hgsz : ctx.g.size = ctx.n)
    (hbg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hv : ∀ γ ∈ out.genTrace.toList,
      checkAutom ctx.g γ ctx.n = true)
    (hstab : ∀ γ ∈ out.genTrace.toList,
      CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = ctx.n) (hinj : LabInj rsLab rsLab.size)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) best := by
  have hne : out.orbits[tv]! ≠ tv := by
    rw [← hcoset]
    exact Nat.ne_of_lt payload.smaller
  exact (h.grow hinc).orbitSkip hnext ho htv hgsz hbg hv hstab hs hinj
    hok hsp hend hvals hic hrange hlf payload.sound hne

/-- Every located generator unwind addressed to this loop consumes the
active child.  Direct carriers use their stored frame and offset; the
special code-two arm uses its sound orbit pointer. -/
theorem SweepCover.unwind {ctx : Ctx}
    {tcLevel specFuel level tc len numcells tcell tv offset : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option Key} {out : SearchSt}
    {trail : FrameTrail} {payload : Unwind ctx tcLevel level out best}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : nextElem tcell cursor = some tv)
    (hloc : payload.Located trail)
    (hframe : trail level = some
      ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
    (ho : offset < len) (htv : rsLab[tc + offset]! = tv)
    (hcoset : out.cosetindex = tv)
    (hgsz : ctx.g.size = ctx.n)
    (hbg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hv : ∀ γ ∈ out.genTrace.toList,
      checkAutom ctx.g γ ctx.n = true)
    (hstab : payload.FrameStable rsPtn level rsLab)
    (hs : rsLab.size = ctx.n) (hinj : LabInj rsLab rsLab.size)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) best := by
  have hrange' : tc + len ≤ rsLab.size := by rwa [hs]
  have hoff : tc + offset < rsLab.size := by omega
  cases hloc with
  | first anchor carrier located =>
      exact h.locatedAnchor hinc hnext anchor located hframe htv hinj
        hrange' hoff
  | canon anchor carrier located =>
      exact h.locatedAnchor hinc hnext anchor located hframe htv hinj
        hrange' hoff
  | orbit orbitPayload =>
      cases hstab with
      | orbit _ stable =>
          exact h.orbitUnwind hinc hnext ho htv orbitPayload hcoset hgsz hbg
            hv stable hs hinj hok hsp hend hvals hic hrange hlf

end Hex.GraphIso.Nauty
