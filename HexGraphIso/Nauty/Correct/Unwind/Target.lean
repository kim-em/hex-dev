/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Outcome

public section

/-!
Where an early return is consumed, and what a generator must stabilize
on the way there.

A direct unwind names the frozen child-loop frame it targets by an
explicit anchor, since the executable state does not retain a parent
loop's refined labelling; an orbit unwind resolves through the receiving
loop's evolving coverage instead.  `ReturnStab` states generator
stabilization at the executable return level.
-/

/-!
Consumption rules for search unwinds at their target child loop.

The executable state does not retain a parent loop's refined labelling:
`recover` reopens the partition but deliberately leaves the descendant
labelling in `SearchSt n`.  A direct unwind therefore needs an explicit
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
@[expose] def Anchor.frame {ctx : Ctx n} {tcLevel level : Nat}
    {best : Option (Key n)} (a : Anchor ctx tcLevel level best) : SweepFrame :=
  ⟨a.specFuel, a.codes, a.rsLab, a.rsPtn, a.tc, a.numcells⟩

/-- The immutable frame named by a generator guide. -/
@[expose] def Guide.frame {ctx : Ctx n} {tcLevel level : Nat}
    {best : Option (Key n)} (g : Guide ctx tcLevel level best) : SweepFrame :=
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
structure TrailOk (ctx : Ctx n) (level : Nat) (st : SearchSt n)
    (trail : FrameTrail) : Prop where
  reach : ∀ target entry, target < level → trail target = some entry →
    cellsPerm entry.frame.rsPtn target entry.frame.rsLab st.lab
  ptnSize : ∀ target entry, target < level → trail target = some entry →
    entry.frame.rsPtn.size = n
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
theorem TrailOk.empty (ctx : Ctx n) (level : Nat) (st : SearchSt n) :
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
@[expose] def Anchor.Located {ctx : Ctx n} {tcLevel level : Nat}
    {best : Option (Key n)} (trail : FrameTrail)
    (a : Anchor ctx tcLevel level best) : Prop :=
  trail level = some ⟨a.frame, a.offset⟩

/-- A guide names the active frame at its target. -/
@[expose] def Guide.Located {ctx : Ctx n} {tcLevel level : Nat}
    {best : Option (Key n)} (trail : FrameTrail)
    (g : Guide ctx tcLevel level best) : Prop :=
  ∃ entry, trail level = some entry ∧ entry.frame = g.frame

/-- Adding a different, deeper active child preserves an older anchor's
location. -/
theorem Anchor.Located.push {ctx : Ctx n} {tcLevel target level : Nat}
    {best : Option (Key n)} {trail : FrameTrail}
    {a : Anchor ctx tcLevel target best} {entry : TrailEntry}
    (h : a.Located trail) (hne : target ≠ level) :
    a.Located (trail.push level entry) := by
  change trail.push level entry target = some ⟨a.frame, a.offset⟩
  rw [FrameTrail.push_of_ne _ entry hne]
  exact h

/-- Adding a different, deeper active child preserves a guide's frame
location. -/
theorem Guide.Located.push {ctx : Ctx n} {tcLevel target level : Nat}
    {best : Option (Key n)} {trail : FrameTrail}
    {g : Guide ctx tcLevel target best} {entry : TrailEntry}
    (h : g.Located trail) (hne : target ≠ level) :
    g.Located (trail.push level entry) := by
  obtain ⟨old, hold, hframe⟩ := h
  exact ⟨old, by rw [FrameTrail.push_of_ne _ entry hne]; exact hold,
    hframe⟩

/-- A guide for the newly pushed frame is located there immediately;
the active descent offset need not be the guide's own explored offset. -/
theorem Guide.Located.pushSelf {ctx : Ctx n} {tcLevel level : Nat}
    {best : Option (Key n)} (trail : FrameTrail)
    (g : Guide ctx tcLevel level best) (offset : Nat) :
    g.Located (trail.push level ⟨g.frame, offset⟩) := by
  exact ⟨⟨g.frame, offset⟩, FrameTrail.push_self _ _ _, rfl⟩

/-- A located guide's ancestor frame reaches the current labelling. -/
theorem Guide.reachAt {ctx : Ctx n} {tcLevel target level : Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (g : Guide ctx tcLevel target best) (hloc : g.Located trail)
    (hok : TrailOk ctx level st trail) (hlt : target < level) :
    cellsPerm g.rsPtn target g.rsLab st.lab := by
  obtain ⟨entry, hentry, hframe⟩ := hloc
  have hreach := hok.reach target entry hlt hentry
  rw [hframe] at hreach
  exact hreach

/-- A located guide identifies the exact active ancestor child followed
by the current descent. -/
theorem Guide.active {ctx : Ctx n} {tcLevel target level : Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
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
theorem Guide.locateAnchor {ctx : Ctx n} {tcLevel level : Nat}
    {before best : Option (Key n)} (trail : FrameTrail)
    (g : Guide ctx tcLevel level before)
    {oCur : Nat} (hentry : trail level = some ⟨g.frame, oCur⟩)
    (hgsz : ctx.g.size = n) (hinc : IncGrows before best)
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
theorem Guide.locateAnchorCell {ctx : Ctx n} {tcLevel level : Nat}
    {before best : Option (Key n)} (trail : FrameTrail)
    (g : Guide ctx tcLevel level before)
    {oCur : Nat} (hentry : trail level = some ⟨g.frame, oCur⟩)
    (hgsz : ctx.g.size = n) (hinc : IncGrows before best)
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
inductive Unwind.Located (trail : FrameTrail) {ctx : Ctx n} {tcLevel target : Nat}
    {out : SearchSt n} {best : Option (Key n)} :
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
inductive Unwind.FrameStable {ctx : Ctx n} {tcLevel target : Nat}
    {out : SearchSt n} {best : Option (Key n)}
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
theorem Unwind.Located.push {ctx : Ctx n} {tcLevel target level : Nat}
    {out : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
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
structure Anchor.At {ctx : Ctx n} {tcLevel level : Nat}
    {best : Option (Key n)} (a : Anchor ctx tcLevel level best)
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
theorem Anchor.at_of_loc {ctx : Ctx n} {tcLevel level specFuel tc numcells : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {best : Option (Key n)}
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
theorem Anchor.offset_of_loc {ctx : Ctx n} {tcLevel level : Nat}
    {best : Option (Key n)} {trail : FrameTrail} {frame : SweepFrame}
    {offset : Nat} (a : Anchor ctx tcLevel level best)
    (hloc : a.Located trail)
    (hframe : trail level = some ⟨frame, offset⟩) :
    a.offset = offset := by
  change trail level = some ⟨a.frame, a.offset⟩ at hloc
  exact congrArg TrailEntry.offset
    (Option.some.inj (hloc.symm.trans hframe))

/-- A located anchor supplies coverage of its stored child offset in the
receiving loop's frame. -/
theorem Anchor.doneAt {ctx : Ctx n} {tcLevel level specFuel tc numcells : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat} {best : Option (Key n)}
    (a : Anchor ctx tcLevel level best)
    (h : a.At specFuel codes rsLab rsPtn tc numcells) :
    ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc numcells
      best a.offset := by
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact a.done

/-- A direct generator anchor addressed to this loop advances coverage
past the current child. -/
theorem SweepCover.anchor {ctx : Ctx n}
    {tcLevel specFuel level tc len numcells : Nat} {tcell : VSet n} {tv : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option (Key n)}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : tcell.nextElem cursor = some tv)
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
theorem SweepCover.locatedAnchor {ctx : Ctx n}
    {tcLevel specFuel level tc len numcells : Nat} {tcell : VSet n} {tv offset : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option (Key n)}
    {trail : FrameTrail}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : tcell.nextElem cursor = some tv)
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
theorem SweepCover.orbitUnwind {ctx : Ctx n}
    {tcLevel specFuel level tc len numcells : Nat} {tcell : VSet n} {tv o : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option (Key n)} {out : SearchSt n}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : tcell.nextElem cursor = some tv)
    (ho : o < len) (htv : rsLab[tc + o]! = tv)
    (payload : OrbitUnwind ctx level out)
    (hcoset : out.cosetindex = tv)
    (hgsz : ctx.g.size = n)
    (hv : ∀ γ ∈ out.genTrace.toList,
      checkAutom ctx.g γ = true)
    (hstab : ∀ γ ∈ out.genTrace.toList,
      CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hinj : LabInj rsLab rsLab.size)
    (hok : LabOk rsLab n) (hsp : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hlf : level + 1 + specFuel ≤ n + 1) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) best := by
  have hne : out.orbits[tv]! ≠ tv := by
    rw [← hcoset]
    exact Nat.ne_of_lt payload.smaller
  exact (h.grow hinc).orbitSkip hnext ho htv hgsz hv hstab hs hinj
    hok hsp hend hvals hic hrange hlf payload.sound hne

/-- Every located generator unwind addressed to this loop consumes the
active child.  Direct carriers use their stored frame and offset; the
special code-two arm uses its sound orbit pointer. -/
theorem SweepCover.unwind {ctx : Ctx n}
    {tcLevel specFuel level tc len numcells : Nat} {tcell : VSet n} {tv offset : Nat}
    {codes : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {before best : Option (Key n)} {out : SearchSt n}
    {trail : FrameTrail} {payload : Unwind ctx tcLevel level out best}
    (h : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell cursor before)
    (hinc : IncGrows before best)
    (hnext : tcell.nextElem cursor = some tv)
    (hloc : payload.Located trail)
    (hframe : trail level = some
      ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
    (ho : offset < len) (htv : rsLab[tc + offset]! = tv)
    (hcoset : out.cosetindex = tv)
    (hgsz : ctx.g.size = n)
    (hv : ∀ γ ∈ out.genTrace.toList,
      checkAutom ctx.g γ = true)
    (hstab : payload.FrameStable rsPtn level rsLab)
    (hs : rsLab.size = n) (hinj : LabInj rsLab rsLab.size)
    (hok : LabOk rsLab n) (hsp : rsPtn.size = n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ n)
    (hlf : level + 1 + specFuel ≤ n + 1) :
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
          exact h.orbitUnwind hinc hnext ho htv orbitPayload hcoset hgsz
            hv stable hs hinj hok hsp hend hvals hic hrange hlf

end Hex.GraphIso.Nauty

/-!
Generator stabilization indexed by the executable return level.

A generator present after a recursive call need not stabilize every
intermediate node crossed by an early unwind.  It must stabilize precisely
the active ancestor frames at or below the returned level.  This is the
form needed both when a first-path loop continues and when an orbit unwind
lands at its target frame.
-/

namespace Hex.GraphIso.Nauty

/-- Every recorded generator stabilizes each active frame that the return
level permits the caller to resume. -/
@[expose] def ReturnStab (trail : FrameTrail) (r : Int)
    (st : SearchSt n) : Prop :=
  ∀ level entry, Int.ofNat level ≤ r → trail level = some entry →
    ∀ γ ∈ st.genTrace.toList,
      CellStab entry.frame.rsPtn level entry.frame.rsLab γ

namespace ReturnStab

/-- Lowering the advertised return level weakens the stabilization
obligation. -/
theorem lower {trail : FrameTrail} {r r' : Int} {st : SearchSt n}
    (h : ReturnStab trail r st) (hle : r' ≤ r) :
    ReturnStab trail r' st := by
  intro level entry hlevel hentry γ hγ
  exact h level entry (Int.le_trans hlevel hle) hentry γ hγ

/-- A state with no recorded generators satisfies every return frame. -/
theorem empty {trail : FrameTrail} {r : Int} {st : SearchSt n}
    (h : st.genTrace = #[]) : ReturnStab trail r st := by
  intro level entry hlevel hentry γ hγ
  rw [h] at hγ
  simp at hγ

/-- Return stabilization depends only on the recorded-generator store. -/
theorem ofGenTraceEq {trail : FrameTrail} {r : Int} {st out : SearchSt n}
    (h : ReturnStab trail r st) (heq : out.genTrace = st.genTrace) :
    ReturnStab trail r out := by
  intro level entry hlevel hentry γ hγ
  apply h level entry hlevel hentry γ
  rwa [heq] at hγ

/-- Fixed-point bookkeeping does not affect return stabilization. -/
theorem setFixed {trail : FrameTrail} {r : Int} {st : SearchSt n}
    (h : ReturnStab trail r st) (fixedpts : VSet n) :
    ReturnStab trail r { st with fixedpts := fixedpts } := by
  unfold ReturnStab at h ⊢
  exact h

/-- First-path return bookkeeping does not affect the generator store or
the ancestor frames it stabilizes. -/
theorem setFirst {trail : FrameTrail} {r : Int} {st : SearchSt n}
    (h : ReturnStab trail r st) (gcaFirst stabvertex : Nat) :
    ReturnStab trail r
      { st with gcaFirst := gcaFirst, stabvertex := stabvertex } := by
  unfold ReturnStab at h ⊢
  exact h

/-- Clearing the one-shot short-prune flag does not affect stabilization. -/
theorem clearShort {trail : FrameTrail} {r : Int} {st : SearchSt n}
    (h : ReturnStab trail r st) :
    ReturnStab trail r { st with needshortprune := false } := by
  unfold ReturnStab at h ⊢
  exact h

/-- Updating the first-path agreement counter does not affect generator
stabilization. -/
theorem setAllsame {trail : FrameTrail} {r : Int} {st : SearchSt n}
    (h : ReturnStab trail r st) (allsamelevel : Nat) :
    ReturnStab trail r { st with allsamelevel := allsamelevel } := by
  unfold ReturnStab at h ⊢
  exact h

/-- Recovering a parent changes no recorded generator, so it preserves
every return-indexed stabilization obligation. -/
theorem recover {trail : FrameTrail} {r : Int} {st : SearchSt n}
    (h : ReturnStab trail r st) (inf level : Nat) :
    ReturnStab trail r (Nauty.recover n inf level st) := by
  intro target entry htarget hentry γ hγ
  apply h target entry htarget hentry γ
  have hstore := recover_store n inf level st
  rwa [hstore.1] at hγ

/-- Appending one generator preserves return stabilization when the old
store already satisfies it and the new generator stabilizes every
resumable frame. -/
theorem pushGen {trail : FrameTrail} {r : Int} {st out : SearchSt n}
    {gamma : Array Nat} (h : ReturnStab trail r st)
    (hpush : out.genTrace = st.genTrace.push gamma)
    (hnew : ∀ level entry, Int.ofNat level ≤ r →
      trail level = some entry →
      CellStab entry.frame.rsPtn level entry.frame.rsLab gamma) :
    ReturnStab trail r out := by
  intro level entry hlevel hentry delta hdelta
  rw [hpush, Array.toList_push] at hdelta
  rcases List.mem_append.mp hdelta with hold | hlast
  · exact h level entry hlevel hentry delta hold
  · have heq : delta = gamma := by simpa using hlast
    subst delta
    exact hnew level entry hlevel hentry

/-- Pushing a child frame preserves all older return obligations.  The
new frame is required only when the return reaches it. -/
theorem push {trail : FrameTrail} {r : Int} {st : SearchSt n}
    {level : Nat} {entry : TrailEntry}
    (h : ReturnStab trail r st)
    (hnew : Int.ofNat level ≤ r → ∀ γ ∈ st.genTrace.toList,
      CellStab entry.frame.rsPtn level entry.frame.rsLab γ) :
    ReturnStab (trail.push level entry) r st := by
  intro target found htarget hfound γ hγ
  rcases Decidable.em (target = level) with rfl | hne
  · have heq : found = entry := by
      rw [FrameTrail.push_self] at hfound
      exact Option.some.inj hfound.symm
    subst found
    exact hnew htarget γ hγ
  · exact h target found htarget (by
      rwa [FrameTrail.push_of_ne trail entry hne] at hfound) γ hγ

/-- At the exact target of a located unwind, return stabilization supplies
the store-wide premise needed by the orbit constructor.  Direct carrier
unwinds are frame-stable without a store-wide premise. -/
theorem frameStable {trail : FrameTrail} {ctx : Ctx n}
    {tcLevel target : Nat} {out : SearchSt n} {best : Option (Key n)}
    {payload : Unwind ctx tcLevel target out best} {entry : TrailEntry}
    (hret : ReturnStab trail
      (min (Int.ofNat target) (Int.ofNat out.gcaFirst)) out)
    (hentry : trail target = some entry) :
    payload.FrameStable entry.frame.rsPtn target entry.frame.rsLab := by
  cases payload with
  | first anchor carrier => exact .first anchor carrier
  | canon anchor carrier => exact .canon anchor carrier
  | orbit payload =>
      apply Unwind.FrameStable.orbit payload
      intro γ hγ
      exact hret target entry (by
        have hb : Int.ofNat target ≤ Int.ofNat out.gcaFirst :=
          Int.ofNat_le.mpr payload.bound
        omega) hentry γ hγ

end ReturnStab

end Hex.GraphIso.Nauty
