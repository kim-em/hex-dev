/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeLoop
public import HexGraphIso.Nauty.SearchOutcomeReturn

public section

/-!
The result-side state shared by recursive node outcomes.

The executable can return a state whose comparison path is deeper than
the caller receiving it.  `EventOut` existentially records that full path,
its incumbent code list, and the event depth, while exposing only the
entry prefix needed by the caller.  Return-indexed stabilization travels
with the same concrete result state.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A recursive result state with a faithful comparison path and every
ancestor stabilization obligation enabled by its returned level. -/
inductive EventOut (G : Colored n k) (ctx : Ctx) (tcLevel : Nat)
    (stem fs : List Nat) (out : SearchSt) (best : Option Key)
    (trail : FrameTrail) (r : Int) : Prop where
  | intro (current : Nat) (codes bestCodes : List Nat)
      (event : RunEvent G ctx tcLevel current codes bestCodes fs out best
        trail)
      (depth : current = codes.length)
      (stemEq : codes.take stem.length = stem)
      (returned : r ≤ Int.ofNat current)
      (stable : ReturnStab trail r out)

namespace RunEvent

/-- Fixed-point bookkeeping changes none of an event state's logical
fields. -/
theorem setFixed {G : Colored n k} {ctx : Ctx}
    {tcLevel current : Nat} {cs bs fs : List Nat} {st : SearchSt}
    {best : Option Key} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail)
    (fixedpts : Nat) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with fixedpts := fixedpts } best trail := by
  let st' : SearchSt := { st with fixedpts := fixedpts }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive,
    h.canonPositive, h.firstBound, h.canonBound, h.bestCodes,
    h.incumbent⟩

/-- Clearing the one-shot short-prune flag changes none of an event
state's logical fields. -/
theorem clearShort {G : Colored n k} {ctx : Ctx}
    {tcLevel current : Nat} {cs bs fs : List Nat} {st : SearchSt}
    {best : Option Key} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with needshortprune := false } best trail := by
  let st' : SearchSt := { st with needshortprune := false }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive,
    h.canonPositive, h.firstBound, h.canonBound, h.bestCodes,
    h.incumbent⟩

/-- Updating the first-path agreement counter changes none of an event
state's logical fields. -/
theorem setAllsame {G : Colored n k} {ctx : Ctx}
    {tcLevel current allsamelevel : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with allsamelevel := allsamelevel } best trail := by
  let st' : SearchSt := { st with allsamelevel := allsamelevel }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-- Installing the first-path return controls preserves an event state
once the caller supplies the new guide and numeric bounds. -/
theorem setFirst {G : Colored n k} {ctx : Ctx}
    {tcLevel current gcaFirst stabvertex : Nat} {cs bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail)
    (hguides : GuideStore ctx tcLevel current
      { st with gcaFirst := gcaFirst, stabvertex := stabvertex }
      best trail)
    (hpositive : 0 < gcaFirst) (hbound : gcaFirst ≤ current) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with gcaFirst := gcaFirst, stabvertex := stabvertex }
      best trail := by
  let st' : SearchSt :=
    { st with gcaFirst := gcaFirst, stabvertex := stabvertex }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.cheap.ofFrames rfl rfl rfl, hrefs, hguides,
    h.trailOk.stateEq rfl rfl, hpositive,
    h.canonPositive, hbound, h.canonBound, h.bestCodes, h.incumbent⟩

end RunEvent

namespace EventOut

/-- A stable state with a nonpositive comparison sign is an event output
at its own code depth. -/
theorem ofRun {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail} {r : Int}
    (h : RunInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hdepth : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hreturn : r ≤ Int.ofNat level) (hnonpositive : st.compCanon ≤ 0)
    (hstable : ReturnStab trail r st) :
    EventOut G ctx tcLevel stem fs st best trail r :=
  .intro level codes bs (h.event hnonpositive) hdepth hstem hreturn hstable

/-- Weakening the returned level preserves an event output. -/
theorem lower {G : Colored n k} {ctx : Ctx} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt} {best : Option Key}
    {trail : FrameTrail} {r r' : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r)
    (hle : r' ≤ r) :
    EventOut G ctx tcLevel stem fs out best trail r' := by
  cases h with
  | intro current codes bestCodes event depth stemEq returned stable =>
      exact .intro current codes bestCodes event depth stemEq
        (Int.le_trans hle returned) (stable.lower hle)

/-- Fixed-point cleanup preserves the full result-side package. -/
theorem setFixed {G : Colored n k} {ctx : Ctx} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt} {best : Option Key}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r)
    (fixedpts : Nat) :
    EventOut G ctx tcLevel stem fs { out with fixedpts := fixedpts }
      best trail r := by
  cases h with
  | intro current codes bestCodes event depth stemEq returned stable =>
      exact .intro current codes bestCodes (event.setFixed fixedpts)
        depth stemEq returned (stable.setFixed fixedpts)

/-- Clearing the short-prune request preserves the full result package. -/
theorem clearShort {G : Colored n k} {ctx : Ctx} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt} {best : Option Key}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    EventOut G ctx tcLevel stem fs
      { out with needshortprune := false } best trail r := by
  cases h with
  | intro current codes bestCodes event depth stemEq returned stable =>
      exact .intro current codes bestCodes event.clearShort depth stemEq
        returned stable.clearShort

/-- Updating the first-path agreement counter preserves the full result
package. -/
theorem setAllsame {G : Colored n k} {ctx : Ctx} {tcLevel allsamelevel : Nat}
    {stem fs : List Nat} {out : SearchSt} {best : Option Key}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    EventOut G ctx tcLevel stem fs
      { out with allsamelevel := allsamelevel } best trail r := by
  cases h with
  | intro current codes bestCodes event depth stemEq returned stable =>
      exact .intro current codes bestCodes event.setAllsame depth stemEq
        returned (stable.setAllsame allsamelevel)

end EventOut

end Hex.GraphIso.Nauty
