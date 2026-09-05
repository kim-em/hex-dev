/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeHistory

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
inductive EventOut (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat)
    (stem fs : List Nat) (out : SearchSt n) (best : Option (Key n))
    (trail : FrameTrail) (r : Int) : Prop where
  | intro (current : Nat) (codes bestCodes : List Nat)
      (event : RunEvent G ctx tcLevel current codes bestCodes fs out best
        trail)
      (depth : current = codes.length)
      (stemEq : codes.take stem.length = stem)
      (past : stem.length < current)
      (returned : r ≤ Int.ofNat current)
      (stable : ReturnStab trail (min r (Int.ofNat out.gcaFirst)) out)
      (history : RefTrail ctx current out trail)

namespace RunEvent

/-- Every event state reads back the semantic incumbent recorded by its
comparison machine.  The row-rejection arm uses its deliberately reset
zero-sign machine. -/
theorem read {G : Colored n k} {ctx : Ctx n}
    {tcLevel current : Nat} {cs bs fs : List Nat} {st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail) :
    stInc ctx st = best := by
  have hread : stInc ctx st = ghostInc ctx bs st.canonlab := by
    rcases h.machines with hplain | hreset
    · apply stInc_eq_ghost hplain.2
      omega
    · exact stInc_eq_ghost hreset.2 (by decide)
  rw [hread, ghostInc]
  simp only [h.bestCodes, ↓reduceIte, h.incumbent]

/-- Fixed-point bookkeeping changes none of an event state's logical
fields. -/
theorem setFixed {G : Colored n k} {ctx : Ctx n}
    {tcLevel current : Nat} {cs bs fs : List Nat} {st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail)
    (fixedpts : VSet n) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with fixedpts := fixedpts } best trail := by
  let st' : SearchSt n := { st with fixedpts := fixedpts }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive,
    h.canonPositive, h.firstBound, h.canonBound, h.bestCodes,
    h.incumbent⟩

/-- Clearing the one-shot short-prune flag changes none of an event
state's logical fields. -/
theorem clearShort {G : Colored n k} {ctx : Ctx n}
    {tcLevel current : Nat} {cs bs fs : List Nat} {st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with needshortprune := false } best trail := by
  let st' : SearchSt n := { st with needshortprune := false }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive,
    h.canonPositive, h.firstBound, h.canonBound, h.bestCodes,
    h.incumbent⟩

/-- Updating the first-path agreement counter changes none of an event
state's logical fields. -/
theorem setAllsame {G : Colored n k} {ctx : Ctx n}
    {tcLevel current allsamelevel : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with allsamelevel := allsamelevel } best trail := by
  let st' : SearchSt n := { st with allsamelevel := allsamelevel }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-- Installing the first-path return controls preserves an event state
once the caller supplies the new guide and numeric bounds. -/
theorem setFirst {G : Colored n k} {ctx : Ctx n}
    {tcLevel current gcaFirst stabvertex : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail)
    (hguides : GuideStore ctx tcLevel current
      { st with gcaFirst := gcaFirst, stabvertex := stabvertex }
      best trail)
    (hpositive : 0 < gcaFirst) (hbound : gcaFirst ≤ current) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with gcaFirst := gcaFirst, stabvertex := stabvertex }
      best trail := by
  let st' : SearchSt n :=
    { st with gcaFirst := gcaFirst, stabvertex := stabvertex }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl,
    hrefs, hguides,
    h.trailOk.stateEq rfl rfl, hpositive,
    h.canonPositive, hbound, h.canonBound, h.bestCodes, h.incumbent⟩

/-- Parking the cheap-automorphism boundary above the current event level
preserves the event invariant. -/
theorem park {G : Colored n k} {ctx : Ctx n}
    {tcLevel current boundary : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail)
    (hpos : 0 < boundary) (hcurrent : current ≤ boundary) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with noncheaplevel := boundary } best trail := by
  let st' : SearchSt n := { st with noncheaplevel := boundary }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.park hpos hcurrent, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-- The comparison-blind cleanup after an empty leaf sweep preserves an
event state. -/
theorem leafFinish {G : Colored n k} {ctx : Ctx n}
    {tcLevel level : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel level cs bs fs st best trail) :
    RunEvent G ctx tcLevel level cs bs fs
      (Nauty.leafFinish level st) best trail := by
  unfold Nauty.leafFinish
  split
  · simp only
    split
    · exact h.clearShort.park (by omega) (by omega)
    · exact h.clearShort
  · simp only
    split
    · exact h.park (by omega) (by omega)
    · exact h

end RunEvent

namespace ReturnStab

/-- Leaf cleanup leaves the recorded-generator store unchanged. -/
theorem leafFinish {level : Nat} {st : SearchSt n}
    {trail : FrameTrail} {r : Int} (h : ReturnStab trail r st) :
    ReturnStab trail r (Nauty.leafFinish level st) := by
  apply h.ofGenTraceEq
  unfold Nauty.leafFinish
  split
  · simp only
    split <;> rfl
  · simp only
    split <;> rfl

end ReturnStab

namespace EventOut

/-- A packaged event reads back its semantic incumbent. -/
theorem read {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    stInc ctx out = best := by
  cases h with
  | intro _ _ _ event _ _ _ _ _ _ => exact event.read

/-- Every event output retains a full-size canonical reference. -/
theorem canonSize {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    out.canonlab.size = n := by
  cases h with
  | intro _ _ _ event _ _ _ _ _ _ => exact event.leafRefs.canonSize

/-- Every pair in a result workspace remains valid at the initial coloured
partition. -/
theorem autosOk {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 out.autos := by
  cases h with
  | intro _ _ _ event _ _ _ _ _ _ => exact event.autosOk

/-- Every event output exposes stabilization through the smaller of its
return target and live first-reference GCA.  Direct carrier returns need
no stronger statement, while the orbit-return arm targets this GCA. -/
theorem returnStab {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    ReturnStab trail (min r (Int.ofNat out.gcaFirst)) out := by
  cases h with
  | intro _ _ _ _ _ _ _ _ stable _ => exact stable

/-- Recovering an event that returned exactly to `level` produces the
stable parent-loop state and retains its generator stabilization. -/
theorem recoverRun {G : Colored n k} {ctx : Ctx n} {tcLevel level inf numcells : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r)
    (hreturn : r = Int.ofNat level) (hstem : stem.length = level)
    (hlevel : 1 ≤ level) (hinf : level < inf)
    (hfirst : out.gcaFirst ≤ level)
    (hok : SearchOk G level numcells
      (Nauty.recover n inf level out)) :
    ∃ bs,
      RunInv G ctx tcLevel level stem bs fs numcells
          (Nauty.recover n inf level out) best trail ∧
        ReturnStab trail
          (Int.ofNat (Nauty.recover n inf level out).gcaFirst)
          (Nauty.recover n inf level out) ∧
        RefTrail ctx level (Nauty.recover n inf level out) trail := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      rw [hreturn] at returned stable
      have hle : level ≤ current := Int.ofNat_le.mp returned
      have hpath : level ≤ codes.length := by omega
      have hrun := event.recover hle hlevel hinf hpath hfirst hok
      have htake : codes.take level = stem := by
        rw [← hstem]
        exact stemEq
      rw [htake] at hrun
      have hfirstEq : (Nauty.recover n inf level out).gcaFirst =
          out.gcaFirst :=
        (recover_frames n inf level out).2.2.2.2.2.2.1
      have hfirst' : Int.ofNat out.gcaFirst ≤ Int.ofNat level :=
        Int.ofNat_le.mpr hfirst
      have hmin : min (Int.ofNat level) (Int.ofNat out.gcaFirst) =
          Int.ofNat out.gcaFirst := by omega
      rw [hmin] at stable
      rw [hfirstEq]
      exact ⟨bestCodes, hrun, stable.recover inf level,
        history.recover hle⟩

/-- A stable state with a nonpositive comparison sign is an event output
at its own code depth. -/
theorem ofRun {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail} {r : Int}
    (h : RunInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hdepth : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hreturn : r ≤ Int.ofNat level) (hnonpositive : st.compCanon ≤ 0)
    (hstable : ReturnStab trail (min r (Int.ofNat st.gcaFirst)) st)
    (hhistory : RefTrail ctx level st trail) :
    EventOut G ctx tcLevel stem fs st best trail r :=
  .intro level codes bs (h.event hnonpositive) hdepth hstem hpast hreturn
    hstable hhistory

/-- Weakening the returned level preserves an event output. -/
theorem lower {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r r' : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r)
    (hle : r' ≤ r) :
    EventOut G ctx tcLevel stem fs out best trail r' := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      have hmin : min r' (Int.ofNat out.gcaFirst) ≤
          min r (Int.ofNat out.gcaFirst) := by omega
      exact .intro current codes bestCodes event depth stemEq past
        (Int.le_trans hle returned) (stable.lower hmin) history

/-- Fixed-point cleanup preserves the full result-side package. -/
theorem setFixed {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r)
    (fixedpts : VSet n) :
    EventOut G ctx tcLevel stem fs { out with fixedpts := fixedpts }
      best trail r := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      exact .intro current codes bestCodes (event.setFixed fixedpts)
        depth stemEq past returned (stable.setFixed fixedpts)
        (history.stateEq rfl rfl rfl rfl)

/-- Clearing the short-prune request preserves the full result package. -/
theorem clearShort {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    EventOut G ctx tcLevel stem fs
      { out with needshortprune := false } best trail r := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      exact .intro current codes bestCodes event.clearShort depth stemEq past
        returned stable.clearShort (history.stateEq rfl rfl rfl rfl)

/-- Updating the first-path agreement counter preserves the full result
package. -/
theorem setAllsame {G : Colored n k} {ctx : Ctx n} {tcLevel allsamelevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    EventOut G ctx tcLevel stem fs
      { out with allsamelevel := allsamelevel } best trail r := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      exact .intro current codes bestCodes event.setAllsame depth stemEq past
        returned (stable.setAllsame allsamelevel)
        (history.stateEq rfl rfl rfl rfl)

end EventOut

end Hex.GraphIso.Nauty
