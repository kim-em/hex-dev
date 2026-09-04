/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeTarget

public section

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
    (st : SearchSt) : Prop :=
  ∀ level entry, Int.ofNat level ≤ r → trail level = some entry →
    ∀ γ ∈ st.genTrace.toList,
      CellStab entry.frame.rsPtn level entry.frame.rsLab γ

namespace ReturnStab

/-- Lowering the advertised return level weakens the stabilization
obligation. -/
theorem lower {trail : FrameTrail} {r r' : Int} {st : SearchSt}
    (h : ReturnStab trail r st) (hle : r' ≤ r) :
    ReturnStab trail r' st := by
  intro level entry hlevel hentry γ hγ
  exact h level entry (Int.le_trans hlevel hle) hentry γ hγ

/-- A state with no recorded generators satisfies every return frame. -/
theorem empty {trail : FrameTrail} {r : Int} {st : SearchSt}
    (h : st.genTrace = #[]) : ReturnStab trail r st := by
  intro level entry hlevel hentry γ hγ
  rw [h] at hγ
  simp at hγ

/-- Fixed-point bookkeeping does not affect return stabilization. -/
theorem setFixed {trail : FrameTrail} {r : Int} {st : SearchSt}
    (h : ReturnStab trail r st) (fixedpts : Nat) :
    ReturnStab trail r { st with fixedpts := fixedpts } := by
  unfold ReturnStab at h ⊢
  exact h

/-- First-path return bookkeeping does not affect the generator store or
the ancestor frames it stabilizes. -/
theorem setFirst {trail : FrameTrail} {r : Int} {st : SearchSt}
    (h : ReturnStab trail r st) (gcaFirst stabvertex : Nat) :
    ReturnStab trail r
      { st with gcaFirst := gcaFirst, stabvertex := stabvertex } := by
  unfold ReturnStab at h ⊢
  exact h

/-- Clearing the one-shot short-prune flag does not affect stabilization. -/
theorem clearShort {trail : FrameTrail} {r : Int} {st : SearchSt}
    (h : ReturnStab trail r st) :
    ReturnStab trail r { st with needshortprune := false } := by
  unfold ReturnStab at h ⊢
  exact h

/-- Pushing a child frame preserves all older return obligations.  The
new frame is required only when the return reaches it. -/
theorem push {trail : FrameTrail} {r : Int} {st : SearchSt}
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
theorem frameStable {trail : FrameTrail} {ctx : Ctx}
    {tcLevel target : Nat} {out : SearchSt} {best : Option Key}
    {payload : Unwind ctx tcLevel target out best} {entry : TrailEntry}
    (hret : ReturnStab trail (Int.ofNat target) out)
    (hentry : trail target = some entry) :
    payload.FrameStable entry.frame.rsPtn target entry.frame.rsLab := by
  cases payload with
  | first anchor carrier => exact .first anchor carrier
  | canon anchor carrier => exact .canon anchor carrier
  | orbit payload =>
      apply Unwind.FrameStable.orbit payload
      intro γ hγ
      exact hret target entry (Int.le_refl _) hentry γ hγ

end ReturnStab

end Hex.GraphIso.Nauty
