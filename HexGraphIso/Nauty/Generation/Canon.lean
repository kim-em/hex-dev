/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Cursor

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- A canonical reference belonging to the current frame comes from a
child already behind its cursor. An older ancestor reference has no local
source obligation. -/
structure CanonPast (level pos : Nat) (cursor : Option Nat) (st : SearchSt n) : Prop where
  cap : st.gcaCanon ≤ level
  source : st.gcaCanon = level → ¬ After cursor st.canonlab[pos]!

/-- An ancestor reference imposes no source obligation at a fresh frame. -/
theorem CanonPast.start {level pos : Nat} {st : SearchSt n} (h : st.gcaCanon < level) :
    CanonPast level pos none st := ⟨Nat.le_of_lt h, fun he => by omega⟩

/-- Advancing a sweep cursor retains every older canonical source. -/
theorem CanonPast.advance {level pos tv : Nat} {cursor : Option Nat} {st : SearchSt n}
    (h : CanonPast level pos cursor st) (ha : After cursor tv) :
    CanonPast level pos (some tv) st := by
  refine ⟨h.cap, ?_⟩
  intro he
  have hs := h.source he
  cases cursor with
  | none => exact (hs trivial).elim
  | some c =>
    change c < tv at ha
    change ¬ c < st.canonlab[pos]! at hs
    change ¬ tv < st.canonlab[pos]!
    omega

/-- The reference child is strictly earlier than the next visited child. -/
theorem CanonPast.before {level pos tv : Nat} {cursor : Option Nat} {st : SearchSt n}
    {tcell : VSet n} (h : CanonPast level pos cursor st)
    (hnext : tcell.nextElem cursor = some tv) (he : st.gcaCanon = level) :
    st.canonlab[pos]! < tv := by
  have hs := h.source he
  have ha := nextElem_after hnext
  cases cursor with
  | none => exact (hs trivial).elim
  | some c =>
    change ¬ c < st.canonlab[pos]! at hs
    change c < tv at ha
    omega

/-- Updates to unrelated bookkeeping preserve the canonical source. -/
theorem CanonPast.stateEq {level pos : Nat} {cursor : Option Nat} {st out : SearchSt n}
    (h : CanonPast level pos cursor st) (hgca : out.gcaCanon = st.gcaCanon)
    (hlab : out.canonlab = st.canonlab) : CanonPast level pos cursor out := by
  exact ⟨hgca ▸ h.cap, fun he => by rw [hlab]; exact h.source (hgca.symm.trans he)⟩

end Hex.GraphIso.Nauty.Generation
