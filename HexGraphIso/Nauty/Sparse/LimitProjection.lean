/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.LimitCount
import all HexGraphIso.Nauty.Search.Generic

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Limited

def Ready (s : State n) : Prop := s.exhausted = false

/-- Erase only limit bookkeeping from a node return. -/
def nodeValue (r : Generic.Exit × State n) : Generic.Exit × Sparse.State n :=
  (r.1, r.2.value)

/-- Erase only limit bookkeeping from a sibling-sweep return. -/
def sweepValue (r : Generic.Exit × Nat × State n) : Generic.Exit × Nat × Sparse.State n :=
  (r.1, r.2.1, r.2.2.value)

/-- On a non-exhausted return, both engines agree exactly; the input was
also non-exhausted. This backward condition excludes recovery from failure. -/
def NodeEq (f : Generic.NodeFn (State n)) (plain : Generic.NodeFn (Sparse.State n)) : Prop :=
  ∀ first level nc s, Ready (f first level nc s).2 →
    Ready s ∧ nodeValue (f first level nc s) = plain first level nc s.value

def SweepEq (f : Generic.SweepFn (State n) n) (plain : Generic.SweepFn (Sparse.State n) n) : Prop :=
  ∀ first level nc tc tv1 cursor cell index s,
    Ready (f first level nc tc tv1 cursor cell index s).2.2 →
      Ready s ∧ sweepValue (f first level nc tc tv1 cursor cell index s) =
        plain first level nc tc tv1 cursor cell index s.value

theorem map_ready (f : Sparse.State n → Sparse.State n) (s : State n) :
    Ready (map f s) ↔ Ready s := by
  unfold map
  split <;> rfl

theorem map_value (f : Sparse.State n → Sparse.State n) {s : State n} (hs : Ready s) :
    (map f s).value = f s.value := by
  dsimp only [Ready] at hs
  simp only [map, hs, Bool.false_eq_true, ite_false]

theorem visit_ready {g : Graph n} {level nc : Nat} {s : State n}
    (h : Ready (visit g level nc s).2.2) : Ready s ∧ 0 < s.remaining := by
  unfold visit at h
  split at h
  · cases h
  · rename_i hg
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hg
    exact ⟨by cases he : s.exhausted <;> simp_all [Ready], by omega⟩

/-- An admitted visit projects to the literal native refinement call. -/
theorem visit_value (g : Graph n) (level nc : Nat) {s : State n}
    (hs : Ready s) (hq : 0 < s.remaining) :
    let r := visit g level nc s
    (r.1, r.2.1, r.2.2.value) = Sparse.visit g level nc s.value := by
  dsimp only [Ready] at hs
  simp only [visit, hs, Bool.false_or, beq_iff_eq, show s.remaining ≠ 0 by omega, ite_false]

theorem recover_ready (inf level : Nat) (s : State n) :
    Ready ((policy (n := n)).recover inf level s) ↔ Ready s := map_ready _ s

theorem recover_value (inf level : Nat) {s : State n} (hs : Ready s) :
    ((policy (n := n)).recover inf level s).value =
      (Sparse.policy (n := n)).recover inf level s.value := map_value _ hs

theorem orbit_value (tv : Nat) {s : State n} (hs : Ready s) :
    (policy (n := n)).orbit s tv = (Sparse.policy (n := n)).orbit s.value tv := by
  change (if s.exhausted then 0 else _) = _
  dsimp only [Ready] at hs
  simp only [hs, Bool.false_eq_true, ite_false]

theorem longprune_value (cell : VSet n) {s : State n} (hs : Ready s) :
    (policy (n := n)).longprune cell s = (Sparse.policy (n := n)).longprune cell s.value := by
  change (if s.exhausted then VSet.empty else _) = _
  dsimp only [Ready] at hs
  simp only [hs, Bool.false_eq_true, ite_false]

theorem shortprune_value (cell : VSet n) {s : State n} (hs : Ready s) :
    (policy (n := n)).shortprune cell s = (Sparse.policy (n := n)).shortprune cell s.value := by
  change (if s.exhausted then VSet.empty else _) = _
  dsimp only [Ready] at hs
  simp only [hs, Bool.false_eq_true, ite_false]

/-- Recovery, the long filter and the orbit-index update project to the
native continuation whenever the resumed sweep returns successfully. -/
theorem resume_eq {next : Generic.SweepFn (State n) n}
    {plain : Generic.SweepFn (Sparse.State n) n} (hn : SweepEq next plain)
    (inf : Nat) (first : Bool) (level nc tc tv1 tv index : Nat) (cell : VSet n) (s : State n)
    (h : Ready (Generic.resume inf next first level nc tc tv1 tv cell index s).2.2) :
    Ready s ∧ sweepValue (Generic.resume inf next first level nc tc tv1 tv cell index s) =
      Generic.resume inf plain first level nc tc tv1 tv cell index s.value := by
  unfold Generic.resume at h ⊢
  simp only [Id.run_pure, apply_ite Id.run] at h ⊢
  split at h
  all_goals rename_i hfilter
  all_goals have hr := hn first level nc tc tv1 _ _ _ _ h
  all_goals have hs : Ready s :=
    (map_ready ((Sparse.policy (n := n)).recover inf level) s).mp hr.1
  all_goals refine ⟨hs, ?_⟩
  all_goals simpa only [hfilter, Bool.false_eq_true, ite_true, ite_false, recover_value inf level hs,
    orbit_value _ hr.1, longprune_value cell hs] using hr.2

/-- Nonlocal returns and the short filter retain exact native control flow. -/
theorem advance_eq {next : Generic.SweepFn (State n) n}
    {plain : Generic.SweepFn (Sparse.State n) n} (hn : SweepEq next plain)
    (inf : Nat) (first : Bool) (level nc tc tv1 tv index : Nat) (cell : VSet n)
    (s : State n) (exit : Generic.Exit)
    (h : Ready (Generic.advance inf next first level nc tc tv1 tv cell index s exit).2.2) :
    Ready s ∧ sweepValue (Generic.advance inf next first level nc tc tv1 tv cell index s exit) =
      Generic.advance inf plain first level nc tc tv1 tv cell index s.value exit := by
  cases exit with
  | fuel => exact ⟨h, rfl⟩
  | done => exact resume_eq hn inf first level nc tc tv1 tv index cell s h
  | unwind target short =>
    unfold Generic.advance at h ⊢
    simp only [Id.run_pure, apply_ite Id.run] at h ⊢
    split at h
    · rename_i ht
      refine ⟨h, ?_⟩
      simp only [ht, ite_true]
      rfl
    · rename_i ht
      cases short with
      | false =>
        have hr := resume_eq hn inf first level nc tc tv1 tv index cell s h
        simpa only [ht, ite_false, Bool.false_eq_true] using hr
      | true =>
        have hr := resume_eq hn inf first level nc tc tv1 tv index
          ((policy (n := n)).shortprune cell s) s h
        refine ⟨hr.1, ?_⟩
        simpa only [ht, ite_false, ite_true, shortprune_value cell hr.1] using hr.2

theorem child_ready (first : Bool) (level tc tv : Nat) (s : State n) :
    Ready ((policy (n := n)).child first level tc tv s) ↔ Ready s := map_ready _ s

theorem child_value (first : Bool) (level tc tv : Nat) {s : State n} (hs : Ready s) :
    ((policy (n := n)).child first level tc tv s).value =
      (Sparse.policy (n := n)).child first level tc tv s.value := map_value _ hs

theorem leave_ready (tv : Nat) (s : State n) :
    Ready ((policy (n := n)).leaveChild tv s) ↔ Ready s := map_ready _ s

theorem leave_value (tv : Nat) {s : State n} (hs : Ready s) :
    ((policy (n := n)).leaveChild tv s).value =
      (Sparse.policy (n := n)).leaveChild tv s.value := map_value _ hs

theorem afterFirst_ready (level tv : Nat) (s : State n) :
    Ready ((policy (n := n)).afterChildFirst level tv s) ↔ Ready s := map_ready _ s

theorem afterFirst_value (level tv : Nat) {s : State n} (hs : Ready s) :
    ((policy (n := n)).afterChildFirst level tv s).value =
      (Sparse.policy (n := n)).afterChildFirst level tv s.value := map_value _ hs

end Hex.GraphIso.Nauty.Sparse.Limited
