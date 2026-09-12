/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexProps
public import HexGraphIso.Nauty.Sparse.Target
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

namespace Scratch

/-- Persistent storage bounds. Hit counts are unrestricted: the executable
clears each touched cell before reading counts in a new refinement pass. -/
structure Bounded (n : Nat) (s : Scratch) : Prop where
  starts_size : s.cellstart.size = n
  ends_size : s.cellend.size = n
  hits_size : s.hits.size = n
  marks_size : s.marks.size = n
  vmarks_size : s.vmarks.size = n
  marks_le : ∀ i, i < n → s.marks[i]! ≤ s.stamp
  vmarks_le : ∀ i, i < n → s.vmarks[i]! ≤ s.stamp

/-- Cache validity is tied to the current partition only while its flag is set. -/
structure Valid (n : Nat) (lab ptn : Array Nat) (level : Nat) (s : Scratch) : Prop
    extends Bounded n s where
  indices : s.indexed = true → Index.Valid n lab ptn level s.cellstart s.cellend

theorem fresh_valid (n : Nat) (lab ptn : Array Nat) (level : Nat) :
    Valid n lab ptn level (.fresh n) := by
  refine ⟨⟨by simp [fresh], by simp [fresh], by simp [fresh], by simp [fresh],
    by simp [fresh], ?_, ?_⟩, ?_⟩
  · intro i hi; simp [fresh, hi]
  · intro i hi; simp [fresh, hi]
  · simp [fresh]

/-- Invalidating cached indices permits a different partition and labelling
while retaining the allocated arrays and generation bounds. -/
theorem Bounded.invalidate {n : Nat} {s : Scratch} (h : Bounded n s)
    (lab ptn : Array Nat) (level : Nat) :
    Valid n lab ptn level { s with indexed := false } :=
  ⟨⟨h.starts_size, h.ends_size, h.hits_size, h.marks_size, h.vmarks_size,
    h.marks_le, h.vmarks_le⟩, fun h => Bool.noConfusion h⟩

theorem Bounded.with_hits {n : Nat} {s : Scratch} (h : Bounded n s)
    (hits : Array Nat) (hs : hits.size = n) : Bounded n { s with hits } :=
  ⟨h.starts_size, h.ends_size, hs, h.marks_size, h.vmarks_size, h.marks_le, h.vmarks_le⟩

/-- Borrowing the count array leaves the partition and mark invariants intact. -/
theorem Valid.with_hits {n level : Nat} {lab ptn : Array Nat} {s : Scratch}
    (h : Valid n lab ptn level s) (hits : Array Nat) (hs : hits.size = n) :
    Valid n lab ptn level { s with hits } :=
  ⟨h.toBounded.with_hits hits hs, h.indices⟩

end Scratch

open Std.Do
set_option mvcgen.warning false

/-- Target selection changes only hit counts and preserves their allocation. -/
theorem bestcellCached_scratch (g : Graph n) (lab : Array Nat) (s : Scratch) :
    let out := (bestcellCached g lab s).2
    out = { s with hits := out.hits } ∧ out.hits.size = s.hits.size := by
  unfold bestcellCached
  apply Id.of_wp_run_eq rfl (fun r : Nat × Scratch =>
    r.2 = { s with hits := r.2.hits } ∧ r.2.hits.size = s.hits.size)
  mvcgen invariants
  | inv1 => ⇓⟨_, state⟩ => ⌜state.1.size = s.hits.size⌝
  | inv2 => ⇓⟨_, state⟩ => ⌜state.1.size = s.hits.size⌝
  | inv3 => ⇓⟨_, hits⟩ => ⌜hits.size = s.hits.size⌝
  | inv4 => ⇓⟨_, state⟩ => ⌜state.1.size = s.hits.size⌝
  all_goals simp_all +zetaDelta

theorem bestcellCached_valid (g : Graph n) (lab ptn : Array Nat) (level : Nat)
    (s : Scratch) (h : Scratch.Valid n lab ptn level s) :
    Scratch.Valid n lab ptn level (bestcellCached g lab s).2 := by
  have hr := bestcellCached_scratch g lab s
  rw [hr.1]
  exact h.with_hits _ (hr.2.trans h.hits_size)

/-- Allocation and generation preservation does not require valid indices. -/
theorem bestcellCached_bounded (g : Graph n) (lab : Array Nat)
    (s : Scratch) (h : Scratch.Bounded n s) :
    Scratch.Bounded n (bestcellCached g lab s).2 := by
  have hr := bestcellCached_scratch g lab s
  rw [hr.1]
  exact h.with_hits _ (hr.2.trans h.hits_size)

/-- Both target dispatch paths retain scratch validity, including borrowed
counts and the fallback used after invalidation. -/
theorem maketargetCached_valid (g : Graph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (s : Scratch) (h : Scratch.Valid n lab ptn level s) :
    Scratch.Valid n lab ptn level (maketargetCached g lab ptn level tcLevel hint s).2.2.2 := by
  unfold maketargetCached
  simp only [Id.run, pure]
  split
  · exact h
  · split
    · exact h
    · split
      · exact bestcellCached_valid g lab ptn level s h
      · exact h

theorem maketargetCached_bounded (g : Graph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (hint : Int) (s : Scratch) (h : Scratch.Bounded n s) :
    Scratch.Bounded n (maketargetCached g lab ptn level tcLevel hint s).2.2.2 := by
  unfold maketargetCached
  simp only [Id.run, pure]
  split
  · exact h
  · split
    · exact h
    · split
      · exact bestcellCached_bounded g lab s h
      · exact h

end Hex.GraphIso.Nauty.Sparse
