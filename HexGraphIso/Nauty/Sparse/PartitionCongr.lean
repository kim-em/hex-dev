/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SortCongr
import all HexGraphIso.Nauty.Sparse.LoopRel

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

private noncomputable def scanLeft (x keys : Array Nat) (fuel a b c v : Nat) :
    Array Nat × Nat × Nat := Id.run do
  let mut x := x
  let mut a := a
  let mut b := b
  for _ in [0:fuel] do
    if b >= c || keys[x[b]!]! > v then break
    if keys[x[b]!]! == v then
      x := x.swapIfInBounds a b
      a := a + 1
    b := b + 1
  return (x, a, b)

private theorem left_congr (h : Agree y z lo hi x)
    (hb : lo ≤ a ∧ a ≤ b ∧ b ≤ hi ∧ c ≤ hi) (fuel v : Nat) :
    scanLeft x y fuel a b c v = scanLeft x z fuel a b c v ∧
    let r := scanLeft x y fuel a b c v
    Agree y z lo hi r.1 ∧ lo ≤ r.2.1 ∧ r.2.1 ≤ r.2.2 ∧ r.2.2 ≤ hi := by
  let P (s : Array Nat × Nat × Nat) :=
    Agree y z lo hi s.1 ∧ lo ≤ s.2.1 ∧ s.2.1 ≤ s.2.2 ∧ s.2.2 ≤ hi
  unfold scanLeft
  simp only [Id.run, bind, pure]
  apply Loop.range_congr 0 fuel _ _ P P (fun _ h => h) ?_ ⟨h, hb.1, hb.2.1, hb.2.2.1⟩
  intro j hj hj' s hs
  by_cases hbc : c ≤ s.2.2
  · simp only [hbc, decide_true, Bool.true_or, ite_true]
    exact ⟨trivial, hs⟩
  · have hk := hs.1.keys s.2.2 (by have := hs.2; omega) (by omega)
    constructor
    · rw [hk]
    · simp only [hbc, decide_false, Bool.false_or]
      split
      · exact hs
      · split <;> dsimp only [Loop.Preserves, P]
        · exact ⟨hs.1.swap ⟨hs.2.1, by have := hs.2; omega⟩
            ⟨by have := hs.2; omega, by omega⟩,
            by have := hs.2; omega, by have := hs.2; omega, by omega⟩
        · exact ⟨hs.1, hs.2.1, by have := hs.2; omega, by omega⟩

private noncomputable def scanRight (x keys : Array Nat) (fuel b c d v : Nat) :
    Array Nat × Nat × Nat := Id.run do
  let mut x := x
  let mut c := c
  let mut d := d
  for _ in [0:fuel] do
    if c <= b || keys[x[c - 1]!]! < v then break
    if keys[x[c - 1]!]! == v then
      x := x.swapIfInBounds (c - 1) (d - 1)
      d := d - 1
    c := c - 1
  return (x, c, d)

private theorem right_congr (h : Agree y z lo hi x)
    (hb : lo ≤ b ∧ lo ≤ c ∧ c ≤ d ∧ d ≤ hi) (fuel v : Nat) :
    scanRight x y fuel b c d v = scanRight x z fuel b c d v ∧
    let r := scanRight x y fuel b c d v
    Agree y z lo hi r.1 ∧ lo ≤ r.2.1 ∧ r.2.1 ≤ r.2.2 ∧ r.2.2 ≤ hi := by
  let P (s : Array Nat × Nat × Nat) :=
    Agree y z lo hi s.1 ∧ lo ≤ s.2.1 ∧ s.2.1 ≤ s.2.2 ∧ s.2.2 ≤ hi
  unfold scanRight
  simp only [Id.run, bind, pure]
  apply Loop.range_congr 0 fuel _ _ P P (fun _ h => h) ?_ ⟨h, hb.2.1, hb.2.2.1, hb.2.2.2⟩
  intro j hj hj' s hs
  by_cases hcb : s.2.1 ≤ b
  · simp only [hcb, decide_true, Bool.true_or, ite_true]
    exact ⟨trivial, hs⟩
  · have hk := hs.1.keys (s.2.1 - 1) (by omega) (by have := hs.2; omega)
    constructor
    · rw [hk]
    · simp only [hcb, decide_false, Bool.false_or]
      split
      · exact hs
      · split <;> dsimp only [Loop.Preserves, P]
        · exact ⟨hs.1.swap ⟨by omega, by have := hs.2; omega⟩
            ⟨by have := hs.2; omega, by have := hs.2; omega⟩,
            by omega, by have := hs.2; omega, by have := hs.2; omega⟩
        · exact ⟨hs.1, by omega, by have := hs.2; omega, hs.2.2.2⟩

private noncomputable def scan (keys : Array Nat) (len v : Nat) (_ : Nat)
    (s : Array Nat × Nat × Nat × Nat × Nat) :
    Id (ForInStep (Array Nat × Nat × Nat × Nat × Nat)) :=
  let l := scanLeft s.1 keys len s.2.1 s.2.2.1 s.2.2.2.1 v
  let r := scanRight l.1 keys len l.2.2 s.2.2.2.1 s.2.2.2.2 v
  if l.2.2 >= r.2.1 then .done (r.1, l.2.1, l.2.2, r.2.1, r.2.2)
  else .yield (r.1.swapIfInBounds l.2.2 (r.2.1 - 1), l.2.1, l.2.2 + 1, r.2.1 - 1, r.2.2)

private def ScanValid (y z : Array Nat) (lo hi : Nat)
    (s : Array Nat × Nat × Nat × Nat × Nat) : Prop :=
  Agree y z lo hi s.1 ∧ lo ≤ s.2.1 ∧ s.2.1 ≤ s.2.2.1 ∧
    s.2.2.1 ≤ hi ∧ lo ≤ s.2.2.2.1 ∧ s.2.2.2.1 ≤ s.2.2.2.2 ∧ s.2.2.2.2 ≤ hi

private theorem scan_congr (h : ScanValid y z lo hi s) (len v i : Nat) :
    scan y len v i s = scan z len v i s ∧
      Loop.Preserves (ScanValid y z lo hi) (ScanValid y z lo hi) (scan y len v i s) := by
  have hl := left_congr (c := s.2.2.2.1) h.1
    ⟨h.2.1, h.2.2.1, h.2.2.2.1, by have := h.2; omega⟩ len v
  have hr := right_congr (b := (scanLeft s.1 y len s.2.1 s.2.2.1 s.2.2.2.1 v).2.2) hl.2.1
    ⟨by have := hl.2.2; omega, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩ len v
  constructor
  · dsimp only [scan]
    rw [← hl.1, ← hr.1]
  · dsimp only [scan]
    split <;> dsimp only [Loop.Preserves, ScanValid]
    · exact ⟨hr.2.1, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2⟩
    · refine ⟨hr.2.1.swap ⟨by have := hl.2.2; omega, by have := hr.2.2; omega⟩
        ⟨by have := hl.2.2; omega, by have := hr.2.2; omega⟩,
        hl.2.2.1, ?_, ?_, ?_, ?_, hr.2.2.2.2⟩
      all_goals have := hl.2.2; have := hr.2.2; omega

private noncomputable def finish (start len : Nat)
    (s : Array Nat × Nat × Nat × Nat × Nat) : Array Nat × Nat × Nat := Id.run do
  let mut x := s.1
  let a := s.2.1
  let b := s.2.2.1
  let c := s.2.2.2.1
  let d := s.2.2.2.2
  let ba := b - a
  let dc := d - c
  let left := min (a - start) ba
  for i in [0:left] do x := x.swapIfInBounds (start + i) (b - left + i)
  let right := min dc (start + len - d)
  for i in [0:right] do x := x.swapIfInBounds (b + i) (start + len - right + i)
  return (x, ba, dc)

/-- The proof decomposition is definitionally the executed partition,
including its scan order, crossing swaps and final equal-key block swaps. -/
private theorem partition_eq (x y : Array Nat) (start len : Nat) :
    partition x y start len = finish start len
      (forIn (m := Id) [0:len + 1] (x, start, start, start + len, start + len)
        (scan y len (pivot x y start len))) := by
  rfl

/-- The exact Bentley–McIlroy partition, including both returned sizes,
depends only on keys stored in its current segment. -/
theorem partition_congr (h : Agree y z start (start + len) x) (hl : 0 < len) :
    partition x y start len = partition x z start len := by
  have hp := pivot_congr h hl
  have hr := Loop.range_congr 0 (len + 1)
    (scan y len (pivot x y start len)) (scan z len (pivot x y start len))
    (ScanValid y z start (start + len)) (ScanValid y z start (start + len))
    (fun _ h => h) (fun i _ _ s hs => scan_congr hs len _ i)
    (show ScanValid y z start (start + len) (x, start, start, start + len, start + len)
      from by dsimp only [ScanValid]; exact ⟨h, by omega, by omega, by omega, by omega, by omega, by omega⟩)
  rw [partition_eq, partition_eq, ← hp]
  exact congrArg (finish start len) hr.1

end Hex.GraphIso.Nauty.Sparse.Sort
