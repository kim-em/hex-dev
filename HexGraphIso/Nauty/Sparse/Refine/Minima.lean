/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine.Counts
public import HexGraphIso.Nauty.Sparse.Window
public import HexGraphIso.Nauty.Sparse.MinimaSort
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.CountSort

open Std.Do
set_option mvcgen.warning false

/-- The initial equal-count scan stops inside the cell or at its exclusive end. -/
theorem firstRun_bounds (lab hits : Array Nat) (first last : Nat) (hf : first < last) :
    first < firstRun lab hits first last ∧ firstRun lab hits first last ≤ last := by
  unfold firstRun
  apply Id.of_wp_run_eq rfl (fun v : Nat => first < v ∧ v ≤ last)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, v⟩ => ⌜first < v ∧ v ≤ last ∧
      (v = first + 1 + cursor.prefix.length ∨ hits[lab[v]!]! ≠ hits[lab[first]!]!)⌝)
  all_goals simp_all +zetaDelta [Std.Legacy.Range.toList]
  all_goals try omega
  all_goals grind

/-- The initial scan records a constant prefix and stops at its first
unequal count, or exhausts the cell. -/
theorem firstRun_spec (lab hits : Array Nat) (first last : Nat) (hf : first < last) :
    let v := firstRun lab hits first last
    first < v ∧ v ≤ last ∧
      (∀ q, first ≤ q → q < v → hits[lab[q]!]! = hits[lab[first]!]!) ∧
      (v = last ∨ hits[lab[v]!]! ≠ hits[lab[first]!]!) := by
  unfold firstRun
  apply Id.of_wp_run_eq rfl (fun v : Nat => first < v ∧ v ≤ last ∧
    (∀ q, first ≤ q → q < v → hits[lab[q]!]! = hits[lab[first]!]!) ∧
    (v = last ∨ hits[lab[v]!]! ≠ hits[lab[first]!]!))
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, v⟩ => ⌜first < v ∧ v ≤ last ∧
      (∀ q, first ≤ q → q < v → hits[lab[q]!]! = hits[lab[first]!]!) ∧
      (v = first + 1 + cursor.prefix.length ∨ hits[lab[v]!]! ≠ hits[lab[first]!]!)⌝)
  all_goals simp_all +zetaDelta [Std.Legacy.Range.toList]
  all_goals try grind

/-- Three-way insertion permutes only the selected cell and leaves ordered,
bounded fragment cuts. It does not require bounds on the count values. -/
theorem minima_window (lab hits : Array Nat) (cap first last begin : Nat)
    (hf : first < begin) (he : begin ≤ last) (hb : last ≤ lab.size) :
    let r := minima lab hits cap first last begin
    Sort.Window lab r.2.2.2.2 first last ∧
      first < r.2.1 ∧ r.2.1 ≤ r.2.2.2.1 ∧ r.2.2.2.1 ≤ last := by
  unfold minima
  apply Id.of_wp_run_eq rfl (fun r : Nat × Nat × Nat × Nat × Array Nat =>
    Sort.Window lab r.2.2.2.2 first last ∧
      first < r.2.1 ∧ r.2.1 ≤ r.2.2.2.1 ∧ r.2.2.2.1 ≤ last)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, r⟩ => ⌜Sort.Window lab r.2.2.2.2 first last ∧
      first < r.2.1 ∧ r.2.1 ≤ r.2.2.2.1 ∧
      r.2.2.2.1 ≤ last - cursor.suffix.length⌝)
  all_goals simp_all +zetaDelta [Std.Legacy.Range.toList]
  all_goals try grind [Sort.Window.refl, Sort.Window.size, Sort.Window.rotate,
    Sort.Window.exchange, rotate_read, range_cursor]

  case vc1.step.isTrue =>
    rename_i hin
    have hj := range_cursor he (by assumption)
    have hs := hin.1.size
    simp only [← Array.set!_eq_setIfInBounds]
    rw [rotate_read _ _ _ _ (by omega) (by omega) (by omega)]
    exact ⟨hin.1.rotate (by omega) (by omega) (by omega) (by omega) (by omega),
      by omega, by omega⟩
  case vc3.step.isFalse.isFalse.isTrue =>
    rename_i hin
    have hj := range_cursor he (by assumption)
    have hs := hin.1.size
    simp only [← Array.set!_eq_setIfInBounds]
    rw [rotate_read _ _ _ _ (by omega) (by omega) (by omega)]
    exact ⟨hin.1.rotate (by omega) (by omega) (by omega) (by omega) (by omega),
      by omega, by omega⟩

/-- Three-way insertion leaves the two minimum-count runs followed by
strictly larger counts. The sentinel need only exceed the initial count. -/
theorem minima_spec (lab hits : Array Nat) (cap first last begin : Nat)
    (hf : first < begin) (he : begin ≤ last) (hb : last ≤ lab.size)
    (hk : hits[lab[first]!]! < cap)
    (hu : ∀ q, first ≤ q → q < begin → hits[lab[q]!]! = hits[lab[first]!]!) :
    let r := minima lab hits cap first last begin
    Minima r.2.2.2.2 hits first r.2.1 r.2.2.2.1 last r.1 r.2.2.1 ∧
      r.2.2.2.2.size = lab.size := by
  unfold minima
  apply Id.of_wp_run_eq rfl (fun r : Nat × Nat × Nat × Nat × Array Nat =>
    Minima r.2.2.2.2 hits first r.2.1 r.2.2.2.1 last r.1 r.2.2.1 ∧
      r.2.2.2.2.size = lab.size)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, r⟩ => ⌜Minima r.2.2.2.2 hits first r.2.1 r.2.2.2.1
      (last - cursor.suffix.length) r.1 r.2.2.1 ∧ r.2.2.2.2.size = lab.size⌝)
  all_goals simp_all +zetaDelta [Std.Legacy.Range.toList]
  all_goals try
    simpa only [show last - (last - begin) = begin by omega] using
      (Minima.initial hf hk hu)
  all_goals
    rename_i hin
    have hj := range_cursor he (by assumption)
    have hj0 := Nat.eq_sub_of_add_eq ((Nat.add_assoc _ _ _).symm.trans hj)
    have hj1 := Nat.eq_sub_of_add_eq ((Nat.add_right_comm _ _ _).trans hj)
    rw [← hj0] at hin
    rw [← hj1]
    have bounds := hin.1.bounds
    have size := hin.2
    try simp only [← Array.set!_eq_setIfInBounds]
    try rw [rotate_read _ _ _ _ (by omega) (by omega) (by omega)]
    first
      | exact hin.1.hit_min (by omega) (by assumption)
      | exact hin.1.hit_second (by omega) (by assumption)
      | exact hin.1.new_min (by omega) (by assumption)
      | exact hin.1.new_second (by omega) (by omega) (by assumption)
      | exact hin.1.above (by omega)

end Hex.GraphIso.Nauty.Sparse.CountSort
