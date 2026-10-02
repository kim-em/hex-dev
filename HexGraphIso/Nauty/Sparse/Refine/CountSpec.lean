/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine.Minima
public import HexGraphIso.Nauty.Sparse.MinimaPerm
public import HexGraphIso.Nauty.Sparse.CountParts
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.CountSort

open Std.Do
set_option mvcgen.warning false

/-- Count insertion preserves the cell's vertices, its bounded counts, and
the sentinel for an empty second fragment. -/
theorem minima_valid (lab hits : Array Nat) (cap first last begin : Nat)
    (hf : first < begin) (he : begin ≤ last) (hb : last ≤ lab.size)
    (hk : ∀ q, first ≤ q → q < last → hits[lab[q]!]! < cap)
    (hu : ∀ q, first ≤ q → q < begin → hits[lab[q]!]! = hits[lab[first]!]!) :
    let r := minima lab hits cap first last begin
    Minima.Permuted lab r.2.2.2.2 hits first last r.2.1 r.2.2.2.1 last r.1 r.2.2.1 cap := by
  unfold minima
  apply Id.of_wp_run_eq rfl (fun r : Nat × Nat × Nat × Nat × Array Nat =>
    Minima.Permuted lab r.2.2.2.2 hits first last r.2.1 r.2.2.2.1 last r.1 r.2.2.1 cap)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, r⟩ => ⌜Minima.Permuted lab r.2.2.2.2 hits first last
      r.2.1 r.2.2.2.1 (last - cursor.suffix.length) r.1 r.2.2.1 cap⌝)
  all_goals simp_all +zetaDelta [Std.Legacy.Range.toList]
  all_goals try
    simpa only [show last - (last - begin) = begin by omega] using
      (Minima.Permuted.initial hf he hb hk hu)
  all_goals
    rename_i hin
    have hj := range_cursor he (by assumption)
    have hj0 := Nat.eq_sub_of_add_eq ((Nat.add_assoc _ _ _).symm.trans hj)
    have hj1 := Nat.eq_sub_of_add_eq ((Nat.add_right_comm _ _ _).trans hj)
    rw [← hj0] at hin
    rw [← hj1]
    have bounds := hin.bounds
    have size := hin.size
    try simp only [← Array.set!_eq_setIfInBounds]
    try rw [rotate_read _ _ _ _ (by omega) (by omega) (by omega)]
    first
      | exact hin.hit_min (by omega) (by assumption)
      | exact hin.hit_second (by omega) (by assumption)
      | exact hin.new_min (by omega) (by assumption)
      | exact hin.new_second (by omega) (by omega) (by assumption)
      | exact hin.above (by omega) (by omega)

end CountSort

/-- Prove a property of count splitting from its uniform-cell return and
fragment installation. The latter receives the verified insertion result. -/
theorem splitCounts_induct (level first : Nat) (distance : Bool) (s : RefineSt n)
    (P : RefineSt n → Prop) (hf : first ≤ s.cellend[first]!)
    (hb : s.cellend[first]! < s.lab.size)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (uniform : (∀ q, first ≤ q → q ≤ s.cellend[first]! →
      s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!) → P (s.hash first))
    (finish : ∀ lab w1 v2 w2 v3,
      Minima.Permuted s.lab lab s.hits first (s.cellend[first]! + 1)
        v2 v3 (s.cellend[first]! + 1) w1 w2 (n + 2) →
      P (CountSort.finish level first (s.cellend[first]! + 1) distance
        { s.hash first with lab } w1 v2 w2 v3)) :
    P (splitCounts level first distance s) := by
  have hv := CountSort.firstRun_spec s.lab s.hits first (s.cellend[first]! + 1) (by omega)
  have hm := CountSort.minima_valid s.lab s.hits (n + 2) first (s.cellend[first]! + 1)
    (CountSort.firstRun s.lab s.hits first (s.cellend[first]! + 1))
    hv.1 hv.2.1 (by omega) (fun q hq he => hk q hq (by omega)) hv.2.2.1
  rw [splitCounts_parts]
  dsimp only
  split
  · next he =>
    simp only [beq_iff_eq] at he
    apply uniform
    intro q hq hq'
    exact hv.2.2.1 q hq (by omega)
  · exact finish _ _ _ _ _ hm

end Hex.GraphIso.Nauty.Sparse
