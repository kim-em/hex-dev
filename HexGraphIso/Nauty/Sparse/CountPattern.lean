/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine.CountSpec
public import HexGraphIso.Nauty.Sparse.CountPartition
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- Fragment installation closes exactly the boundaries between unequal
adjacent counts and preserves every other partition value. -/
theorem CountSort.finish_partition (level first last : Nat) (distance : Bool)
    (s : RefineSt n) (w1 v2 w2 v3 : Nat)
    (hb : last ≤ s.ptn.size)
    (hm : Minima.Bounded s.lab s.hits first last v2 v3 last w1 w2 (n + 2)) :
    CountPartition level first (last - 1)
      (CountSort.finish level first last distance s w1 v2 w2 v3).lab s.hits s.ptn
      (CountSort.finish level first last distance s w1 v2 w2 v3).ptn := by
  have bounds := hm.positions
  have gap : v2 < last → v2 < v3 := hm.second_pos
  cases distance <;> unfold CountSort.finish
  all_goals simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
  all_goals apply Id.of_wp_run_eq rfl (fun t : RefineSt n =>
    CountPartition level first (last - 1) t.lab s.hits s.ptn t.ptn)
  all_goals mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨cursor, state⟩ => ⌜
          CountPartition level first state.2.2.2 state.1.lab s.hits s.ptn state.1.ptn ∧
          first ≤ state.2.2.2 ∧ state.2.2.2 ≤ last - 1 ∧
          (state.2.2.2 = last - 1 ∨
            s.hits[state.1.lab[state.2.2.2]!]! ≠ s.hits[state.1.lab[state.2.2.2 + 1]!]!) ∧
          last - 1 ≤ state.2.2.2 + cursor.suffix.length ∧ state.1.hits = s.hits⌝)
      | exact (let r : RefineSt n × Option Nat × Nat × Nat := by assumption
          ⇓⟨cursor, state⟩ => ⌜
            r.2.2.2 + 1 ≤ state.2 ∧ state.2 + cursor.suffix.length ≤ last - 1 ∧
            state.1.lab = r.1.lab ∧ state.1.hits = s.hits ∧
            CountPartition level first state.2 state.1.lab s.hits s.ptn state.1.ptn ∧
            s.hits[state.1.lab[state.2]!]! = s.hits[r.1.lab[r.2.2.2 + 1]!]! ∧
            (state.2 = r.2.2.2 + 1 + cursor.prefix.length ∨
              s.hits[state.1.lab[state.2 + 1]!]! ≠ s.hits[r.1.lab[r.2.2.2 + 1]!]!)⌝)
      | exact (⇓_ => ⌜True⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push]
    try omega
  all_goals try
    exact CountPartition.constant (fun q hq hu => hm.minimum q hq (by omega))
  all_goals try
    rename_i hin
    have he := Nat.le_antisymm hin.2.2.1 hin.2.2.2.2.1
    simpa only [he] using hin.1
  all_goals try
    have bounds := hm.positions
    have gap := hm.second_pos (by omega)
    have hp := CountPartition.minima (level := level) hm.toMinima gap
      (by omega : _ < s.ptn.size)
    grind
  all_goals try grind [CountPartition.equal, CountPartition.different]
  all_goals try
    have bounds := hm.positions
    have gap := hm.second_pos (by omega)
    have ht := hm.toMinima.indirect hm.size
    have hp := CountPartition.minima (level := level) ht gap
      (by omega : _ < s.ptn.size)
    have hn := ht.next_different gap (by omega)
    grind

/-- Count splitting closes exactly the boundaries between unequal counts. -/
theorem splitCounts_partition (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hs : s.ptn.size = n) (hf : first ≤ s.cellend[first]!)
    (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    CountPartition level first s.cellend[first]!
      (splitCounts level first distance s).lab s.hits s.ptn
      (splitCounts level first distance s).ptn := by
  apply splitCounts_induct level first distance s
    (fun t => CountPartition level first s.cellend[first]! t.lab s.hits s.ptn t.ptn)
    hf (by omega) hk
  · intro hu; exact CountPartition.constant hu
  · intro lab w1 v2 w2 v3 hm
    exact CountSort.finish_partition level first (s.cellend[first]! + 1) distance
      { s.hash first with lab } w1 v2 w2 v3 (by dsimp only [RefineSt.hash]; omega) hm.toBounded

end Hex.GraphIso.Nauty.Sparse
