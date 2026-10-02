/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountProgress
public import HexGraphIso.Nauty.Sparse.CountUniform
public import HexGraphIso.Nauty.Sparse.Refine.CountSpec
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do CountTrace
set_option mvcgen.warning false
set_option maxHeartbeats 3000000

/-- The fragment installer emits the count-run control trace, including
both hash conventions and the final largest-fragment replacement. -/
theorem CountSort.finish_trace (level first last : Nat) (distance : Bool) (s : RefineSt n)
    (lab : Array Nat) (w1 v2 w2 v3 : Nat)
    (hm : Minima.Permuted s.lab lab s.hits first last v2 v3 last w1 w2 (n + 2))
    (hn : ∃ q, first ≤ q ∧ q < last ∧ s.hits[s.lab[q]!]! ≠ s.hits[s.lab[first]!]!) :
    let t := CountSort.finish level first last distance { s.hash first with lab } w1 v2 w2 v3
    Result distance first last s t.lab (control t) := by
  have bounds := hm.positions
  have hv2 : v2 < last := by
    apply Nat.lt_of_le_of_ne (by omega)
    intro he
    obtain ⟨q, hq, hq', hne⟩ := hn
    exact hne (hm.constant he hq hq')
  have hv := hm.toBounded.second_pos hv2
  cases hmode : distance <;> unfold CountSort.finish
  all_goals simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
  all_goals apply Id.of_wp_run_eq rfl (fun t : RefineSt n => Result _ first last s t.lab (control t))
  all_goals mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨cursor, state⟩ => ⌜state.1.hits = s.hits ∧
          Progress distance first (last) s state.1.lab state.2.2.2
            (control state.1) state.2.1 state.2.2.1 ∧
          (last - 1) ≤ state.2.2.2 + cursor.suffix.length⌝)
      | exact (let r : RefineSt n × Option Nat × Nat × Nat := by assumption
          ⇓⟨cursor, state⟩ => ⌜
            state.1.lab = r.1.lab ∧ state.1.hits = s.hits ∧
            control state.1 = (control r.1).advance distance r.2.2.2 s.hits[r.1.lab[r.2.2.2 + 1]!]! ∧
            CountTrace.Scan r.1.lab s.hits (r.2.2.2 + 1) (last - 1)
              state.2 cursor.prefix.length cursor.suffix.length⌝)
      | exact (⇓_ => ⌜True⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, CountTrace.control,
      Std.Legacy.Range.toList, ← Option.eq_none_iff_forall_ne_some]
    try omega
  all_goals try
    have bounds := hm.positions
    have hv := hm.toBounded.second_pos (by omega)
    refine Result.divided hn hm.toMinima hv ?_
    simp_all [Control.base, Control.hash, Control.pair, Control.push, CountTrace.control]
  all_goals try
    rename_i hin
    have hp := hin.2.1
    have bounds := hp.bounds
    have hd := hp.done (by omega)
    simp_all [Control.finish, Control.hash, Array.set!_eq_setIfInBounds]
  all_goals try
    have bounds := hm.positions
    have hv := hm.toBounded.second_pos (by omega)
    have hi := Progress.initial (distance := distance) hn (hm.toMinima.indirect hm.size) hv (by omega)
    simp_all [Control.more, Control.base, Control.hash, Control.push, CountTrace.control]
    all_goals try simp (disch := omega) only [ite_eq_right] at hi
    all_goals try simp_all
    all_goals omega
  all_goals try
    rename_i hi0
    have hi := hi0.2.2.2
    first
      | exact hi.step (by assumption)
      | exact hi.stop (by assumption)
  all_goals try
    constructor
    · rfl
    · exact CountTrace.Scan.initial (by omega)
  all_goals try
    rename_i ho hh hi
    have hr := hi.2.2.2.run
    have hp := ho.2.1.next (by omega) hr
    have bounds := hr.bounds
    have budget := ho.2.2
    have hq := congrArg Control.queue hi.2.2.1
    simp_all [Control.choose, Control.advance, Control.hash, Control.push]
    all_goals try simp (disch := omega) only [ite_eq_right] at hp
    all_goals try simp_all
    all_goals omega
  all_goals try
    rename_i ho hh hh2 hi
    have hr := hi.2.2.2.run
    have hp := ho.2.1.next (by omega) hr
    have bounds := hr.bounds
    have budget := ho.2.2
    have hq := congrArg Control.queue hi.2.2.1
    simp_all [Control.choose, Control.advance, Control.hash, Control.push]
    all_goals try simp (disch := omega) only [ite_eq_right] at hp
    all_goals try simp_all
    all_goals omega


/-- Every executed count split has its literal hash and queue trace. -/
theorem splitCounts_trace (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hl : s.lab.size = n) (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2) :
    Result distance first (s.cellend[first]! + 1) s
      (splitCounts level first distance s).lab (control (splitCounts level first distance s)) := by
  classical
  by_cases hu : ∀ q, first ≤ q → q < s.cellend[first]! + 1 →
      s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!
  · rw [splitCounts_uniform level first distance s hf (fun q hq he => hu q hq (by omega))]
    exact Result.uniform hu
  · have hn : ∃ q, first ≤ q ∧ q < s.cellend[first]! + 1 ∧
        s.hits[s.lab[q]!]! ≠ s.hits[s.lab[first]!]! := by
      apply Classical.byContradiction
      intro hn
      apply hu
      intro q hq he
      apply Classical.byContradiction
      intro hne
      exact hn ⟨q, hq, he, hne⟩
    apply splitCounts_induct level first distance s
      (fun t => Result distance first (s.cellend[first]! + 1) s t.lab (control t))
      hf (by omega) hk
    · intro h
      exact False.elim (hu (fun q hq he => h q hq (by omega)))
    · intro lab w1 v2 w2 v3 hm
      exact CountSort.finish_trace level first (s.cellend[first]! + 1) distance s lab w1 v2 w2 v3 hm hn

end Hex.GraphIso.Nauty.Sparse
