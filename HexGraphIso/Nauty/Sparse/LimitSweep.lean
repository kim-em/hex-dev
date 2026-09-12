/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.LimitProjection
import all HexGraphIso.Nauty.Search.Generic

public section

namespace Hex.GraphIso.Nauty.Sparse.Limited

/-- One bounded sibling step projects to the native step, including
first-child cleanup, orbit skips and nonlocal child returns. -/
theorem sweepStep_eq {descend : Generic.NodeFn (State n)}
    {plainDescend : Generic.NodeFn (Sparse.State n)}
    {next : Generic.SweepFn (State n) n} {plainNext : Generic.SweepFn (Sparse.State n) n}
    (hd : NodeEq descend plainDescend) (hn : SweepEq next plainNext)
    (inf : Nat) (first : Bool) (level nc tc tv1 tv index : Nat) (cell : VSet n) (s : State n)
    (h : Ready (Generic.sweepStep inf descend next first level nc tc tv1 tv cell index s).2.2) :
    Ready s ∧ sweepValue (Generic.sweepStep inf descend next first level nc tc tv1 tv cell index s) =
      Generic.sweepStep inf plainDescend plainNext first level nc tc tv1 tv cell index s.value := by
  unfold Generic.sweepStep at h
  simp only [Id.run_pure, apply_ite Id.run] at h
  split at h
  · rename_i hg
    generalize he : descend (first && tv == tv1) (level + 1) (nc + 1)
      ((policy (n := n)).child first level tc tv s) = r at h
    obtain ⟨exit, out⟩ := r
    by_cases hb : (first && tv == tv1) = true
    all_goals
      simp only [hb, Bool.false_eq_true, ite_true, ite_false] at h
      have hr := advance_eq hn inf first level nc tc tv1 tv index cell _ exit h
      have hleft := (leave_ready tv _).mp hr.1
      have hout : Ready out := by
        first | exact hleft | exact (afterFirst_ready level tv1 out).mp hleft
      have hdret := hd (first && tv == tv1) (level + 1) (nc + 1)
        ((policy (n := n)).child first level tc tv s) (by rw [he]; exact hout)
      have hs := (child_ready first level tc tv s).mp hdret.1
      have hePlain : plainDescend (first && tv == tv1) (level + 1) (nc + 1)
          ((Sparse.policy (n := n)).child first level tc tv s.value) = (exit, out.value) := by
        have hh := hdret.2
        rw [he] at hh
        simpa only [nodeValue, child_value first level tc tv hs] using hh.symm
      have hg' : (!first || (Sparse.policy (n := n)).orbit s.value tv == tv) = true := by
        simpa only [orbit_value tv hs] using hg
      have he' := he
      simp only [hb] at he' hePlain
      refine ⟨hs, ?_⟩
      simpa only [Generic.sweepStep, Id.run_pure, apply_ite Id.run,
        orbit_value tv hs, hg', hb, Bool.false_eq_true, ite_true, ite_false, he', hePlain,
        leave_value tv hleft, afterFirst_value level tv1 hout] using hr.2
  · rename_i hg
    have hr := hn first level nc tc tv1 _ _ _ s h
    have hg' : ¬(!first || (Sparse.policy (n := n)).orbit s.value tv == tv) = true := by
      simpa only [orbit_value tv hr.1] using hg
    refine ⟨hr.1, ?_⟩
    simpa only [Generic.sweepStep, Id.run_pure, apply_ite Id.run, orbit_value tv hr.1,
      hg', Bool.false_eq_true, ite_false] using hr.2

end Hex.GraphIso.Nauty.Sparse.Limited
