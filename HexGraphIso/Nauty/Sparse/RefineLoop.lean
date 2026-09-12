/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineBranches
public import HexGraphIso.Nauty.Sparse.LoopRel

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The full literal main refinement loop transports its observations,
including both stopping guards, first-ten preference, swap/pop removal,
hashing and both native splitter branches. -/
theorem refine_loop_equiv (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (level : Nat) (s t : RefineSt n)
    (hs : RefineSt.Valid level s) (ht : RefineSt.Valid level t)
    (he : RefineSt.Equiv (renamingOf p) level s t) :
    let run (g : Graph n) (s : RefineSt n) := Id.run do
      let mut s := s
      for _ in [0:n] do
        if s.queue.isEmpty || s.numcells >= n then break
        let mut pos := s.queue.size - 1
        for i in [0:min s.queue.size 10] do
          if s.ptn[s.queue[i]!]! <= level then
            pos := i
            break
        let split := s.queue[pos]!
        let queue := (s.queue.set! pos s.queue[s.queue.size - 1]!).pop
        s := { s with queue, active := s.active.erase split }
        s := s.hash split
        if s.ptn[split]! <= level then s := splitSingleton g level split s
        else s := splitNontrivial g level split s
      return s
    RefineSt.Equiv (renamingOf p) level (run (.ofGraph G) s) (run (.ofGraph H) t) := by
  let R (a b : RefineSt n) := RefineSt.Valid level a ∧ RefineSt.Valid level b ∧
    RefineSt.Equiv (renamingOf p) level a b
  let step (g : Graph n) (_ : Nat) (a : RefineSt n) : Id (ForInStep (RefineSt n)) :=
    if a.queue.isEmpty || a.numcells >= n then .done a
    else .yield (RefineSt.selected g level (a.position level) a)
  have hr := Loop.range_rel n (step (.ofGraph G)) (step (.ofGraph H)) R (by
    intro _i a b h
    rcases h with ⟨ha, hb, he⟩
    dsimp only [step]
    rw [← he.queue, ← he.count]
    by_cases hstop : (a.queue.isEmpty || decide (a.numcells ≥ n)) = true
    · simp only [ite_eq_left hstop]
      exact .done ⟨ha, hb, he⟩
    · simp only [ite_eq_right hstop]
      have hsize : 0 < a.queue.size := by
        simp only [Bool.or_eq_true, Array.isEmpty, decide_eq_true_eq] at hstop
        omega
      have hpos := RefineSt.position_lt level a hsize
      have hpos' : RefineSt.position level a < b.queue.size := he.queue ▸ hpos
      rw [← he.position]
      exact .yield ⟨ha.selected G level _ a hpos, hb.selected H level _ b hpos',
        he.selected G H p hiso ha hb _ hpos⟩)
    (show R s t from ⟨hs, ht, he⟩)
  apply Eq.mp (congr (congrArg (RefineSt.Equiv (renamingOf p) level) ?_) ?_) hr.2.2
  all_goals
    simp only [step, RefineSt.position, RefineSt.selected, Id.run, bind, pure,
      apply_ite ForInStep.yield]

end Hex.GraphIso.Nauty.Sparse
