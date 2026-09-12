/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SingletonCongr
public import HexGraphIso.Nauty.Sparse.NontrivialCongr
public import HexGraphIso.Nauty.Sparse.RefineParts

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Queue removal, hashing and the actual splitter branch retain literal
label agreement between two admissible refinement states. -/
theorem RefineSt.Equiv.selected_lab (G : Hex.SparseGraph n)
    {s t : RefineSt n} (h : RefineSt.Equiv σ level s t)
    (hs : s.Valid level) (ht : t.Valid level) (hl : t.lab = s.lab)
    (pos : Nat) (hp : pos < s.queue.size) :
    (RefineSt.selected (.ofGraph G) level pos s).lab =
      (RefineSt.selected (.ofGraph G) level pos t).lab := by
  have hp' : pos < t.queue.size := h.queue ▸ hp
  have hc := hs.queue_cell hp
  let a := ({ s with
    active := s.active.erase s.queue[pos]!
    queue := (s.queue.set! pos s.queue[s.queue.size - 1]!).pop }).hash s.queue[pos]!
  let b := ({ t with
    active := t.active.erase t.queue[pos]!
    queue := (t.queue.set! pos t.queue[t.queue.size - 1]!).pop }).hash t.queue[pos]!
  have ha : RefineSt.Valid level a := (hs.remove hp).hash s.queue[pos]!
  have hb : RefineSt.Valid level b := (ht.remove hp').hash t.queue[pos]!
  change (if s.ptn[s.queue[pos]!]! ≤ level then splitSingleton (.ofGraph G) level s.queue[pos]! a
      else splitNontrivial (.ofGraph G) level s.queue[pos]! a).lab =
    (if t.ptn[t.queue[pos]!]! ≤ level then splitSingleton (.ofGraph G) level t.queue[pos]! b
      else splitNontrivial (.ofGraph G) level t.queue[pos]! b).lab
  rw [h.ptn, ← h.queue]
  split
  · exact splitSingleton_lab G level _ a b ha hb hl h.ptn hc.1
  · exact splitNontrivial_lab G level _ _ a b ha hb hl h.ptn hc.2.1 (by omega)

/-- The complete native main loop preserves literal label equality through
first-ten queue preference, swap/pop removal, both splitter branches and
both stopping guards. -/
theorem Refinement.loop_lab (G : Hex.SparseGraph n) (level : Nat) (s t : RefineSt n)
    (hs : s.Valid level) (ht : t.Valid level)
    (he : RefineSt.Equiv (renamingOf (Perm.id n)) level s t) (hl : t.lab = s.lab) :
    (loop (.ofGraph G) level s).lab = (loop (.ofGraph G) level t).lab := by
  let R (a b : RefineSt n) := a.Valid level ∧ b.Valid level ∧
    RefineSt.Equiv (renamingOf (Perm.id n)) level a b ∧ b.lab = a.lab
  let step (_ : Nat) (a : RefineSt n) : Id (ForInStep (RefineSt n)) :=
    if a.queue.isEmpty || a.numcells >= n then .done a
    else .yield (RefineSt.selected (.ofGraph G) level (a.position level) a)
  have hr := Loop.range_rel n step step R (by
    intro i a b h
    rcases h with ⟨ha, hb, he, hl⟩
    dsimp only [step]
    rw [← he.queue, ← he.count]
    by_cases hstop : (a.queue.isEmpty || decide (a.numcells ≥ n)) = true
    · simp only [ite_eq_left hstop]
      exact .done ⟨ha, hb, he, hl⟩
    · simp only [ite_eq_right hstop]
      have hsize : 0 < a.queue.size := by
        simp only [Bool.or_eq_true, Array.isEmpty, decide_eq_true_eq] at hstop
        omega
      have hp := RefineSt.position_lt level a hsize
      have hp' : RefineSt.position level a < b.queue.size := he.queue ▸ hp
      rw [← he.position]
      exact .yield ⟨ha.selected G level _ a hp, hb.selected G level _ b hp',
        he.selected G G (Perm.id n) (by intro u v; simp) ha hb _ hp,
        (he.selected_lab G ha hb hl _ hp).symm⟩)
    (show R s t from ⟨hs, ht, he, hl⟩)
  simpa only [loop, step, RefineSt.position, RefineSt.selected, Id.run, bind, pure,
    apply_ite ForInStep.yield] using hr.2.2.2.symm

end Hex.GraphIso.Nauty.Sparse
