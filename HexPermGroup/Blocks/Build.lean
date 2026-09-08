/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Blocks.Queue

public section

namespace Hex.PermGroup.Blocks

/-- A canonical minimal invariant partition with its independently replayable
sequence of forced unions. -/
structure Solution (S : Array (Perm n)) (seeds : List (Fin n × Fin n)) where
  partition : Partition n
  trace : List (Fin n × Fin n)
  checked : check S seeds partition trace = true

/-- Process the FIFO queue until no closure obligations remain. Effective
merges decrease the block count; redundant requests decrease the queue length. -/
@[expose] def run (S : Array (Perm n)) (seeds : List (Fin n × Fin n))
    (p : Partition n) (todo : List (Fin n × Fin n)) (st : State S seeds p todo) : Solution S seeds :=
  match todo with
  | [] => ⟨p, st.trace, st.check⟩
  | (x, y) :: rest =>
    if h : p.Same x y then run S seeds p rest (st.skip h)
    else run S seeds (p.merge x y) (rest ++ images S x y) (st.merge h)
termination_by (p.roots.length, todo.length)
decreasing_by
  · apply Prod.Lex.right
    simp
  · apply Prod.Lex.left
    have h := p.roots_merge x y h
    omega

/-- Least invariant equivalence relation containing arbitrary independent
seed pairs. Only effective unions enqueue generator images. -/
@[expose] def solve (S : Array (Perm n)) (seeds : List (Fin n × Fin n)) : Solution S seeds :=
  run S seeds (Partition.discrete n) seeds (State.initial S seeds)

namespace Solution

variable {S : Array (Perm n)} {seeds : List (Fin n × Fin n)}

theorem admissible (s : Solution S seeds) : Admissible S seeds s.partition.Same :=
  (check_spec s.checked).1

theorem least (s : Solution S seeds) (R : Fin n → Fin n → Prop)
    (hR : Admissible S seeds R) : s.partition.Refines R :=
  (check_spec s.checked).2 R hR

/-- Any two accepted solutions have the same canonical partition. -/
theorem unique (s t : Solution S seeds) : s.partition = t.partition := by
  apply Partition.ext
  intro x y
  exact ⟨s.least t.partition.Same t.admissible x y,
    t.least s.partition.Same s.admissible x y⟩

/-- At most `n-1` unions are needed; degree zero has an empty trace. -/
theorem trace_bound (s : Solution S seeds) : s.trace.length ≤ n - 1 := by
  have h := s.checked
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  have hl := replay_length h.1.1
  have hd : (Partition.discrete n).roots.length = n := by
    simp only [Partition.roots, Partition.discrete, Hex.Vector.getElem_ofFn']
    rw [List.filter_eq_self.mpr (by simp), List.length_finRange]
  rw [hd] at hl
  by_cases hn : 0 < n
  · have hp := s.partition.roots_pos hn
    omega
  · omega

end Solution

end Hex.PermGroup.Blocks
