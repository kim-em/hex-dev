/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineEquiv
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.RefineSt

/-- The literal first-ten singleton-preference expression in `refineWith`.
This name is used only to factor its proof; production keeps the inline loop. -/
@[expose] def position (level : Nat) (s : RefineSt n) : Nat := Id.run do
  let mut pos := s.queue.size - 1
  for i in [0:min s.queue.size 10] do
    if s.ptn[s.queue[i]!]! <= level then
      pos := i
      break
  return pos

open Std.Do
set_option mvcgen.warning false

/-- Singleton preference always selects an allocated entry when the queue
is nonempty, including its fallback to the last entry. -/
theorem position_lt (level : Nat) (s : RefineSt n) (h : 0 < s.queue.size) :
    position level s < s.queue.size := by
  unfold position
  apply Id.of_wp_run_eq rfl (fun pos => pos < s.queue.size)
  mvcgen
  case inv1 => exact (⇓⟨_, pos⟩ => ⌜pos < s.queue.size⌝)
  all_goals simp_all
  all_goals try omega
  all_goals
    rename_i pref i rest hr state hin hp
    have hi := range_cursor (Nat.zero_le (min s.queue.size 10)) hr
    omega

/-- The literal preference scan depends only on ordered partition and queue. -/
theorem Equiv.position {s t : RefineSt n} (h : Equiv σ level s t) :
    position level s = position level t := by
  simp only [RefineSt.position, h.ptn, h.queue]

/-- The literal removal, hashing and splitter dispatch after selecting a
queue position. This expression is kept separate only in the proof. -/
@[expose] def selected (g : Graph n) (level pos : Nat) (s : RefineSt n) : RefineSt n :=
  let split := s.queue[pos]!
  let queue := (s.queue.set! pos s.queue[s.queue.size - 1]!).pop
  let s := ({ s with queue, active := s.active.erase split }).hash split
  if s.ptn[split]! <= level then splitSingleton g level split s
  else splitNontrivial g level split s

/-- An actual selected splitter preserves the full working-state invariant. -/
theorem Valid.selected (G : Hex.SparseGraph n) (level pos : Nat) (s : RefineSt n)
    (h : Valid level s) (hp : pos < s.queue.size) :
    Valid level (selected (.ofGraph G) level pos s) := by
  have hc := h.queue_cell hp
  have ht := (h.remove hp).hash s.queue[pos]!
  unfold RefineSt.selected
  dsimp only
  split
  · exact (ht.singleton G _ hc.1).1
  · exact (ht.nontrivial G _ _ hc.2.1 (by omega)).1

end Hex.GraphIso.Nauty.Sparse.RefineSt
