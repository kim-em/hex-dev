/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineParts
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.Refinement

open Std.Do
set_option mvcgen.warning false

/-- The literal packed active scan exhausts its bounded queue enumeration. -/
theorem queue_scan (active : VSet n) : ActiveScan active (queue active) none := by
  have done {q : Array Nat} {next : Option Nat} (h : ActiveScan active q next)
      (hl : next ≠ none → q.size = n) : ActiveScan active q none := by
    by_cases hn : next = none
    · exact hn ▸ h
    · exact h.exhausted (by rw [hl hn]; exact Nat.le_refl _) ▸ h
  unfold queue
  apply Id.of_wp_run_eq rfl (fun q => ActiveScan active q none)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜ActiveScan active state.1 state.2 ∧
      (state.2 ≠ none → state.1.size = cursor.prefix.length)⌝)
  all_goals simp_all +zetaDelta
  all_goals try grind only [ActiveScan.initial, ActiveScan.step, done]
  all_goals try exact ActiveScan.initial active
  case vc1.step.h_1 =>
    rename_i hn hin
    exact hin.1.step rfl
  case vc2.step.h_2 =>
    rename_i next hnone he hin
    cases next <;> simp_all
  case vc4.post.success =>
    rename_i hin
    exact done hin.1 hin.2

/-- Index rebuilding establishes a valid working state from any bounded
scratch, regardless of its old cache flag and contents. -/
theorem initial_valid (level : Nat) (lab ptn : Array Nat) (active : VSet n)
    (numcells : Nat) (scratch : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n scratch) :
    RefineSt.Valid level (indexed level (start lab ptn active numcells scratch)) := by
  have cached := indexCells_valid lab ptn scratch.cellstart scratch.cellend level hs hend
    (fun i hi => perm_bound hp hi) (fun i j hi hj he => perm_injective hp hi hj he)
    hb.starts_size hb.ends_size
  exact ⟨hp, hs, hend, cached,
    ⟨cached.starts_size, cached.ends_size, hb.hits_size, hb.marks_size, hb.vmarks_size,
      hb.marks_le, hb.vmarks_le⟩, CellQueue.of_scan (queue_scan active) ha⟩

/-- Initial observations depend on cell contents and the supplied count,
independently of rebuilt index representations and scratch contents. -/
theorem initial_equiv (σ : Renaming n) (level : Nat) (lab out ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (s t : Scratch)
    (hc : cellsPerm ptn level out (lab.map σ.toFun)) :
    RefineSt.Equiv σ level (indexed level (start lab ptn active numcells s))
      (indexed level (start out ptn active numcells t)) := ⟨rfl, hc, rfl, rfl⟩

/-- The literal final hash cleanup preserves observation equivalence. -/
theorem finish_equiv {s t : RefineSt n} (h : RefineSt.Equiv σ level s t) :
    RefineSt.Equiv σ level (finish s) (finish t) := by
  refine ⟨h.ptn, h.cells, ?_, h.count⟩
  simp only [finish, CountTrace.control, h.active, h.queue, h.code, h.count]

end Hex.GraphIso.Nauty.Sparse.Refinement
