/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BfsScan
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

/-- The executed packed-adjacency BFS computes shortest-path distances,
including its early exit once all vertices have been discovered. -/
theorem distvals_correct (G : Hex.SparseGraph n) (root : Fin n) :
    Distances G root (distvals (.ofGraph G) root.val) := by
  unfold distvals
  apply Id.of_wp_run_eq rfl (fun a : Array Nat => Distances G root a)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜
      Bfs G root s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
      (s.2.2.1 = cursor.prefix.length ∨ n ≤ s.2.2.2 ∨ s.2.2.2 ≤ s.2.2.1)⌝
  | inv2 pref it suff hr outer dist pair queue pair2 head tail hguard i newhead next hout =>
      ⇓⟨cursor, s⟩ => ⌜Scan G root s.1 s.2.1 head s.2.2 i next cursor.prefix⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.add_sub_cancel, Nat.sub_zero,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.length_range', Graph.ofGraph, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq] at *
  case vc1.step.isTrue =>
    rename_i hin hr hguard
    exact ⟨hin.1, Or.inr hguard⟩
  case vc2.step.isTrue =>
    rename_i hin hr hguard he hnew
    have he' := List.mem_of_range'_eq_append_cons he
    simp only [List.mem_range'_1] at he'
    exact hin.add (by omega) (by omega) hnew
  case vc3.step.isFalse =>
    rename_i hin hr hguard he hnew
    have he' := List.mem_of_range'_eq_append_cons he
    simp only [List.mem_range'_1] at he'
    exact hin.keep (by omega) hnew
  case vc4.step.isFalse.pre =>
    rename_i hin hr hguard
    exact Scan.initial hin.1 (by omega) (by omega)
  case vc5.step.isFalse.post.success =>
    rename_i hin
    refine ⟨hin.finish, Or.inl ?_⟩
    omega
  case vc6.pre => exact ⟨Bfs.initial G root, Or.inl trivial⟩
  case vc7.post.success =>
    rename_i hin
    apply hin.1.complete
    have hh := hin.1.head_le
    have ht := hin.1.tail_le
    omega

@[simp] theorem distvals_root (G : Hex.SparseGraph n) (root : Fin n) :
    (distvals (.ofGraph G) root.val)[root.val]! = 0 := (distvals_correct G root).root_eq

theorem distvals_unreachable (G : Hex.SparseGraph n) (root v : Fin n) :
    (distvals (.ofGraph G) root.val)[v.val]! = n ↔ ¬∃ length, Walk G root v length :=
  (distvals_correct G root).unreachable

/-- Relabelling changes queue order but preserves all computed distances. -/
theorem distvals_relabel (G : Hex.SparseGraph n) (p : Perm n) (root v : Fin n) :
    (distvals (.ofGraph (G.relabel p)) root.val)[v.val]! =
      (distvals (.ofGraph G) (p.get root).val)[(p.get v).val]! := by
  have hnew := distvals_correct (G.relabel p) root
  have hold := distvals_correct G (p.get root)
  have hn := hnew.bound v
  have ho := hold.bound (p.get v)
  by_cases hf : (distvals (.ofGraph (G.relabel p)) root.val)[v.val]! < n
  · have hwalk := (Walk.relabel p).mp (hnew.sound v hf)
    have hle := hold.complete hwalk
    have hwalk' := (Walk.relabel p).mpr (hold.sound (p.get v) hle.1)
    have hle' := hnew.complete hwalk'
    omega
  · have hfinite : ¬(distvals (.ofGraph G) (p.get root).val)[(p.get v).val]! < n := by
      intro h
      exact hf (hnew.complete ((Walk.relabel p).mpr (hold.sound (p.get v) h))).1
    omega

end Hex.GraphIso.Nauty.Sparse
