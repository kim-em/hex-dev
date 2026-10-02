/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetProps
public import HexGraphIso.Nauty.Sparse.JoinSweep
public import HexGraphIso.Nauty.Sparse.Rows
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

namespace Target

/-- The cell indices met by the representative vertex's adjacency row. -/
@[expose] def row (g : Graph n) (lab : Array Nat) (s : Scratch) (first : Nat) : List Nat :=
  (List.range' g.offsets[lab[first]!]!
    (g.offsets[lab[first]! + 1]! - g.offsets[lab[first]!]!)).map
    fun e => s.cellstart[g.neighbor e]!

/-- The number of partial joins, including a join to the cell itself. -/
@[expose] def score (g : Graph n) (lab : Array Nat) (s : Scratch) (keys : List Nat)
    (first : Nat) : Nat :=
  keys.countP (Join.qualifies (row g lab s first) fun k => s.cellend[k]! - k + 1)

/-- Strict improvement retains the earliest cell on ties. -/
@[expose] def select (score : Nat → Nat) (best : Nat × Nat) (k : Nat) : Nat × Nat :=
  if score k > best.2 then (k, score k) else best

@[expose] def best (keys : List Nat) (score : Nat → Nat) (empty : Nat) : Nat :=
  if keys.isEmpty then empty else (keys.foldl (select score) (keys.headD 0, 0)).1

end Target

private theorem array_head (a : Array Nat) : a[0]! = a.toList.headD 0 := by
  cases a with
  | mk xs => cases xs <;> rfl

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 1200000

/-- Cached target selection attains the first maximum partial-join score.
The reused hit array may initially contain arbitrary values. -/
theorem bestcellCached_spec (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level : Nat)
    (s : Scratch) (l : Label n) (hl : Label.ofArray? n lab = some l)
    (hptn : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hidx : Index.Valid n lab ptn level s.cellstart s.cellend) (hsize : s.hits.size = n) :
    (bestcellCached (.ofGraph G) lab s).1 =
      Target.best (Target.nontrivial (cells ptn level n))
        (Target.score (.ofGraph G) lab s (Target.nontrivial (cells ptn level n))) n := by
  let keys := Target.nontrivial (cells ptn level n)
  let read := fun e => s.cellstart[(Graph.ofGraph G).neighbor e]!
  let sizes := fun k => s.cellend[k]! - k + 1
  let score := Target.score (.ofGraph G) lab s keys
  have key_bound : ∀ k ∈ keys, k < n := fun k hk => Target.bound hptn hend hk
  have hn : n ∉ keys := fun h => Nat.lt_irrefl n (key_bound n h)
  have key_nodup := Target.nodup ptn level n
  have lookup (first e : Nat) (hf : first ∈ keys)
      (he : e < G.offsets[lab[first]! + 1]!) : read e = n ∨ read e ∈ keys := by
    have hfirst := key_bound first hf
    have hv : lab[first]! < n := by
      rw [← Label.ofArray?_get hl first hfirst]
      exact (l.get ⟨first, hfirst⟩).isLt
    have hb := Graph.neighbor_lt G ⟨lab[first]!, hv⟩ he
    exact Target.vertex_index hidx hptn hend l hl ⟨_, hb⟩
  unfold bestcellCached
  apply Id.of_wp_run_eq rfl (fun r : Nat × Scratch => r.1 = Target.best keys score n)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, state⟩ => ⌜
      Target.Scan n ptn level cursor.prefix.length state.2.2 state.2.1.toList ∧
      state.1.size = n ∧ ∀ k ∈ state.2.1.toList, state.1[k]! = 0⌝
  | inv2 => ⇓⟨cursor, state⟩ => ⌜
      cursor.prefix ++ cursor.suffix = keys ∧ state.1.size = n ∧
      (∀ k ∈ keys, state.1[k]! = 0) ∧
      state.2 = cursor.prefix.foldl
        (Target.select (Target.score (.ofGraph G) lab s keys)) (keys.headD 0, 0)⌝
  | inv3 => ⇓⟨cursor, hits⟩ => ⌜
      hits.size = n ∧ Join.Counts keys (cursor.prefix.map read) hits⌝
  | inv4 => ⇓⟨cursor, state⟩ => ⌜
      state.1.size = n ∧ Join.Sweep keys ((cursor.prefix ++ cursor.suffix).map read)
        (cursor.prefix.map read) (fun k => s.cellend[k]! - k + 1) state.1 state.2⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.length_range', List.map_append, List.map_cons, List.map_nil,
      Array.toList_push, Array.size_set!, Bool.and_eq_true, bne_iff_ne,
      decide_eq_true_eq, List.append_nil, List.nil_append] at *
  case vc1.step.isTrue =>
    rename_i hg hin hr
    have hf : _ = n := Nat.le_antisymm hin.1.first_le hg
    refine ⟨⟨by omega, hin.1.first_le, hin.1.boundary, hin.1.before, ?_⟩, hin.2⟩
    refine ⟨cells ptn level n, by simp [cells.go], hin.1.finish (Or.inr hf)⟩
  case vc2.step.isFalse.isTrue =>
    rename_i pre it suff b hits pair starts cursor hg last jp ht ns nh nc hin hr
    have hf : b.2.2 < n := by omega
    have he := hidx.end_eq hptn hend hf hin.1.boundary
    have hu : pre.length < n := by have := hin.1.used_le; omega
    have hstep := hin.1.step hptn hend hu hf
    rw [← he, ite_eq_left ht] at hstep
    refine ⟨hstep, hin.2.1, ?_⟩
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · have hne : b.2.2 ≠ k := by have := hin.1.before k hk; omega
      rw [Array.getElem!_set!_ne _ _ _ _ hne]
      exact hin.2.2 k hk
    · simp only [List.mem_singleton] at hk
      subst k
      exact Array.getElem!_set!_self _ _ _ (by rw [hin.2.1]; exact hf)
  case vc3.step.isFalse.isFalse =>
    rename_i pre it suff b hits pair starts cursor hg last jp ht nc hin hr
    have hf : b.2.2 < n := by omega
    have he := hidx.end_eq hptn hend hf hin.1.boundary
    have hu : pre.length < n := by have := hin.1.used_le; omega
    have hstep := hin.1.step hptn hend hu hf
    rw [← he, ite_eq_right ht] at hstep
    exact ⟨hstep, hin.2⟩
  case vc4.pre => exact ⟨.initial n ptn level, hsize, by simp⟩
  case vc5.post.success.isTrue =>
    rename_i hempty hin
    have hk := hin.1.finish (Or.inl rfl)
    have hz : Target.nontrivial (cells ptn level n) = [] := by
      rw [← hk]
      simpa using congrArg Array.toList (Array.isEmpty_iff.mp hempty)
    simp [Target.best, hz]
  case vc6.step.isTrue =>
    rename_i pre first suff houter old oh op best max v hout pree e sufe arr k nh hin hscan hr hne
    refine ⟨hin.1, hin.2.add ?_⟩
    have he := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Graph.ofGraph] at he
    exact (lookup first e (by rw [← hout.1]; simp) (by omega)).resolve_left hne
  case vc7.step.isFalse =>
    rename_i hin hscan hr he
    simp only [ne_eq, Decidable.not_not] at he
    exact ⟨hin.1, hin.2.skip (by simpa only [he] using hn)⟩
  case vc8.step.pre =>
    rename_i hout hscan
    exact ⟨hout.2.1, Join.Counts.initial (by intro k hk; rw [hout.2.1]; exact key_bound k hk)
      hout.2.2.1⟩
  case vc9.step.isTrue.isTrue =>
    rename_i pre first suff houter old oh op best max v hout counted pree e sufe arr hits count k jp nc nh hscan hc hr hne htest hin
    refine ⟨hin.1, ?_⟩
    have he := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Graph.ofGraph] at he
    have hk := (lookup first e (by rw [← hout.1]; simp) (by omega)).resolve_left hne
    have hh := hin.2.clear key_nodup hk (by simp)
    simpa only [htest, and_self, ite_true, List.append_assoc, List.singleton_append] using hh
  case vc10.step.isTrue.isFalse =>
    rename_i pre first suff houter old oh op best max v hout counted pree e sufe arr hits count k jp nh hscan hc hr hne htest hin
    refine ⟨hin.1, ?_⟩
    have he := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Graph.ofGraph] at he
    have hk := (lookup first e (by rw [← hout.1]; simp) (by omega)).resolve_left hne
    have hh := hin.2.clear key_nodup hk (by simp)
    simpa only [htest, ite_false, Nat.add_zero, List.append_assoc, List.singleton_append] using hh
  case vc11.step.isFalse =>
    rename_i hscan hc hr he hin
    simp only [ne_eq, Decidable.not_not] at he
    have hh := hin.2.skip (by simpa only [he] using hn)
    exact ⟨hin.1, by simpa only [he, List.append_assoc, List.singleton_append] using hh⟩
  case vc12.step.post.success.pre =>
    rename_i hscan hin
    exact ⟨hin.1, Join.Sweep.initial _ hin.2⟩
  case vc13.step.post.success.post.success.isTrue =>
    rename_i hout hitout result hits count htest hscan hc hin
    obtain ⟨hcount, hz⟩ := hin.2.finish
    refine ⟨by simpa only [List.append_assoc, List.singleton_append] using hout.1, hin.1, hz, ?_⟩
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hout.2.2.2]
    simp only [Target.select, Target.score, Target.row, ← hcount, ite_eq_left htest]
  case vc14.step.post.success.post.success.isFalse =>
    rename_i hout hitout result hits count htest hscan hc hin
    obtain ⟨hcount, hz⟩ := hin.2.finish
    refine ⟨by simpa only [List.append_assoc, List.singleton_append] using hout.1, hin.1, hz, ?_⟩
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hout.2.2.2]
    simp only [Target.select, Target.score, Target.row, ← hcount, ite_eq_right htest]
  case vc15.post.success.isFalse.pre =>
    rename_i hempty hin
    have hk := hin.1.finish (Or.inl rfl)
    refine ⟨hk, hin.2.1, ?_, ?_⟩
    · simpa only [hk] using hin.2.2
    · simp only [List.foldl_nil, Prod.mk.injEq, and_true]
      rw [← hk]
      exact array_head _
  case vc16.post.success.isFalse.post.success =>
    rename_i hempty first r hits pair best max hscan hin
    have hk := hin.1
    have hz : (Target.nontrivial (cells ptn level n)).isEmpty = false := by
      rw [← hk]
      simpa using hempty
    simp only [Target.best, hz, Bool.false_eq_true, ite_false]
    exact congrArg Prod.fst (by simpa only [hk] using hin.2.2.2)

end Hex.GraphIso.Nauty.Sparse
