/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Run
public import HexGraphIso.Nauty.Spec.SpecIso
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

private def endStep (acc : List Nat × Nat) (cl : List Nat) : List Nat × Nat :=
  if cl.isEmpty then acc
  else ((acc.2 + cl.length - 1) :: acc.1, acc.2 + cl.length)

private theorem buckets_classes (G : GraphIso.Sparse.Colored n k)
    (buckets : Array (List Nat)) (hsize : buckets.size = k)
    (h : ∀ c, c < k → buckets[c]! =
      ((List.range n).filter fun v => keyOf G.toDense v == c).reverse) :
    buckets.toList.map List.reverse = (List.range k).map (colorClass G.toDense) := by
  apply List.ext_getElem
  · simp [hsize]
  · intro c hc hd
    have hck : c < k := by simpa [hsize] using hc
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [← getElem!_pos buckets c (by omega), h c hck, List.reverse_reverse]
    exact (colorClass_eq_key hck).symm

/-- The stable bucket loops implement the ordered-colour partition specification.
The dense conversion in this statement is only a proof bridge: neither the
bucket initializer nor the sparse search constructs dense adjacency. -/
theorem initialPartition_eq (G : GraphIso.Sparse.Colored n k) :
    initialPartitionWith n k G.coloring.cells.toArray Fin.val =
      Nauty.initialPartition G.toDense := by
  unfold initialPartitionWith
  apply Id.of_wp_run_eq rfl (fun r : Array Nat × List Nat =>
    r = Nauty.initialPartition G.toDense)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, buckets⟩ => ⌜buckets.size = k ∧
      ∀ c, c < k → buckets[c]! =
        (cursor.prefix.filter fun v => keyOf G.toDense v == c).reverse⌝
  | inv2 buckets hb => ⇓⟨cursor, s⟩ => ⌜
      s.1.toList = (cursor.prefix.map List.reverse).flatten ∧
      (s.2, s.1.size) = (cursor.prefix.map List.reverse).foldl endStep ([], 0)⌝
  | inv3 pref cl suff he s lab ends hc hs => ⇓⟨cursor, a⟩ =>
      ⌜a.toList = s.1.toList ++ cursor.prefix⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.sub_zero, Nat.div_one, Nat.add_sub_cancel,
      Vector.size_toArray] at *
  case vc1.step =>
    rename_i pref i suff b c buckets hb hi
    have him := List.mem_of_range'_eq_append_cons hi
    have hin : i < n := by
      have hi' := (List.mem_range'_1.mp him).2
      omega
    have hkey : keyOf G.toDense i = (G.coloring.cells[i]'hin).val := by
      simp [keyOf, hin, GraphIso.Sparse.Colored.toDense]
    simp only [hin, ↓reduceDIte, Vector.getElem_toArray]
    constructor
    · simpa using hb.1
    · intro color hc
      have hbc : color < b.size := by omega
      rw [List.filter_append]
      simp only [List.filter_cons, List.filter_nil, List.reverse_append, hkey]
      by_cases he : (G.coloring.cells[i]'hin).val = color
      · rw [he, Array.getElem!_set!_self _ _ _ hbc, hb.2 color hc]
        simp
      · rw [Array.getElem!_set!_ne _ _ _ _ he, hb.2 color hc]
        simp [he]
  case vc2.pre =>
    simp only [Array.size_replicate, List.filter_nil, List.reverse_nil, true_and]
    intro c hc
    rw [getElem!_pos _ c (by simpa using hc)]
    simp
  case vc3.step => simp_all [List.append_assoc]
  case vc4.step.isTrue.pre => simp
  case vc5.step.isTrue.post.success =>
    rename_i pref cl suff hlist st oldlab oldends hc hs a newends he hb
    have hsize := congrArg List.length he
    simp only [Array.length_toList, List.length_append, List.length_reverse] at hsize
    simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil, ← hs.2, endStep]
    simp_all
  case vc6.step.isFalse =>
    rename_i pref cl suff hlist st oldlab oldends hc hs hb
    have he : cl = [] := by simpa using hc
    subst cl
    simpa [endStep] using hs
  case vc8.post.success.post.success =>
    rename_i buckets lab ends st newlab newends hs hb
    have hc := buckets_classes G buckets hb.1 (fun c hc => by
      simpa only [List.range_eq_range'] using hb.2 c hc)
    apply Prod.ext
    · apply Array.toList_inj.mp
      simpa only [Nauty.initialPartition, List.toList_toArray, List.flatMap_id, hc]
        using hs.1
    · have he := congrArg Prod.fst hs.2
      simp only at he
      rw [he, hc]
      rfl

/-- Stable bucketing neither loses nor repeats any vertex. -/
theorem initialPartition_perm (G : GraphIso.Sparse.Colored n k) :
    (initialPartitionWith n k G.coloring.cells.toArray Fin.val).1.toList.Perm
      (List.range n) := by
  rw [initialPartition_eq, Nauty.initialPartition_fst, List.toList_toArray]
  exact flatten_classes_perm G.toDense

@[simp] theorem initialPartition_size (G : GraphIso.Sparse.Colored n k) :
    (initialPartitionWith n k G.coloring.cells.toArray Fin.val).1.size = n := by
  simpa using (initialPartition_perm G).length_eq

theorem initialPartition_sorted (G : GraphIso.Sparse.Colored n k) :
    (initialPartitionWith n k G.coloring.cells.toArray Fin.val).2.Pairwise (· < ·) := by
  rw [initialPartition_eq, Nauty.initialPartition_snd_eq]
  exact endsOf_pairwise _ _

theorem initialPartition_lt (G : GraphIso.Sparse.Colored n k) {e : Nat}
    (he : e ∈ (initialPartitionWith n k G.coloring.cells.toArray Fin.val).2) : e < n := by
  rw [initialPartition_eq, Nauty.initialPartition_snd_eq] at he
  simpa only [Nat.zero_add, totalOf_classes] using endsOf_lt _ 0 e he

theorem initialPartition_last (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    n - 1 ∈ (initialPartitionWith n k G.coloring.cells.toArray Fin.val).2 := by
  rw [initialPartition_eq, Nauty.initialPartition_snd_eq]
  have he := endsOf_last_mem ((List.range k).map (colorClass G.toDense)) 0
    (by simpa only [totalOf_classes] using hn)
  simpa only [Nat.zero_add, totalOf_classes] using he

private theorem ends_length : ∀ (classes : List (List Nat)) (start : Nat),
    (∀ cl ∈ classes, cl ≠ []) → (endsOf classes start).length = classes.length
  | [], _, _ => rfl
  | cl :: classes, start, h => by
    have hc : cl.isEmpty = false := by simpa using h cl (by simp)
    rw [endsOf, hc]
    simp only [Bool.false_eq_true, ite_false, List.length_cons]
    rw [ends_length classes _ (fun c hc => h c (List.mem_cons_of_mem _ hc))]

/-- The colouring is onto, so the initializer creates exactly `k` cells. -/
theorem initialPartition_count (G : GraphIso.Sparse.Colored n k) :
    (initialPartitionWith n k G.coloring.cells.toArray Fin.val).2.length = k := by
  rw [initialPartition_eq, Nauty.initialPartition_snd_eq, ends_length]
  · simp
  · intro cl hcl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcl
    have hck := List.mem_range.mp hc
    obtain ⟨v, hv⟩ := G.toDense.coloring.onto ⟨c, hck⟩
    have hm : v.val ∈ colorClass G.toDense c :=
      mem_colorClass.mpr ⟨v.isLt, hck, hv⟩
    intro he
    rw [he] at hm
    cases hm

end Hex.GraphIso.Nauty.Sparse
