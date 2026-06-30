/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section

/-!
Low-level vector update helper used for efficient code generation.
-/

namespace Vector

/--
In-place update of the element at index `i` via `f`, wrapping `Array.modify`
so the underlying swap-with-placeholder ownership transfer survives codegen.
Calling `xs.set i (f xs[i])` forces a `lean_inc` on the borrowed entry and
loses uniqueness on nested-array shapes (e.g. matrix rows); `modify` avoids
that copy when `xs` is uniquely owned.
-/
@[expose, inline] def modify (xs : Vector α n) (i : Nat) (f : α → α) : Vector α n :=
  ⟨xs.toArray.modify i f, by simp⟩

/-- Entrywise read of `modify`: the modified index gets `f` applied, every other
index is unchanged. -/
@[grind =] theorem getElem_modify {xs : Vector α n} {i : Nat} {f : α → α}
    {j : Nat} (hj : j < n) :
    (xs.modify i f)[j] = if i = j then f xs[j] else xs[j] := by
  rcases xs with ⟨a, rfl⟩
  simp only [modify, Vector.getElem_mk]
  rw [Array.getElem_modify]

/-- The modified index of `modify` reads back `f` applied to the old value. -/
theorem getElem_modify_self {xs : Vector α n} {i : Nat} {f : α → α} (hi : i < n) :
    (xs.modify i f)[i] = f xs[i] := by
  rw [getElem_modify hi, if_pos rfl]

/-- Any index other than the modified one is unchanged by `modify`. -/
theorem getElem_modify_of_ne {xs : Vector α n} {i j : Nat} {f : α → α}
    (hj : j < n) (h : i ≠ j) :
    (xs.modify i f)[j] = xs[j] := by
  rw [getElem_modify hj, if_neg h]

/-- `modify` agrees with the read-then-`set` form (value-level; `modify` avoids
the copy this form would force). -/
theorem modify_eq_set (xs : Vector α n) (i : Nat) (f : α → α) (h : i < n) :
    xs.modify i f = xs.set i (f xs[i]) := by
  apply Vector.ext
  intro j hj
  rw [getElem_modify hj, Vector.getElem_set]
  grind

/-- A left fold of per-index `modify`s over a list of `Fin n` indices leaves
index `r` untouched when `r` is not among the folded indices. The backing engine
for the in-place indexed row scatter (`Matrix.mapRowsIdx`). -/
theorem getElem_foldl_modify_not_mem (g : Fin n → α → α)
    {r : Nat} (hr : r < n) :
    ∀ (xs : List (Fin n)) (v0 : Vector α n), (∀ i ∈ xs, i.val ≠ r) →
      (xs.foldl (fun v i => v.modify i.val (g i)) v0)[r] = v0[r] := by
  intro xs
  induction xs with
  | nil => intro v0 _; rfl
  | cons x xs ih =>
    intro v0 hnm
    rw [List.foldl_cons, ih _ (fun i hi => hnm i (List.mem_cons_of_mem _ hi)),
      Vector.getElem_modify_of_ne hr (hnm x List.mem_cons_self)]

/-- A left fold of per-index `modify`s over a `Nodup` list writes `g r` at every
member index `r` (reading the value `r` held before the fold, since each index
is visited at most once). -/
theorem getElem_foldl_modify_mem (g : Fin n → α → α) :
    ∀ (xs : List (Fin n)), xs.Nodup → ∀ (v0 : Vector α n) (r : Fin n), r ∈ xs →
      (xs.foldl (fun v i => v.modify i.val (g i)) v0)[r.val]'r.isLt = g r v0[r.val] := by
  intro xs
  induction xs with
  | nil => intro _ v0 r hr; simp at hr
  | cons x xs ih =>
    intro hnd v0 r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [getElem_foldl_modify_not_mem g r.isLt xs _ (fun i hi heq => by
        apply (List.nodup_cons.mp hnd).1
        rwa [← (Fin.ext heq : i = r)])]
      exact Vector.getElem_modify_self r.isLt
    · have hxr : x.val ≠ r.val := by
        intro heq
        apply (List.nodup_cons.mp hnd).1
        rwa [(Fin.ext heq : x = r)]
      rw [ih (List.nodup_cons.mp hnd).2 _ r hr',
        Vector.getElem_modify_of_ne r.isLt hxr]

/-- `List.finRange n` has no repeated indices (core-only proof; the Batteries
`nodup_finRange` is outside this Mathlib-free module's import closure). -/
private theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.finRange_succ, List.nodup_cons]
    exact ⟨by simp [Fin.ext_iff], List.Pairwise.map _ (fun _ _ hab h => hab (Fin.succ_inj.mp h)) ih⟩

/-- Reading index `r` of a `Fin.foldl` of per-index `modify`s yields `g r`
applied to the original entry — every index is visited exactly once. This is the
in-place (no intermediate `List.finRange` allocation) scatter form. -/
theorem getElem_finFoldl_modify (v0 : Vector α n)
    (g : Fin n → α → α) (r : Fin n) :
    (Fin.foldl n (fun v i => v.modify i.val (g i)) v0)[r.val]'r.isLt = g r v0[r.val] := by
  rw [Fin.foldl_eq_finRange_foldl]
  exact getElem_foldl_modify_mem g (List.finRange n) (nodup_finRange n) v0 r (by simp)

end Vector
