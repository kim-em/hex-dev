/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Std
import all Init.Data.List.Sort.Basic

@[expose] public section

namespace Hex.List

/-- Kernel-reducible stable merge. -/
def merge (le : α → α → Bool) (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if le x y then x :: merge le xs (y :: ys) else y :: merge le (x :: xs) ys
termination_by xs.length + ys.length
decreasing_by all_goals simp_wf

theorem merge_eq (le : α → α → Bool) (xs ys : List α) : merge le xs ys = xs.merge ys le := by
  induction xs generalizing ys with
  | nil => simp [merge]
  | cons x xs ih =>
    induction ys with
    | nil => simp [merge]
    | cons y ys ihy =>
      rw [merge, _root_.List.cons_merge_cons]
      split <;> simp_all

/-- Stable merge sort with structural recursion and exposed implementation helpers.
The fuel is the input length, which bounds the depth of its halving recursion. -/
def sort (xs : List α) (le : α → α → Bool) : List α := go le xs.length xs
where
  go (le : α → α → Bool) : Nat → List α → List α
    | 0, xs => xs
    | _ + 1, [] => []
    | _ + 1, [x] => [x]
    | fuel + 1, x :: y :: xs =>
      let all := x :: y :: xs
      let half := (all.length + 1) / 2
      merge le (go le fuel (all.take half)) (go le fuel (all.drop half))

private theorem go_eq (le : α → α → Bool) (fuel : Nat) (xs : List α)
    (h : xs.length ≤ fuel) : sort.go le fuel xs = xs.mergeSort le := by
  induction fuel generalizing xs with
  | zero =>
    have : xs = [] := by simpa using h
    simp [this, sort.go]
  | succ fuel ih =>
    cases xs with
    | nil => simp [sort.go]
    | cons x xs =>
      cases xs with
      | nil => simp [sort.go]
      | cons y xs =>
        rw [sort.go, _root_.List.mergeSort]
        simp only [_root_.List.MergeSort.Internal.splitInTwo_fst,
          _root_.List.MergeSort.Internal.splitInTwo_snd]
        rw [ih _ (by simp only [List.length_take, List.length_cons] at *; omega),
          ih _ (by simp only [List.length_drop, List.length_cons] at *; omega), merge_eq]

/-- The exposed sort agrees with core's stable merge sort for every comparator. -/
@[simp] theorem sort_eq (le : α → α → Bool) (xs : List α) : sort xs le = xs.mergeSort le :=
  go_eq le xs.length xs (Nat.le_refl _)

/-- Compiled code keeps core's efficient merge-sort implementation. -/
@[csimp] theorem sort_eq_mergeSort : @sort = @List.mergeSort := by
  funext α xs le
  exact sort_eq le xs

end Hex.List
