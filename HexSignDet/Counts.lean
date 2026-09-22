/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Support

public section

/-! Finite counting on a complete candidate support. Observations may repeat:
distinct roots with equal sign vectors contribute separate units. -/
namespace Hex.SignDet

open scoped Hex

/-- Exact integer multiplicities of the supplied observations. -/
def counts {r : Nat} (columns : Vector (List Int) r) (xs : List (List Int)) : Vector Int r :=
  Vector.ofFn fun i => (xs.countP fun x => decide (x = columns[i]) : Nat)

/-- The moments of a finite family of sign observations. -/
def moments {r : Nat} (rows : Vector (List Nat) r) (xs : List (List Int)) : Vector Int r :=
  Vector.ofFn fun i => (xs.map (entry rows[i])).sum

private theorem counts_cons {r : Nat} (columns : Vector (List Int) r)
    (hn : columns.toList.Nodup) (i : Fin r) (xs : List (List Int)) :
    counts columns (columns[i] :: xs) = counts columns xs + Vector.unit Int i := by
  apply Vector.ext
  intro j hj
  have he : columns[i.val] = columns[j] ↔ i.val = j := by
    constructor
    · intro h
      apply hn.eq_of_getElem_eq (i := i.val) (j := j)
        (by simp) (by simpa using hj)
      simpa using h
    · intro h
      subst j
      rfl
  simp only [counts, Vector.unit, Fin.getElem_fin, Vector.getElem_ofFn,
    List.countP_cons, Vector.getElem_add, decide_eq_true_eq, Fin.ext_iff]
  change (↑(xs.countP (fun x => decide (x = columns[j])) +
    if columns[i.val] = columns[j] then 1 else 0) : Int) =
    ↑(xs.countP (fun x => decide (x = columns[j]))) + if i.val = j then 1 else 0
  by_cases h : i.val = j
  · simp [h]
  · simp [he, h]

/-- Complete candidate support lets finite counting satisfy the moment system.
Without the coverage hypothesis this identity is false. -/
theorem count_moments {r : Nat} (rows : Vector (List Nat) r)
    (columns : Vector (List Int) r) (hn : columns.toList.Nodup)
    (xs : List (List Int)) (cover : ∀ x ∈ xs, x ∈ columns.toList) :
    momentMatrix rows columns * counts columns xs = moments rows xs := by
  induction xs with
  | nil =>
    have hc : counts columns [] = 0 := by ext i hi; simp [counts]
    rw [hc, Matrix.mulVec_zero]
    ext i hi
    simp [moments]
  | cons x xs ih =>
    have hx := cover x (by simp)
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
    have hir : i < r := by simpa using hi
    have he' : columns[(⟨i, hir⟩ : Fin r)] = x := by simpa using he
    rw [← he', counts_cons columns hn, Matrix.mulVec_add, Matrix.mulVec_unit,
      ih (fun y hy => cover y (by simp [hy]))]
    apply Vector.ext
    intro j hj
    rw [Vector.getElem_add]
    change (moments rows xs)[j] + (Matrix.col (momentMatrix rows columns) ⟨i, hir⟩)[j] = _
    simp only [moments, Vector.getElem_ofFn, List.map_cons, List.sum_cons]
    have hc : (Matrix.col (momentMatrix rows columns) ⟨i, hir⟩)[j] =
        entry rows[(⟨j, hj⟩ : Fin r)] columns[(⟨i, hir⟩ : Fin r)] :=
      (Matrix.getElem_col (momentMatrix rows columns) ⟨i, hir⟩ ⟨j, hj⟩).trans
        (Matrix.getElem_ofFn _ _ _)
    rw [hc]
    exact Int.add_comm _ _

/-- A checked complete system recovers the actual finite multiplicities. -/
theorem System.counts_eq {r : Nat} {arity : Nat} (s : System r)
    (h : s.check arity = true) (xs : List (List Int))
    (cover : ∀ x ∈ xs, x ∈ s.columns.toList)
    (hm : s.values = moments s.rows xs) : SignDet.counts s.columns xs = s.counts := by
  have hn : s.columns.toList.Nodup := by
    simp only [System.check, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.2
  apply s.unique h
  rw [count_moments s.rows s.columns hn xs cover, hm]

/-- Every observed condition remains after pruning, once complete support and
the finite moment interpretation have been established independently. -/
theorem System.covers_support {r : Nat} {arity : Nat} (s : System r)
    (h : s.check arity = true) (xs : List (List Int))
    (cover : ∀ x ∈ xs, x ∈ s.columns.toList)
    (hm : s.values = moments s.rows xs) : ∀ x ∈ xs, x ∈ s.support := by
  intro x hx
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (cover x hx)
  have hir : i < r := by simpa using hi
  have he' : s.columns[(⟨i, hir⟩ : Fin r)] = x := by simpa using he
  have hc := s.counts_eq h xs cover hm
  have hp : 0 < s.counts[(⟨i, hir⟩ : Fin r)] := by
    rw [← hc]
    simp only [SignDet.counts, Fin.getElem_fin, Vector.getElem_ofFn]
    change 0 < (↑(xs.countP (fun y => decide (y = s.columns[(⟨i, hir⟩ : Fin r)]))) : Int)
    rw [he']
    have : 0 < xs.countP (fun y => decide (y = x)) :=
      List.countP_pos_iff.mpr ⟨x, hx, by simp⟩
    omega
  rw [← he']
  apply List.mem_map.mpr
  refine ⟨⟨i, hir⟩, ?_, rfl⟩
  simpa [System.positive] using hp

/-- Exact counts prohibit spurious positive columns, as well as preserving
realized ones. This direction needs no separate coverage hypothesis. -/
theorem System.support_subset {r : Nat} (s : System r) (xs : List (List Int))
    (hc : SignDet.counts s.columns xs = s.counts) : ∀ x ∈ s.support, x ∈ xs := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have hp : 0 < s.counts[i] := by simpa [System.positive] using hi
  rw [← hc] at hp
  simp only [SignDet.counts, Fin.getElem_fin, Vector.getElem_ofFn] at hp
  change 0 < (↑(xs.countP (fun x => decide (x = s.columns[i]))) : Int) at hp
  have hp' : 0 < xs.countP (fun x => decide (x = s.columns[i])) := by omega
  obtain ⟨y, hy, he⟩ := List.countP_pos_iff.mp hp'
  exact (of_decide_eq_true he) ▸ hy

end Hex.SignDet
