/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnumMathlib.Bounds
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

/-- The two integer streams still represented by a coefficient cursor. -/
noncomputable def remaining (s : Coefficients) : Finset Int :=
  Finset.Icc s.interval.lo s.left ∪ Finset.Icc s.right s.interval.hi

/-- Initializing the cursor partitions the entire closed interval. -/
theorem remaining_coefficients (s : Interval) (c : Rat) :
    remaining (coefficients s c) = Finset.Icc s.lo s.hi := by
  ext z
  simp only [remaining, coefficients, Finset.mem_union, Finset.mem_Icc]
  omega

/-- Initial streams are disjoint. -/
theorem coefficients_disjoint (s : Interval) (c : Rat) :
    (coefficients s c).left < (coefficients s c).right := by
  simp only [coefficients]
  omega

/-- A cursor reports exhaustion exactly when neither stream has any values left. -/
theorem next_none (s : Coefficients) : s.next? = none ↔ remaining s = ∅ := by
  simp only [Coefficients.next?]
  split_ifs with hleft hright
  · have hl : s.interval.lo ≤ s.left := by simp_all
    simp only [false_iff]
    intro he
    have : s.left ∈ remaining s := Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hl, le_rfl⟩)
    simp [he] at this
  · simp only [false_iff]
    intro he
    have : s.right ∈ remaining s := Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨le_rfl, hright⟩)
    simp [he] at this
  · have hl : s.left < s.interval.lo := by
      simp_all
    simp only [remaining, Finset.union_eq_empty]
    simp [Finset.Icc_eq_empty_of_lt hl, Finset.Icc_eq_empty_of_lt (lt_of_not_ge hright)]

/-- Each stream step removes exactly its returned value and preserves disjointness. -/
theorem next_some (s s' : Coefficients) (z : Int) (hsep : s.left < s.right)
    (h : s.next? = some (z, s')) :
    z ∈ remaining s ∧ remaining s' = (remaining s).erase z ∧ s'.left < s'.right := by
  simp only [Coefficients.next?] at h
  split_ifs at h with hl hr
  · cases h
    have hleft : s.interval.lo ≤ s.left := by simp_all
    refine ⟨Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hleft, le_rfl⟩), ?_, by dsimp; omega⟩
    ext x
    simp only [remaining, Finset.mem_union, Finset.mem_Icc, Finset.mem_erase]
    dsimp
    omega
  · cases h
    refine ⟨Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨le_rfl, hr⟩), ?_, by dsimp; omega⟩
    ext x
    simp only [remaining, Finset.mem_union, Finset.mem_Icc, Finset.mem_erase]
    dsimp
    omega
private theorem stream_spec (fuel : Nat) (s : Coefficients) (hsep : s.left < s.right)
    (hf : (remaining s).card ≤ fuel) :
    (Coefficients.toList.go fuel s).toFinset = remaining s ∧
      (Coefficients.toList.go fuel s).Nodup := by
  induction fuel generalizing s with
  | zero =>
    have he : remaining s = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [Coefficients.toList.go, he]
  | succ fuel ih =>
    cases hn : s.next? with
    | none => simp [Coefficients.toList.go, hn, (next_none s).mp hn]
    | some step =>
      rcases step with ⟨z, s'⟩
      obtain ⟨hz, he, hsep'⟩ := next_some s s' z hsep hn
      have hcard : (remaining s').card ≤ fuel := by
        rw [he, Finset.card_erase_of_mem hz]
        have := Finset.card_pos.mpr ⟨z, hz⟩
        omega
      obtain ⟨hset, hnodup⟩ := ih s' hsep' hcard
      simp only [Coefficients.toList.go, hn, List.toFinset_cons, List.nodup_cons]
      refine ⟨?_, ?_, hnodup⟩
      · rw [hset, he, Finset.insert_erase hz]
      · intro hz'
        have : z ∈ (Coefficients.toList.go fuel s').toFinset := List.mem_toFinset.mpr hz'
        rw [hset, he] at this
        exact (Finset.mem_erase.mp this).1 rfl

/-- The finite coefficient iterator covers the exact interval once, without duplicates. -/
theorem coefficients_spec (s : Interval) (c : Rat) :
    (coefficients s c).toList.toFinset = Finset.Icc s.lo s.hi ∧
      (coefficients s c).toList.Nodup := by
  have hcard : (remaining (coefficients s c)).card ≤ s.size := by
    rw [remaining_coefficients, Int.card_Icc]
    simp only [Interval.size]
    omega
  have h := stream_spec s.size (coefficients s c) (coefficients_disjoint s c) hcard
  rw [remaining_coefficients] at h
  change (Coefficients.toList.go s.size (coefficients s c)).toFinset = _ ∧
    (Coefficients.toList.go s.size (coefficients s c)).Nodup
  exact h

/-- Iterator membership is precisely the closed interval test. -/
theorem mem_coefficients (s : Interval) (c : Rat) (z : Int) :
    z ∈ (coefficients s c).toList ↔ s.lo ≤ z ∧ z ≤ s.hi := by
  rw [← List.mem_toFinset, (coefficients_spec s c).1, Finset.mem_Icc]

end HexLatticeEnumMathlib
