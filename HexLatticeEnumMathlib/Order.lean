/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnumMathlib.Bounds
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Field.Rat
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

/-- Exact distance order with the smaller integer first on a tie. -/
@[expose] def Nearer (c : Rat) (a b : Int) : Prop :=
  |(a : Rat) - c| ≤ |(b : Rat) - c| ∧ (|(a : Rat) - c| = |(b : Rat) - c| → a ≤ b)

/-- Clearing the positive rational denominator preserves exact coefficient-distance comparisons. -/
theorem distance_compare (c : Rat) (a b : Int) :
    (a * (c.den : Int) - c.num).natAbs ≤ (b * (c.den : Int) - c.num).natAbs ↔
      |(a : Rat) - c| ≤ |(b : Rat) - c| := by
  have hd : (0 : Rat) < c.den := by exact_mod_cast c.den_pos
  have hc : (c.num : Rat) = c * c.den := (div_eq_iff (ne_of_gt hd)).mp c.num_div_den
  have hscale (a : Int) : ((a * (c.den : Int) - c.num).natAbs : Rat) = |(a : Rat) - c| * c.den := by
    have hn : ((a * (c.den : Int) - c.num).natAbs : Rat) = |((a * (c.den : Int) - c.num : Int) : Rat)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    rw [hn]
    push_cast
    rw [hc, ← sub_mul, abs_mul, abs_of_pos hd]
  have hcast : (a * (c.den : Int) - c.num).natAbs ≤ (b * (c.den : Int) - c.num).natAbs ↔
      ((a * (c.den : Int) - c.num).natAbs : Rat) ≤ ((b * (c.den : Int) - c.num).natAbs : Rat) := by
    norm_cast
  rw [hcast, hscale, hscale, mul_le_mul_iff_left₀ hd]

/-- Descending left-stream values move monotonically away from the centre. -/
theorem nearer_left (c : Rat) (a b : Int) (ha : (a : Rat) ≤ c) (hb : b ≤ a) : Nearer c a b := by
  have hbq : (b : Rat) ≤ a := by exact_mod_cast hb
  have hbc : (b : Rat) ≤ c := le_trans hbq ha
  simp only [Nearer, abs_of_nonpos (sub_nonpos.mpr ha), abs_of_nonpos (sub_nonpos.mpr hbc)]
  constructor
  · linarith
  · intro he
    have h : (a : Rat) = b := by linarith
    have h : a = b := by exact_mod_cast h
    omega

/-- Ascending right-stream values move monotonically away from the centre. -/
theorem nearer_right (c : Rat) (a b : Int) (ha : c ≤ (a : Rat)) (hb : a ≤ b) : Nearer c a b := by
  have hbq : (a : Rat) ≤ b := by exact_mod_cast hb
  have hbc : c ≤ (b : Rat) := le_trans ha hbq
  simp only [Nearer, abs_of_nonneg (sub_nonneg.mpr ha), abs_of_nonneg (sub_nonneg.mpr hbc)]
  exact ⟨by linarith, fun _ => hb⟩

/-- Each lazy step chooses the nearest remaining integer and preserves the two streams around the centre. -/
theorem next_nearer (s s' : Coefficients) (z : Int)
    (hl : s.left ≤ s.centre.floor) (hr : s.centre.floor < s.right)
    (h : s.next? = some (z, s')) :
    s'.centre = s.centre ∧ s'.left ≤ s'.centre.floor ∧ s'.centre.floor < s'.right ∧
      ∀ x, x ∈ remaining s → Nearer s.centre z x := by
  have hleft : (s.left : Rat) ≤ s.centre :=
    le_trans (by exact_mod_cast hl) (Rat.floor_le _)
  have hright : s.centre ≤ (s.right : Rat) := by
    have hi : s.centre.floor + 1 ≤ s.right := by omega
    exact le_trans (le_of_lt (Rat.lt_floor_add_one _)) (by exact_mod_cast hi)
  simp only [Coefficients.next?] at h
  split_ifs at h with hchoose hhas
  · cases h
    refine ⟨rfl, by dsimp; omega, hr, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact nearer_left s.centre s.left x hleft (Finset.mem_Icc.mp hx).2
    · obtain ⟨hx, hhi⟩ := Finset.mem_Icc.mp hx
      have hhas : s.right ≤ s.interval.hi := by omega
      have hcmp : (s.left * (s.centre.den : Int) - s.centre.num).natAbs ≤
          (s.right * (s.centre.den : Int) - s.centre.num).natAbs := by
        have hc : s.interval.lo ≤ s.left ∧
            (s.left * (s.centre.den : Int) - s.centre.num).natAbs ≤
              (s.right * (s.centre.den : Int) - s.centre.num).natAbs := by simpa [hhas] using hchoose
        exact hc.2
      have hd := (distance_compare s.centre s.left s.right).mp hcmp
      exact ⟨le_trans hd (nearer_right s.centre s.right x hright hx).1, fun _ => by omega⟩
  · cases h
    refine ⟨rfl, hl, by dsimp; omega, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hlo, hx⟩ := Finset.mem_Icc.mp hx
      have hhasLeft : s.interval.lo ≤ s.left := by omega
      have hcmp : (s.right * (s.centre.den : Int) - s.centre.num).natAbs <
          (s.left * (s.centre.den : Int) - s.centre.num).natAbs := by
        simpa [hhasLeft, hhas] using hchoose
      have hd : |(s.right : Rat) - s.centre| < |(s.left : Rat) - s.centre| := by
        apply lt_of_not_ge
        intro he
        exact not_le_of_gt hcmp ((distance_compare s.centre s.left s.right).mpr he)
      have hd' := lt_of_lt_of_le hd (nearer_left s.centre s.left x hleft hx).1
      exact ⟨le_of_lt hd', fun he => False.elim (ne_of_lt hd' he)⟩
    · exact nearer_right s.centre s.right x hright (Finset.mem_Icc.mp hx).1

/-- A truncated stream still returns only coefficients represented by its initial cursor. -/
theorem stream_subset (fuel : Nat) (s : Coefficients) (hsep : s.left < s.right) :
    ∀ x, x ∈ Coefficients.toList.go fuel s → x ∈ remaining s := by
  induction fuel generalizing s with
  | zero => simp [Coefficients.toList.go]
  | succ fuel ih =>
    cases he : s.next? with
    | none => simp [Coefficients.toList.go, he]
    | some step =>
      rcases step with ⟨a, s'⟩
      obtain ⟨ha, hr, hsep'⟩ := next_some s s' a hsep he
      intro x hx
      simp only [Coefficients.toList.go, he, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · have hm := ih s' hsep' x hx
        rw [hr] at hm
        exact (Finset.mem_erase.mp hm).2

/-- Every finite prefix respects exact Schnorr–Euchner distance order and the smaller-integer tie rule. -/
theorem stream_ordered (fuel : Nat) (s : Coefficients)
    (hl : s.left ≤ s.centre.floor) (hr : s.centre.floor < s.right) :
    (Coefficients.toList.go fuel s).Pairwise (Nearer s.centre) := by
  induction fuel generalizing s with
  | zero => simp [Coefficients.toList.go]
  | succ fuel ih =>
    cases he : s.next? with
    | none => simp [Coefficients.toList.go, he]
    | some step =>
      rcases step with ⟨a, s'⟩
      obtain ⟨hc, hl', hr', hm⟩ := next_nearer s s' a hl hr he
      have hsep : s.left < s.right := by omega
      have hsep' : s'.left < s'.right := by omega
      have hs := (next_some s s' a hsep he).2.1
      simp only [Coefficients.toList.go, he, List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro x hx
        have hx := stream_subset fuel s' hsep' x hx
        rw [hs] at hx
        exact hm x (Finset.mem_erase.mp hx).2
      · have h := ih s' hl' hr'
        rwa [hc] at h

/-- The complete coefficient iterator is ordered by exact distance, with smaller integers first on ties. -/
theorem coefficients_ordered (interval : Interval) (c : Rat) :
    (coefficients interval c).toList.Pairwise (Nearer c) := by
  have h := stream_ordered interval.size (coefficients interval c)
    (min_le_right _ _) (by
      have h := le_max_right interval.lo (c.floor + 1)
      change c.floor < max interval.lo (c.floor + 1)
      omega)
  exact h

/-- The two adjacent integers around a centre have the exact midpoint comparison used by rounding. -/
theorem round_compare (c : Rat) :
    2 * (c.num - c.floor * (c.den : Int)) ≤ (c.den : Int) ↔
      |(c.floor : Rat) - c| ≤ |((c.floor + 1 : Int) : Rat) - c| := by
  have hd : (0 : Int) < c.den := by exact_mod_cast c.den_pos
  have hl : c.floor * (c.den : Int) ≤ c.num := by
    rw [Rat.floor_def]
    exact Int.ediv_mul_le _ (ne_of_gt hd)
  have hr : c.num < (c.floor + 1) * (c.den : Int) := by
    rw [Rat.floor_def]
    exact Int.lt_ediv_add_one_mul_self _ hd
  rw [← distance_compare]
  have hcast : ((c.floor * (c.den : Int) - c.num).natAbs : Int) ≤
      (((c.floor + 1) * (c.den : Int) - c.num).natAbs : Int) ↔
        2 * (c.num - c.floor * (c.den : Int)) ≤ (c.den : Int) := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
    constructor <;> intro h <;> nlinarith
  have hh : (c.floor * (c.den : Int) - c.num).natAbs ≤
      ((c.floor + 1) * (c.den : Int) - c.num).natAbs ↔
        2 * (c.num - c.floor * (c.den : Int)) ≤ (c.den : Int) := by exact_mod_cast hcast
  exact hh.symm

/-- Nearest-plane rounding chooses a globally nearest integer, with the smaller integer on ties. -/
theorem nearest_spec (c : Rat) (z : Int) : Nearer c (nearest c) z := by
  have hl : (c.floor : Rat) ≤ c := Rat.floor_le c
  have hr : c ≤ ((c.floor + 1 : Int) : Rat) := le_of_lt (Rat.lt_floor_add_one c)
  by_cases hround : 2 * (c.num - c.floor * (c.den : Int)) ≤ (c.den : Int)
  · simp only [nearest, ite_eq_left hround]
    have hd := (round_compare c).mp hround
    by_cases hz : z ≤ c.floor
    · exact nearer_left c c.floor z hl hz
    · have hz : c.floor + 1 ≤ z := by omega
      exact ⟨le_trans hd (nearer_right c (c.floor + 1) z hr hz).1, fun _ => by omega⟩
  · simp only [nearest, ite_eq_right hround]
    have hd : |((c.floor + 1 : Int) : Rat) - c| < |(c.floor : Rat) - c| :=
      lt_of_not_ge (fun h => hround ((round_compare c).mpr h))
    by_cases hz : c.floor + 1 ≤ z
    · exact nearer_right c (c.floor + 1) z hr hz
    · have hz : z ≤ c.floor := by omega
      have hd' := lt_of_lt_of_le hd (nearer_left c c.floor z hl hz).1
      exact ⟨le_of_lt hd', fun he => False.elim (ne_of_lt hd' he)⟩

/-- Rounding an integer leaves it unchanged. -/
theorem nearest_int (z : Int) : nearest (z : Rat) = z := by
  have h := (nearest_spec (z : Rat) z).1
  simp only [sub_self, abs_zero, abs_nonpos_iff] at h
  have h' : (nearest (z : Rat) : Rat) = z := sub_eq_zero.mp h
  exact_mod_cast h'

end HexLatticeEnumMathlib
