/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.ExactDiv
public import HexMatrix.Basic

public section

namespace Hex.Matrix.Dixon

/-- The common gcd of an integer vector and its denominator. -/
@[expose] def common (y : Vector Int n) (d : Int) : Nat :=
  y.foldl (fun g x => Nat.gcd g x.natAbs) d.natAbs

theorem common_dvd (y : Vector Int n) (d g : Int) :
    g ∣ (common y d : Int) ↔ g ∣ d ∧ ∀ i : Fin n, g ∣ y[i] := by
  have go (xs : List Int) (s : Nat) :
      g.natAbs ∣ xs.foldl (fun a x => Nat.gcd a x.natAbs) s ↔
        g.natAbs ∣ s ∧ ∀ x ∈ xs, g.natAbs ∣ x.natAbs := by
    induction xs generalizing s with
    | nil => simp
    | cons x xs ih => simp [List.foldl_cons, ih, Nat.dvd_gcd_iff, and_assoc]
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, common, ← Vector.foldl_toList, go]
  constructor
  · rintro ⟨hd, hy⟩
    exact ⟨Int.natAbs_dvd_natAbs.mp hd, fun i => Int.natAbs_dvd_natAbs.mp
      (hy _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt)))⟩
  · rintro ⟨hd, hy⟩
    refine ⟨Int.natAbs_dvd_natAbs.mpr hd, ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    exact Int.natAbs_dvd_natAbs.mpr (hy ⟨i, hi⟩)

theorem common_pos (y : Vector Int n) (d : Int) (hd : 0 < d) : 0 < common y d := by
  have h := (common_dvd y d (common y d)).mp (Int.dvd_refl _)
  have hn := Int.natAbs_dvd_natAbs.mpr h.1
  simp only [Int.natAbs_natCast] at hn
  exact Nat.pos_of_dvd_of_pos hn (by omega)

/-- Remove the common gcd. Reconstruction supplies a positive denominator. -/
def normalise (y : Vector Int n) (d : Int) : Vector Int n × Int :=
  let g := (common y d : Int)
  (y.map (fun x => x / g), d / g)

theorem normalise_scale (y : Vector Int n) (d : Int) :
    (common y d : Int) * (normalise y d).2 = d ∧
      ∀ i : Fin n, (common y d : Int) * (normalise y d).1[i] = y[i] := by
  obtain ⟨hd, hy⟩ := (common_dvd y d (common y d)).mp (Int.dvd_refl _)
  refine ⟨Int.mul_ediv_cancel' hd, ?_⟩
  intro i
  simp only [normalise, Fin.getElem_fin, Vector.getElem_map]
  exact Int.mul_ediv_cancel' (hy i)

theorem normalise_pos (y : Vector Int n) (d : Int) (hd : 0 < d) :
    0 < (normalise y d).2 := by
  have hg : (0 : Int) < common y d := by exact_mod_cast common_pos y d hd
  have h := (normalise_scale y d).1
  by_cases hn : 0 < (normalise y d).2
  · exact hn
  have hle : (common y d : Int) * (normalise y d).2 ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  omega

theorem normalise_reduced (y : Vector Int n) (d : Int) (hd : 0 < d) :
    ∀ g : Int, (∀ i : Fin n, g ∣ (normalise y d).1[i]) →
      g ∣ (normalise y d).2 → g ∣ 1 := by
  intro g hy hg
  let c : Int := common y d
  have hc : c ≠ 0 := by have := common_pos y d hd; dsimp [c]; omega
  obtain ⟨hs, hv⟩ := normalise_scale y d
  have hdiv : g * c ∣ c := by
    apply (common_dvd y d (g * c)).mpr
    constructor
    · obtain ⟨t, ht⟩ := hg
      refine ⟨t, ?_⟩
      rw [← hs, ht]
      dsimp [c]
      grind only
    · intro i
      obtain ⟨t, ht⟩ := hy i
      refine ⟨t, ?_⟩
      rw [← hv i, ht]
      dsimp [c]
      grind only
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨t, ?_⟩
  apply Int.eq_of_mul_eq_mul_left hc
  grind only

theorem normalise_num_le (y : Vector Int n) (d : Int) (i : Fin n) :
    (normalise y d).1[i].natAbs ≤ y[i].natAbs := by
  have hy := ((common_dvd y d (common y d)).mp (Int.dvd_refl _)).2 i
  simp only [Fin.getElem_fin] at hy
  simp only [normalise, Fin.getElem_fin, Vector.getElem_map]
  rw [Int.natAbs_ediv_of_dvd hy]
  exact Nat.div_le_self _ _

theorem normalise_den_le (y : Vector Int n) (d : Int) (hd : 0 < d) :
    (normalise y d).2 ≤ d := by
  have hg := ((common_dvd y d (common y d)).mp (Int.dvd_refl _)).1
  have hb : (normalise y d).2.natAbs ≤ d.natAbs := by
    simp only [normalise, Int.natAbs_ediv_of_dvd hg]
    exact Nat.div_le_self _ _
  have hp := normalise_pos y d hd
  have h1 := Int.natAbs_of_nonneg (Int.le_of_lt hp)
  have h2 := Int.natAbs_of_nonneg (Int.le_of_lt hd)
  omega

theorem normalise_eq {y : Vector Int n} {d : Int}
    (hred : ∀ g : Int, (∀ i : Fin n, g ∣ y[i]) → g ∣ d → g ∣ 1) :
    normalise y d = (y, d) := by
  have h := (common_dvd y d (common y d)).mp (Int.dvd_refl _)
  have hc : common y d = 1 := Nat.eq_one_of_dvd_one (Int.ofNat_dvd.mp (hred _ h.2 h.1))
  simp [normalise, hc]

end Hex.Matrix.Dixon
