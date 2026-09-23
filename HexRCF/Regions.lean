/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.CellsCheck
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Instances.Sign

public section

/-!
# Cells cut out by finitely many real points

The same indexed cells describe the real line for a finite list of points.
Strict order gives a partition into nonempty cells; coverage and connectedness
do not require it. These proofs and polynomial sign constancy serve both the
rational and algebraic coefficient solvers.
-/

namespace Polynomial

/-- The sign of a continuous polynomial evaluation is constant on a
preconnected set containing no root of the polynomial. -/
theorem sign_eq_of_noRoot {p : Polynomial ℝ} {s : Set ℝ}
    (hs : IsPreconnected s) (hnz : ∀ z ∈ s, ¬p.IsRoot z)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    SignType.sign (p.eval x) = SignType.sign (p.eval y) := by
  have hcont : ContinuousOn (SignType.sign ∘ fun z => p.eval z) s := by
    refine (continuousOn_of_forall_continuousAt fun q hq => ?_).comp
      p.continuousOn (Set.mapsTo_image (fun z => p.eval z) s)
    obtain ⟨z, hz, rfl⟩ := hq
    exact continuousAt_sign_of_ne_zero (fun hzero => hnz z hz hzero)
  exact (hs.image _ hcont).subsingleton
    (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy)

end Polynomial

namespace Hex.RCF.Cell

/-- `rank` is an injective encoding of the alternating cell order. -/
theorem rank_injective : Function.Injective (@rank n) := by
  intro c d h
  cases c with
  | «open» i =>
      cases d with
      | «open» j =>
          simp only [rank] at h
          congr
          apply Fin.ext
          omega
      | root j =>
          simp only [rank] at h
          omega
  | root i =>
      cases d with
      | «open» j =>
          simp only [rank] at h
          omega
      | root j =>
          simp only [rank] at h
          congr
          apply Fin.ext
          omega

/-- Membership in a singleton or open interval cut out by a finite list of real points. -/
@[expose]
def Region {n : Nat} (root : Fin n → ℝ) :
    Cell n → ℝ → Prop
  | .root i, x => x = root i
  | .open cut, x =>
      if hzero : n = 0 then True
      else if hleft : cut.val = 0 then
        x < root ⟨0, by omega⟩
      else if hright : cut.val = n then
        root ⟨n - 1, by omega⟩ < x
      else
        root ⟨cut.val - 1, by omega⟩ < x ∧
          x < root ⟨cut.val, by omega⟩

namespace Region

/-- Every real point belongs to at least one semantic cell. -/
theorem exists_mem {n : Nat} (root : Fin n → ℝ) (x : ℝ) :
    ∃ c : Cell n, Region root c x := by
  classical
  by_cases hzero : n = 0
  · refine ⟨.open ⟨0, by omega⟩, ?_⟩
    simp [Region, hzero]
  let first : Fin n := ⟨0, by omega⟩
  by_cases hleft : x < root first
  · refine ⟨.open ⟨0, by omega⟩, ?_⟩
    simpa [Region, hzero, first] using hleft
  by_cases hsome : ∃ i : Fin n, x ≤ root i
  · let i := Fin.find (fun j => x ≤ root j) hsome
    have hxi : x ≤ root i := Fin.find_spec hsome
    by_cases heq : x = root i
    · exact ⟨.root i, by simpa [Region] using heq⟩
    · have hi0 : i.val ≠ 0 := by
        intro hi
        have hieq : i = first := Fin.ext hi
        have hrx : root first ≤ x := not_lt.mp hleft
        apply heq
        rw [hieq] at hxi ⊢
        exact le_antisymm hxi hrx
      let prev : Fin n := ⟨i.val - 1, by omega⟩
      have hprev : root prev < x := by
        apply lt_of_not_ge
        apply Fin.find_min hsome
        show prev.val < i.val
        simp only [prev]
        omega
      have hnext : x < root i := lt_of_le_of_ne hxi heq
      refine ⟨.open ⟨i.val, by omega⟩, ?_⟩
      simpa [Region, hzero, hi0, show i.val ≠ n by omega,
        prev] using And.intro hprev hnext
  · let last : Fin n :=
      ⟨n - 1, by omega⟩
    have hlast : root last < x := by
      exact lt_of_not_ge (fun hx => hsome ⟨last, hx⟩)
    refine ⟨.open (Fin.last n), ?_⟩
    simpa [Region, hzero, last] using hlast

/-- A point in an open cell lies below the root at the cell's upper boundary. -/
private theorem open_lt_upper {n : Nat} (root : Fin n → ℝ) (cut : Fin (n + 1)) (x : ℝ)
    (hcut : cut.val < n) (hx : Region root (.open cut) x) :
    x < root ⟨cut.val, hcut⟩ := by
  have hzero : n ≠ 0 := by omega
  by_cases hleft : cut.val = 0
  · simpa [Region, hzero, hleft] using hx
  · have hright : cut.val ≠ n := by omega
    simp [Region, hzero, hleft, hright] at hx
    exact hx.2

/-- A point in an open cell lies above the root at the cell's lower boundary. -/
private theorem lower_lt_open {n : Nat} (root : Fin n → ℝ) (cut : Fin (n + 1)) (x : ℝ)
    (hcut : 0 < cut.val) (hx : Region root (.open cut) x) :
    root ⟨cut.val - 1, by omega⟩ < x := by
  have hzero : n ≠ 0 := by omega
  have hleft : cut.val ≠ 0 := by omega
  by_cases hright : cut.val = n
  · simpa [Region, hzero, hleft, hright] using hx
  · simp [Region, hzero, hleft, hright] at hx
    exact hx.1

/-- Cells earlier in the alternating enumeration lie strictly to the left. -/
theorem lt_of_rank_lt {n : Nat} (root : Fin n → ℝ) (hmono : StrictMono root) {c d : Cell n} {x y : ℝ}
    (hcd : rank c < rank d) (hx : Region root c x) (hy : Region root d y) : x < y := by
  cases c with
  | root i =>
      cases d with
      | root j =>
          simp only [rank] at hcd
          simp only [Region] at hx hy
          rw [hx, hy]
          exact hmono (by omega)
      | «open» cut =>
          simp only [rank] at hcd
          simp only [Region] at hx
          rw [hx]
          have hlower := lower_lt_open root cut y (by omega) hy
          have hmono : root i ≤ root ⟨cut.val - 1, by omega⟩ :=
            hmono.monotone (by show i.val ≤ cut.val - 1; omega)
          exact lt_of_le_of_lt hmono hlower
  | «open» cut =>
      cases d with
      | root j =>
          simp only [rank] at hcd
          simp only [Region] at hy
          rw [hy]
          have hupper := open_lt_upper root cut x (by omega) hx
          have hmono : root ⟨cut.val, by omega⟩ ≤ root j :=
            hmono.monotone (by show cut.val ≤ j.val; omega)
          exact lt_of_lt_of_le hupper hmono
      | «open» next =>
          simp only [rank] at hcd
          have hupper := open_lt_upper root cut x (by omega) hx
          have hlower := lower_lt_open root next y (by omega) hy
          have hmono : root ⟨cut.val, by omega⟩ ≤
              root ⟨next.val - 1, by omega⟩ :=
            hmono.monotone (by show cut.val ≤ next.val - 1; omega)
          exact lt_trans hupper (lt_of_le_of_lt hmono hlower)

/-- Semantic cell membership is unique. -/
theorem unique_mem {n : Nat} (root : Fin n → ℝ) (hmono : StrictMono root) (x : ℝ) {c d : Cell n}
    (hc : Region root c x) (hd : Region root d x) : c = d := by
  by_contra hne
  have hrank : rank c ≠ rank d := fun h => hne (rank_injective h)
  rcases lt_or_gt_of_ne hrank with hlt | hgt
  · exact (lt_irrefl x) (lt_of_rank_lt root hmono hlt hc hd)
  · exact (lt_irrefl x) (lt_of_rank_lt root hmono hgt hd hc)

/-- The semantic cells form a genuine partition of the real line. -/
theorem existsUnique_mem {n : Nat} (root : Fin n → ℝ) (hmono : StrictMono root) (x : ℝ) :
    ∃! c : Cell n, Region root c x := by
  obtain ⟨c, hc⟩ := exists_mem root x
  exact ⟨c, hc, fun d hd => unique_mem root hmono x hd hc⟩

/-- An open cell contains none of the points defining the partition. -/
theorem open_ne {n : Nat} (root : Fin n → ℝ) (hmono : StrictMono root)
    {cut : Fin (n + 1)} {x : ℝ} (hx : Region root (.open cut) x) (i : Fin n) :
    x ≠ root i := by
  intro heq
  have hr : Region root (.root i) x := heq
  have := unique_mem root hmono x hx hr
  cases this

/-- Every semantic cell contains a real point. -/
theorem exists_point {n : Nat} (root : Fin n → ℝ) (hmono : StrictMono root) (c : Cell n) :
    ∃ x : ℝ, Region root c x := by
  cases c with
  | root i => exact ⟨root i, by simp [Region]⟩
  | «open» cut =>
      by_cases hzero : n = 0
      · exact ⟨0, by simp [Region, hzero]⟩
      by_cases hleft : cut.val = 0
      · refine ⟨root ⟨0, by omega⟩ - 1, ?_⟩
        simp [Region, hzero, hleft]
      by_cases hright : cut.val = n
      · refine ⟨root ⟨n - 1, by omega⟩ + 1, ?_⟩
        simp [Region, hzero, hright]
      · have hroots : root ⟨cut.val - 1, by omega⟩ <
            root ⟨cut.val, by omega⟩ := by
          apply hmono
          show cut.val - 1 < cut.val
          omega
        obtain ⟨x, hx⟩ := exists_between hroots
        exact ⟨x, by simpa [Region, hzero, hleft, hright] using hx⟩

/-- Every open semantic cell is an interval, hence preconnected. -/
theorem isPreconnected_open {n : Nat} (root : Fin n → ℝ) (cut : Fin (n + 1)) :
    IsPreconnected {x : ℝ | Region root (.open cut) x} := by
  by_cases hzero : n = 0
  · simpa [Region, hzero] using (isPreconnected_univ :
      IsPreconnected (Set.univ : Set ℝ))
  by_cases hleft : cut.val = 0
  · have heq : {x : ℝ | Region root (.open cut) x} =
        Set.Iio (root ⟨0, by omega⟩) := by
      ext x
      simp [Region, hzero, hleft, Set.mem_Iio]
    rw [heq]
    exact isPreconnected_Iio
  by_cases hright : cut.val = n
  · have heq : {x : ℝ | Region root (.open cut) x} =
        Set.Ioi (root ⟨n - 1, by omega⟩) := by
      ext x
      simp [Region, hzero, hright, Set.mem_Ioi]
    rw [heq]
    exact isPreconnected_Ioi
  · have heq : {x : ℝ | Region root (.open cut) x} =
        Set.Ioo (root ⟨cut.val - 1, by omega⟩)
          (root ⟨cut.val, by omega⟩) := by
      ext x
      simp [Region, hzero, hleft, hright, Set.mem_Ioo]
    rw [heq]
    exact isPreconnected_Ioo

/-- Polynomial signs are constant on each cell when the defining points
contain every root. The zero polynomial is handled separately, since its
root set cannot be contained in a finite list. -/
theorem sign_eq {n : Nat} (root : Fin n → ℝ) (hmono : StrictMono root)
    (p : Polynomial ℝ)
    (hroots : p = 0 ∨ ∀ z, p.IsRoot z → ∃ i, root i = z)
    (c : Cell n) {x y : ℝ} (hx : Cell.Region root c x) (hy : Cell.Region root c y) :
    SignType.sign (p.eval x) = SignType.sign (p.eval y) := by
  rcases hroots with rfl | hroots
  · simp
  cases c with
  | root i =>
      simp only [Cell.Region] at hx hy
      rw [hx, hy]
  | «open» cut =>
      apply Polynomial.sign_eq_of_noRoot (Cell.Region.isPreconnected_open root cut) _ hx hy
      intro z hz hp
      obtain ⟨i, hi⟩ := hroots z hp
      exact Cell.Region.open_ne root hmono hz i hi.symm

end Region

end Hex.RCF.Cell
