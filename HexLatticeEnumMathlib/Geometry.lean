/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnumMathlib.Correspondence
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

variable {n m : Nat}

/-- Squared norm of an executable vector, expressed in Euclidean space. -/
theorem real_norm_sq (v : Vector Int m) : ‖realVector v‖ ^ 2 = (distance v 0 : Real) := by
  simpa using real_distance v 0

/-- A returned shortest squared norm is positive; rank zero returns no such answer. -/
theorem shortest_positive (b : Basis n m) (a : Minimum n m) (h : shortest b = some a) :
    0 < a.distanceSq := by
  obtain ⟨q, hq⟩ := shortest_nonempty b a h
  have hs := (shortest_radius_spec b a h q.ambient).mp (List.mem_map.mpr ⟨q, hq, rfl⟩)
  have hn : realVector q.ambient ≠ 0 := by
    rw [← realVector_zero, realVector_injective.ne_iff]
    exact hs.2.1
  have hp := sq_pos_of_pos (norm_pos_iff.mpr hn)
  rw [real_norm_sq, hs.2.2] at hp
  exact_mod_cast hp

/-- A shortest vector attains the positive square root of the exact reported squared norm. -/
theorem shortest_real_radius (b : Basis n m) (a : Minimum n m) (h : shortest b = some a)
    (x : EuclideanSpace Real (Fin m)) :
    x ∈ (a.points.map Point.ambient).map realVector ↔
      x ∈ realLattice b ∧ x ≠ 0 ∧ ‖x‖ = Real.sqrt (a.distanceSq : Real) := by
  rw [List.mem_map]
  simp only [shortest_radius_spec b a h]
  have hn (v : Vector Int m) : realVector v ≠ 0 ↔ v ≠ 0 := by
    rw [← realVector_zero, realVector_injective.ne_iff]
  have hp : (0 : Real) < a.distanceSq := by exact_mod_cast shortest_positive b a h
  constructor
  · rintro ⟨v, ⟨hv, hvn, hd⟩, rfl⟩
    refine ⟨(mem_realLattice b _).mpr ⟨v, hv, rfl⟩, (hn v).mpr hvn, ?_⟩
    have he := real_norm_sq v
    rw [hd] at he
    nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (a.distanceSq : Real), norm_nonneg (realVector v)]
  · rintro ⟨hx, hxn, hd⟩
    obtain ⟨v, hv, rfl⟩ := (mem_realLattice b x).mp hx
    refine ⟨v, ⟨hv, (hn v).mp hxn, ?_⟩, rfl⟩
    have he := real_norm_sq v
    rw [hd, Real.sq_sqrt hp.le] at he
    exact_mod_cast he.symm

/-- Distinct lattice centres are separated by at least the shortest-vector length. -/
theorem shortest_separation (b : Basis n m) (a : Minimum n m) (h : shortest b = some a)
    {x y : EuclideanSpace Real (Fin m)} (hx : x ∈ realLattice b) (hy : y ∈ realLattice b)
    (hne : x ≠ y) : Real.sqrt (a.distanceSq : Real) ≤ dist x y := by
  obtain ⟨q, hq⟩ := shortest_nonempty b a h
  have hqr : realVector q.ambient ∈ (a.points.map Point.ambient).map realVector :=
    List.mem_map.mpr ⟨q.ambient, List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩
  have hmin := ((shortest_real_spec b a h _).mp hqr).2.2
  have hr := ((shortest_real_radius b a h _).mp hqr).2.2
  rw [dist_eq_norm, ← hr]
  exact hmin (x - y) ((realLattice b).sub_mem hx hy) (sub_ne_zero.mpr hne)

/-- Open balls centred at lattice points form a packing within the lattice's real span. -/
def IsPacking (b : Basis n m) (r : Real) : Prop :=
  ∀ x ∈ realLattice b, ∀ y ∈ realLattice b, x ≠ y →
    Disjoint (Metric.ball x r ∩ (realSpan b : Set (EuclideanSpace Real (Fin m))))
      (Metric.ball y r ∩ (realSpan b : Set (EuclideanSpace Real (Fin m))))

/-- The packing radius is exactly half the shortest-vector length, within the real span.
The existence of a shortest answer excludes the zero lattice. -/
theorem packing_radius (b : Basis n m) (a : Minimum n m) (h : shortest b = some a) (r : Real) :
    IsPacking b r ↔ r ≤ Real.sqrt (a.distanceSq : Real) / 2 := by
  constructor
  · intro hpack
    by_contra hlarge
    have hlarge : Real.sqrt (a.distanceSq : Real) / 2 < r := lt_of_not_ge hlarge
    obtain ⟨q, hq⟩ := shortest_nonempty b a h
    have hqr : realVector q.ambient ∈ (a.points.map Point.ambient).map realVector :=
      List.mem_map.mpr ⟨q.ambient, List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩
    obtain ⟨hx, hxn, hr⟩ := (shortest_real_radius b a h _).mp hqr
    have hd := hpack 0 (realLattice b).zero_mem (realVector q.ambient) hx hxn.symm
    have hm : midpoint Real 0 (realVector q.ambient) ∈ realSpan b :=
      (realSpan b).convex.midpoint_mem (realSpan b).zero_mem (realLattice_mem_span b hx)
    have hleft : midpoint Real 0 (realVector q.ambient) ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_midpoint_left]
      simpa [dist_zero_left, hr, div_eq_mul_inv, mul_comm] using hlarge
    have hright : midpoint Real 0 (realVector q.ambient) ∈ Metric.ball (realVector q.ambient) r := by
      rw [Metric.mem_ball, dist_midpoint_right]
      simpa [dist_zero_left, hr, div_eq_mul_inv, mul_comm] using hlarge
    exact Set.disjoint_left.mp hd ⟨hleft, hm⟩ ⟨hright, hm⟩
  · intro hr x hx y hy hne
    have hs := shortest_separation b a h hx hy hne
    exact (Metric.ball_disjoint_ball (by linarith : r + r ≤ dist x y)).mono
      Set.inter_subset_left Set.inter_subset_left

/-- Centres of spheres touching the sphere at the origin in a lattice packing of radius `r`. -/
def contacts (b : Basis n m) (r : Real) : Set (EuclideanSpace Real (Fin m)) :=
  {x | x ∈ realLattice b ∧ x ≠ 0 ∧ ‖x‖ = 2 * r}

/-- At the packing radius, the contact centres are exactly the complete shortest-vector list. -/
theorem contacts_spec (b : Basis n m) (a : Minimum n m) (h : shortest b = some a)
    (x : EuclideanSpace Real (Fin m)) :
    x ∈ contacts b (Real.sqrt (a.distanceSq : Real) / 2) ↔
      x ∈ (a.points.map Point.ambient).map realVector := by
  rw [shortest_real_radius b a h]
  simp only [contacts, Set.mem_ofPred_eq]
  ring_nf

/-- The lattice kissing number counts all shortest vectors, including both signs. -/
theorem kissing_number (b : Basis n m) (a : Minimum n m) (h : shortest b = some a) :
    (contacts b (Real.sqrt (a.distanceSq : Real) / 2)).ncard = a.points.length := by
  classical
  have he : contacts b (Real.sqrt (a.distanceSq : Real) / 2) =
      (((a.points.map Point.ambient).map realVector).toFinset : Set _) := by
    ext x
    simp only [Finset.mem_coe, List.mem_toFinset, contacts_spec b a h]
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup]
  · simp
  · exact (shortest_ambient_nodup b a h).map realVector_injective

/-- Contact centres occur in antipodal pairs. -/
theorem contacts_neg (b : Basis n m) (r : Real) (x : EuclideanSpace Real (Fin m)) :
    -x ∈ contacts b r ↔ x ∈ contacts b r := by
  simp [contacts]

end HexLatticeEnumMathlib
