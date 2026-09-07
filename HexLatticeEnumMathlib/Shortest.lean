/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Shortest
public import HexLatticeEnumMathlib.Closest
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

/-- The executable seed fold chooses a minimum-norm input row. -/
theorem shortestSeed_eq_argmin (b : Basis n m) :
    shortestSeed b = ((List.finRange n).map fun i => point b 0 (Vector.unit Int i)).argmin
      Point.distanceSq := by
  rw [List.argmin, List.foldl_map]
  unfold shortestSeed
  congr 1
  funext best i
  cases best <;> simp [List.argAux]

/-- There is no nonzero seed exactly when the input rank is zero. -/
theorem shortestSeed_none (b : Basis n m) : shortestSeed b = none ↔ n = 0 := by
  rw [shortestSeed_eq_argmin, List.argmin_eq_none, List.map_eq_nil_iff]
  simp

/-- Independence makes every input row nonzero. -/
theorem row_nonzero (b : Basis n m) (i : Fin n) : vector b (Vector.unit Int i) ≠ 0 := by
  intro h
  have hz : vector b (Vector.unit Int i) = vector b 0 := by simpa [vector] using h
  have he := congrArg (fun z : Vector Int n => z[i]) (vector_injective b hz)
  simp [Vector.unit] at he
  change (1 : Int) = 0 at he
  omega

/-- A selected seed is reconstructed, nonzero, and no longer than any input row. -/
theorem shortestSeed_spec (b : Basis n m) (q : Point n m) (hq : shortestSeed b = some q) :
    q = point b 0 q.coefficients ∧ q.ambient ≠ 0 ∧
      ∀ i : Fin n, q.distanceSq ≤ distanceSq b 0 (Vector.unit Int i) := by
  rw [shortestSeed_eq_argmin] at hq
  have hmem := List.argmin_mem hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
  refine ⟨rfl, row_nonzero b i, ?_⟩
  intro j
  exact List.le_of_mem_argmin (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩) hq

/-- Rank zero is precisely the case without a shortest nonzero vector. -/
theorem shortest_none (b : Basis n m) : shortest b = none ↔ n = 0 := by
  simp only [shortest, Option.map_eq_none_iff, shortestSeed_none]

/-- Every successful shortest query comes from a checked, nonzero seed. -/
theorem shortest_run (b : Basis n m) (answer : Minimum n m) (h : shortest b = some answer) :
    ∃ seed, shortestSeed b = some seed ∧
      answer = ⟨minimumPoints .shortest
        (optimize {} b 0 (prepare b 0) .shortest seed).traversal.state.points,
        (optimize {} b 0 (prepare b 0) .shortest seed).incumbent.distanceSq⟩ := by
  obtain ⟨seed, hs, ha⟩ := Option.map_eq_some_iff.mp h
  exact ⟨seed, hs, ha.symm⟩

/-- The shortest-vector list consists exactly of nonzero points on the minimum shell. -/
theorem shortest_point_spec (b : Basis n m) (answer : Minimum n m) (h : shortest b = some answer)
    (q : Point n m) : q ∈ answer.points ↔
      q = point b 0 q.coefficients ∧ q.ambient ≠ 0 ∧ q.distanceSq = answer.distanceSq := by
  obtain ⟨seed, hs, rfl⟩ := shortest_run b answer h
  obtain ⟨hp, he, _⟩ := shortestSeed_spec b seed hs
  have hm := minimum_points b 0 (prepare b 0) (prepare_valid b 0) .shortest (by decide)
    seed hp (Or.inr he) q
  simpa [Eligible] using hm

/-- The attained nonzero minimum bounds every nonzero lattice vector. -/
theorem shortest_le (b : Basis n m) (answer : Minimum n m) (h : shortest b = some answer)
    (z : Vector Int n) (hz : vector b z ≠ 0) : answer.distanceSq ≤ distanceSq b 0 z := by
  obtain ⟨seed, hs, rfl⟩ := shortest_run b answer h
  obtain ⟨hp, he, _⟩ := shortestSeed_spec b seed hs
  have hm := (optimize_spec b 0 (prepare b 0) (prepare_valid b 0) .shortest (by decide)
    seed hp (Or.inr he)).1
  exact hm.2.2 (point b 0 z) rfl (Or.inr hz)

/-- Positive-rank shortest-vector queries attain their nonzero minimum. -/
theorem shortest_nonempty (b : Basis n m) (answer : Minimum n m) (h : shortest b = some answer) :
    ∃ q, q ∈ answer.points := by
  obtain ⟨seed, hs, rfl⟩ := shortest_run b answer h
  obtain ⟨hp, he, _⟩ := shortestSeed_spec b seed hs
  exact minimum_nonempty b 0 (prepare b 0) (prepare_valid b 0) .shortest (by decide)
    seed hp (Or.inr he)

/-- The shortest-vector list never repeats a point record. -/
theorem shortest_nodup (b : Basis n m) (answer : Minimum n m) (h : shortest b = some answer) :
    answer.points.Nodup := by
  obtain ⟨seed, hs, rfl⟩ := shortest_run b answer h
  obtain ⟨hp, he, _⟩ := shortestSeed_spec b seed hs
  exact minimum_nodup b 0 (prepare b 0) (prepare_valid b 0) .shortest (by decide)
    seed hp (Or.inr he)

/-- Every nonzero lattice point at the attained radius occurs in the shortest-vector list. -/
theorem shortest_radius_spec (b : Basis n m) (answer : Minimum n m) (h : shortest b = some answer)
    (v : Vector Int m) : v ∈ answer.points.map Point.ambient ↔
      b.rows.memLattice v ∧ v ≠ 0 ∧ distance v 0 = answer.distanceSq := by
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
    obtain ⟨he, hn, hd⟩ := (shortest_point_spec b answer h q).mp hq
    have ha : q.ambient = vector b q.coefficients := congrArg Point.ambient he
    refine ⟨⟨q.coefficients, ha.symm⟩, hn, ?_⟩
    have hr : q.distanceSq = distance q.ambient 0 := by
      conv_lhs => rw [he]
      change distance (vector b q.coefficients) 0 = _
      rw [ha]
    exact hr.symm.trans hd
  · rintro ⟨⟨z, rfl⟩, hn, hd⟩
    exact List.mem_map.mpr ⟨point b 0 z, (shortest_point_spec b answer h _).mpr ⟨rfl, hn, hd⟩, rfl⟩

/-- Global shortest-vector correctness, excluding zero and including every minimum and both signs. -/
theorem shortest_spec (b : Basis n m) (answer : Minimum n m) (h : shortest b = some answer)
    (v : Vector Int m) : v ∈ answer.points.map Point.ambient ↔
      b.rows.memLattice v ∧ v ≠ 0 ∧
        ∀ w, b.rows.memLattice w → w ≠ 0 → distance v 0 ≤ distance w 0 := by
  rw [shortest_radius_spec b answer h]
  constructor
  · rintro ⟨hv, hn, hd⟩
    refine ⟨hv, hn, ?_⟩
    rintro w ⟨z, rfl⟩ hz
    rw [hd]
    exact shortest_le b answer h z hz
  · rintro ⟨hv, hn, hmin⟩
    refine ⟨hv, hn, le_antisymm ?_ ?_⟩
    · obtain ⟨q, hq⟩ := shortest_nonempty b answer h
      have hq := (shortest_radius_spec b answer h q.ambient).mp (List.mem_map.mpr ⟨q, hq, rfl⟩)
      rw [← hq.2.2]
      exact hmin _ hq.1 hq.2.1
    · obtain ⟨z, rfl⟩ := hv
      exact shortest_le b answer h z hn

/-- Distinct shortest-vector records have distinct ambient vectors. -/
theorem shortest_ambient_nodup (b : Basis n m) (answer : Minimum n m) (h : shortest b = some answer) :
    (answer.points.map Point.ambient).Nodup := by
  apply List.Nodup.map_on ?_ (shortest_nodup b answer h)
  intro q hq q' hq' he
  have hr := ((shortest_point_spec b answer h q).mp hq).1
  have hr' := ((shortest_point_spec b answer h q').mp hq').1
  have ha := congrArg Point.ambient hr
  have ha' := congrArg Point.ambient hr'
  have hz : q.coefficients = q'.coefficients := vector_injective b (ha.symm.trans (he.trans ha'))
  rw [hr, hr', hz]

/-- Shortest-vector ties are returned in ambient lexicographic order. -/
theorem shortest_sorted (b : Basis n m) (answer : Minimum n m) (h : shortest b = some answer) :
    answer.points.Pairwise (fun p q => compare p.ambient.toList q.ambient.toList ≠ .gt) := by
  obtain ⟨seed, _, rfl⟩ := shortest_run b answer h
  exact sortPoints_sorted _

end HexLatticeEnumMathlib
