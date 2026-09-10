/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnumMathlib.Preprocess
public import HexLLLMathlib.IntegerLattice
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

variable {n m : Nat}

/-- Integer coordinates embedded linearly over `ℤ` into rational coordinate space. -/
def rationalEmbedding : (Fin m → Int) →ₗ[Int] (Fin m → Rat) where
  toFun v i := (v i : Rat)
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp [Int.cast_mul]

/-- The integer row lattice in rational coordinates; scalar coefficients remain integers. -/
def rationalLattice (b : Basis n m) : Submodule Int (Fin m → Rat) :=
  (HexLLLMathlib.latticeSubmodule b.rows).map rationalEmbedding

/-- The rational coordinate embedding is injective. -/
theorem rationalEmbedding_injective : Function.Injective (rationalEmbedding (m := m)) := by
  intro v w h
  funext i
  have h := congrFun h i
  change (v i : Rat) = (w i : Rat) at h
  exact_mod_cast h

/-- Integer-span membership in rational space is exactly executable lattice membership. -/
theorem mem_rationalLattice (b : Basis n m) (v : Vector Int m) :
    rationalEmbedding (HexMatrixMathlib.vectorEquiv v) ∈ rationalLattice b ↔ b.rows.memLattice v := by
  rw [rationalLattice, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, he⟩
    have he := rationalEmbedding_injective he
    rw [he] at hw
    exact (HexLLLMathlib.mem_latticeSubmodule_iff b.rows v).mp hw
  · intro h
    exact ⟨HexMatrixMathlib.vectorEquiv v, (HexLLLMathlib.mem_latticeSubmodule_iff b.rows v).mpr h, rfl⟩

/-- Integer coordinates embedded linearly over `ℤ` into real Euclidean space. -/
noncomputable def realEmbedding : (Fin m → Int) →ₗ[Int] EuclideanSpace Real (Fin m) where
  toFun := HexLLLMathlib.intVectorToEuclidean
  map_add' v w := by ext i; simp [HexLLLMathlib.intVectorToEuclidean]
  map_smul' c v := by ext i; simp [HexLLLMathlib.intVectorToEuclidean, Int.cast_mul]

/-- The integer row lattice viewed in real Euclidean space. -/
noncomputable def realLattice (b : Basis n m) : Submodule Int (EuclideanSpace Real (Fin m)) :=
  (HexLLLMathlib.latticeSubmodule b.rows).map realEmbedding

/-- The real span in which lattice packing takes place. -/
noncomputable def realSpan (b : Basis n m) : Submodule Real (EuclideanSpace Real (Fin m)) :=
  Submodule.span Real (realLattice b : Set (EuclideanSpace Real (Fin m)))

/-- Embed a rational query target in real Euclidean space coordinatewise. -/
noncomputable def realTarget (t : Vector Rat m) : EuclideanSpace Real (Fin m) :=
  WithLp.toLp 2 (fun i => (t[i] : Real))

/-- Embed an executable integer vector in real Euclidean space. -/
noncomputable abbrev realVector (v : Vector Int m) : EuclideanSpace Real (Fin m) :=
  HexLLLMathlib.intRowToEuclidean v

/-- The two integer-coordinate representations have the same Euclidean image. -/
theorem realEmbedding_vector (v : Vector Int m) :
    realEmbedding (HexMatrixMathlib.vectorEquiv v) = realVector v := by
  ext i
  simp [realEmbedding, realVector, HexLLLMathlib.intVectorToEuclidean,
    HexLLLMathlib.intRowToEuclidean, HexMatrixMathlib.vectorEquiv]

/-- Real coordinate casting is injective on integer vectors. -/
theorem realVector_injective : Function.Injective (realVector (m := m)) := by
  intro v w h
  apply Vector.ext
  intro i hi
  have he := congrArg (fun x : EuclideanSpace Real (Fin m) => x ⟨i, hi⟩) h
  change (v[i] : Real) = (w[i] : Real) at he
  exact_mod_cast he

/-- Real coordinate casting is injective on Mathlib's integer coordinate functions. -/
theorem realEmbedding_injective : Function.Injective (realEmbedding (m := m)) := by
  intro v w h
  funext i
  have he := congrArg (fun x : EuclideanSpace Real (Fin m) => x i) h
  change (v i : Real) = (w i : Real) at he
  exact_mod_cast he

/-- A real lattice point has an integer-coordinate preimage in the executable row lattice. -/
theorem mem_realLattice (b : Basis n m) (x : EuclideanSpace Real (Fin m)) :
    x ∈ realLattice b ↔ ∃ v : Vector Int m, b.rows.memLattice v ∧ realVector v = x := by
  rw [realLattice, Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨HexMatrixMathlib.vectorEquiv.symm v, ?_, ?_⟩
    · apply (HexLLLMathlib.mem_latticeSubmodule_iff b.rows _).mp
      simpa using hv
    · rw [← realEmbedding_vector, Equiv.apply_symm_apply]
      exact he
  · rintro ⟨v, hv, he⟩
    exact ⟨HexMatrixMathlib.vectorEquiv v, (HexLLLMathlib.mem_latticeSubmodule_iff b.rows v).mpr hv,
      (realEmbedding_vector v).trans he⟩

/-- Every real lattice point lies in the lattice's real span. -/
theorem realLattice_mem_span (b : Basis n m) {x : EuclideanSpace Real (Fin m)} (h : x ∈ realLattice b) :
    x ∈ realSpan b := Submodule.subset_span h

/-- Rational squared distances cast exactly to real Euclidean squared distances, including off-span targets. -/
theorem real_distance (v : Vector Int m) (t : Vector Rat m) :
    dist (realVector v) (realTarget t) ^ 2 = (distance v t : Real) := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp only [realVector, HexLLLMathlib.intRowToEuclidean, realTarget, PiLp.sub_apply]
  simp only [distance, subtract_eq, castVector_eq, Vector.normSq, HexMatrixMathlib.dotProduct_eq, dotProduct]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.getElem_fin, Vector.getElem_sub, Vector.getElem_map, HexMatrixMathlib.vectorEquiv_apply]
  push_cast
  ring

/-- The rational integer-span formulation of complete ball enumeration. -/
theorem enumerate_rational_spec (b : Basis n m) (t : Vector Rat m) (r : Rat) (v : Vector Int m) :
    v ∈ (enumerate b t r).map Point.ambient ↔
      rationalEmbedding (HexMatrixMathlib.vectorEquiv v) ∈ rationalLattice b ∧ distance v t ≤ r := by
  rw [mem_rationalLattice, enumerate_spec]

/-- The real Euclidean formulation of complete ball enumeration. -/
theorem enumerate_real_spec (b : Basis n m) (t : Vector Rat m) (r : Rat) (x : EuclideanSpace Real (Fin m)) :
    x ∈ ((enumerate b t r).map Point.ambient).map realVector ↔
      x ∈ realLattice b ∧ dist x (realTarget t) ^ 2 ≤ (r : Real) := by
  rw [List.mem_map]
  simp only [enumerate_spec, mem_realLattice]
  constructor
  · rintro ⟨v, ⟨hv, hd⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, by rw [real_distance]; exact_mod_cast hd⟩
  · rintro ⟨⟨v, hv, rfl⟩, hd⟩
    rw [real_distance] at hd
    exact ⟨v, ⟨hv, by exact_mod_cast hd⟩, rfl⟩

/-- Zero has its usual Euclidean image. -/
@[simp] theorem realVector_zero : realVector (0 : Vector Int m) = 0 := by
  ext i
  simp [realVector, HexLLLMathlib.intRowToEuclidean]

/-- The zero rational target is the Euclidean origin. -/
@[simp] theorem realTarget_zero : realTarget (0 : Vector Rat m) = 0 := by
  ext i
  simp [realTarget]

/-- Rational integer-span formulation of all global closest vectors. -/
theorem closest_rational_spec (b : Basis n m) (t : Vector Rat m) (v : Vector Int m) :
    v ∈ (closest b t).points.map Point.ambient ↔
      rationalEmbedding (HexMatrixMathlib.vectorEquiv v) ∈ rationalLattice b ∧
      ∀ w, rationalEmbedding (HexMatrixMathlib.vectorEquiv w) ∈ rationalLattice b →
        distance v t ≤ distance w t := by
  simp only [mem_rationalLattice, closest_spec]

/-- Rational integer-span formulation of all global nonzero shortest vectors. -/
theorem shortest_rational_spec (b : Basis n m) (a : Minimum n m) (h : shortest b = some a)
    (v : Vector Int m) : v ∈ a.points.map Point.ambient ↔
      rationalEmbedding (HexMatrixMathlib.vectorEquiv v) ∈ rationalLattice b ∧ v ≠ 0 ∧
      ∀ w, rationalEmbedding (HexMatrixMathlib.vectorEquiv w) ∈ rationalLattice b → w ≠ 0 →
        distance v 0 ≤ distance w 0 := by
  simp only [mem_rationalLattice, shortest_spec b a h]

/-- All global closest vectors in real Euclidean distance, with arbitrary rational targets. -/
theorem closest_real_spec (b : Basis n m) (t : Vector Rat m) (x : EuclideanSpace Real (Fin m)) :
    x ∈ ((closest b t).points.map Point.ambient).map realVector ↔
      x ∈ realLattice b ∧ ∀ y ∈ realLattice b, dist x (realTarget t) ≤ dist y (realTarget t) := by
  rw [List.mem_map]
  simp only [closest_spec, mem_realLattice]
  constructor
  · rintro ⟨v, ⟨hv, hmin⟩, rfl⟩
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have hd : dist (realVector v) (realTarget t) ^ 2 ≤ dist (realVector w) (realTarget t) ^ 2 := by
      rw [real_distance, real_distance]
      exact_mod_cast hmin w hw
    nlinarith [(dist_nonneg : 0 ≤ dist (realVector v) (realTarget t)), (dist_nonneg : 0 ≤ dist (realVector w) (realTarget t))]
  · rintro ⟨⟨v, hv, rfl⟩, hmin⟩
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    intro w hw
    have hd := hmin (realVector w) ⟨w, hw, rfl⟩
    have hs := mul_self_le_mul_self ((dist_nonneg : 0 ≤ dist (realVector v) (realTarget t))) hd
    rw [← sq, ← sq, real_distance, real_distance] at hs
    exact_mod_cast hs

/-- All global nonzero shortest vectors in real Euclidean norm, including every tie. -/
theorem shortest_real_spec (b : Basis n m) (a : Minimum n m) (h : shortest b = some a)
    (x : EuclideanSpace Real (Fin m)) : x ∈ (a.points.map Point.ambient).map realVector ↔
      x ∈ realLattice b ∧ x ≠ 0 ∧ ∀ y ∈ realLattice b, y ≠ 0 → ‖x‖ ≤ ‖y‖ := by
  rw [List.mem_map]
  simp only [shortest_spec b a h, mem_realLattice]
  have hn (v : Vector Int m) : realVector v ≠ 0 ↔ v ≠ 0 := by
    rw [← realVector_zero, realVector_injective.ne_iff]
  constructor
  · rintro ⟨v, ⟨hv, hvn, hmin⟩, rfl⟩
    refine ⟨⟨v, hv, rfl⟩, (hn v).mpr hvn, ?_⟩
    rintro _ ⟨w, hw, rfl⟩ hwn
    have hd : (distance v 0 : Real) ≤ (distance w 0 : Real) := by
      exact_mod_cast hmin w hw ((hn w).mp hwn)
    rw [← real_distance, ← real_distance, realTarget_zero, dist_zero_right, dist_zero_right] at hd
    nlinarith [norm_nonneg (realVector v), norm_nonneg (realVector w)]
  · rintro ⟨⟨v, hv, rfl⟩, hvn, hmin⟩
    refine ⟨v, ⟨hv, (hn v).mp hvn, ?_⟩, rfl⟩
    intro w hw hwn
    have hd := hmin (realVector w) ⟨w, hw, rfl⟩ ((hn w).mpr hwn)
    have hs := mul_self_le_mul_self (norm_nonneg (realVector v)) hd
    have he (z : Vector Int m) : ‖realVector z‖ ^ 2 = (distance z 0 : Real) := by
      simpa using real_distance z 0
    rw [← sq, ← sq, he, he] at hs
    exact_mod_cast hs

/-- The integer coordinate embedding is closed, including in dimension zero. -/
theorem realEmbedding_closed : Topology.IsClosedEmbedding (realEmbedding (m := m)) := by
  exact (PiLp.homeomorph 2 (fun _ : Fin m => Real)).symm.isClosedEmbedding.comp
    (Topology.IsClosedEmbedding.piMap fun _ => Real.isClosedEmbedding_intCast)

/-- Integer row lattices are discrete because they lie in the embedded integer coordinate grid. -/
theorem realLattice_discrete (b : Basis n m) : IsDiscrete (realLattice b : Set (EuclideanSpace Real (Fin m))) := by
  apply realEmbedding_closed.isEmbedding.isInducing.isDiscrete_range.mono
  rintro x hx
  obtain ⟨v, hv, rfl⟩ := (mem_realLattice b x).mp hx
  exact ⟨HexMatrixMathlib.vectorEquiv v, realEmbedding_vector v⟩

end HexLatticeEnumMathlib
