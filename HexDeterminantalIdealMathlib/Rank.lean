/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdealMathlib.Transport
public import HexRowReduceMathlib
public import Mathlib.RingTheory.Localization.FractionRing

public section

/-!
The rank-versus-minors theorem for `Matrix.rank`, under an arbitrary ring
homomorphism `φ` from the coefficient ring into a field: the rank of
`(matrixEquiv A).map φ` is below `r` exactly when `φ` kills every `r × r`
minor of `A`. The proof is the computational theorem for `A.map φ`, with
`Matrix.rank` replaced by the row-reduction rank through
`HexMatrixMathlib.rank_eq` and `φ` moved onto the minors through
`map_minors`. The corollary `rank_map_le_rank_fractionRing` says that no
specialisation of a matrix over a domain has rank above its generic rank.
-/

namespace HexDeterminantalIdealMathlib

open HexMatrixMathlib

universe u v

variable {R : Type u} {K : Type v} {n m : Nat}

/-- The rank under `φ` is below `r` exactly when `φ` kills every `r × r`
minor. -/
theorem rank_lt_iff_minors_map_eq_zero [CommRing R] [Field K] (φ : R →+* K)
    (A : Hex.Matrix R n m) (r : Nat) :
    ((matrixEquiv A).map φ).rank < r ↔ ∀ M ∈ Hex.Matrix.minors r A, φ M = 0 := by
  classical
  rw [← matrixEquiv_map, ← rank_eq (Hex.Matrix.rowReduce_isRowReduced (A.map φ))]
  rw [show (Hex.Matrix.rowReduce (A.map φ)).rank = Hex.Matrix.rowReduce_rank (A.map φ) from rfl,
    Hex.Matrix.rank_lt_iff_minors_eq_zero, ← map_minors, List.forall_mem_map]

/-- `r` is at most the rank under `φ` exactly when `φ` keeps some `r × r`
minor nonzero. -/
theorem le_rank_iff_exists_minor_map_ne_zero [CommRing R] [Field K] (φ : R →+* K)
    (A : Hex.Matrix R n m) (r : Nat) :
    r ≤ ((matrixEquiv A).map φ).rank ↔ ∃ M ∈ Hex.Matrix.minors r A, φ M ≠ 0 := by
  rw [← not_lt, rank_lt_iff_minors_map_eq_zero]
  push Not
  rfl

/-- The rank under `φ` is at most `r` exactly when `φ` kills every
`(r + 1) × (r + 1)` minor. -/
theorem rank_le_iff_minors_succ_map_eq_zero [CommRing R] [Field K] (φ : R →+* K)
    (A : Hex.Matrix R n m) (r : Nat) :
    ((matrixEquiv A).map φ).rank ≤ r ↔ ∀ M ∈ Hex.Matrix.minors (r + 1) A, φ M = 0 := by
  rw [← rank_lt_iff_minors_map_eq_zero, Nat.lt_succ_iff]

/-- The field case: the rank is below `r` exactly when every `r × r` minor
vanishes. -/
theorem rank_lt_iff_minors_eq_zero [Field K] (A : Hex.Matrix K n m) (r : Nat) :
    (matrixEquiv A).rank < r ↔ ∀ M ∈ Hex.Matrix.minors r A, M = 0 := by
  have h := rank_lt_iff_minors_map_eq_zero (RingHom.id K) A r
  simpa using h

/-- The field case for a Mathlib matrix: read through `matrixEquiv.symm`. -/
theorem _root_.Matrix.rank_lt_iff_minors_eq_zero' [Field K] (B : Matrix (Fin n) (Fin m) K)
    (r : Nat) :
    B.rank < r ↔ ∀ M ∈ Hex.Matrix.minors r (matrixEquiv.symm B), M = 0 := by
  have h := rank_lt_iff_minors_eq_zero (matrixEquiv.symm B) r
  rwa [Equiv.apply_symm_apply] at h

/-- No specialisation of a matrix over a domain has rank above the rank over
the fraction field. -/
theorem rank_map_le_rank_fractionRing [CommRing R] [IsDomain R] [Field K] (φ : R →+* K)
    (A : Hex.Matrix R n m) :
    ((matrixEquiv A).map φ).rank ≤
      ((matrixEquiv A).map (algebraMap R (FractionRing R))).rank := by
  rw [le_rank_iff_exists_minor_map_ne_zero]
  obtain ⟨M, hM, hne⟩ := (le_rank_iff_exists_minor_map_ne_zero φ A _).mp le_rfl
  refine ⟨M, hM, fun h0 => hne ?_⟩
  rw [IsFractionRing.to_map_eq_zero_iff.mp h0, map_zero]

end HexDeterminantalIdealMathlib
