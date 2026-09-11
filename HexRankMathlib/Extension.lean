/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Cert
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.RatFunc.Basic

public section

/-!
Scalar extension: the rank of a matrix over a domain is unchanged by passing
to any fraction field, proved through the certificate. Every domain has an
exact quotient classically, so `rankCertWith_check` supplies a certificate for
the matrix, and `checkRank_sound` and `checkRank_sound_map` read the same rank
off it over `R` and over `K`. The certificate is a proof device and is never
computed. The `Decidable (A.rank = r)` instance over `ℤ` runs the integer
producer.
-/

open Matrix

namespace HexMatrixMathlib

universe u v

variable {R : Type u} {n m : Nat}

/-- The rank is unchanged by extension of scalars to a fraction field. -/
theorem rank_map_eq [CommRing R] [IsDomain R] {K : Type v} [Field K] [Algebra R K]
    [IsFractionRing R K] (M : Matrix (Fin n) (Fin m) R) :
    (M.map (algebraMap R K)).rank = M.rank := by
  classical
  obtain ⟨c, hc⟩ := exists_rankCert (matrixEquiv.symm M)
  have h1 := checkRank_sound hc
  have h2 := checkRank_sound_map (algebraMap R K) (IsFractionRing.injective R K) hc
  simp only [Equiv.apply_symm_apply] at h1 h2
  rw [h1, h2]

/-- The rank is unchanged by passing to the field of fractions. -/
theorem rank_map_eq_rank_fractionRing [CommRing R] [IsDomain R] (M : Matrix (Fin n) (Fin m) R) :
    (M.map (algebraMap R (FractionRing R))).rank = M.rank :=
  rank_map_eq M

/-- The rank of a polynomial matrix is its rank over rational functions. -/
theorem rank_eq_ratFunc_rank' {F : Type u} [Field F]
    (M : Matrix (Fin n) (Fin m) (Polynomial F)) :
    (M.map (algebraMap (Polynomial F) (RatFunc F))).rank = M.rank :=
  rank_map_eq M

/-- Rank equations over `ℤ` are decided by the integer producer. -/
instance (A : Matrix (Fin n) (Fin m) ℤ) (r : Nat) : Decidable (A.rank = r) :=
  decidable_of_iff (Hex.Matrix.rank (matrixEquiv.symm A) = r)
    (by rw [rank_eq_rank, Equiv.apply_symm_apply])

end HexMatrixMathlib
