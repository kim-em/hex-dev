/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib.Transport
public import HexRankMathlib.Extension
public import HexDeterminantalIdealMathlib.Rank

public section

namespace HexGenericRankMathlib

open Hex HexMatrixMathlib
open scoped HexMvPolyMathlib

universe u v

variable {k n m : Nat} {C : Type u} [CommRing C] [IsDomain C]
  [DecidableEq C] [BEq C] [LawfulBEq C]

/-- A passing polynomial certificate gives the generic rank. -/
theorem rank_eq {P : Hex.Matrix (MvPoly k C Mono.grevlex) n m}
    {c : Hex.Matrix.RankCert (MvPoly k C Mono.grevlex) n m}
    (h : Hex.Matrix.checkRank P c = true) : (symbolic P).rank = c.rank := by
  exact checkRank_sound_map (A := P) (c := c)
    (HexMvPolyMathlib.equiv (n := k) (R := C) (cmp := Mono.grevlex)).toRingHom
    (HexMvPolyMathlib.equiv (n := k) (R := C) (cmp := Mono.grevlex)).injective h

/-- The generic rank is unchanged in any fraction field of the polynomial ring. -/
theorem rank_fraction {K : Type v} [Field K] [Algebra (MvPolynomial (Fin k) C) K]
    [IsFractionRing (MvPolynomial (Fin k) C) K]
    {P : Hex.Matrix (MvPoly k C Mono.grevlex) n m}
    {c : Hex.Matrix.RankCert (MvPoly k C Mono.grevlex) n m}
    (h : Hex.Matrix.checkRank P c = true) :
    ((symbolic P).map (algebraMap _ K)).rank = c.rank := by
  rw [HexMatrixMathlib.rank_map_eq, rank_eq h]

/-- Producer correctness at the polynomial exact quotient. -/
theorem genericCert_check [Dvd C] [GcdOps C] [LawfulGcdOps C]
    (P : Hex.Matrix (MvPoly k C Mono.grevlex) n m) :
    Hex.Matrix.checkRank P (GenericRank.genericCert P) = true := by
  apply rankCertWith_check
  · intro a b hb
    exact Hex.exactDiv_mul_right a hb
  · intro h
    have := congrArg (HexMvPolyMathlib.equiv (cmp := Mono.grevlex)) h
    simp at this

/-- The executable generic rank is the rank of the polynomial matrix. -/
theorem genericRank_eq [Dvd C] [GcdOps C] [LawfulGcdOps C]
    (P : Hex.Matrix (MvPoly k C Mono.grevlex) n m) :
    GenericRank.genericRank P = (symbolic P).rank :=
  (rank_eq (genericCert_check P)).symm

/-- The producer selects a nonzero minor of the generic rank. -/
theorem genericCert_minor [Dvd C] [GcdOps C] [LawfulGcdOps C]
    (P : Hex.Matrix (MvPoly k C Mono.grevlex) n m) :
    Hex.Matrix.det (Hex.Matrix.selectedSubmatrix P
      (GenericRank.genericCert P).rows (GenericRank.genericCert P).cols) ≠ 0 :=
  Hex.Matrix.RankCert.det_ne_zero (genericCert_check P)

/-- Every minor one size above the generic rank vanishes. -/
theorem genericRank_succ_minor [Dvd C] [GcdOps C] [LawfulGcdOps C]
    (P : Hex.Matrix (MvPoly k C Mono.grevlex) n m)
    (rows : Vector (Fin n) (GenericRank.genericRank P + 1))
    (cols : Vector (Fin m) (GenericRank.genericRank P + 1)) :
    Hex.Matrix.det (Hex.Matrix.selectedSubmatrix P rows cols) = 0 :=
  Hex.Matrix.RankCert.det_succ_eq_zero (genericCert_check P) rows cols

omit [IsDomain C] in
/-- A checked polynomial certificate gives the rank at every point where
its denominator remains nonzero. -/
theorem rank_at {F : Type v} [CommRing F] [IsDomain F] (ι : C →+* F) (v : Fin k → F)
    {P : Hex.Matrix (MvPoly k C Mono.grevlex) n m}
    {c : Hex.Matrix.RankCert (MvPoly k C Mono.grevlex) n m}
    (h : Hex.Matrix.checkRank P c = true)
    (hd : HexMvPolyMathlib.eval₂MathlibHom ι v c.denom ≠ 0) :
    ((symbolic P).map (MvPolynomial.eval₂Hom ι v)).rank = c.rank := by
  rw [symbolic_map]
  exact checkRank_sound_at (A := P) (c := c) (HexMvPolyMathlib.eval₂MathlibHom ι v) h hd

omit [DecidableEq C] [BEq C] [LawfulBEq C] in
/-- Specialisation cannot increase rank, including into a domain that is not a field. -/
theorem rank_map_le {F : Type v} [CommRing F] [IsDomain F]
    (φ : MvPolynomial (Fin k) C →+* F)
    (S : Matrix (Fin n) (Fin m) (MvPolynomial (Fin k) C)) :
    (S.map φ).rank ≤ S.rank := by
  rw [← rank_map_eq_rank_fractionRing (S.map φ)]
  have h := HexDeterminantalIdealMathlib.rank_map_le_rank_fractionRing
    ((algebraMap F (FractionRing F)).comp φ) (matrixEquiv.symm S)
  simpa only [Equiv.apply_symm_apply, Matrix.map_map, Function.comp_def,
    RingHom.coe_comp, rank_map_eq_rank_fractionRing] using h

/-- The integer interpretation into a polynomial ring has constant image. -/
theorem int_cast_C {D : Type*} [CommRing D] {σ : Type*} :
    Int.castRingHom (MvPolynomial σ D) = MvPolynomial.C.comp (Int.castRingHom D) := by
  ext
  simp

omit [IsDomain C] in
/-- Independent atoms justify an unconditional rank statement about the
source polynomial matrix. Both coefficient factorisation and atom
injectivity are explicit hypotheses. -/
theorem rank_variables {D : Type*} [CommRing D] [IsDomain D] {σ : Type*}
    (ι : C →+* MvPolynomial σ D) (ι₀ : C →+* D) (hι : Function.Injective ι₀)
    (hC : ι = MvPolynomial.C.comp ι₀) (v : Fin k → MvPolynomial σ D)
    (f : Fin k → σ) (hf : Function.Injective f) (hv : v = MvPolynomial.X ∘ f)
    {P : Hex.Matrix (MvPoly k C Mono.grevlex) n m}
    {c : Hex.Matrix.RankCert (MvPoly k C Mono.grevlex) n m}
    (h : Hex.Matrix.checkRank P c = true)
    (A : Matrix (Fin n) (Fin m) (MvPolynomial σ D))
    (hA : A = (symbolic P).map (MvPolynomial.eval₂Hom ι v)) : A.rank = c.rank := by
  rw [hA, symbolic_map, hC, hv]
  exact checkRank_sound_map
    (HexMvPolyMathlib.eval₂MathlibHom (MvPolynomial.C.comp ι₀) (MvPolynomial.X ∘ f))
    (eval₂_injective ι₀ hι f hf) h

/-- The integer provider satisfies coefficient injectivity exactly in
characteristic zero on the coefficient domain. -/
theorem rank_variables_int {D : Type*} [CommRing D] [IsDomain D] [CharZero D]
    {σ : Type*} (v : Fin k → MvPolynomial σ D) (f : Fin k → σ)
    (hf : Function.Injective f) (hv : v = MvPolynomial.X ∘ f)
    {P : Hex.Matrix (MvPoly k Int Mono.grevlex) n m}
    {c : Hex.Matrix.RankCert (MvPoly k Int Mono.grevlex) n m}
    (h : Hex.Matrix.checkRank P c = true)
    (A : Matrix (Fin n) (Fin m) (MvPolynomial σ D))
    (hA : A = (symbolic P).map (MvPolynomial.eval₂Hom (Int.castRingHom _) v)) :
    A.rank = c.rank :=
  rank_variables (Int.castRingHom _) (Int.castRingHom D) Int.cast_injective
    int_cast_C v f hf hv h A hA

end HexGenericRankMathlib
