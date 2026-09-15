/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdealMathlib.Reify

public section

namespace HexDeterminantalIdealMathlib

open Hex HexMatrixMathlib
open scoped HexMvPolyMathlib

universe u v w z

variable {C : Type} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
  {k n m : Nat}

/-- The sealed polynomial interpretation and its exact generator list. -/
structure PolyData {F : Type u} [CommRing F] (A : Matrix (Fin n) (Fin m) F)
    (r : Nat) (gs : List F) (C : Type) (k : Nat) where
  coefficientRing : CommRing C
  coefficientDecEq : DecidableEq C
  coefficientBEq : BEq C
  coefficientLawfulBEq : @LawfulBEq C coefficientBEq
  environment : List F
  environment_length : environment.length = k
  valuation : Fin k → F
  sealed : valuation = vecOfList k environment
  coefficientMap : letI := coefficientRing; C →+* F
  matrix : letI := coefficientRing; Hex.Matrix (MvPoly k C Mono.grevlex) n m
  generators : letI := coefficientRing; List (MvPoly k C Mono.grevlex)
  generators_eq : letI := coefficientRing; letI := coefficientDecEq; letI := coefficientBEq
    letI := coefficientLawfulBEq
    generators = Hex.Matrix.detIdealGens r matrix
  interpretation : letI := coefficientRing; letI := coefficientDecEq; letI := coefficientBEq
    letI := coefficientLawfulBEq
    A = (matrixEquiv matrix).map (HexMvPolyMathlib.eval₂MathlibHom coefficientMap valuation)
  display : letI := coefficientRing; letI := coefficientDecEq; letI := coefficientBEq
    letI := coefficientLawfulBEq
    generators.map (HexMvPolyMathlib.eval₂MathlibHom coefficientMap valuation) = gs

variable {F : Type (max v w)} [CommRing F]

/-- The symbolic-matrix payload holds over coefficient domains, including `ℤ`.
Its vanishing theorem quantifies over field-valued points. -/
structure IdealData (ι : C →+* F) (v : Fin k → F)
    (P : Hex.Matrix (MvPoly k C Mono.grevlex) n m) (r : Nat)
    (D : Type v) [CommRing D] (σ : Type w) where
  coefficientMap : C →+* D
  coefficient_injective : Function.Injective coefficientMap
  indices : Fin k → σ
  indices_injective : Function.Injective indices
  coefficient_eq : HEq ι ((MvPolynomial.C : D →+* MvPolynomial σ D).comp coefficientMap)
  valuation_eq : HEq v (MvPolynomial.X ∘ indices : Fin k → MvPolynomial σ D)
  generators : List (MvPolynomial σ D)
  generators_eq : generators = (Hex.Matrix.detIdealGens r P).map
    (MvPolynomial.rename indices ∘ MvPolynomial.map coefficientMap ∘ HexMvPolyMathlib.equiv)
  span_eq : Ideal.span {g | g ∈ generators} =
    Ideal.map (MvPolynomial.rename indices).toRingHom
      (Ideal.map (MvPolynomial.map coefficientMap)
        (Ideal.span {g | g ∈ (Hex.Matrix.minors r P).map HexMvPolyMathlib.equiv}))

/-- The same ideal payload gives the locus over fields in every universe. -/
theorem IdealData.vanishing {D : Type v} [CommRing D] {σ : Type w}
    {ι : C →+* F} {v : Fin k → F} {P : Hex.Matrix (MvPoly k C Mono.grevlex) n m}
    {r : Nat} (d : IdealData ι v P r D σ) (K : Type z) [Field K]
    (ψ : D →+* K) (p : σ → K) :
    (∀ g ∈ d.generators, MvPolynomial.eval₂ ψ p g = 0) ↔
      ((matrixEquiv P).map (HexMvPolyMathlib.eval₂MathlibHom
        (ψ.comp d.coefficientMap) (p ∘ d.indices))).rank < r := by
  rw [d.generators_eq]
  exact gens_map_vanish_iff_rank_lt d.coefficientMap d.indices P r ψ p

/-- The fixed four-field result shared by the term and programmatic frontends.
For symbolic matrices, `D` and `σ` are their coefficient and variable types.
Otherwise the provider uses `D := F` and `σ := Empty`, with `ideal? := none`. -/
structure LocusResult (A : Matrix (Fin n) (Fin m) F) (r : Nat) (C : Type) (k : Nat)
    (D : Type v) [CommRing D] (σ : Type w) where
  gens : List F
  proof : A.rank < r ↔ AllZero gens
  poly : PolyData A r gens C k
  ideal? : letI := poly.coefficientRing; letI := poly.coefficientDecEq; letI := poly.coefficientBEq
    letI := poly.coefficientLawfulBEq
    Option (IdealData.{v, w} poly.coefficientMap poly.valuation poly.matrix r D σ)

/-- Construct the optional payload from independent-variable evidence. -/
noncomputable def idealData {D : Type v} [CommRing D] {σ : Type w}
    (ι : C →+* F) (v : Fin k → F) (P : Hex.Matrix (MvPoly k C Mono.grevlex) n m) (r : Nat)
    (ι₀ : C →+* D) (hι : Function.Injective ι₀) (f : Fin k → σ) (hf : Function.Injective f)
    (hc : HEq ι ((MvPolynomial.C : D →+* MvPolynomial σ D).comp ι₀))
    (hv : HEq v (MvPolynomial.X ∘ f : Fin k → MvPolynomial σ D)) :
    IdealData.{v, w} ι v P r D σ where
  coefficientMap := ι₀
  coefficient_injective := hι
  indices := f
  indices_injective := hf
  coefficient_eq := hc
  valuation_eq := hv
  generators := (Hex.Matrix.detIdealGens r P).map
    (MvPolynomial.rename f ∘ MvPolynomial.map ι₀ ∘ HexMvPolyMathlib.equiv)
  generators_eq := rfl
  span_eq := span_gens_map_eq ι₀ f P r

/-- Integer coefficients give the symbolic payload when the coefficient
interpretation is injective and the sealed atoms are distinct variables. -/
noncomputable def idealData_int {D : Type v} [CommRing D] [CharZero D] {σ : Type w}
    (v : Fin k → MvPolynomial σ D) (f : Fin k → σ)
    (hf : Function.Injective f) (hv : v = MvPolynomial.X ∘ f)
    (P : Hex.Matrix (MvPoly k Int Mono.grevlex) n m) (r : Nat) :
    IdealData.{v, w} (Int.castRingHom (MvPolynomial σ D)) v P r D σ := by
  have hc : Int.castRingHom (MvPolynomial σ D) = MvPolynomial.C.comp (Int.castRingHom D) := by
    ext
    simp
  exact idealData _ v P r (Int.castRingHom D) Int.cast_injective f hf
    (heq_of_eq hc) (heq_of_eq hv)

end HexDeterminantalIdealMathlib
