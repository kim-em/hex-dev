/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRank
public import HexMvPolyTheory.Aeval
public import HexMatrixTheory.Algebra
public import Mathlib.Algebra.MvPolynomial.Rename

public section

namespace HexGenericRankTheory

open Hex HexMatrixTheory
open scoped HexMvPolyTheory

universe u v w

variable {k n m : Nat} {C : Type u} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]

/-- The polynomial matrix represented by a sealed reflection batch. -/
@[expose] noncomputable def symbolic (P : Hex.Matrix (MvPoly k C Mono.grevlex) n m) :
    Matrix (Fin n) (Fin m) (MvPolynomial (Fin k) C) :=
  (matrixEquiv P).map HexMvPolyTheory.equiv

/-- The executable evaluation homomorphism factors through the polynomial equivalence. -/
theorem eval₂_comp {F : Type v} [CommRing F] (ι : C →+* F) (v : Fin k → F) :
    HexMvPolyTheory.eval₂MathlibHom (cmp := Mono.grevlex) ι v =
      (MvPolynomial.eval₂Hom ι v).comp HexMvPolyTheory.equiv.toRingHom := by
  ext p
  change HexMvPolyTheory.eval₂MathlibHom ι v p =
    MvPolynomial.eval₂ ι v (HexMvPolyTheory.equiv p)
  rw [HexMvPolyTheory.eval₂MathlibHom_apply, HexMvPolyTheory.equiv_apply,
    HexMvPolyTheory.eval₂_toMvPolynomial]

/-- Interpreting the symbolic matrix agrees with executable polynomial evaluation. -/
theorem symbolic_map {F : Type v} [CommRing F] (ι : C →+* F) (v : Fin k → F)
    (P : Hex.Matrix (MvPoly k C Mono.grevlex) n m) :
    (symbolic P).map (MvPolynomial.eval₂Hom ι v) =
      (matrixEquiv P).map (HexMvPolyTheory.eval₂MathlibHom ι v) := by
  rw [eval₂_comp]
  rfl

omit [DecidableEq C] [BEq C] [LawfulBEq C] in
/-- Independent polynomial variables and constant coefficients give the
composition of coefficient mapping and variable renaming. -/
theorem eval₂_X {D : Type v} [CommRing D] {σ : Type w}
    (ι : C →+* D) (f : Fin k → σ) :
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp ι) (MvPolynomial.X ∘ f) =
      (MvPolynomial.rename f).toRingHom.comp (MvPolynomial.map ι) := by
  ext a i <;> simp

/-- The atom condition makes polynomial interpretation injective. -/
theorem eval₂_injective {D : Type v} [CommRing D] {σ : Type w}
    (ι : C →+* D) (hι : Function.Injective ι) (f : Fin k → σ)
    (hf : Function.Injective f) :
    Function.Injective
      (HexMvPolyTheory.eval₂MathlibHom (cmp := Mono.grevlex)
        (MvPolynomial.C.comp ι) (MvPolynomial.X ∘ f)) := by
  rw [eval₂_comp, eval₂_X]
  exact ((MvPolynomial.rename_injective f hf).comp (MvPolynomial.map_injective ι hι)).comp
    HexMvPolyTheory.equiv.injective

end HexGenericRankTheory
