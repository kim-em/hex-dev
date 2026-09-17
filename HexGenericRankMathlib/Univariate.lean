/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib.Modular

public section

namespace HexGenericRankMathlib

open Hex HexMatrixMathlib
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64

/-- A single formal polynomial variable gives an injective interpretation. -/
theorem rank_univariate {C D : Type*} [CommRing C] [CommRing D] [IsDomain D]
    [DecidableEq C] [BEq C] [LawfulBEq C]
    (ι : C →+* Polynomial D) (ι₀ : C →+* D) (hι : Function.Injective ι₀)
    (hC : ι = Polynomial.C.comp ι₀) (v : Fin 1 → Polynomial D)
    (hv : v = fun _ => Polynomial.X)
    {n m : Nat} {P : Hex.Matrix (MvPoly 1 C Mono.grevlex) n m}
    {c : Hex.Matrix.RankCert (MvPoly 1 C Mono.grevlex) n m}
    (h : Hex.Matrix.checkRank P c = true)
    (A : Matrix (Fin n) (Fin m) (Polynomial D))
    (hA : A = (symbolic P).map (MvPolynomial.eval₂Hom ι v)) : A.rank = c.rank := by
  rw [hA, symbolic_map]
  apply checkRank_sound_map _ ?_ h
  rw [eval₂_comp, hC, hv]
  have he : MvPolynomial.eval₂Hom (Polynomial.C.comp ι₀) (fun _ : Fin 1 => Polynomial.X) =
      (MvPolynomial.uniqueAlgEquiv D (Fin 1)).toRingHom.comp (MvPolynomial.map ι₀) := by
    ext a i <;> simp [MvPolynomial.uniqueAlgEquiv_apply]
  rw [he]
  exact ((MvPolynomial.uniqueAlgEquiv D (Fin 1)).injective.comp
    (MvPolynomial.map_injective ι₀ hι)).comp HexMvPolyMathlib.equiv.injective

theorem rank_univariate_int {D : Type*} [CommRing D] [IsDomain D] [CharZero D]
    (v : Fin 1 → Polynomial D) (hv : v = fun _ => Polynomial.X)
    {n m : Nat} {P : Hex.Matrix (MvPoly 1 Int Mono.grevlex) n m}
    {c : Hex.Matrix.RankCert (MvPoly 1 Int Mono.grevlex) n m}
    (h : Hex.Matrix.checkRank P c = true)
    (A : Matrix (Fin n) (Fin m) (Polynomial D))
    (hA : A = (symbolic P).map (MvPolynomial.eval₂Hom (Int.castRingHom _) v)) : A.rank = c.rank :=
  rank_univariate _ (Int.castRingHom D) Int.cast_injective
    (by ext; simp) v hv h A hA

theorem rank_univariate_residue (p : Nat) [Hex.ZMod64.Bounds p]
    {D : Type*} [CommRing D] [IsDomain D] [CharP D p]
    (v : Fin 1 → Polynomial D) (hv : v = fun _ => Polynomial.X)
    {n m : Nat} {P : Hex.Matrix (MvPoly 1 (Hex.ZMod64 p) Mono.grevlex) n m}
    {c : Hex.Matrix.RankCert (MvPoly 1 (Hex.ZMod64 p) Mono.grevlex) n m}
    (h : Hex.Matrix.checkRank P c = true)
    (A : Matrix (Fin n) (Fin m) (Polynomial D))
    (hA : A = (symbolic P).map (MvPolynomial.eval₂Hom (HexReflectMathlib.residueHom p _) v)) :
    A.rank = c.rank :=
  rank_univariate _ (HexReflectMathlib.residueHom p D) (HexReflectMathlib.residueHom_injective p D)
    (HexReflectMathlib.residueHom_polynomial p D) v hv h A hA

end HexGenericRankMathlib
