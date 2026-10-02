/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.AdjoinRoot
public import HexRankMathlib.Quotient

public section

open Polynomial
open scoped Hex.PolyQuot.QAdjoinField

namespace Hex.PolyQuot.Rank

open HexMatrixMathlib.PolyWitness

variable {p : ZPoly} {x : SimpleRoot p} [ZPoly.CheckedIrreducible p]

/-- The executable generator of the fixed presentation. -/
@[expose] def generator (p : ZPoly) (x : SimpleRoot p) : PolyQuot p x :=
  PolyQuot.reduce p x (DensePoly.monomial 1 1)

theorem polynomial_coeffs (p : ZPoly) :
    eval (X : Polynomial Int) p.coeffs.toList = HexPolyZMathlib.toPolynomial p := by
  ext n
  rw [coeff_polynomial, HexPolyMathlib.coeff_toPolynomial]
  simp only [Int.cast_id, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  simp only [DensePoly.coeff, Array.getD_eq_getD_getElem?]
  rfl

omit [ZPoly.CheckedIrreducible p] in
theorem generator_value (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = x) :
    PolyQuot.toComplex (generator p x) rep hrep = rep.root := by
  unfold PolyQuot.toComplex generator
  change Polynomial.eval₂ (algebraMap Rat ℂ) rep.root
    (HexPolyMathlib.toPolynomial (PolyQuot.reduceCoeffs p (DensePoly.monomial 1 1))) = rep.root
  rw [PolyQuot.eval_reduceCoeffs, HexPolyMathlib.toPolynomial_monomial, Polynomial.eval₂_monomial, _root_.map_one, pow_one, one_mul]

theorem generator_relation : eval (generator p x) p.coeffs.toList = 0 := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  let emb := PolyQuot.embedding rep hrep
  apply PolyQuot.toComplex_injective rep hrep
  change emb (eval (generator p x) p.coeffs.toList) = emb 0
  rw [map_eval, _root_.map_zero]
  change eval (PolyQuot.toComplex (generator p x) rep hrep) p.coeffs.toList = 0
  rw [generator_value, ← eval₂_polynomial (Int.castRingHom ℂ), polynomial_coeffs]
  have hp := PolyQuot.eval_reduceCoeffs (p := p) (ZPoly.toRatPoly p) rep
  rw [PolyQuot.reduceCoeffs, HexPolyMathlib.toPolynomial_mod, EuclideanDomain.mod_self,
    Polynomial.eval₂_zero, HexPolyZMathlib.toPolynomial_toRatPoly] at hp
  have hcomp : (algebraMap Rat ℂ).comp (Int.castRingHom Rat) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  simpa only [HexPolyZMathlib.toPolyℚ, Polynomial.eval₂_map, hcomp] using hp.symm

/-- Interpret the integral polynomial model in the executable field. -/
noncomputable def integerHom : IntQuot p.coeffs.toList →+* PolyQuot p x :=
  AdjoinRoot.lift (Int.castRingHom _) (generator p x)
    (by rw [eval₂_polynomial]; exact generator_relation)

/-- The primitive defining polynomial gives an injective integral model,
even when the generator is not an algebraic integer. -/
theorem integerHom_injective : Function.Injective (integerHom (p := p) (x := x)) := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  let emb := PolyQuot.embedding rep hrep
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  induction a using AdjoinRoot.induction_on with
  | _ g =>
    rw [AdjoinRoot.mk_eq_zero, polynomial_coeffs]
    have hc := congrArg emb ha
    simp only [integerHom, AdjoinRoot.lift_mk, _root_.map_zero] at hc
    rw [Polynomial.hom_eval₂] at hc
    have hcomp : emb.comp (Int.castRingHom (PolyQuot p x)) = Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    rw [hcomp] at hc
    change Polynomial.eval₂ (Int.castRingHom ℂ)
      (PolyQuot.toComplex (generator p x) rep hrep) g = 0 at hc
    rw [generator_value] at hc
    have hdiv : PolyQuot.definingPolynomial p ∣ g.map (Int.castRingHom Rat) := by
      apply AdjoinRoot.mk_eq_zero.mp
      apply (PolyQuot.rootHom rep).injective
      rw [_root_.map_zero, PolyQuot.rootHom, AdjoinRoot.lift_mk, Polynomial.eval₂_map]
      have hcomp' : (algebraMap Rat ℂ).comp (Int.castRingHom Rat) = Int.castRingHom ℂ :=
        RingHom.ext_int _ _
      rwa [hcomp']
    have hirr : _root_.Irreducible (HexPolyZMathlib.toPolynomial p) :=
      (ZPoly.Irreducible_iff_polynomialIrreducible p).mp
        ((ZPoly.isIrreducible_iff p).mp ZPoly.CheckedIrreducible.is_true)
    have hprim := hirr.isPrimitive (by
      rw [HexPolyMathlib.natDegree_toPolynomial]
      exact Nat.ne_of_gt (ZPoly.CheckedIrreducible.pos_degree (p := p)))
    apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ hprim).mpr
    rw [PolyQuot.definingPolynomial, Polynomial.smul_eq_C_mul] at hdiv
    exact (dvd_mul_left _ _).trans hdiv

/-- Rank of integral-coordinate rows in the executable number field. -/
theorem rank_eq_integral (n m : Nat) (L : List (List (List Int))) (c : Hex.Matrix.PolyWitness)
    (h : Hex.Matrix.checkRankPoly n m p.coeffs.toList L c = true) :
    (ofPolys (generator p x) n m L).rank = c.rank :=
  rank_eq_embedded p.coeffs.toList integerHom integerHom_injective (generator p x)
    (by simp [integerHom]) n m L c h

/-- Clearing positive integer row denominators preserves rank. The field
arithmetic is checked only in this entrywise identification; the rank
certificate itself uses integer coefficient lists. -/
theorem rank_eq_scaled {n m : Nat} (A : _root_.Matrix (Fin n) (Fin m) (PolyQuot p x))
    (s : List Nat) (L : List (List (List Int))) (c : Hex.Matrix.PolyWitness)
    (hs : s.length = n) (hpos : s.all (0 < ·) = true)
    (hA : HexMatrixMathlib.entriesEq n m
      (fun i j => (s.getD i 1 : PolyQuot p x) * A i j)
      (L.map (List.map (HexMatrixMathlib.PolyWitness.eval (generator p x)))) = true)
    (hc : Hex.Matrix.checkRankPoly n m p.coeffs.toList L c = true) :
    A.rank = c.rank := by
  classical
  let D : _root_.Matrix (Fin n) (Fin n) (PolyQuot p x) :=
    Matrix.diagonal fun i => (s.getD i 1 : PolyQuot p x)
  have hD : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hi : i.val < s.length := hs ▸ i.isLt
    have hp := List.all_eq_true.mp hpos (s[i.val]) (List.getElem_mem hi)
    have hp : 0 < s[i.val] := of_decide_eq_true hp
    simpa only [List.getD_eq_getElem _ _ hi] using
      (Nat.cast_ne_zero.mpr hp.ne' : (s[i.val] : PolyQuot p x) ≠ 0)
  have hDA : D * A = ofPolys (generator p x) n m L := by
    have h := HexMatrixMathlib.eq_ofLists_of_entriesEq _ _ _ _ hA
    funext i j
    rw [_root_.Matrix.diagonal_mul]
    exact congrFun (congrFun h i) j
  calc
    A.rank = (D * A).rank := (Matrix.rank_mul_eq_right_of_det_ne_zero D A hD).symm
    _ = (ofPolys (generator p x) n m L).rank := congrArg _root_.Matrix.rank hDA
    _ = c.rank := rank_eq_integral n m L c hc

end Hex.PolyQuot.Rank
