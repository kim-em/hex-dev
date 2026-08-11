/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import Mathlib.Data.Rat.Cast.Defs
public import HexNumberFieldTowerMathlib.ArithmeticCore
public import HexResultantMathlib

public section

/-!
# Tower polynomial and relative norm semantics

The actual interpretation functions in this module make the one-level
resultant statement precise before the later Trager proof consumes it.
-/

namespace Hex.NumberTower

namespace Norm

/-- Interpret raw coordinates for a validated level list. The fallback is
unreachable when the list comes from a {name}`Hex.NumberTower`. -/
@[expose]
noncomputable def rawToComplex (levels : List Level) (a : Array Rat) : ℂ :=
  (RawEvaluation.evalCoords? levels a).map AlgebraicRoot.toComplex |>.getD 0

/-- The total raw evaluator agrees with direct mixed-radix denotation. -/
theorem rawToComplex_eq_denote (levels : List Level) (a : Array Rat) :
    rawToComplex levels a = LevelSemantics.denote levels a := by
  obtain ⟨root, hroot⟩ := Option.isSome_iff_exists.mp
    (evalCoords_isSome levels a)
  simp [rawToComplex, hroot,
    LevelSemantics.evalCoords_sound levels a hroot]

/-- Interpret a raw lower-tower dense polynomial in `Polynomial ℂ`. -/
@[expose]
noncomputable def rawPolynomial (levels : List Level)
    (f : DensePoly (Arithmetic.Coeff levels)) : Polynomial ℂ :=
  f.toArray.foldr
    (fun a value =>
      Polynomial.C (rawToComplex levels a.data) + Polynomial.X * value) 0

/-- Interpret an outer dense polynomial over raw lower-tower polynomials. -/
@[expose]
noncomputable def rawOuter (levels : List Level)
    (f : DensePoly (DensePoly (Arithmetic.Coeff levels))) :
    Polynomial (Polynomial ℂ) :=
  f.toArray.foldr
    (fun a value => Polynomial.C (rawPolynomial levels a) +
      Polynomial.X * value) 0

theorem raw_coeff_horner (levels : List Level) :
    ∀ (coefficients : List (Arithmetic.Coeff levels)) (n : Nat),
      (coefficients.foldr
          (fun (a : Arithmetic.Coeff levels) value =>
            Polynomial.C (rawToComplex levels a.data) +
            Polynomial.X * value) 0).coeff n =
        rawToComplex levels (coefficients.getD n 0).data
  | [], n => by
      change 0 = rawToComplex levels (0 : Arithmetic.Coeff levels).data
      rw [rawToComplex_eq_denote]
      simpa only [LevelSemantics.coeffDenote] using
        (LevelSemantics.coeffDenote_zero levels).symm
  | (a : Arithmetic.Coeff levels) :: tail, 0 => by
      simp
  | _ :: coefficients, n + 1 => by
      simpa using raw_coeff_horner levels coefficients n

/-- Coefficients of a semantically interpreted raw polynomial are the
denotations of its executable coefficients. -/
theorem coeff_rawPolynomial (levels : List Level)
    (f : DensePoly (Arithmetic.Coeff levels)) (n : Nat) :
    (rawPolynomial levels f).coeff n =
      rawToComplex levels (f.coeff n).data := by
  rw [rawPolynomial, ← Array.foldr_toList, raw_coeff_horner]
  have hget : f.toArray.toList.getD n (0 : Arithmetic.Coeff levels) =
      f.coeff n := by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      ← Array.getD_eq_getD_getElem?]
    exact DensePoly.toArray_getD f n
  exact congrArg (fun a : Arithmetic.Coeff levels =>
    rawToComplex levels a.data) hget

/-- Raw semantic interpretation preserves the polynomial zero. -/
@[simp]
theorem rawPolynomial_zero (levels : List Level) :
    rawPolynomial levels 0 = 0 := by
  ext n
  rw [coeff_rawPolynomial, DensePoly.coeff_zero, rawToComplex_eq_denote]
  simpa [LevelSemantics.coeffDenote] using
    LevelSemantics.coeffDenote_zero levels

/-- The transferred field with its zero projection pinned to the executable
coefficient instance. This lets existing `DensePoly` values retain their
instance-indexed type while the Mathlib laws are available locally. -/
@[expose, reducible]
noncomputable def coeffFieldPoly (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹) :
    Field (Arithmetic.Coeff levels) :=
  let zero := (inferInstance : Zero (Arithmetic.Coeff levels))
  { LevelSemantics.coeffField levels hvalid hinjective hinv with
    zero := zero.zero }

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

/-- Proof-local Mathlib ring laws for executable dense-polynomial operations. -/
@[expose, implicit_reducible]
noncomputable def denseCommRing {R : Type*} [CommRing R]
    [DecidableEq R] : CommRing (DensePoly R) :=
  let s := (inferInstance : Lean.Grind.CommRing (DensePoly R))
  { s with
    zero_add := Lean.Grind.AddCommMonoid.zero_add
    right_distrib := Lean.Grind.Semiring.right_distrib
    mul_zero := Lean.Grind.Semiring.mul_zero
    one_mul := Lean.Grind.Semiring.one_mul
    nsmul := nsmulRec
    zsmul := zsmulRec
    npow := npowRec
    natCast := Nat.cast
    natCast_zero := Lean.Grind.Semiring.natCast_zero
    natCast_succ n := Lean.Grind.Semiring.natCast_succ n
    intCast := Int.cast
    intCast_ofNat := Lean.Grind.Ring.intCast_natCast
    intCast_negSucc n := by
      rw [Int.negSucc_eq, Lean.Grind.Ring.intCast_neg,
        Lean.Grind.Ring.intCast_natCast_add_one,
        Lean.Grind.Semiring.natCast_succ] }

/-- Embed the canonical lower coefficient field as the constant block of the
next extension.  The construction is parameterized by top-level injectivity,
which is exactly the hypothesis available inside the recursive Trager proof. -/
@[expose]
noncomputable def lowerHom (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower)) :
    let hinjectiveLower := hinjectiveTop.tail level lower
      hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    Arithmetic.Coeff lower →+* Arithmetic.Coeff (level :: lower) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  exact
    { toFun := LevelSemantics.liftCoeff level lower
      map_zero' := by
        apply hinjectiveTop
        rw [LevelSemantics.coeffDenote_lift level lower
          (Nat.zero_lt_of_lt hvalid.1.1),
          LevelSemantics.coeffDenote_zero lower,
          LevelSemantics.coeffDenote_zero (level :: lower)]
      map_one' := by
        apply hinjectiveTop
        rw [LevelSemantics.coeffDenote_lift level lower
          (Nat.zero_lt_of_lt hvalid.1.1),
          LevelSemantics.coeffDenote_one lower hvalid.2.2,
          LevelSemantics.coeffDenote_one (level :: lower) hvalid]
      map_add' := by
        intro a b
        apply hinjectiveTop
        rw [LevelSemantics.coeffDenote_lift level lower
          (Nat.zero_lt_of_lt hvalid.1.1),
          LevelSemantics.coeffDenote_add lower,
          LevelSemantics.coeffDenote_add (level :: lower),
          LevelSemantics.coeffDenote_lift level lower
            (Nat.zero_lt_of_lt hvalid.1.1),
          LevelSemantics.coeffDenote_lift level lower
            (Nat.zero_lt_of_lt hvalid.1.1)]
      map_mul' := by
        intro a b
        apply hinjectiveTop
        rw [LevelSemantics.coeffDenote_lift level lower
          (Nat.zero_lt_of_lt hvalid.1.1),
          LevelSemantics.coeffDenote_mul lower hvalid.2.2,
          LevelSemantics.coeffDenote_mul (level :: lower) hvalid,
          LevelSemantics.coeffDenote_lift level lower
            (Nat.zero_lt_of_lt hvalid.1.1),
          LevelSemantics.coeffDenote_lift level lower
            (Nat.zero_lt_of_lt hvalid.1.1)] }

@[simp]
theorem lowerHom_apply (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (a : Arithmetic.Coeff lower) :
    let hinjectiveLower := hinjectiveTop.tail level lower
      hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    lowerHom level lower hvalid hinjectiveTop a =
      LevelSemantics.liftCoeff level lower a := by
  simp only [lowerHom]
  change LevelSemantics.liftCoeff level lower a = _
  rfl

/-- The executable representative of the newest generator denotes the
selected root.  In relative degree one the generator is already the lower
constant forced by the monic linear relation. -/
theorem topGenerator_denote (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    LevelSemantics.coeffDenote (level :: lower)
        (Factor.topGenerator level lower) = level.root.toComplex := by
  unfold Factor.topGenerator
  split
  · rename_i hdegree
    rw [LevelSemantics.coeffDenote_neg]
    change -LevelSemantics.denote (level :: lower)
        (Arithmetic.fixedCoeffs (levelsDim (level :: lower))
          (level.defining.getD 0 #[])) = _
    rw [LevelSemantics.denote_fixed]
    have hzero : 0 < level.defining.size := by
      rw [hvalid.1.2.1, hdegree]
      omega
    have hsize : (level.defining.getD 0 #[]).size = levelsDim lower := by
      rw [show level.defining.getD 0 #[] = level.defining[0] by
        simp [Array.getD, hzero]]
      exact hvalid.1.2.2 0 hzero
    rw [LevelSemantics.denote_embed level lower hvalid _ hsize]
    have hrelation := LevelSemantics.relation_sum level lower hvalid
    have hdegree' : level.degree = 1 := hdegree
    rw [hdegree', Finset.sum_range_one, pow_zero, mul_one, pow_one] at hrelation
    simp only [Array.getD] at hrelation ⊢
    linear_combination -hrelation
  · rename_i hdegree
    change LevelSemantics.denote (level :: lower)
        (Arithmetic.fixedCoeffs (levelsDim (level :: lower))
          ((Array.replicate (levelsDim lower) 0).push 1)) = _
    rw [LevelSemantics.denote_fixed]
    apply LevelSemantics.denote_generator level lower hvalid
    have := hvalid.1.1
    omega

/-- The executable newest-generator representative evaluates to any root of
the current monic relation, including the relative-degree-one encoding. -/
theorem topGenerator_evalAt (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          LevelSemantics.denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0) :
    LevelSemantics.evalAt level lower x
        (Factor.topGenerator level lower).data = x := by
  by_cases hdegree : level.degree = 1
  · have hstored := LevelSemantics.relation_sum level lower hvalid
    rw [hdegree, Finset.sum_range_one, pow_zero, mul_one, pow_one] at hrelation hstored
    have hx : level.root.toComplex = x := by
      apply sub_eq_zero.mp
      linear_combination hstored - hrelation
    calc
      LevelSemantics.evalAt level lower x
          (Factor.topGenerator level lower).data =
          LevelSemantics.evalAt level lower level.root.toComplex
            (Factor.topGenerator level lower).data := by
            unfold LevelSemantics.evalAt
            rw [hdegree]
            simp
      _ = LevelSemantics.coeffDenote (level :: lower)
          (Factor.topGenerator level lower) :=
            LevelSemantics.evalAt_root level lower _
      _ = level.root.toComplex := topGenerator_denote level lower hvalid
      _ = x := hx
  · have hdegree' : 1 < level.degree := by
      have := hvalid.1.1
      omega
    unfold Factor.topGenerator
    rw [if_neg hdegree]
    change LevelSemantics.evalAt level lower x
        (Arithmetic.fixedCoeffs (level.degree * levelsDim lower)
          ((Array.replicate (levelsDim lower) 0).push 1)) = x
    rw [LevelSemantics.evalAt_fixed,
      LevelSemantics.evalAt_generator level lower hvalid hdegree' x]

/-- The newest generator satisfies the executable monic relation over the
constant-block copy of the lower coefficient field. -/
theorem relation_eval_top (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower)) :
    let hinjectiveLower := hinjectiveTop.tail level lower
      hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    (HexPolyMathlib.toPolynomial
        (Arithmetic.Coeff.relation level lower)).eval₂
      (lowerHom level lower hvalid hinjectiveTop)
      (Factor.topGenerator level lower) = 0 := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  apply hinjectiveTop
  change LevelSemantics.coeffDenote (level :: lower)
      ((HexPolyMathlib.toPolynomial
        (Arithmetic.Coeff.relation level lower)).eval₂
          (lowerHom level lower hvalid hinjectiveTop)
          (Factor.topGenerator level lower)) =
    LevelSemantics.coeffDenote (level :: lower) 0
  rw [LevelSemantics.coeffDenote_zero]
  change (LevelSemantics.coeffHom (level :: lower) hvalid
      hinjectiveTop hinvTop)
        ((HexPolyMathlib.toPolynomial
          (Arithmetic.Coeff.relation level lower)).eval₂
            (lowerHom level lower hvalid hinjectiveTop)
            (Factor.topGenerator level lower)) = 0
  rw [Polynomial.hom_eval₂]
  have hcomp :
      (LevelSemantics.coeffHom (level :: lower) hvalid hinjectiveTop
          hinvTop).comp (lowerHom level lower hvalid hinjectiveTop) =
        LevelSemantics.coeffHom lower hvalid.2.2 hinjectiveLower hinvLower := by
    ext a
    change LevelSemantics.coeffDenote (level :: lower)
        (lowerHom level lower hvalid hinjectiveTop a) =
      LevelSemantics.coeffDenote lower a
    rw [lowerHom_apply, LevelSemantics.coeffDenote_lift level lower
      (Nat.zero_lt_of_lt hvalid.1.1)]
  have hgen :
      LevelSemantics.coeffHom (level :: lower) hvalid hinjectiveTop hinvTop
          (Factor.topGenerator level lower) = level.root.toComplex :=
    topGenerator_denote level lower hvalid
  rw [hcomp, hgen]
  rw [show (HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level lower)).eval₂
        (LevelSemantics.coeffHom lower hvalid.2.2
          hinjectiveLower hinvLower) level.root.toComplex =
      LevelSemantics.denseMap lower level.root.toComplex hvalid.2.2
        hinjectiveLower hinvLower
          (Arithmetic.Coeff.relation level lower) by rfl]
  rw [LevelSemantics.denseMap_eq_denseEval lower level.root.toComplex
    hvalid.2.2 hinjectiveLower hinvLower (level.degree + 1)
    (Arithmetic.Coeff.relation level lower) (by
      rw [LevelSemantics.relation_degree level lower hvalid]
      omega)]
  exact LevelSemantics.denseEval_relation level lower hvalid

/-- Coefficientwise semantic interpretation is a ring homomorphism once the
canonical lower tower has its transferred field structure. -/
@[expose]
noncomputable def rawPolynomialHom (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹) :
    letI : Field (Arithmetic.Coeff levels) :=
      coeffFieldPoly levels hvalid hinjective hinv
    letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
    DensePoly (Arithmetic.Coeff levels) →+* Polynomial ℂ := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffFieldPoly levels hvalid hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
  exact (Polynomial.mapRingHom
    (LevelSemantics.coeffHom levels hvalid hinjective hinv)).comp
      (HexPolyMathlib.equiv (R := Arithmetic.Coeff levels)).toRingHom

theorem rawPolynomialHom_apply (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f : DensePoly (Arithmetic.Coeff levels)) :
    letI : Field (Arithmetic.Coeff levels) :=
      coeffFieldPoly levels hvalid hinjective hinv
    letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
    rawPolynomialHom levels hvalid hinjective hinv f =
      rawPolynomial levels f := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffFieldPoly levels hvalid hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
  ext n
  rw [coeff_rawPolynomial, rawToComplex_eq_denote]
  simp [rawPolynomialHom, LevelSemantics.coeffHom,
    LevelSemantics.coeffDenote]

/-- Raw polynomial interpretation is coefficientwise mapping through the
fixed complex denotation. -/
theorem rawPolynomial_eq_map (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f : DensePoly (Arithmetic.Coeff levels)) :
    letI : Field (Arithmetic.Coeff levels) :=
      coeffFieldPoly levels hvalid hinjective hinv
    rawPolynomial levels f =
      (HexPolyMathlib.toPolynomial f).map
        (LevelSemantics.coeffHom levels hvalid hinjective hinv) := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffFieldPoly levels hvalid hinjective hinv
  rw [← rawPolynomialHom_apply levels hvalid hinjective hinv]
  rfl

/-- Injective coefficient denotation makes raw polynomial interpretation
injective coefficientwise. -/
theorem rawPolynomial_injective (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹) :
    Function.Injective (rawPolynomial levels) := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffFieldPoly levels hvalid hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
  intro f g h
  apply (HexPolyMathlib.equiv
    (R := Arithmetic.Coeff levels)).injective
  apply Polynomial.map_injective
    (LevelSemantics.coeffHom levels hvalid hinjective hinv)
    (LevelSemantics.coeffHom levels hvalid hinjective hinv).injective
  rw [← rawPolynomialHom_apply levels hvalid hinjective hinv,
    ← rawPolynomialHom_apply levels hvalid hinjective hinv] at h
  change (HexPolyMathlib.toPolynomial f).map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) =
    (HexPolyMathlib.toPolynomial g).map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) at h
  exact h

@[simp]
theorem rawPolynomial_one (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹) :
    rawPolynomial levels 1 = 1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffFieldPoly levels hvalid hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
  rw [← rawPolynomialHom_apply levels hvalid hinjective hinv]
  exact (rawPolynomialHom levels hvalid hinjective hinv).map_one

@[simp]
theorem rawPolynomial_mul (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f g : DensePoly (Arithmetic.Coeff levels)) :
    rawPolynomial levels (f * g) =
      rawPolynomial levels f * rawPolynomial levels g := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffFieldPoly levels hvalid hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
  let φ := rawPolynomialHom levels hvalid hinjective hinv
  calc
    rawPolynomial levels (f * g) = φ (f * g) :=
      (rawPolynomialHom_apply levels hvalid hinjective hinv (f * g)).symm
    _ = φ f * φ g := φ.map_mul f g
    _ = rawPolynomial levels f * rawPolynomial levels g := by
      rw [rawPolynomialHom_apply levels hvalid hinjective hinv,
        rawPolynomialHom_apply levels hvalid hinjective hinv]

/-- A constant executable polynomial denotes the corresponding constant
complex polynomial. -/
@[simp]
theorem rawPolynomial_C (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (a : Arithmetic.Coeff levels) :
    rawPolynomial levels (DensePoly.C a) =
      Polynomial.C (LevelSemantics.coeffDenote levels a) := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffFieldPoly levels hvalid hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
  rw [← rawPolynomialHom_apply levels hvalid hinjective hinv]
  simp [rawPolynomialHom, HexPolyMathlib.toPolynomial_C,
    LevelSemantics.coeffHom]

/-- Evaluation at a conjugate root, bundled using the proof-local field whose
zero agrees definitionally with the executable coefficient carrier. -/
@[expose]
noncomputable def conjugateMap (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : LevelSemantics.DenoteInjective (level :: lower))
    (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          LevelSemantics.denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0) :
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjective
        (LevelSemantics.coeffDenote_inv (level :: lower) hvalid hinjective)
    Arithmetic.Coeff (level :: lower) →+* ℂ := by
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjective
      (LevelSemantics.coeffDenote_inv (level :: lower) hvalid hinjective)
  exact
    { toFun := fun a => LevelSemantics.evalAt level lower x a.data
      map_zero' := LevelSemantics.evalAt_zero level lower hvalid x
      map_one' := LevelSemantics.evalAt_one level lower hvalid x
      map_add' := LevelSemantics.evalAt_add level lower hvalid x
      map_mul' := fun a b =>
        LevelSemantics.evalAt_mul level lower hvalid x hrelation a.data b.data }

@[simp]
theorem conjugateMap_apply (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : LevelSemantics.DenoteInjective (level :: lower))
    (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          LevelSemantics.denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0)
    (a : Arithmetic.Coeff (level :: lower)) :
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjective
        (LevelSemantics.coeffDenote_inv (level :: lower) hvalid hinjective)
    conjugateMap level lower hvalid hinjective x hrelation a =
      LevelSemantics.evalAt level lower x a.data := by
  rfl

/-- Interpret raw top-tower polynomial coefficients at one conjugate of the
newest generator. -/
@[expose]
noncomputable def conjugatePolynomial (level : Level) (lower : List Level)
    (x : ℂ) (f : Array (Array Rat)) : Polynomial ℂ :=
  f.toList.foldr
    (fun a value => Polynomial.C (LevelSemantics.evalAt level lower x a) +
      Polynomial.X * value) 0

theorem conjugate_coeff_horner (level : Level) (lower : List Level)
    (x : ℂ) : ∀ (coefficients : List (Array Rat)) (n : Nat),
      (coefficients.foldr
          (fun a value =>
            Polynomial.C (LevelSemantics.evalAt level lower x a) +
              Polynomial.X * value) 0).coeff n =
        LevelSemantics.evalAt level lower x (coefficients.getD n #[])
  | [], n => by
      simp only [List.foldr_nil, Polynomial.coeff_zero, List.getD_nil]
      unfold LevelSemantics.evalAt
      symm
      apply Finset.sum_eq_zero
      intro i hi
      have hblock : Arithmetic.block #[] i (levelsDim lower) =
          Arithmetic.fixedCoeffs (levelsDim lower) #[] := by
        apply Array.ext
        · simp [Arithmetic.block, Arithmetic.fixedCoeffs]
        · intro j hj₁ hj₂
          simp [Arithmetic.block, Arithmetic.fixedCoeffs, Array.getD]
      rw [hblock, LevelSemantics.denote_zero]
      simp
  | _ :: _, 0 => by simp
  | _ :: coefficients, n + 1 => by
      simpa using conjugate_coeff_horner level lower x coefficients n

theorem coeff_conjugatePolynomial (level : Level) (lower : List Level)
    (x : ℂ) (f : Array (Array Rat)) (n : Nat) :
    (conjugatePolynomial level lower x f).coeff n =
      LevelSemantics.evalAt level lower x (f.getD n #[]) := by
  rw [conjugatePolynomial, conjugate_coeff_horner]
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_toList]

/-- Conjugate coefficient interpretation is coefficientwise mapping through
the corresponding ring homomorphism. -/
theorem conjugatePolynomial_eq_map (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : LevelSemantics.DenoteInjective (level :: lower))
    (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          LevelSemantics.denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0)
    (f : Array (Array Rat)) :
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjective
        (LevelSemantics.coeffDenote_inv (level :: lower) hvalid hinjective)
    conjugatePolynomial level lower x f =
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) f)).map
          (conjugateMap level lower hvalid hinjective x hrelation) := by
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjective
      (LevelSemantics.coeffDenote_inv (level :: lower) hvalid hinjective)
  ext n
  rw [coeff_conjugatePolynomial, Polynomial.coeff_map,
    HexPolyMathlib.coeff_toPolynomial, Factor.rawPoly,
    DensePoly.coeff_ofCoeffs, conjugateMap_apply]
  by_cases hn : n < f.size
  · have hleft : f.getD n #[] = f[n] := by
      simp [Array.getD, hn]
    have hnmap : n < (f.map
        (Arithmetic.Coeff.ofData (level :: lower))).size := by simpa
    have hright : (f.map
        (Arithmetic.Coeff.ofData (level :: lower))).getD n 0 =
          Arithmetic.Coeff.ofData (level :: lower) f[n] := by
      rw [Array.getD, dif_pos hnmap]
      simp
    rw [hleft]
    calc
      LevelSemantics.evalAt level lower x f[n] =
          LevelSemantics.evalAt level lower x
            (Arithmetic.fixedCoeffs
              (level.degree * levelsDim lower) f[n]) :=
        (LevelSemantics.evalAt_fixed level lower x f[n]).symm
      _ = LevelSemantics.evalAt level lower x
            ((f.map (Arithmetic.Coeff.ofData
              (level :: lower))).getD n 0).data :=
        congrArg (LevelSemantics.evalAt level lower x)
          (congrArg Arithmetic.Coeff.data hright).symm
  · have hnmap : ¬n < (f.map
        (Arithmetic.Coeff.ofData (level :: lower))).size := by simpa using hn
    have hleft : f.getD n #[] = #[] := by
      simp [Array.getD, hn]
    have hright : (f.map
        (Arithmetic.Coeff.ofData (level :: lower))).getD n 0 = 0 := by
      rw [Array.getD, dif_neg hnmap]
    rw [hleft]
    calc
      LevelSemantics.evalAt level lower x #[] =
          LevelSemantics.evalAt level lower x
            (Arithmetic.fixedCoeffs
              (level.degree * levelsDim lower) #[]) :=
        (LevelSemantics.evalAt_fixed level lower x #[]).symm
      _ = LevelSemantics.evalAt level lower x
            ((f.map (Arithmetic.Coeff.ofData
              (level :: lower))).getD n 0).data :=
        congrArg (LevelSemantics.evalAt level lower x)
          (congrArg Arithmetic.Coeff.data hright).symm

/-- The runtime-indexed derivative has the ordinary formal derivative after
coefficient denotation. -/
theorem rawPolynomial_derivative (levels : List Level)
    (f : DensePoly (Arithmetic.Coeff levels)) :
    rawPolynomial levels (derivative levels f) =
      Polynomial.derivative (rawPolynomial levels f) := by
  ext n
  rw [coeff_rawPolynomial, Polynomial.coeff_derivative,
    coeff_rawPolynomial, rawToComplex_eq_denote,
    rawToComplex_eq_denote]
  by_cases hn : n < f.size - 1
  · simp [derivative, DensePoly.coeff_ofCoeffs, Array.getD, hn,
      Arithmetic.Coeff.ofData, LevelSemantics.denote_fixed]
    simpa [Nat.cast_add, Nat.cast_one, mul_comm] using
      LevelSemantics.denote_smul levels ((n + 1 : Nat) : Rat)
        (f.coeff (n + 1)).data
  · have hdegree : f.size ≤ n + 1 := by omega
    rw [DensePoly.coeff_eq_zero_of_size_le f hdegree]
    simp [derivative, DensePoly.coeff_ofCoeffs, Array.getD, hn]
    change LevelSemantics.coeffDenote levels 0 =
      LevelSemantics.coeffDenote levels 0 * ((n : ℂ) + 1)
    rw [LevelSemantics.coeffDenote_zero]
    simp

/-- Under the transferred coefficient field, the custom runtime-indexed
derivative is the ordinary executable dense derivative. -/
theorem derivative_eq (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f : DensePoly (Arithmetic.Coeff levels)) :
    letI : Field (Arithmetic.Coeff levels) :=
      coeffFieldPoly levels hvalid hinjective hinv
    derivative levels f = DensePoly.derivative f := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffFieldPoly levels hvalid hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
  apply rawPolynomial_injective levels hvalid hinjective hinv
  rw [rawPolynomial_derivative]
  have hmap (g : DensePoly (Arithmetic.Coeff levels)) :
      rawPolynomial levels g =
        (HexPolyMathlib.toPolynomial g).map
          (LevelSemantics.coeffHom levels hvalid hinjective hinv) := by
    rw [← rawPolynomialHom_apply levels hvalid hinjective hinv]
    rfl
  rw [hmap f, hmap (DensePoly.derivative f),
    Polynomial.derivative_map, HexPolyMathlib.toPolynomial_derivative]

/-- The executable gcd-based squarefreeness test is exactly ordinary
polynomial squarefreeness after semantic coefficient interpretation. -/
theorem isSquarefree_iff (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f : Array (Array Rat)) :
    Norm.isSquarefree levels f ↔
      Squarefree (rawPolynomial levels (Factor.rawPoly levels f)) := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffFieldPoly levels hvalid hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
  let p := Factor.rawPoly levels f
  let P := HexPolyMathlib.toPolynomial p
  let d := DensePoly.derivative p
  let g := DensePoly.gcd p d
  let G := EuclideanDomain.gcd P P.derivative
  have hderivative : derivative levels p = d :=
    derivative_eq levels hvalid hinjective hinv p
  have hassociated : Associated (HexPolyMathlib.toPolynomial g) G := by
    simpa only [g, G, P, d, HexPolyMathlib.toPolynomial_derivative] using
      HexPolyMathlib.toPolynomial_gcd_associated p d
  have hboolean : Norm.isSquarefree levels f ↔ P.Separable := by
    change ((!p.isZero &&
      decide ((DensePoly.gcd p (derivative levels p)).size ≤ 1)) = true) ↔ _
    rw [hderivative]
    change ((!p.isZero && decide (g.size ≤ 1)) = true) ↔ _
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    constructor
    · rintro ⟨hpzero, hgdegree⟩
      have hpne : P ≠ 0 := by
        intro hzero
        have hpDense : p ≠ 0 := by
          intro hpEq
          have hsize := (DensePoly.isZero_eq_false_iff p).mp hpzero
          rw [hpEq] at hsize
          simp at hsize
        apply hpDense
        apply (HexPolyMathlib.equiv
          (R := Arithmetic.Coeff levels)).injective
        change HexPolyMathlib.toPolynomial p =
          HexPolyMathlib.toPolynomial (0 : DensePoly (Arithmetic.Coeff levels))
        rw [HexPolyMathlib.toPolynomial_zero]
        exact hzero
      have hGne : G ≠ 0 := by
        intro hzero
        exact hpne (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
      have hgne : HexPolyMathlib.toPolynomial g ≠ 0 :=
        fun hzero => hGne (hassociated.eq_zero_iff.mp hzero)
      have hgunit : IsUnit (HexPolyMathlib.toPolynomial g) := by
        apply Polynomial.isUnit_iff_degree_eq_zero.mpr
        rw [Polynomial.degree_eq_natDegree hgne,
          (HexPolyZMathlib.size_le_one_iff_natDegree_eq_zero g).mp hgdegree]
        rfl
      rw [Polynomial.separable_def, ← EuclideanDomain.gcd_isUnit_iff]
      exact hassociated.isUnit_iff.mp hgunit
    · intro hseparable
      have hpne : P ≠ 0 := hseparable.ne_zero
      have hpDense : p ≠ 0 := by
        intro hzero
        apply hpne
        have hmapZero := congrArg HexPolyMathlib.toPolynomial hzero
        simpa only [P, HexPolyMathlib.toPolynomial_zero] using hmapZero
      have hpzero : p.isZero = false := by
        rw [DensePoly.isZero_eq_false_iff]
        by_contra hsize
        apply hpDense
        exact (DensePoly.size_eq_zero_iff p).mp
          (Nat.eq_zero_of_not_pos hsize)
      have hGunit : IsUnit G := by
        rw [EuclideanDomain.gcd_isUnit_iff]
        exact hseparable
      have hgunit : IsUnit (HexPolyMathlib.toPolynomial g) :=
        hassociated.isUnit_iff.mpr hGunit
      refine ⟨hpzero, ?_⟩
      rw [HexPolyZMathlib.size_le_one_iff_natDegree_eq_zero]
      exact Polynomial.natDegree_eq_zero_of_isUnit hgunit
  have hsemantic :
      Squarefree (rawPolynomial levels p) ↔ P.Separable := by
    rw [← PerfectField.separable_iff_squarefree]
    have hmap : rawPolynomial levels p =
        P.map (LevelSemantics.coeffHom levels hvalid hinjective hinv) := by
      rw [← rawPolynomialHom_apply levels hvalid hinjective hinv]
      rfl
    rw [hmap]
    change IsCoprime
        (P.map (LevelSemantics.coeffHom levels hvalid hinjective hinv))
        (Polynomial.derivative
          (P.map (LevelSemantics.coeffHom levels hvalid hinjective hinv))) ↔
      IsCoprime P P.derivative
    rw [Polynomial.derivative_map]
    exact Polynomial.isCoprime_map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv)
  exact hboolean.trans hsemantic.symm

theorem outer_coeff_horner (levels : List Level) :
    ∀ (coefficients : List (DensePoly (Arithmetic.Coeff levels)))
      (n : Nat),
      (coefficients.foldr
          (fun a value => Polynomial.C (rawPolynomial levels a) +
            Polynomial.X * value) 0).coeff n =
        rawPolynomial levels (coefficients.getD n 0)
  | [], n => by simp [rawPolynomial_zero]
  | _ :: _, 0 => by simp
  | _ :: coefficients, n + 1 => by
      simpa using outer_coeff_horner levels coefficients n

theorem dense_array_toList_getD (levels : List Level)
    (coefficients : Array (DensePoly (Arithmetic.Coeff levels))) (n : Nat) :
    coefficients.toList.getD n 0 = coefficients.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_toList]

theorem coeff_rawOuter (levels : List Level)
    (f : DensePoly (DensePoly (Arithmetic.Coeff levels))) (n : Nat) :
    (rawOuter levels f).coeff n = rawPolynomial levels (f.coeff n) := by
  rw [rawOuter, ← Array.foldr_toList, outer_coeff_horner,
    dense_array_toList_getD]
  rfl

theorem rawOuter_eq_map (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f : DensePoly (DensePoly (Arithmetic.Coeff levels))) :
    letI : Field (Arithmetic.Coeff levels) :=
      coeffFieldPoly levels hvalid hinjective hinv
    letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
    rawOuter levels f = (HexPolyMathlib.toPolynomial f).map
      (rawPolynomialHom levels hvalid hinjective hinv) := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffFieldPoly levels hvalid hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff levels)) := denseCommRing
  ext n
  rw [coeff_rawOuter, Polynomial.coeff_map,
    HexPolyMathlib.coeff_toPolynomial,
    rawPolynomialHom_apply levels hvalid hinjective hinv]

/-- Specialize a polynomial in the outer elimination variable at the newest
generator, while embedding its `lower[X]` coefficients into
`(level :: lower)[X]`. -/
@[expose]
noncomputable def outerEvalHom (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower)) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
    Polynomial (DensePoly (Arithmetic.Coeff lower)) →+*
      Polynomial (Arithmetic.Coeff (level :: lower)) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let coefficientHom : DensePoly (Arithmetic.Coeff lower) →+*
      Polynomial (Arithmetic.Coeff (level :: lower)) :=
    (Polynomial.mapRingHom (lowerHom level lower hvalid hinjectiveTop)).comp
      (HexPolyMathlib.equiv
        (R := Arithmetic.Coeff lower)).toRingHom
  exact Polynomial.eval₂RingHom coefficientHom
    (Polynomial.C (Factor.topGenerator level lower))

/-- Evaluate an outer polynomial in the newest generator while embedding its
`lower[X]` coefficients into `(level :: lower)[X]`. -/
@[expose]
noncomputable def outerEval (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (g : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
    Polynomial (Arithmetic.Coeff (level :: lower)) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let coefficientHom : DensePoly (Arithmetic.Coeff lower) →+*
      Polynomial (Arithmetic.Coeff (level :: lower)) :=
    (Polynomial.mapRingHom (lowerHom level lower hvalid hinjectiveTop)).comp
      (HexPolyMathlib.equiv
        (R := Arithmetic.Coeff lower)).toRingHom
  exact (HexPolyMathlib.toPolynomial g).eval₂ coefficientHom
    (Polynomial.C (Factor.topGenerator level lower))

theorem outerEvalHom_apply (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (g : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
    outerEvalHom level lower hvalid hinjectiveTop
        (HexPolyMathlib.toPolynomial g) =
      outerEval level lower hvalid hinjectiveTop g := by
  rfl

/-- Mapping `outerEval` into the fixed complex embedding is specialization of
the semantic outer polynomial at the selected root. -/
theorem outerEval_map (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (g : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
    (outerEval level lower hvalid hinjectiveTop g).map
        (LevelSemantics.coeffHom (level :: lower) hvalid hinjectiveTop
          hinvTop) =
      (rawOuter lower g).eval (Polynomial.C level.root.toComplex) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let topHom := LevelSemantics.coeffHom (level :: lower) hvalid
    hinjectiveTop hinvTop
  let lowerPolyHom : DensePoly (Arithmetic.Coeff lower) →+*
      Polynomial (Arithmetic.Coeff (level :: lower)) :=
    (Polynomial.mapRingHom (lowerHom level lower hvalid hinjectiveTop)).comp
      (HexPolyMathlib.equiv
        (R := Arithmetic.Coeff lower)).toRingHom
  have hcomp : (Polynomial.mapRingHom topHom).comp lowerPolyHom =
      rawPolynomialHom lower hvalid.2.2 hinjectiveLower hinvLower := by
    apply RingHom.ext
    intro a
    apply Polynomial.ext
    intro n
    change ((lowerPolyHom a).map topHom).coeff n =
      ((rawPolynomialHom lower hvalid.2.2 hinjectiveLower hinvLower) a).coeff n
    rw [Polynomial.coeff_map,
      rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower hinvLower,
      coeff_rawPolynomial]
    dsimp only [lowerPolyHom]
    rw [RingHom.comp_apply]
    change topHom
        (((HexPolyMathlib.toPolynomial a).map
          (lowerHom level lower hvalid hinjectiveTop)).coeff n) = _
    rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial]
    change LevelSemantics.coeffDenote (level :: lower)
        (lowerHom level lower hvalid hinjectiveTop (a.coeff n)) =
      rawToComplex lower (a.coeff n).data
    rw [lowerHom_apply, LevelSemantics.coeffDenote_lift level lower
      (Nat.zero_lt_of_lt hvalid.1.1), rawToComplex_eq_denote]
    rfl
  have hgen : topHom (Factor.topGenerator level lower) =
      level.root.toComplex := topGenerator_denote level lower hvalid
  have hC : (Polynomial.mapRingHom topHom)
      (Polynomial.C (Factor.topGenerator level lower)) =
        Polynomial.C (topHom (Factor.topGenerator level lower)) := by
    change (Polynomial.C (Factor.topGenerator level lower)).map topHom = _
    rw [Polynomial.map_C]
  change ((HexPolyMathlib.toPolynomial g).eval₂ lowerPolyHom
      (Polynomial.C (Factor.topGenerator level lower))).map topHom = _
  change (Polynomial.mapRingHom topHom)
      ((HexPolyMathlib.toPolynomial g).eval₂ lowerPolyHom
        (Polynomial.C (Factor.topGenerator level lower))) = _
  rw [Polynomial.hom_eval₂]
  rw [hC, hcomp, hgen]
  rw [← Polynomial.eval_map]
  rw [← rawOuter_eq_map lower hvalid.2.2 hinjectiveLower hinvLower]

/-- After interpreting the lower tower, a lifted top-level coefficient
specializes at a conjugate root to the corresponding constant polynomial. -/
theorem eval_liftCoefficient (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : LevelSemantics.DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      LevelSemantics.coeffDenote lower a⁻¹ =
        (LevelSemantics.coeffDenote lower a)⁻¹)
    (a : Array Rat) (x : ℂ) :
    (rawOuter lower (liftCoefficient level lower a)).eval
        (Polynomial.C x) =
      Polynomial.C (LevelSemantics.evalAt level lower x a) := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let lifted := liftCoefficient level lower a
  have hsize : lifted.size ≤ level.degree := by
    exact (DensePoly.size_ofCoeffs_le _).trans (by simp [lifted,
      liftCoefficient])
  have hdegree : (HexPolyMathlib.toPolynomial lifted).natDegree <
      level.degree := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    by_cases hzero : lifted.size = 0
    · have hlifted : lifted = 0 := (DensePoly.size_eq_zero_iff lifted).mp hzero
      simpa [hlifted] using Nat.zero_lt_of_lt hvalid.1.1
    · rw [DensePoly.degree?_eq_some_of_pos_size lifted (Nat.pos_of_ne_zero hzero),
        Option.getD_some]
      omega
  rw [rawOuter_eq_map lower hvalid.2.2 hinjective hinv,
    Polynomial.eval_map,
    Polynomial.eval₂_eq_sum_range'
      (rawPolynomialHom lower hvalid.2.2 hinjective hinv) hdegree]
  rw [LevelSemantics.evalAt]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < level.degree := Finset.mem_range.mp hj
  have hcoeff : lifted.coeff j = DensePoly.C
      (Arithmetic.Coeff.ofData lower
        (Arithmetic.block a j (levelsDim lower))) := by
    simp [lifted, liftCoefficient, Array.getD, hj']
  rw [HexPolyMathlib.coeff_toPolynomial, hcoeff,
    rawPolynomialHom_apply lower hvalid.2.2 hinjective hinv,
    rawPolynomial_C lower hvalid.2.2 hinjective hinv]
  simp [LevelSemantics.coeffDenote, Arithmetic.Coeff.ofData,
    LevelSemantics.denote_fixed]

/-- The linear substitution base specializes to `X - c·x` at the chosen
conjugate `x`. -/
theorem eval_shiftBase (lower : List Level)
    (hvalid : LevelsValid lower)
    (hinjective : LevelSemantics.DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      LevelSemantics.coeffDenote lower a⁻¹ =
        (LevelSemantics.coeffDenote lower a)⁻¹)
    (c : Int) (x : ℂ) :
    let base : DensePoly (DensePoly (Arithmetic.Coeff lower)) :=
      DensePoly.ofCoeffs #[DensePoly.monomial 1 1,
        DensePoly.C (Arithmetic.Coeff.ofData lower #[(-(c : Rat))])]
    (rawOuter lower base).eval (Polynomial.C x) =
      Polynomial.X - Polynomial.C ((c : ℂ) * x) := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let base : DensePoly (DensePoly (Arithmetic.Coeff lower)) :=
    DensePoly.ofCoeffs #[DensePoly.monomial 1 1,
      DensePoly.C (Arithmetic.Coeff.ofData lower #[(-(c : Rat))])]
  change (rawOuter lower base).eval (Polynomial.C x) =
    Polynomial.X - Polynomial.C ((c : ℂ) * x)
  have hbase : HexPolyMathlib.toPolynomial base =
      Polynomial.C (DensePoly.monomial 1 1) +
        Polynomial.X * Polynomial.C
          (DensePoly.C (Arithmetic.Coeff.ofData lower
            #[(-(c : Rat))])) := by
    ext n
    rcases n with _ | n
    · simp [base, Array.getD]
    · rcases n with _ | n
      · simp [base, Array.getD]
      · simp [base, Array.getD]
  have hone : LevelSemantics.denote lower
      (1 : Arithmetic.Coeff lower).data = 1 :=
    LevelSemantics.coeffDenote_one lower hvalid
  rw [rawOuter_eq_map lower hvalid hinjective hinv, hbase]
  simp [rawPolynomialHom, HexPolyMathlib.toPolynomial_monomial,
    HexPolyMathlib.toPolynomial_C, LevelSemantics.coeffHom,
    LevelSemantics.coeffDenote, Arithmetic.Coeff.ofData,
    LevelSemantics.denote_fixed,
    LevelSemantics.denote_rat lower hvalid]
  rw [hone]
  rw [Polynomial.monomial_one_one_eq_X]
  push_cast
  ring

/-- Specializing the shifted bivariate input at a conjugate gives ordinary
polynomial composition by `X - c·x`. -/
theorem eval_shiftedOuter (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : LevelSemantics.DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      LevelSemantics.coeffDenote lower a⁻¹ =
        (LevelSemantics.coeffDenote lower a)⁻¹)
    (f : Array (Array Rat)) (c : Int) (x : ℂ) :
    (rawOuter lower (shiftedOuter level lower f c)).eval
        (Polynomial.C x) =
      (conjugatePolynomial level lower x f).comp
        (Polynomial.X - Polynomial.C ((c : ℂ) * x)) := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let ψ (g : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
      Polynomial ℂ := (rawOuter lower g).eval (Polynomial.C x)
  let q := Polynomial.X - Polynomial.C ((c : ℂ) * x)
  let base : DensePoly (DensePoly (Arithmetic.Coeff lower)) :=
    DensePoly.ofCoeffs #[DensePoly.monomial 1 1,
      DensePoly.C (Arithmetic.Coeff.ofData lower #[(-(c : Rat))])]
  have hlift (a : Array Rat) :
      ψ (liftCoefficient level lower a) =
        Polynomial.C (LevelSemantics.evalAt level lower x a) := by
    exact eval_liftCoefficient level lower hvalid hinjective hinv a x
  have hbase : ψ base = q := by
    exact eval_shiftBase lower hvalid.2.2 hinjective hinv c x
  have hzero : ψ 0 = 0 := by
    simp only [ψ]
    rw [rawOuter_eq_map lower hvalid.2.2 hinjective hinv]
    simp
  have hone : ψ 1 = 1 := by
    simp only [ψ]
    rw [rawOuter_eq_map lower hvalid.2.2 hinjective hinv]
    simp
  have hadd (u v : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
      ψ (u + v) = ψ u + ψ v := by
    simp only [ψ]
    rw [rawOuter_eq_map lower hvalid.2.2 hinjective hinv,
      rawOuter_eq_map lower hvalid.2.2 hinjective hinv,
      rawOuter_eq_map lower hvalid.2.2 hinjective hinv,
      HexPolyMathlib.toPolynomial_add, Polynomial.map_add,
      Polynomial.eval_add]
  have hmul (u v : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
      ψ (u * v) = ψ u * ψ v := by
    simp only [ψ]
    rw [rawOuter_eq_map lower hvalid.2.2 hinjective hinv,
      rawOuter_eq_map lower hvalid.2.2 hinjective hinv,
      rawOuter_eq_map lower hvalid.2.2 hinjective hinv,
      HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul,
      Polynomial.eval_mul]
  have hfold : ∀ (items : List (Array Rat))
      (state : DensePoly (DensePoly (Arithmetic.Coeff lower)) ×
        DensePoly (DensePoly (Arithmetic.Coeff lower))),
      ψ ((items.foldl (fun state coefficient =>
          (state.1 + liftCoefficient level lower coefficient * state.2,
            state.2 * base)) state).1) =
        ψ state.1 + ψ state.2 *
          ((items.foldr
            (fun a value =>
              Polynomial.C (LevelSemantics.evalAt level lower x a) +
                Polynomial.X * value) 0).comp q) := by
    intro items
    induction items with
    | nil =>
        intro state
        simp [hzero]
    | cons a items ih =>
        intro state
        simp only [List.foldl_cons, List.foldr_cons]
        rw [ih]
        simp only [Prod.fst, Prod.snd]
        rw [hadd, hmul, hmul, hlift, hbase]
        simp only [
          Polynomial.add_comp, Polynomial.C_comp,
          Polynomial.mul_comp, Polynomial.X_comp]
        ring
  change ψ ((f.foldl (fun state coefficient =>
      (state.1 + liftCoefficient level lower coefficient * state.2,
        state.2 * base)) (0, 1)).1) = _
  rw [← Array.foldl_toList]
  simpa [conjugatePolynomial, q, hzero, hone] using
    hfold f.toList (0, 1)

/-- The executable outer defining polynomial is the constant-coefficient lift
of the ordinary lower-field relation. -/
theorem rawOuter_defining (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : LevelSemantics.DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      LevelSemantics.coeffDenote lower a⁻¹ =
        (LevelSemantics.coeffDenote lower a)⁻¹) :
    rawOuter lower (definingOuter level lower) =
      (rawPolynomial lower
        (Arithmetic.Coeff.relation level lower)).map Polynomial.C := by
  have hcoeff (n : Nat) (hn : n ≤ level.degree) :
      (definingOuter level lower).coeff n =
        DensePoly.C ((Arithmetic.Coeff.relation level lower).coeff n) := by
    by_cases hlt : n < level.degree
    · have hle : n ≤ level.degree := Nat.le_of_lt hlt
      simp [definingOuter, Arithmetic.Coeff.relation, Array.getD, hlt,
        hle]
    · have heq : n = level.degree := by omega
      subst n
      simp [definingOuter, Arithmetic.Coeff.relation, Array.getD]
  have houterZero (n : Nat) (hn : ¬n ≤ level.degree) :
      (definingOuter level lower).coeff n = 0 := by
    simp [definingOuter, Array.getD, hn]
    change (DensePoly.zero : DensePoly (Arithmetic.Coeff lower)) =
      DensePoly.zero
    rfl
  have hrelationZero (n : Nat) (hn : ¬n ≤ level.degree) :
      (Arithmetic.Coeff.relation level lower).coeff n = 0 := by
    simp [Arithmetic.Coeff.relation, Array.getD, hn]
    change Arithmetic.Coeff.ofData lower #[] =
      Arithmetic.Coeff.ofData lower #[]
    rfl
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjective hinv
  letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ level.degree
  · rw [coeff_rawOuter, hcoeff n hn, Polynomial.coeff_map,
      coeff_rawPolynomial,
      rawPolynomial_C lower hvalid.2.2 hinjective hinv,
      rawToComplex_eq_denote]
    rfl
  · rw [coeff_rawOuter, houterZero n hn, rawPolynomial_zero,
      Polynomial.coeff_map, coeff_rawPolynomial, hrelationZero n hn,
      rawToComplex_eq_denote]
    change (0 : Polynomial ℂ) =
      Polynomial.C (LevelSemantics.coeffDenote lower 0)
    rw [LevelSemantics.coeffDenote_zero]
    simp

/-- The outer defining polynomial vanishes when specialized at the executable
top generator. -/
theorem outerEval_defining (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower)) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
    outerEval level lower hvalid hinjectiveTop
      (definingOuter level lower) = 0 := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let topHom := LevelSemantics.coeffHom (level :: lower) hvalid
    hinjectiveTop hinvTop
  apply Polynomial.map_injective topHom topHom.injective
  rw [outerEval_map level lower hvalid hinjectiveTop, Polynomial.map_zero]
  rw [rawOuter_defining level lower hvalid hinjectiveLower hinvLower]
  have hrelation :
      (rawPolynomial lower
        (Arithmetic.Coeff.relation level lower)).eval
          level.root.toComplex = 0 := by
    have hraw : rawPolynomial lower
        (Arithmetic.Coeff.relation level lower) =
      (HexPolyMathlib.toPolynomial
        (Arithmetic.Coeff.relation level lower)).map
          (LevelSemantics.coeffHom lower hvalid.2.2
            hinjectiveLower hinvLower) := by
      rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower hinvLower]
      rfl
    rw [hraw, Polynomial.eval_map]
    change LevelSemantics.denseMap lower level.root.toComplex hvalid.2.2
      hinjectiveLower hinvLower
        (Arithmetic.Coeff.relation level lower) = 0
    rw [LevelSemantics.denseMap_eq_denseEval lower level.root.toComplex
      hvalid.2.2 hinjectiveLower hinvLower (level.degree + 1)
      (Arithmetic.Coeff.relation level lower) (by
        rw [LevelSemantics.relation_degree level lower hvalid]
        omega)]
    exact LevelSemantics.denseEval_relation level lower hvalid
  rw [Polynomial.eval_map]
  simpa [hrelation]

theorem rawPoly_polyCoords (levels : List Level)
    (f : DensePoly (Arithmetic.Coeff levels)) :
    Factor.rawPoly levels (Factor.polyCoords f) = f := by
  rw [Factor.rawPoly, Factor.polyCoords, Array.map_map]
  have harray : f.toArray.map
      (Arithmetic.Coeff.ofData levels ∘ Arithmetic.Coeff.data) =
        f.toArray := by
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp [Function.comp_def]
  rw [harray, DensePoly.ofCoeffs_toArray]

/-- Shifting at the executable newest generator specializes at every
conjugate to the corresponding scalar affine shift. -/
theorem conjugatePolynomial_shiftTop (level : Level)
    (lower : List Level) (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          LevelSemantics.denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0)
    (f : Array (Array Rat)) (c : Int) :
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    conjugatePolynomial level lower x (Factor.shiftTop level lower f c) =
      (conjugatePolynomial level lower x f).comp
        (Polynomial.X - Polynomial.C ((c : ℂ) * x)) := by
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let conjugate := conjugateMap level lower hvalid hinjectiveTop x hrelation
  have hsource : conjugatePolynomial level lower x f =
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) f)).map conjugate := by
    simpa [conjugate] using conjugatePolynomial_eq_map level lower hvalid
      hinjectiveTop x hrelation f
  have htarget : conjugatePolynomial level lower x
      (Factor.shiftTop level lower f c) =
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly (level :: lower)
            (Factor.shiftTop level lower f c))).map conjugate := by
    simpa [conjugate] using conjugatePolynomial_eq_map level lower hvalid
      hinjectiveTop x hrelation (Factor.shiftTop level lower f c)
  let delta := Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)] *
    Factor.topGenerator level lower
  let substitution : DensePoly (Arithmetic.Coeff (level :: lower)) :=
    DensePoly.ofCoeffs #[-delta, 1]
  have hshift : Factor.rawPoly (level :: lower)
      (Factor.shiftTop level lower f c) =
        DensePoly.compose (Factor.rawPoly (level :: lower) f) substitution := by
    rw [Factor.shiftTop, rawPoly_polyCoords]
  have hratCoeff : Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)] =
      ((c : Rat) : Arithmetic.Coeff (level :: lower)) := by
    apply hinjectiveTop
    let topHom := LevelSemantics.coeffHom (level :: lower) hvalid
      hinjectiveTop hinvTop
    change topHom (Arithmetic.Coeff.ofData
      (level :: lower) #[(c : Rat)]) = topHom
        ((c : Rat) : Arithmetic.Coeff (level :: lower))
    have hleft : topHom (Arithmetic.Coeff.ofData
        (level :: lower) #[(c : Rat)]) = ((c : Rat) : ℂ) := by
      change LevelSemantics.denote (level :: lower)
        (Arithmetic.fixedCoeffs (levelsDim (level :: lower)) #[(c : Rat)]) = _
      rw [LevelSemantics.denote_fixed,
        LevelSemantics.denote_rat (level :: lower) hvalid]
    rw [hleft, map_ratCast topHom]
  have hrat : conjugate
      (Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)]) = (c : ℂ) := by
    rw [hratCoeff, map_ratCast conjugate]
    norm_num
  have hdelta : conjugate delta = (c : ℂ) * x := by
    dsimp only [delta]
    rw [conjugate.map_mul, hrat]
    change (c : ℂ) * LevelSemantics.evalAt level lower x
      (Factor.topGenerator level lower).data = _
    rw [topGenerator_evalAt level lower hvalid x hrelation]
  have hsubRaw : HexPolyMathlib.toPolynomial substitution =
      Polynomial.X - Polynomial.C delta := by
    ext n
    rw [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_sub]
    rcases n with _ | n
    · simp [substitution, DensePoly.coeff_ofCoeffs, Array.getD]
    · rcases n with _ | n
      · simp [substitution, DensePoly.coeff_ofCoeffs, Array.getD]
      · simp [substitution, DensePoly.coeff_ofCoeffs, Array.getD,
          Polynomial.coeff_X_of_ne_one (R := Arithmetic.Coeff
            (level :: lower)) (show n + 1 + 1 ≠ 1 by omega)]
        rfl
  have hsub : (HexPolyMathlib.toPolynomial substitution).map conjugate =
      Polynomial.X - Polynomial.C ((c : ℂ) * x) := by
    rw [hsubRaw, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      hdelta]
  rw [htarget, hshift, HexPolyMathlib.toPolynomial_compose,
    Polynomial.map_comp, hsub, ← hsource]

/-- Specializing the shifted outer presentation at the executable generator
is exactly the current-level shifted polynomial. -/
theorem outerEval_shifted (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat)) (c : Int) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
    outerEval level lower hvalid hinjectiveTop
        (shiftedOuter level lower f c) =
      HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower)
          (Factor.shiftTop level lower f c)) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let topHom := LevelSemantics.coeffHom (level :: lower) hvalid
    hinjectiveTop hinvTop
  have hrelation :
    (∑ j ∈ Finset.range level.degree,
        LevelSemantics.denote lower (level.defining.getD j #[]) *
          level.root.toComplex ^ j) +
      level.root.toComplex ^ level.degree = 0 :=
    LevelSemantics.relation_sum level lower hvalid
  let conjugate := conjugateMap level lower hvalid hinjectiveTop
    level.root.toComplex hrelation
  have hconjugate : conjugate = topHom := by
    apply RingHom.ext
    intro a
    change LevelSemantics.evalAt level lower level.root.toComplex a.data =
      LevelSemantics.coeffDenote (level :: lower) a
    rw [LevelSemantics.evalAt_root]
    rfl
  have hconjugatePolynomial :
      conjugatePolynomial level lower level.root.toComplex f =
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly (level :: lower) f)).map topHom := by
    have h := conjugatePolynomial_eq_map level lower hvalid hinjectiveTop
      level.root.toComplex hrelation f
    simpa [conjugate, hconjugate] using h
  let delta := Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)] *
    Factor.topGenerator level lower
  let substitution : DensePoly (Arithmetic.Coeff (level :: lower)) :=
    DensePoly.ofCoeffs #[-delta, 1]
  have hshift : Factor.rawPoly (level :: lower)
      (Factor.shiftTop level lower f c) =
        DensePoly.compose (Factor.rawPoly (level :: lower) f) substitution := by
    rw [Factor.shiftTop, rawPoly_polyCoords]
  have hrat : topHom
      (Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)]) = (c : ℂ) := by
    change LevelSemantics.denote (level :: lower)
      (Arithmetic.fixedCoeffs (levelsDim (level :: lower)) #[(c : Rat)]) = _
    rw [LevelSemantics.denote_fixed,
      LevelSemantics.denote_rat (level :: lower) hvalid]
    rfl
  have hdelta : topHom delta = (c : ℂ) * level.root.toComplex := by
    dsimp only [delta]
    change LevelSemantics.coeffDenote (level :: lower)
      (Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)] *
        Factor.topGenerator level lower) = _
    rw [LevelSemantics.coeffDenote_mul (level :: lower) hvalid]
    change topHom (Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)]) *
      LevelSemantics.coeffDenote (level :: lower)
        (Factor.topGenerator level lower) = _
    rw [hrat, topGenerator_denote level lower hvalid]
  have hsubRaw : HexPolyMathlib.toPolynomial substitution =
      Polynomial.X - Polynomial.C delta := by
    ext n
    rw [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_sub]
    rcases n with _ | n
    · simp [substitution, DensePoly.coeff_ofCoeffs, Array.getD]
    · rcases n with _ | n
      · simp [substitution, DensePoly.coeff_ofCoeffs, Array.getD]
      · simp [substitution, DensePoly.coeff_ofCoeffs, Array.getD,
          Polynomial.coeff_X_of_ne_one (R := Arithmetic.Coeff
            (level :: lower)) (show n + 1 + 1 ≠ 1 by omega)]
        rfl
  have hsub : (HexPolyMathlib.toPolynomial substitution).map topHom =
      Polynomial.X - Polynomial.C ((c : ℂ) * level.root.toComplex) := by
    rw [hsubRaw, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      hdelta]
  apply Polynomial.map_injective topHom topHom.injective
  rw [outerEval_map level lower hvalid hinjectiveTop]
  rw [eval_shiftedOuter level lower hvalid hinjectiveLower hinvLower]
  rw [hshift, HexPolyMathlib.toPolynomial_compose, Polynomial.map_comp, hsub]
  rw [← hconjugatePolynomial]

end Norm

end Hex.NumberTower
