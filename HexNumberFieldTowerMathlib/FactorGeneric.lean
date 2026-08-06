/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.NormCore
public import HexBerlekampZassenhausMathlib

public section

/-!
# Correctness of recursive Trager factorization

The semantic irreducibility predicate is phrased directly on the executable
tower-polynomial carrier.  Once the arithmetic laws are packaged as a field,
it is equivalent to Mathlib's ordinary polynomial irreducibility predicate.
-/

namespace Hex.NumberTower

private theorem rawPoly_polyCoords (levels : List Level)
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

private theorem rawPoly_shiftTop (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (c : Int) :
    Factor.rawPoly (level :: lower) (Factor.shiftTop level lower f c) =
      DensePoly.compose (Factor.rawPoly (level :: lower) f)
        (DensePoly.ofCoeffs
          #[-(Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)] *
                Factor.topGenerator level lower), 1]) := by
  rw [Factor.shiftTop, rawPoly_polyCoords]

private theorem polyCoords_rawPoly_shiftTop (level : Level)
    (lower : List Level) (f : Array (Array Rat)) (c : Int) :
    Factor.polyCoords
        (Factor.rawPoly (level :: lower)
          (Factor.shiftTop level lower f c)) =
      Factor.shiftTop level lower f c := by
  rw [Factor.shiftTop, rawPoly_polyCoords]

private theorem rawPoly_embedLower (level : Level) (lower : List Level)
    (f : Array (Array Rat)) :
    Factor.rawPoly (level :: lower) (Factor.embedLower level lower f) =
      DensePoly.ofCoeffs
        (f.map fun coefficient =>
          Arithmetic.Coeff.ofData (level :: lower) coefficient) := by
  rw [Factor.embedLower, rawPoly_polyCoords]

private theorem ofData_lower_eq_lowerHom (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (a : Arithmetic.Coeff lower) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    Arithmetic.Coeff.ofData (level :: lower) a.data =
      Norm.lowerHom level lower hvalid hinjectiveTop a := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  rw [Norm.lowerHom_apply]
  apply hinjectiveTop
  rw [LevelSemantics.coeffDenote_lift level lower
    (Nat.zero_lt_of_lt hvalid.1.1)]
  rw [Arithmetic.Coeff.ofData, LevelSemantics.coeffDenote,
    LevelSemantics.denote_fixed,
    LevelSemantics.denote_embed level lower hvalid a.data a.size_eq]
  rfl

private theorem rawPoly_embedLower_polyCoords (level : Level)
    (lower : List Level) (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (q : DensePoly (Arithmetic.Coeff lower)) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    Factor.rawPoly (level :: lower)
        (Factor.embedLower level lower (Factor.polyCoords q)) =
      HexPolyMathlib.ofPolynomial
        ((HexPolyMathlib.toPolynomial q).map
          (Norm.lowerHom level lower hvalid hinjectiveTop)) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  rw [rawPoly_embedLower]
  apply (HexPolyMathlib.equiv
    (R := Arithmetic.Coeff (level :: lower))).injective
  change HexPolyMathlib.toPolynomial
      (DensePoly.ofCoeffs
        ((Factor.polyCoords q).map fun coefficient =>
          Arithmetic.Coeff.ofData (level :: lower) coefficient)) =
    HexPolyMathlib.toPolynomial
      (HexPolyMathlib.ofPolynomial
        ((HexPolyMathlib.toPolynomial q).map
          (Norm.lowerHom level lower hvalid hinjectiveTop)))
  rw [HexPolyMathlib.toPolynomial_ofPolynomial]
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_map,
    HexPolyMathlib.coeff_toPolynomial]
  by_cases hn : n < q.size
  · have hcoeff : q.toArray[n] = q.coeff n :=
      (Array.getElem_eq_getD (0 : Arithmetic.Coeff lower)).trans
        (DensePoly.toArray_getD q n)
    simp [DensePoly.coeff_ofCoeffs, Factor.polyCoords, Array.getD, hn,
      ofData_lower_eq_lowerHom level lower hvalid hinjectiveTop]
    exact congrArg (LevelSemantics.liftCoeff level lower) hcoeff
  · simp [DensePoly.coeff_ofCoeffs, Factor.polyCoords, Array.getD, hn,
      DensePoly.coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hn)]
    exact (Norm.lowerHom level lower hvalid hinjectiveTop).map_zero.symm

private theorem toPolynomial_affine {K : Type*} [Field K]
    [DecidableEq K] (delta : K) :
    HexPolyMathlib.toPolynomial
        (DensePoly.ofCoeffs #[-delta, 1]) =
      Polynomial.X - Polynomial.C delta := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_sub]
  rcases n with _ | n
  · simp [DensePoly.coeff_ofCoeffs, Array.getD]
  · rcases n with _ | n
    · simp [DensePoly.coeff_ofCoeffs, Array.getD]
    · simp [DensePoly.coeff_ofCoeffs, Array.getD,
        Polynomial.coeff_X_of_ne_one (R := K)
          (show n + 1 + 1 ≠ 1 by omega)]
      rfl

/-- Semantic polynomial translation performed by the executable top-level
shift. -/
theorem toPolynomial_shiftTop (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat)) (c : Int) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    let delta := Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)] *
      Factor.topGenerator level lower
    HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower)
          (Factor.shiftTop level lower f c)) =
      Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly (level :: lower) f)) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let delta := Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)] *
    Factor.topGenerator level lower
  change HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower f c)) =
    Polynomial.taylor (-delta)
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) f))
  rw [rawPoly_shiftTop, HexPolyMathlib.toPolynomial_compose,
    toPolynomial_affine, Polynomial.taylor_apply]
  congr 1
  change Polynomial.X + (-Polynomial.C delta) =
    Polynomial.X + Polynomial.C (-delta)
  congr 1
  exact Polynomial.C_neg.symm

private theorem shiftDelta_neg (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (c : Int) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    let deltaNeg := Arithmetic.Coeff.ofData (level :: lower)
      #[(-(c : Rat))] * Factor.topGenerator level lower
    let delta := Arithmetic.Coeff.ofData (level :: lower)
      #[(c : Rat)] * Factor.topGenerator level lower
    (-deltaNeg) = delta := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  dsimp only
  apply hinjectiveTop
  have hrat (q : Rat) : LevelSemantics.coeffDenote (level :: lower)
      (Arithmetic.Coeff.ofData (level :: lower) #[q]) = (q : ℂ) := by
    change LevelSemantics.denote (level :: lower)
      (Arithmetic.fixedCoeffs (levelsDim (level :: lower)) #[q]) = (q : ℂ)
    rw [LevelSemantics.denote_fixed,
      LevelSemantics.denote_rat (level :: lower) hvalid]
  rw [LevelSemantics.coeffDenote_neg,
    LevelSemantics.coeffDenote_mul (level :: lower) hvalid,
    LevelSemantics.coeffDenote_mul (level :: lower) hvalid, hrat, hrat]
  push_cast
  ring

private theorem irreducible_shiftTop_iff (level : Level)
    (lower : List Level) (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat)) (c : Int) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    Irreducible (HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower f c))) ↔
      Irreducible (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) f)) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let delta := Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)] *
    Factor.topGenerator level lower
  change Irreducible (HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower f c))) ↔
    Irreducible (HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower) f))
  rw [toPolynomial_shiftTop level lower hvalid hinjectiveTop]
  exact (MulEquiv.irreducible_iff
    (Polynomial.taylorEquiv (-delta)).toMulEquiv)

/-- The canonical coordinate representative of rational zero is the
coefficient-field zero. -/
theorem ofData_zero_eq_zero (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels) :
    Arithmetic.Coeff.ofData levels #[(0 : Rat)] = 0 := by
  apply hinjective
  rw [LevelSemantics.coeffDenote_zero]
  change LevelSemantics.denote levels
      (Arithmetic.fixedCoeffs (levelsDim levels) #[(0 : Rat)]) = 0
  rw [LevelSemantics.denote_fixed,
    LevelSemantics.denote_rat levels hvalid]
  norm_num

private theorem rawPoly_shiftTop_zero (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : DensePoly (Arithmetic.Coeff (level :: lower))) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower (Factor.polyCoords f) 0) = f := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  apply (HexPolyMathlib.equiv
    (R := Arithmetic.Coeff (level :: lower))).injective
  change HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower (Factor.polyCoords f) 0)) =
    HexPolyMathlib.toPolynomial f
  rw [toPolynomial_shiftTop level lower hvalid hinjectiveTop,
    rawPoly_polyCoords]
  have hzero : Arithmetic.Coeff.ofData (level :: lower) #[(0 : Rat)] = 0 :=
    ofData_zero_eq_zero (level :: lower) hvalid hinjectiveTop
  simp [hzero, Polynomial.taylor_zero]

/-- The zero shift leaves the represented polynomial unchanged. -/
theorem toPolynomial_shiftTop_zero (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat)) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower)
          (Factor.shiftTop level lower f 0)) =
      HexPolyMathlib.toPolynomial (Factor.rawPoly (level :: lower) f) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  dsimp only
  rw [toPolynomial_shiftTop level lower hvalid hinjectiveTop]
  have hzero : Arithmetic.Coeff.ofData (level :: lower)
      #[((0 : Int) : Rat)] = 0 := by
    simpa using ofData_zero_eq_zero (level :: lower) hvalid hinjectiveTop
  rw [hzero]
  simp [Polynomial.taylor_zero]

/-- The lower-field polynomial produced by one unshifted Trager elimination. -/
private def tragerNorm (level : Level) (lower : List Level)
    (f : DensePoly (Arithmetic.Coeff (level :: lower))) :
    DensePoly (Arithmetic.Coeff lower) :=
  Factor.rawPoly lower
    (Norm.oneLevel level lower (Factor.polyCoords f) 0)

private theorem tragerNorm_shiftTop (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat)) (c : Int) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    tragerNorm level lower
        (Factor.rawPoly (level :: lower)
          (Factor.shiftTop level lower f c)) =
      Factor.rawPoly lower (Norm.oneLevel level lower f c) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  rw [tragerNorm, polyCoords_rawPoly_shiftTop]
  exact Norm.oneLevel_shift_zero level lower hvalid hinjectiveTop f c

private theorem tragerNorm_mul (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (a b : DensePoly (Arithmetic.Coeff (level :: lower))) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    tragerNorm level lower (a * b) =
      tragerNorm level lower a * tragerNorm level lower b := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  exact Norm.oneLevel_mul level lower hvalid hinjectiveTop a b 0

private theorem tragerNorm_lift (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (q : DensePoly (Arithmetic.Coeff lower)) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    let lifted := HexPolyMathlib.ofPolynomial
      ((HexPolyMathlib.toPolynomial q).map
        (Norm.lowerHom level lower hvalid hinjectiveTop))
    HexPolyMathlib.toPolynomial (tragerNorm level lower lifted) =
      (HexPolyMathlib.toPolynomial q) ^ level.degree := by
  exact Norm.oneLevel_lift level lower hvalid hinjectiveTop q

private theorem tragerNorm_dvd (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    {a b : DensePoly (Arithmetic.Coeff (level :: lower))} :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    HexPolyMathlib.toPolynomial a ∣ HexPolyMathlib.toPolynomial b →
      HexPolyMathlib.toPolynomial (tragerNorm level lower a) ∣
        HexPolyMathlib.toPolynomial (tragerNorm level lower b) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  change (HexPolyMathlib.toPolynomial a ∣
      HexPolyMathlib.toPolynomial b) → _
  intro hab
  rcases hab with ⟨r, hr⟩
  let rd := HexPolyMathlib.ofPolynomial r
  have hdense : b = a * rd := by
    apply (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff (level :: lower))).injective
    change HexPolyMathlib.toPolynomial b =
      HexPolyMathlib.toPolynomial (a * rd)
    rw [HexPolyMathlib.toPolynomial_mul,
      HexPolyMathlib.toPolynomial_ofPolynomial, ← hr]
  rw [hdense, tragerNorm_mul level lower hvalid hinjectiveTop,
    HexPolyMathlib.toPolynomial_mul]
  exact dvd_mul_right _ _

private theorem tragerNorm_not_isUnit (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : DensePoly (Arithmetic.Coeff (level :: lower)))
    (hdegree : 0 < f.degree?.getD 0) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    ¬ IsUnit (HexPolyMathlib.toPolynomial
      (tragerNorm level lower f)) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  change ¬ IsUnit (HexPolyMathlib.toPolynomial
    (tragerNorm level lower f))
  intro hunit
  let φ := Norm.lowerHom level lower hvalid hinjectiveTop
  have hliftUnit : IsUnit
      ((HexPolyMathlib.toPolynomial (tragerNorm level lower f)).map φ) :=
    hunit.map (Polynomial.mapRingHom φ).toMonoidHom
  have hdvd := Norm.shifted_dvd_norm level lower hvalid hinjectiveTop
    (Factor.polyCoords f) 0
  rw [rawPoly_shiftTop_zero level lower hvalid hinjectiveTop] at hdvd
  change HexPolyMathlib.toPolynomial f ∣
    (HexPolyMathlib.toPolynomial (tragerNorm level lower f)).map φ at hdvd
  have hfUnit : IsUnit (HexPolyMathlib.toPolynomial f) :=
    isUnit_of_dvd_one (hdvd.trans (isUnit_iff_dvd_one.mp hliftUnit))
  have hzero := Polynomial.natDegree_eq_zero_of_isUnit hfUnit
  rw [HexPolyMathlib.natDegree_toPolynomial] at hzero
  omega

private theorem toPolynomial_monic_associated (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f : DensePoly (Arithmetic.Coeff levels)) (hf : f ≠ 0) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    Associated (HexPolyMathlib.toPolynomial (Norm.monic f))
      (HexPolyMathlib.toPolynomial f) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hzero : f.isZero = false := by
    rw [DensePoly.isZero_eq_false_iff]
    exact Nat.pos_of_ne_zero fun hsize =>
      hf ((DensePoly.size_eq_zero_iff f).mp hsize)
  rw [Norm.monic, hzero]
  simp only [Bool.false_eq_true, if_false]
  rw [HexPolyMathlib.toPolynomial_scale]
  exact associated_unit_mul_left _ _
    (Polynomial.isUnit_C.mpr
      (inv_ne_zero (DensePoly.leadingCoeff_ne_zero_of_pos_size f
        ((DensePoly.isZero_eq_false_iff f).mp hzero))).isUnit)

private theorem toPolynomial_monic_monic (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f : DensePoly (Arithmetic.Coeff levels)) (hf : f ≠ 0) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    (HexPolyMathlib.toPolynomial (Norm.monic f)).Monic := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hzero : f.isZero = false := by
    rw [DensePoly.isZero_eq_false_iff]
    exact Nat.pos_of_ne_zero fun hsize =>
      hf ((DensePoly.size_eq_zero_iff f).mp hsize)
  have hpolyNe : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro h
    apply hf
    apply (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff levels)).injective
    simpa using h
  rw [Norm.monic, hzero]
  simp only [Bool.false_eq_true, if_false]
  rw [HexPolyMathlib.toPolynomial_scale, mul_comm]
  simpa only [HexPolyMathlib.leadingCoeff_toPolynomial] using
    Polynomial.monic_mul_leadingCoeff_inv hpolyNe

private theorem monic_eq_self (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f : DensePoly (Arithmetic.Coeff levels)) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    (HexPolyMathlib.toPolynomial f).Monic → Norm.monic f = f := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  intro hf
  apply (HexPolyMathlib.equiv
    (R := Arithmetic.Coeff levels)).injective
  exact Polynomial.eq_of_monic_of_associated
    (toPolynomial_monic_monic levels hvalid hinjective hinv f
      (fun hzero => by simpa [hzero] using hf))
    hf (toPolynomial_monic_associated levels hvalid hinjective hinv f
      (fun hzero => by simpa [hzero] using hf))

private theorem not_two_nonunits_of_squarefree_primePower
    {K : Type*} [Field K] {N q a b : Polynomial K} {d : Nat}
    (hN : Squarefree N) (hq : Irreducible q)
    (hNdiv : a * b ∣ N) (hqdiv : a * b ∣ q ^ d)
    (haUnit : ¬ IsUnit a) (hbUnit : ¬ IsUnit b) : False := by
  have habNe : a * b ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne_zero hNdiv
  have haNe : a ≠ 0 := left_ne_zero_of_mul habNe
  have hbNe : b ≠ 0 := right_ne_zero_of_mul habNe
  obtain ⟨pa, hpa, hpaDvd⟩ :=
    WfDvdMonoid.exists_irreducible_factor haUnit haNe
  obtain ⟨pb, hpb, hpbDvd⟩ :=
    WfDvdMonoid.exists_irreducible_factor hbUnit hbNe
  have hpaPow : pa ∣ q ^ d :=
    (dvd_mul_of_dvd_left hpaDvd b).trans hqdiv
  have hpbPow : pb ∣ q ^ d :=
    (dvd_mul_of_dvd_right hpbDvd a).trans hqdiv
  have hpaQ : pa ∣ q := hpa.prime.dvd_of_dvd_pow hpaPow
  have hpbQ : pb ∣ q := hpb.prime.dvd_of_dvd_pow hpbPow
  have hqA : q ∣ a := (hpa.dvd_symm hq hpaQ).trans hpaDvd
  have hqB : q ∣ b := (hpb.dvd_symm hq hpbQ).trans hpbDvd
  exact hq.not_isUnit (hN q ((mul_dvd_mul hqA hqB).trans hNdiv))

private theorem recoveredCommon_irreducible (level : Level)
    (lower : List Level) (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (P : DensePoly (Arithmetic.Coeff (level :: lower)))
    (q : DensePoly (Arithmetic.Coeff lower)) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    let lifted := Factor.rawPoly (level :: lower)
      (Factor.embedLower level lower (Factor.polyCoords q))
    let common := Norm.monic (DensePoly.gcd P lifted)
    Squarefree (HexPolyMathlib.toPolynomial (tragerNorm level lower P)) →
      Irreducible (HexPolyMathlib.toPolynomial q) →
      0 < common.degree?.getD 0 →
      Irreducible (HexPolyMathlib.toPolynomial common) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let lifted := Factor.rawPoly (level :: lower)
    (Factor.embedLower level lower (Factor.polyCoords q))
  let g := DensePoly.gcd P lifted
  let common := Norm.monic g
  change Squarefree
      (HexPolyMathlib.toPolynomial (tragerNorm level lower P)) →
    Irreducible (HexPolyMathlib.toPolynomial q) →
    0 < common.degree?.getD 0 →
    Irreducible (HexPolyMathlib.toPolynomial common)
  intro hsquarefree hq hdegree
  have hcommonNe : common ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simpa using hdegree
  have hgNe : g ≠ 0 := by
    intro hzero
    apply hcommonNe
    simp [common, Norm.monic, hzero]
  have hcommonAssoc : Associated
      (HexPolyMathlib.toPolynomial common)
      (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial P)
        (HexPolyMathlib.toPolynomial lifted)) :=
    (toPolynomial_monic_associated (level :: lower) hvalid
      hinjectiveTop hinvTop g hgNe).trans
        (HexPolyMathlib.toPolynomial_gcd_associated P lifted)
  have hcommonDvdP : HexPolyMathlib.toPolynomial common ∣
      HexPolyMathlib.toPolynomial P :=
    hcommonAssoc.dvd.trans
      (EuclideanDomain.gcd_dvd_left _ _)
  have hcommonDvdLifted : HexPolyMathlib.toPolynomial common ∣
      HexPolyMathlib.toPolynomial lifted :=
    hcommonAssoc.dvd.trans
      (EuclideanDomain.gcd_dvd_right _ _)
  have hcommonNotUnit : ¬ IsUnit
      (HexPolyMathlib.toPolynomial common) := by
    intro hunit
    have hzero := Polynomial.natDegree_eq_zero_of_isUnit hunit
    rw [HexPolyMathlib.natDegree_toPolynomial] at hzero
    omega
  refine ⟨hcommonNotUnit, ?_⟩
  intro a b hab
  by_cases haUnit : IsUnit a
  · exact Or.inl haUnit
  by_cases hbUnit : IsUnit b
  · exact Or.inr hbUnit
  exfalso
  have hcommonPolyNe : HexPolyMathlib.toPolynomial common ≠ 0 := by
    intro hzero
    apply hcommonNe
    apply (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff (level :: lower))).injective
    simpa using hzero
  have habNe : a * b ≠ 0 := by
    rw [← hab]
    exact hcommonPolyNe
  have haNe : a ≠ 0 := left_ne_zero_of_mul habNe
  have hbNe : b ≠ 0 := right_ne_zero_of_mul habNe
  let ad := HexPolyMathlib.ofPolynomial a
  let bd := HexPolyMathlib.ofPolynomial b
  have hdense : common = ad * bd := by
    apply (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff (level :: lower))).injective
    change HexPolyMathlib.toPolynomial common =
      HexPolyMathlib.toPolynomial (ad * bd)
    rw [HexPolyMathlib.toPolynomial_mul,
      HexPolyMathlib.toPolynomial_ofPolynomial,
      HexPolyMathlib.toPolynomial_ofPolynomial, hab]
  have haNatDegree : a.natDegree ≠ 0 := by
    intro hzero
    apply haUnit
    apply Polynomial.isUnit_iff_degree_eq_zero.mpr
    rw [Polynomial.degree_eq_natDegree haNe, hzero]
    rfl
  have hbNatDegree : b.natDegree ≠ 0 := by
    intro hzero
    apply hbUnit
    apply Polynomial.isUnit_iff_degree_eq_zero.mpr
    rw [Polynomial.degree_eq_natDegree hbNe, hzero]
    rfl
  have hadDegree : 0 < ad.degree?.getD 0 := by
    rw [← HexPolyMathlib.natDegree_toPolynomial]
    change 0 < (HexPolyMathlib.toPolynomial ad).natDegree
    rw [show HexPolyMathlib.toPolynomial ad = a by simp [ad]]
    exact Nat.pos_of_ne_zero haNatDegree
  have hbdDegree : 0 < bd.degree?.getD 0 := by
    rw [← HexPolyMathlib.natDegree_toPolynomial]
    change 0 < (HexPolyMathlib.toPolynomial bd).natDegree
    rw [show HexPolyMathlib.toPolynomial bd = b by simp [bd]]
    exact Nat.pos_of_ne_zero hbNatDegree
  have hnormAUnit : ¬ IsUnit (HexPolyMathlib.toPolynomial
      (tragerNorm level lower ad)) :=
    tragerNorm_not_isUnit level lower hvalid hinjectiveTop ad hadDegree
  have hnormBUnit : ¬ IsUnit (HexPolyMathlib.toPolynomial
      (tragerNorm level lower bd)) :=
    tragerNorm_not_isUnit level lower hvalid hinjectiveTop bd hbdDegree
  have hnormP := tragerNorm_dvd level lower hvalid hinjectiveTop
    hcommonDvdP
  rw [hdense, tragerNorm_mul level lower hvalid hinjectiveTop,
    HexPolyMathlib.toPolynomial_mul] at hnormP
  have hnormLifted := tragerNorm_dvd level lower hvalid hinjectiveTop
    hcommonDvdLifted
  rw [hdense, tragerNorm_mul level lower hvalid hinjectiveTop,
    HexPolyMathlib.toPolynomial_mul] at hnormLifted
  have hlifted : lifted = HexPolyMathlib.ofPolynomial
      ((HexPolyMathlib.toPolynomial q).map
        (Norm.lowerHom level lower hvalid hinjectiveTop)) :=
    rawPoly_embedLower_polyCoords level lower hvalid hinjectiveTop q
  have hnormLiftedPower : HexPolyMathlib.toPolynomial
      (tragerNorm level lower
        (HexPolyMathlib.ofPolynomial
          ((HexPolyMathlib.toPolynomial q).map
            (Norm.lowerHom level lower hvalid hinjectiveTop)))) =
      (HexPolyMathlib.toPolynomial q) ^ level.degree := by
    exact tragerNorm_lift level lower hvalid hinjectiveTop q
  rw [← hlifted] at hnormLiftedPower
  rw [hnormLiftedPower] at hnormLifted
  exact not_two_nonunits_of_squarefree_primePower hsquarefree hq
    hnormP hnormLifted hnormAUnit hnormBUnit

private theorem recoveredFactor_irreducible (level : Level)
    (lower : List Level) (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (component lowerFactor : Array (Array Rat)) (shift : Int) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    let shifted := Factor.rawPoly (level :: lower)
      (Factor.shiftTop level lower component shift)
    let q := Factor.rawPoly lower lowerFactor
    let lifted := Factor.rawPoly (level :: lower)
      (Factor.embedLower level lower lowerFactor)
    let common := Norm.monic (DensePoly.gcd shifted lifted)
    let unshifted := Factor.rawPoly (level :: lower)
      (Factor.shiftTop level lower (Factor.polyCoords common) (-shift))
    let result := Norm.monic unshifted
    Squarefree (HexPolyMathlib.toPolynomial
      (tragerNorm level lower shifted)) →
      Irreducible (HexPolyMathlib.toPolynomial q) →
      Factor.polyCoords q = lowerFactor →
      0 < common.degree?.getD 0 →
      Irreducible (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) (Factor.polyCoords result))) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let shifted := Factor.rawPoly (level :: lower)
    (Factor.shiftTop level lower component shift)
  let q := Factor.rawPoly lower lowerFactor
  let lifted := Factor.rawPoly (level :: lower)
    (Factor.embedLower level lower lowerFactor)
  let common := Norm.monic (DensePoly.gcd shifted lifted)
  let unshifted := Factor.rawPoly (level :: lower)
    (Factor.shiftTop level lower (Factor.polyCoords common) (-shift))
  let result := Norm.monic unshifted
  change Squarefree (HexPolyMathlib.toPolynomial
      (tragerNorm level lower shifted)) →
    Irreducible (HexPolyMathlib.toPolynomial q) →
    Factor.polyCoords q = lowerFactor →
    0 < common.degree?.getD 0 →
    Irreducible (HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower) (Factor.polyCoords result)))
  intro hsquarefree hq hlowerCoords hdegree
  have hcommon : Irreducible (HexPolyMathlib.toPolynomial common) := by
    have hdegree' : 0 < (Norm.monic (DensePoly.gcd shifted
        (Factor.rawPoly (level :: lower)
          (Factor.embedLower level lower (Factor.polyCoords q))))).degree?.getD 0 := by
      simpa [common, lifted, hlowerCoords] using hdegree
    have h := recoveredCommon_irreducible level lower hvalid
      hinjectiveTop shifted q
    simpa [common, lifted, hlowerCoords] using
      (h hsquarefree hq hdegree')
  have hunshifted : Irreducible
      (HexPolyMathlib.toPolynomial unshifted) := by
    apply (irreducible_shiftTop_iff level lower hvalid hinjectiveTop
      (Factor.polyCoords common) (-shift)).mpr
    rw [rawPoly_polyCoords]
    exact hcommon
  have hunshiftedNe : unshifted ≠ 0 := by
    intro hzero
    apply hunshifted.ne_zero
    rw [hzero, HexPolyMathlib.toPolynomial_zero]
  have hresult : Irreducible
      (HexPolyMathlib.toPolynomial result) :=
    (toPolynomial_monic_associated (level :: lower) hvalid
      hinjectiveTop hinvTop unshifted hunshiftedNe).symm.irreducible hunshifted
  rw [rawPoly_polyCoords]
  exact hresult

private theorem findSquarefreeShiftAux_squarefree (level : Level)
    (lower : List Level) (f : Array (Array Rat)) (start fuel : Nat)
    {shift : Int} {norm : Array (Array Rat)}
    (h : Norm.findSquarefreeShiftAux level lower f start fuel =
      some (shift, norm)) : Norm.isSquarefree lower norm := by
  induction fuel generalizing start with
  | zero => simp [Norm.findSquarefreeShiftAux] at h
  | succ fuel ih =>
      simp only [Norm.findSquarefreeShiftAux] at h
      split at h
      · rename_i hsquarefree
        cases h
        exact hsquarefree
      · exact ih (start := start + 1) h

private theorem findSquarefreeShiftAux_norm (level : Level)
    (lower : List Level) (f : Array (Array Rat)) (start fuel : Nat)
    {shift : Int} {norm : Array (Array Rat)}
    (h : Norm.findSquarefreeShiftAux level lower f start fuel =
      some (shift, norm)) :
    norm = Norm.oneLevel level lower f shift := by
  induction fuel generalizing start with
  | zero => simp [Norm.findSquarefreeShiftAux] at h
  | succ fuel ih =>
      simp only [Norm.findSquarefreeShiftAux] at h
      split at h
      · cases h
        rfl
      · exact ih (start := start + 1) h

private theorem findSquarefreeShift_squarefree (level : Level)
    (lower : List Level) (f : Array (Array Rat))
    {shift : Int} {norm : Array (Array Rat)}
    (h : Norm.findSquarefreeShift level lower f = some (shift, norm)) :
    Norm.isSquarefree lower norm := by
  exact findSquarefreeShiftAux_squarefree level lower f 0
    (Norm.tragerShiftCount level.degree (f.size - 1)) h

private theorem findSquarefreeShift_norm (level : Level)
    (lower : List Level) (f : Array (Array Rat))
    {shift : Int} {norm : Array (Array Rat)}
    (h : Norm.findSquarefreeShift level lower f = some (shift, norm)) :
    norm = Norm.oneLevel level lower f shift := by
  exact findSquarefreeShiftAux_norm level lower f 0
    (Norm.tragerShiftCount level.degree (f.size - 1)) h

private theorem oneLevel_size (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (shift : Int) :
    (Norm.oneLevel level lower f shift).size =
      (Factor.rawPoly lower (Norm.oneLevel level lower f shift)).size := by
  rw [Norm.rawPoly_oneLevel]
  simp [Norm.oneLevel]

private theorem array_degree_pos_of_raw_degree_pos (levels : List Level)
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0) :
    0 < f.size - 1 := by
  let p := Factor.rawPoly levels f
  change 0 < p.degree?.getD 0 at hdegree
  have hpSize : p.size ≠ 0 := by
    intro hzero
    have hpDegree : p.degree?.getD 0 = 0 := by
      rw [(DensePoly.degree?_eq_none_iff p).2 hzero, Option.getD_none]
    omega
  have hpDegree : p.degree?.getD 0 = p.size - 1 := by
    rw [DensePoly.degree?_eq_some_of_pos_size p (Nat.pos_of_ne_zero hpSize),
      Option.getD_some]
  have hpSizeLe : p.size ≤ f.size := by
    exact (DensePoly.size_ofCoeffs_le _).trans (by simp [p, Factor.rawPoly])
  rw [hpDegree] at hdegree
  omega

private theorem oneLevel_degree_pos (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat)) (shift : Int)
    (hdegree : 0 < (Factor.rawPoly (level :: lower) f).degree?.getD 0) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    Squarefree (HexPolyMathlib.toPolynomial
      (Factor.rawPoly lower (Norm.oneLevel level lower f shift))) →
    0 < (Factor.rawPoly lower
      (Norm.oneLevel level lower f shift)).degree?.getD 0 := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  dsimp only
  intro hsquarefree
  let shifted := Factor.rawPoly (level :: lower)
    (Factor.shiftTop level lower f shift)
  let norm := Factor.rawPoly lower (Norm.oneLevel level lower f shift)
  have hshiftedDegree : 0 < shifted.degree?.getD 0 := by
    have hnatDegree := congrArg Polynomial.natDegree
      (toPolynomial_shiftTop level lower hvalid hinjectiveTop f shift)
    rw [Polynomial.natDegree_taylor,
      HexPolyMathlib.natDegree_toPolynomial,
      HexPolyMathlib.natDegree_toPolynomial] at hnatDegree
    change 0 < (Factor.rawPoly (level :: lower)
      (Factor.shiftTop level lower f shift)).degree?.getD 0
    rw [hnatDegree]
    exact hdegree
  have hnotUnit : ¬ IsUnit (HexPolyMathlib.toPolynomial norm) := by
    have h := tragerNorm_not_isUnit level lower hvalid hinjectiveTop
      shifted hshiftedDegree
    rw [tragerNorm_shiftTop level lower hvalid hinjectiveTop f shift] at h
    exact h
  have hnormNe : HexPolyMathlib.toPolynomial norm ≠ 0 := by
    exact hsquarefree.ne_zero
  have hnatDegree : (HexPolyMathlib.toPolynomial norm).natDegree ≠ 0 := by
    intro hzero
    apply hnotUnit
    apply Polynomial.isUnit_iff_degree_eq_zero.mpr
    rw [Polynomial.degree_eq_natDegree hnormNe, hzero]
    rfl
  rw [HexPolyMathlib.natDegree_toPolynomial] at hnatDegree
  exact Nat.pos_of_ne_zero hnatDegree

private theorem squarefree_toPolynomial_of_check (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f : Array (Array Rat)) (hcheck : Norm.isSquarefree levels f) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    Squarefree (HexPolyMathlib.toPolynomial
      (Factor.rawPoly levels f)) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let P := HexPolyMathlib.toPolynomial (Factor.rawPoly levels f)
  let φ := LevelSemantics.coeffHom levels hvalid hinjective hinv
  letI : CharZero (Arithmetic.Coeff levels) :=
    { cast_injective := by
        intro m n hmn
        apply CharZero.cast_injective (R := ℂ)
        have hmapped := congrArg φ hmn
        simpa only [map_natCast] using hmapped }
  have hraw := (Norm.isSquarefree_iff levels hvalid hinjective hinv f).mp hcheck
  have hmap : Norm.rawPolynomial levels (Factor.rawPoly levels f) =
      P.map φ := by
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    rfl
  have hsepMap : (P.map φ).Separable := by
    rw [← hmap]
    exact PerfectField.separable_iff_squarefree.mpr hraw
  exact PerfectField.separable_iff_squarefree.mp
    ((Polynomial.separable_map φ).mp hsepMap)

private theorem mem_foldl_push_if {α β : Type*}
    (p : α → Prop) [DecidablePred p] (g : α → β) :
    ∀ (items : List α) (init : Array β) (x : β),
      x ∈ items.foldl
          (fun out item => if p item then out.push (g item) else out) init →
        x ∈ init ∨ ∃ item ∈ items, p item ∧ g item = x := by
  intro items
  induction items with
  | nil =>
      intro init x hx
      exact Or.inl hx
  | cons item items ih =>
      intro init x hx
      simp only [List.foldl_cons] at hx
      rcases ih _ x hx with hxinit | ⟨source, hsource, hpass, rfl⟩
      · by_cases hitem : p item
        · rw [if_pos hitem] at hxinit
          rcases Array.mem_push.mp hxinit with hxold | rfl
          · exact Or.inl hxold
          · exact Or.inr ⟨item, by simp, hitem, rfl⟩
        · rw [if_neg hitem] at hxinit
          exact Or.inl hxinit
      · exact Or.inr ⟨source, List.mem_cons_of_mem item hsource,
          hpass, rfl⟩

private theorem foldl_push_if_toList {α β : Type*}
    (p : α → Prop) [DecidablePred p] (g : α → β) :
    ∀ (items : List α) (init : Array β),
      (items.foldl
          (fun out item => if p item then out.push (g item) else out)
          init).toList =
        init.toList ++ items.filterMap
          (fun item => if p item then some (g item) else none) := by
  intro items
  induction items with
  | nil => intro init; simp
  | cons item items ih =>
      intro init
      simp only [List.foldl_cons]
      by_cases hitem : p item
      · rw [if_pos hitem, ih]
        simp [hitem]
      · rw [if_neg hitem, ih]
        simp [hitem]

private theorem filterMap_prod_associated {K α : Type*} [Field K]
    (p : α → Prop) [DecidablePred p]
    (result common : α → Polynomial K)
    (hpass : ∀ item, p item → Associated (result item) (common item))
    (hskip : ∀ item, ¬ p item → IsUnit (common item)) :
    ∀ items : List α,
      Associated
        ((items.filterMap fun item =>
          if p item then some (result item) else none).prod)
        ((items.map common).prod) := by
  intro items
  induction items with
  | nil => simp
  | cons item items ih =>
      by_cases hitem : p item
      · simpa [hitem] using (hpass item hitem).mul_mul ih
      · have hunit : Associated (1 : Polynomial K) (common item) :=
          (associated_one_iff_isUnit.mpr (hskip item hitem)).symm
        simpa [hitem] using hunit.mul_mul ih

private theorem taylor_list_prod {K : Type*} [CommRing K]
    (c : K) : ∀ ps : List (Polynomial K),
    Polynomial.taylor c ps.prod =
      (ps.map (Polynomial.taylor c)).prod := by
  intro ps
  induction ps with
  | nil => simp
  | cons p ps ih => simp [Polynomial.taylor_mul, ih]

private theorem polynomial_squarefree_map {K L : Type*}
    [Field K] [Field L] [CharZero K] [CharZero L]
    (f : K →+* L) {p : Polynomial K} (hp : Squarefree p) :
    Squarefree (p.map f) :=
  PerfectField.separable_iff_squarefree.mp
    ((PerfectField.separable_iff_squarefree.mpr hp).map (f := f))

private theorem recover_mem (level : Level) (lower : List Level)
    (shift : Int) (component : Array (Array Rat))
    (lowerFactors : Array (Array (Array Rat)))
    {factor : Array (Array Rat)}
    (hfactor : factor ∈
      Factor.recover level lower shift component lowerFactors) :
    ∃ lowerFactor ∈ lowerFactors,
      let shifted := Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower component shift)
      let lifted := Factor.rawPoly (level :: lower)
        (Factor.embedLower level lower lowerFactor)
      let common := Norm.monic (DensePoly.gcd shifted lifted)
      0 < common.degree?.getD 0 ∧
        Factor.polyCoords
          (Norm.monic (Factor.rawPoly (level :: lower)
            (Factor.shiftTop level lower (Factor.polyCoords common)
              (-shift)))) = factor := by
  let shifted := Factor.rawPoly (level :: lower)
    (Factor.shiftTop level lower component shift)
  let lifted (lowerFactor : Array (Array Rat)) :=
    Factor.rawPoly (level :: lower)
      (Factor.embedLower level lower lowerFactor)
  let common (lowerFactor : Array (Array Rat)) :=
    Norm.monic (DensePoly.gcd shifted (lifted lowerFactor))
  let pass (lowerFactor : Array (Array Rat)) :=
    0 < (common lowerFactor).degree?.getD 0
  let recovered (lowerFactor : Array (Array Rat)) :=
    Factor.polyCoords
      (Norm.monic (Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower (Factor.polyCoords (common lowerFactor))
          (-shift))))
  have hfold : factor ∈ lowerFactors.toList.foldl
      (fun out lowerFactor =>
        if pass lowerFactor then out.push (recovered lowerFactor) else out) #[] := by
    simpa only [Factor.recover, Array.foldl_toList, shifted, lifted,
      common, pass, recovered] using hfactor
  rcases mem_foldl_push_if pass recovered lowerFactors.toList #[] factor hfold with
      hnil | ⟨lowerFactor, hlower, hpass, hrecovered⟩
  · simp at hnil
  · refine ⟨lowerFactor, Array.mem_toList_iff.mp hlower, ?_⟩
    exact ⟨hpass, hrecovered⟩

private theorem recover_mem_sound (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (component : Array (Array Rat)) (shift : Int)
    (lowerFactors : Array (Array (Array Rat))) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    let shifted := Factor.rawPoly (level :: lower)
      (Factor.shiftTop level lower component shift)
    Squarefree (HexPolyMathlib.toPolynomial
      (tragerNorm level lower shifted)) →
    (∀ lowerFactor ∈ lowerFactors,
      Factor.polyCoords (Factor.rawPoly lower lowerFactor) = lowerFactor ∧
        Irreducible (HexPolyMathlib.toPolynomial
          (Factor.rawPoly lower lowerFactor))) →
    ∀ factor ∈ Factor.recover level lower shift component lowerFactors,
      Factor.polyCoords (Factor.rawPoly (level :: lower) factor) = factor ∧
        Irreducible (HexPolyMathlib.toPolynomial
          (Factor.rawPoly (level :: lower) factor)) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let shifted := Factor.rawPoly (level :: lower)
    (Factor.shiftTop level lower component shift)
  dsimp only
  intro hsquarefree hlower factor hfactor
  obtain ⟨lowerFactor, hlowerFactor, hdegree, hrecovered⟩ :=
    recover_mem level lower shift component lowerFactors hfactor
  have hlowerSound := hlower lowerFactor hlowerFactor
  constructor
  · rw [← hrecovered, rawPoly_polyCoords]
  · rw [← hrecovered]
    exact recoveredFactor_irreducible level lower hvalid hinjectiveTop
      component lowerFactor shift hsquarefree hlowerSound.2 hlowerSound.1
      hdegree

private theorem toRatPoly_ofRatPoly (f : DensePoly Rat) :
    Factor.toRatPoly (Factor.ofRatPoly f) = f := by
  rw [Factor.toRatPoly, Factor.ofRatPoly, Array.map_map]
  have harray : f.toArray.map
      ((fun coefficient : Array Rat => coefficient.getD 0 0) ∘
        fun coefficient : Rat => #[coefficient]) = f.toArray := by
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp [Function.comp_def]
  rw [harray, DensePoly.ofCoeffs_toArray]

private theorem polyCoords_rawPoly_ofRatPoly (f : DensePoly Rat)
    (hf : f ≠ 0) :
    Factor.polyCoords (Factor.rawPoly [] (Factor.ofRatPoly f)) =
      Factor.ofRatPoly f := by
  letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  let q := Factor.rawPoly [] (Factor.ofRatPoly f)
  have hmap : (HexPolyMathlib.toPolynomial q).map
      LevelSemantics.coeffRatEquiv.toRingHom =
      HexPolyMathlib.toPolynomial f := by
    simpa [q, toRatPoly_ofRatPoly] using
      LevelSemantics.map_rawPoly_nil (Factor.ofRatPoly f)
  have hq : q ≠ 0 := by
    intro hzero
    apply hf
    apply (HexPolyMathlib.equiv (R := Rat)).injective
    change HexPolyMathlib.toPolynomial f =
      HexPolyMathlib.toPolynomial (0 : DensePoly Rat)
    rw [← hmap, hzero, HexPolyMathlib.toPolynomial_zero,
      Polynomial.map_zero, HexPolyMathlib.toPolynomial_zero]
  have hdegree : q.degree?.getD 0 = f.degree?.getD 0 := by
    have hmapDegree := congrArg Polynomial.natDegree hmap
    rw [Polynomial.natDegree_map_eq_of_injective
      (f := LevelSemantics.coeffRatEquiv.toRingHom)
      LevelSemantics.coeffRatEquiv.injective] at hmapDegree
    simpa only [HexPolyMathlib.natDegree_toPolynomial] using hmapDegree
  have hsize : q.size = f.size := by
    have hqpos : 0 < q.size := Nat.pos_of_ne_zero fun h =>
      hq ((DensePoly.size_eq_zero_iff q).mp h)
    have hfpos : 0 < f.size := Nat.pos_of_ne_zero fun h =>
      hf ((DensePoly.size_eq_zero_iff f).mp h)
    rw [DensePoly.degree?_eq_some_of_pos_size q hqpos,
      DensePoly.degree?_eq_some_of_pos_size f hfpos] at hdegree
    simp only [Option.getD_some] at hdegree
    omega
  change Factor.polyCoords q = Factor.ofRatPoly f
  rw [Factor.polyCoords, Factor.ofRatPoly]
  apply Array.ext
  · simpa using hsize
  · intro i hi₁ hi₂
    have hi : i < f.size := by simpa using hi₂
    have hiq : i < q.toArray.size := by simpa [hsize] using hi
    have hif : i < f.toArray.size := by simpa using hi
    have hcoeff : q.toArray[i] = q.coeff i :=
      (Array.getElem_eq_getD (0 : Arithmetic.Coeff []) (h := hiq)).trans
        (DensePoly.toArray_getD q i)
    have hcoeffF : f.toArray[i] = f.coeff i :=
      (Array.getElem_eq_getD (0 : Rat) (h := hif)).trans
        (DensePoly.toArray_getD f i)
    simp only [Array.getElem_map]
    rw [hcoeff, hcoeffF]
    simp [q, Factor.rawPoly, Factor.ofRatPoly, DensePoly.coeff_ofCoeffs,
      Arithmetic.Coeff.ofData, Arithmetic.fixedCoeffs, Array.getD, hi]
    rw [hcoeffF]
    apply Array.ext
    · simp [levelsDim]
    · intro j hj₁ hj₂
      have hj : j = 0 := by simpa using hj₂
      subst j
      simp

private theorem toPolynomial_scale_inv_monic (f : DensePoly Rat)
    (hf : f ≠ 0) :
    (HexPolyMathlib.toPolynomial
      (DensePoly.scale f.leadingCoeff⁻¹ f)).Monic := by
  rw [HexPolyMathlib.toPolynomial_scale, Polynomial.Monic.def,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    HexPolyMathlib.leadingCoeff_toPolynomial]
  exact inv_mul_cancel₀ (DensePoly.leadingCoeff_ne_zero_of_pos_size f
    (Nat.pos_of_ne_zero fun hsize =>
      hf ((DensePoly.size_eq_zero_iff f).mp hsize)))

private theorem scale_inv_associated (f : DensePoly Rat) (hf : f ≠ 0) :
    Associated
      (HexPolyMathlib.toPolynomial (DensePoly.scale f.leadingCoeff⁻¹ f))
      (HexPolyMathlib.toPolynomial f) := by
  rw [HexPolyMathlib.toPolynomial_scale]
  exact associated_unit_mul_left _ _
    (Polynomial.isUnit_C.mpr
      (inv_ne_zero (DensePoly.leadingCoeff_ne_zero_of_pos_size f
        (Nat.pos_of_ne_zero fun hsize =>
          hf ((DensePoly.size_eq_zero_iff f).mp hsize)))).isUnit)

private noncomputable def normalizedRatFactor (f : ZPoly) : Polynomial Rat :=
  HexPolyMathlib.toPolynomial <|
    DensePoly.scale f.toRatPoly.leadingCoeff⁻¹ f.toRatPoly

private theorem toRatPoly_ne_zero {f : ZPoly} (hf : f ≠ 0) :
    f.toRatPoly ≠ 0 := by
  intro hzero
  have hmapped := congrArg HexPolyMathlib.toPolynomial hzero
  rw [HexPolyZMathlib.toPolynomial_toRatPoly,
    HexPolyMathlib.toPolynomial_zero] at hmapped
  exact HexPolyZMathlib.toPolyℚ_ne_zero hf hmapped

private theorem normalizedRatFactors_monic_associated
    (factors : List ZPoly) (hne : ∀ f ∈ factors, f ≠ 0) :
    (factors.map normalizedRatFactor).prod.Monic ∧
      Associated (factors.map normalizedRatFactor).prod
        (factors.map HexPolyZMathlib.toPolyℚ).prod := by
  induction factors with
  | nil => simp
  | cons factor factors ih =>
      have hfactorNe : factor ≠ 0 := hne factor (by simp)
      have htailNe : ∀ f ∈ factors, f ≠ 0 := by
        intro f hf
        exact hne f (by simp [hf])
      obtain ⟨htailMonic, htailAssociated⟩ := ih htailNe
      have hfactorMonic : (normalizedRatFactor factor).Monic :=
        toPolynomial_scale_inv_monic factor.toRatPoly
          (toRatPoly_ne_zero hfactorNe)
      have hfactorAssociated : Associated (normalizedRatFactor factor)
          (HexPolyZMathlib.toPolyℚ factor) := by
        refine (scale_inv_associated factor.toRatPoly
          (toRatPoly_ne_zero hfactorNe)).trans ?_
        rw [HexPolyZMathlib.toPolynomial_toRatPoly]
      exact ⟨hfactorMonic.mul htailMonic,
        hfactorAssociated.mul_mul htailAssociated⟩

private theorem factorPower_toPolyℚ (f : ZPoly) (n : Nat) :
    HexPolyZMathlib.toPolyℚ (Hex.Factorization.factorPower f n) =
      HexPolyZMathlib.toPolyℚ f ^ n := by
  rw [HexPolyZMathlib.toPolyℚ, HexPolyZMathlib.toPolyℚ,
    ← Polynomial.map_pow,
    ← HexBerlekampZassenhausMathlib.factorPower_toPolynomial]

private theorem toPolyℚ_mul (f g : ZPoly) :
    HexPolyZMathlib.toPolyℚ (f * g) =
      HexPolyZMathlib.toPolyℚ f * HexPolyZMathlib.toPolyℚ g := by
  rw [HexPolyZMathlib.toPolyℚ, HexPolyZMathlib.toPolynomial_mul,
    Polynomial.map_mul]

private theorem factorizationProduct_toPolyℚ_foldl
    (entries : List (ZPoly × Nat)) (init : ZPoly) :
    HexPolyZMathlib.toPolyℚ
        (entries.foldl (fun product entry =>
          product * Hex.Factorization.factorPower entry.1 entry.2) init) =
      HexPolyZMathlib.toPolyℚ init *
        (entries.flatMap fun entry =>
          List.replicate entry.2 (HexPolyZMathlib.toPolyℚ entry.1)).prod := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, ih, toPolyℚ_mul, factorPower_toPolyℚ]
      simp only [List.flatMap_cons, List.prod_append, List.prod_replicate]
      ring

private theorem factorizationProduct_toPolyℚ (factorization : Hex.Factorization) :
    HexPolyZMathlib.toPolyℚ factorization.product =
      Polynomial.C (factorization.scalar : Rat) *
        (factorization.factors.toList.flatMap fun entry =>
          List.replicate entry.2 (HexPolyZMathlib.toPolyℚ entry.1)).prod := by
  rw [Hex.Factorization.product_eq_foldl_factorPower,
    ← Array.foldl_toList, factorizationProduct_toPolyℚ_foldl,
    HexPolyZMathlib.toPolyℚ, HexPolyZMathlib.toPolynomial_C,
    Polynomial.map_C]
  congr 2

private theorem factorize_normalized_product (f : ZPoly) (hf : f ≠ 0) :
    let factors := (ZPoly.factorize f).factors.toList.flatMap
      (fun entry => List.replicate entry.2 entry.1)
    (factors.map normalizedRatFactor).prod.Monic ∧
      Associated (factors.map normalizedRatFactor).prod
        (HexPolyZMathlib.toPolyℚ f) := by
  let φ := ZPoly.factorize f
  let factors := φ.factors.toList.flatMap
    (fun entry => List.replicate entry.2 entry.1)
  have hfactorsNe : ∀ factor ∈ factors, factor ≠ 0 := by
    intro factor hfactor
    simp only [factors] at hfactor
    simp only [List.mem_flatMap, List.mem_replicate] at hfactor
    obtain ⟨entry, hentry, _, rfl⟩ := hfactor
    exact (HexBerlekampZassenhausMathlib.factorize_irreducible_of_nonUnit
      f entry (Array.mem_toList_iff.mp hentry)).not_zero
  obtain ⟨hmonic, hassociated⟩ :=
    normalizedRatFactors_monic_associated factors hfactorsNe
  refine ⟨hmonic, hassociated.trans ?_⟩
  have hfactorize : φ.product = f := by
    exact HexBerlekampZassenhausMathlib.factorize_product f
  have hproductRat := factorizationProduct_toPolyℚ φ
  rw [hfactorize] at hproductRat
  have hflat : (List.map HexPolyZMathlib.toPolyℚ factors).prod =
      (φ.factors.toList.flatMap fun entry =>
        List.replicate entry.2 (HexPolyZMathlib.toPolyℚ entry.1)).prod := by
    simp only [factors, List.map_flatMap, List.map_replicate]
  have hproductRat' : HexPolyZMathlib.toPolyℚ f =
      Polynomial.C (φ.scalar : Rat) *
        (List.map HexPolyZMathlib.toPolyℚ factors).prod := by
    rw [hflat]
    exact hproductRat
  have hscalarNe : (φ.scalar : Rat) ≠ 0 := by
    intro hzero
    have hzeroPoly : HexPolyZMathlib.toPolyℚ f = 0 := by
      simpa [hzero] using hproductRat'
    exact HexPolyZMathlib.toPolyℚ_ne_zero hf hzeroPoly
  rw [show (List.map HexPolyZMathlib.toPolyℚ factors).prod =
      Polynomial.C (φ.scalar : Rat)⁻¹ * HexPolyZMathlib.toPolyℚ f by
    rw [hproductRat', ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hscalarNe,
      Polynomial.C_1, one_mul]]
  exact associated_unit_mul_left _ _
    (Polynomial.isUnit_C.mpr (inv_ne_zero hscalarNe).isUnit)

private theorem normalizedRatFactor_irreducible (integer : ZPoly)
    (hinteger : integer ≠ 0) (entry : ZPoly × Nat)
    (hentry : entry ∈ (ZPoly.factorize integer).factors) :
    Irreducible (normalizedRatFactor entry.1) := by
  obtain ⟨hprimitive, hirreducibleInt, _⟩ :=
    (HexBerlekampZassenhausMathlib.factorize_normalized integer hinteger).2.1
      entry hentry
  have hprimitivePoly :
      (HexPolyZMathlib.toPolynomial entry.1).IsPrimitive :=
    HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive entry.1 hprimitive
  have hirreducibleRat :
      Irreducible (HexPolyZMathlib.toPolyℚ entry.1) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hprimitivePoly).mp hirreducibleInt
  have hentryNe : entry.1 ≠ 0 :=
    (HexBerlekampZassenhausMathlib.factorize_irreducible_of_nonUnit
      integer entry hentry).not_zero
  refine (scale_inv_associated entry.1.toRatPoly
    (toRatPoly_ne_zero hentryNe)).symm.irreducible ?_
  rw [HexPolyZMathlib.toPolynomial_toRatPoly]
  exact hirreducibleRat

private theorem rawRatFactor_irreducible (integer : ZPoly)
    (hinteger : integer ≠ 0) (entry : ZPoly × Nat)
    (hentry : entry ∈ (ZPoly.factorize integer).factors) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    let q := DensePoly.scale entry.1.toRatPoly.leadingCoeff⁻¹
      entry.1.toRatPoly
    Irreducible (HexPolyMathlib.toPolynomial
      (Factor.rawPoly [] (Factor.ofRatPoly q))) := by
  letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  let q := DensePoly.scale entry.1.toRatPoly.leadingCoeff⁻¹
    entry.1.toRatPoly
  dsimp only
  apply (MulEquiv.irreducible_iff
    (Polynomial.mapEquiv LevelSemantics.coeffRatEquiv).toMulEquiv).mp
  change Irreducible
    ((HexPolyMathlib.toPolynomial
      (Factor.rawPoly [] (Factor.ofRatPoly q))).map
        LevelSemantics.coeffRatEquiv.toRingHom)
  rw [LevelSemantics.map_rawPoly_nil, toRatPoly_ofRatPoly]
  exact normalizedRatFactor_irreducible integer hinteger entry hentry

set_option maxHeartbeats 800000 in
private theorem generatedRatFactors_sound (integer : ZPoly)
    (hinteger : integer ≠ 0) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    let rawFactors := (ZPoly.factorize integer).factors.flatMap fun entry =>
      Array.replicate entry.2 entry.1
    let factors := rawFactors.map fun factor =>
      let q := DensePoly.scale factor.toRatPoly.leadingCoeff⁻¹ factor.toRatPoly
      Factor.ofRatPoly q
    ∀ factor ∈ factors,
      Factor.polyCoords (Factor.rawPoly [] factor) = factor ∧
        Irreducible (HexPolyMathlib.toPolynomial
          (Factor.rawPoly [] factor)) := by
  letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  let rawFactors := (ZPoly.factorize integer).factors.flatMap fun entry =>
    Array.replicate entry.2 entry.1
  let factors := rawFactors.map fun factor =>
    let q := DensePoly.scale factor.toRatPoly.leadingCoeff⁻¹ factor.toRatPoly
    Factor.ofRatPoly q
  dsimp only
  intro factor hfactor
  obtain ⟨rawFactor, hrawFactor, rfl⟩ := Array.mem_map.mp hfactor
  have hrawList := Array.mem_toList_iff.mpr hrawFactor
  simp only [Array.toList_flatMap, List.mem_flatMap] at hrawList
  obtain ⟨entry, hentryList, hrawReplicate⟩ := hrawList
  have hrawEq : rawFactor = entry.1 := by
    have hrep : entry.2 ≠ 0 ∧ rawFactor = entry.1 := by
      simpa using hrawReplicate
    exact hrep.2
  subst rawFactor
  have hentry : entry ∈ (ZPoly.factorize integer).factors :=
    Array.mem_toList_iff.mp hentryList
  let q := DensePoly.scale entry.1.toRatPoly.leadingCoeff⁻¹
    entry.1.toRatPoly
  have hirreducible : Irreducible (HexPolyMathlib.toPolynomial
      (Factor.rawPoly [] (Factor.ofRatPoly q))) := by
    exact rawRatFactor_irreducible integer hinteger entry hentry
  have hq : q ≠ 0 := by
    intro hzero
    apply hirreducible.ne_zero
    apply (Polynomial.mapEquiv LevelSemantics.coeffRatEquiv).injective
    have hmapZero : (HexPolyMathlib.toPolynomial
        (Factor.rawPoly [] (Factor.ofRatPoly q))).map
          LevelSemantics.coeffRatEquiv.toRingHom = 0 := by
      rw [LevelSemantics.map_rawPoly_nil, toRatPoly_ofRatPoly, hzero,
        HexPolyMathlib.toPolynomial_zero]
    simpa using hmapZero
  exact ⟨polyCoords_rawPoly_ofRatPoly q hq, hirreducible⟩

set_option maxHeartbeats 800000 in
private theorem factorRat_mem_sound (input : DensePoly Rat)
    {factors : Array (Array (Array Rat))}
    (hresult : Factor.factorRat? input = some factors) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    ∀ factor ∈ factors,
      Factor.polyCoords (Factor.rawPoly [] factor) = factor ∧
        Irreducible (HexPolyMathlib.toPolynomial
          (Factor.rawPoly [] factor)) := by
  letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  intro factor hfactor
  simp only [Factor.factorRat?] at hresult
  split at hresult
  · cases hresult
    simp at hfactor
  · split at hresult
    · cases hresult
      simp at hfactor
    · split at hresult
      · split at hresult
        · cases hresult
          rename_i hinputZero hpZero hgcd hproduct
          let p := DensePoly.scale input.leadingCoeff⁻¹ input
          have hpNe : p ≠ 0 := by
            intro hzero
            have hpIsZero : p.isZero = true := by
              rw [DensePoly.isZero_eq_true_iff, hzero]
              rfl
            exact hpZero (by simpa [p] using hpIsZero)
          have hinteger : ZPoly.ratPolyPrimitivePart p ≠ 0 := by
            intro hzero
            obtain ⟨unit, hunit⟩ :=
              ZPoly.ratPolyPrimitivePart_rational_associate p
            apply hpNe
            rw [hunit]
            have hprimitiveZero :
                (ZPoly.ratPolyPrimitivePart p).toRatPoly = 0 := by
              rw [hzero]
              exact ZPoly.toRatPoly_zero
            rw [hprimitiveZero]
            simp
          have hsound := generatedRatFactors_sound
            (ZPoly.ratPolyPrimitivePart p) hinteger factor
          exact hsound (by simpa [p] using hfactor)
        · cases hresult
      · cases hresult

theorem factorSquarefree_mem_sound :
    ∀ (levels : List Level) (hvalid : LevelsValid levels)
      (hinjective : LevelSemantics.DenoteInjective levels)
      (f : Array (Array Rat)) {factors : Array (Array (Array Rat))},
      Factor.factorSquarefree? levels f = some factors →
      let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
      letI : Field (Arithmetic.Coeff levels) :=
        Norm.coeffFieldPoly levels hvalid hinjective hinv
      ∀ factor ∈ factors,
        Factor.polyCoords (Factor.rawPoly levels factor) = factor ∧
          Irreducible (HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels factor)) := by
  intro levels
  induction levels with
  | nil =>
      intro hvalid hinjective f factors hresult
      let hinv := LevelSemantics.coeffDenote_inv [] hvalid hinjective
      letI : Field (Arithmetic.Coeff []) :=
        Norm.coeffFieldPoly [] hvalid hinjective hinv
      have hvalidEq : hvalid = (trivial : LevelsValid []) :=
        Subsingleton.elim _ _
      have hinjectiveEq : hinjective = LevelSemantics.DenoteInjective.nil :=
        Subsingleton.elim _ _
      subst hvalid
      subst hinjective
      exact factorRat_mem_sound (Factor.toRatPoly f) hresult
  | cons level lower ih =>
      intro hvalid hinjectiveTop f factors hresult
      let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
      let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
        hinjectiveLower
      let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
        hinjectiveTop
      letI : Field (Arithmetic.Coeff lower) :=
        Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
      letI : Field (Arithmetic.Coeff (level :: lower)) :=
        Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
      dsimp only
      simp only [Factor.factorSquarefree?] at hresult
      split at hresult
      · rename_i hinputSquarefree
        obtain ⟨pair, hfind, hresult⟩ := Option.bind_eq_some_iff.mp hresult
        rcases pair with ⟨shift, norm⟩
        obtain ⟨lowerFactors, hlower, hresult⟩ :=
          Option.bind_eq_some_iff.mp hresult
        split at hresult
        · cases hresult
          intro factor hfactor
          have hlower' : Factor.factorSquarefree? lower norm =
              some lowerFactors := by simpa using hlower
          have hlowerSound : ∀ lowerFactor ∈ lowerFactors,
              Factor.polyCoords (Factor.rawPoly lower lowerFactor) =
                  lowerFactor ∧
                Irreducible (HexPolyMathlib.toPolynomial
                  (Factor.rawPoly lower lowerFactor)) := by
            exact ih hvalid.2.2 hinjectiveLower norm hlower'
          have hnormCheck : Norm.isSquarefree lower norm :=
            findSquarefreeShift_squarefree level lower f (by simpa using hfind)
          have hnormSquarefree : Squarefree
              (HexPolyMathlib.toPolynomial
                (Factor.rawPoly lower norm)) :=
            squarefree_toPolynomial_of_check lower hvalid.2.2
              hinjectiveLower hinvLower norm hnormCheck
          have hnormEq : norm = Norm.oneLevel level lower f shift :=
            findSquarefreeShift_norm level lower f (by simpa using hfind)
          have htragerSquarefree : Squarefree
              (HexPolyMathlib.toPolynomial
                (tragerNorm level lower
                  (Factor.rawPoly (level :: lower)
                    (Factor.shiftTop level lower f shift)))) := by
            rw [tragerNorm_shiftTop level lower hvalid hinjectiveTop,
              ← hnormEq]
            exact hnormSquarefree
          exact recover_mem_sound level lower hvalid hinjectiveTop f shift
            lowerFactors htragerSquarefree hlowerSound factor hfactor
        · contradiction
      · contradiction

private theorem polynomial_map_list_prod {R S : Type*}
    [Semiring R] [Semiring S] (f : R →+* S)
    (ps : List (Polynomial R)) :
    ps.prod.map f = (ps.map fun p => p.map f).prod := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

private theorem rawPoly_nil_eq_zero_iff (f : Array (Array Rat)) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    Factor.rawPoly [] f = 0 ↔ Factor.toRatPoly f = 0 := by
  letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  constructor
  · intro h
    have hmap := LevelSemantics.map_rawPoly_nil f
    rw [h, HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero] at hmap
    apply (HexPolyMathlib.equiv (R := Rat)).injective
    simpa using hmap.symm
  · intro h
    apply (HexPolyMathlib.equiv (R := Arithmetic.Coeff [])).injective
    change HexPolyMathlib.toPolynomial (Factor.rawPoly [] f) = 0
    apply Polynomial.map_injective LevelSemantics.coeffRatEquiv.toRingHom
      LevelSemantics.coeffRatEquiv.injective
    rw [LevelSemantics.map_rawPoly_nil, h,
      HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero]

private theorem map_monic_rawPoly_nil (f : Array (Array Rat)) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    (HexPolyMathlib.toPolynomial
      (Norm.monic (Factor.rawPoly [] f))).map
        LevelSemantics.coeffRatEquiv.toRingHom =
      HexPolyMathlib.toPolynomial
        (let p := Factor.toRatPoly f
         if p.isZero then 0 else DensePoly.scale p.leadingCoeff⁻¹ p) := by
  letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  let raw := Factor.rawPoly [] f
  let p := Factor.toRatPoly f
  have hmap : (HexPolyMathlib.toPolynomial raw).map
      LevelSemantics.coeffRatEquiv.toRingHom =
        HexPolyMathlib.toPolynomial p := by
    exact LevelSemantics.map_rawPoly_nil f
  have hzero : raw = 0 ↔ p = 0 := by
    constructor
    · intro h
      have := hmap
      rw [h, HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero] at this
      apply (HexPolyMathlib.equiv (R := Rat)).injective
      simpa using this.symm
    · intro h
      apply (HexPolyMathlib.equiv (R := Arithmetic.Coeff [])).injective
      change HexPolyMathlib.toPolynomial raw = 0
      apply Polynomial.map_injective LevelSemantics.coeffRatEquiv.toRingHom
        LevelSemantics.coeffRatEquiv.injective
      rw [hmap, h, HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero]
  have hlc : LevelSemantics.coeffRatEquiv raw.leadingCoeff =
      p.leadingCoeff := by
    change LevelSemantics.coeffRatEquiv.toRingHom raw.leadingCoeff = _
    rw [← HexPolyMathlib.leadingCoeff_toPolynomial raw,
      ← Polynomial.leadingCoeff_map_of_injective
        LevelSemantics.coeffRatEquiv.injective, hmap,
      HexPolyMathlib.leadingCoeff_toPolynomial p]
  simp only [Norm.monic]
  split
  · rename_i hrawZero
    change raw.isZero = true at hrawZero
    have hpZero : p.isZero = true := by
      rw [DensePoly.isZero_eq_true_iff, DensePoly.size_eq_zero_iff,
        ← hzero, ← DensePoly.size_eq_zero_iff,
        ← DensePoly.isZero_eq_true_iff]
      exact hrawZero
    rw [hpZero]
    simp only [if_true]
    have hraw : raw = 0 :=
      (DensePoly.size_eq_zero_iff raw).mp
        ((DensePoly.isZero_eq_true_iff raw).mp hrawZero)
    simp
  · rename_i hrawZero
    change ¬ raw.isZero = true at hrawZero
    have hpZero : p.isZero = false := by
      rw [DensePoly.isZero_eq_false_iff]
      exact Nat.pos_of_ne_zero fun hpSize => by
        apply hrawZero
        rw [DensePoly.isZero_eq_true_iff, DensePoly.size_eq_zero_iff,
          hzero, ← DensePoly.size_eq_zero_iff]
        exact hpSize
    rw [hpZero]
    simp only [Bool.false_eq_true, if_false]
    change (HexPolyMathlib.toPolynomial
        (DensePoly.scale raw.leadingCoeff⁻¹ raw)).map
          LevelSemantics.coeffRatEquiv.toRingHom =
      HexPolyMathlib.toPolynomial (DensePoly.scale p.leadingCoeff⁻¹ p)
    rw [HexPolyMathlib.toPolynomial_scale,
      HexPolyMathlib.toPolynomial_scale, Polynomial.map_mul,
      Polynomial.map_C, map_inv₀]
    have hlc' : LevelSemantics.coeffRatEquiv.toRingHom raw.leadingCoeff =
        p.leadingCoeff := hlc
    rw [hlc', hmap]

private theorem rawFactorFoldl (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (factors : List (Array (Array Rat)))
    (init : DensePoly (Arithmetic.Coeff levels)) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    HexPolyMathlib.toPolynomial
        (factors.foldl (fun product factor =>
          product * Factor.rawPoly levels factor) init) =
      HexPolyMathlib.toPolynomial init *
        (factors.map fun factor => HexPolyMathlib.toPolynomial
          (R := Arithmetic.Coeff levels)
          (Factor.rawPoly levels factor)).prod := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction factors generalizing init with
  | nil => simp
  | cons factor factors ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.prod_cons,
        HexPolyMathlib.toPolynomial_mul]
      ring

private theorem ratFactorFoldl (factors : List (Array (Array Rat)))
    (init : DensePoly Rat) :
    HexPolyMathlib.toPolynomial
        (factors.foldl (fun product factor =>
          product * Factor.toRatPoly factor) init) =
      HexPolyMathlib.toPolynomial init *
        (factors.map fun factor => HexPolyMathlib.toPolynomial
          (Factor.toRatPoly factor)).prod := by
  induction factors generalizing init with
  | nil => simp
  | cons factor factors ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.prod_cons,
        HexPolyMathlib.toPolynomial_mul]
      ring

theorem factorSquarefree_product (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat)) {factors : Array (Array (Array Rat))}
    (hf : Factor.rawPoly levels f ≠ 0)
    (hresult : Factor.factorSquarefree? levels f = some factors) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    (factors.toList.map fun factor => HexPolyMathlib.toPolynomial
      (Factor.rawPoly levels factor)).prod =
        HexPolyMathlib.toPolynomial
          (Norm.monic (Factor.rawPoly levels f)) := by
  cases levels with
  | nil =>
      letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil
      dsimp only
      have hinputNe : Factor.toRatPoly f ≠ 0 :=
        mt (rawPoly_nil_eq_zero_iff f).mpr hf
      have hinputZero : (Factor.toRatPoly f).isZero = false := by
        rw [DensePoly.isZero_eq_false_iff]
        exact Nat.pos_of_ne_zero fun hsize =>
          hinputNe ((DensePoly.size_eq_zero_iff _).mp hsize)
      let p := DensePoly.scale (Factor.toRatPoly f).leadingCoeff⁻¹
        (Factor.toRatPoly f)
      have hpNe : p ≠ 0 := by
        intro hzero
        have hpoly := congrArg HexPolyMathlib.toPolynomial hzero
        rw [HexPolyMathlib.toPolynomial_scale,
          HexPolyMathlib.toPolynomial_zero] at hpoly
        have hleadingNe : (Factor.toRatPoly f).leadingCoeff ≠ 0 :=
          DensePoly.leadingCoeff_ne_zero_of_pos_size _
            ((DensePoly.isZero_eq_false_iff _).mp hinputZero)
        have hinputPoly : HexPolyMathlib.toPolynomial
            (Factor.toRatPoly f) = 0 :=
          (mul_eq_zero.mp hpoly).resolve_left
            (Polynomial.C_ne_zero.mpr (inv_ne_zero hleadingNe))
        apply hinputNe
        apply (HexPolyMathlib.equiv (R := Rat)).injective
        simpa using hinputPoly
      simp only [Factor.factorSquarefree?] at hresult
      simp only [Factor.factorRat?] at hresult
      split at hresult
      · cases hresult
        exfalso
        apply hf
        have hp : Factor.toRatPoly f = 0 :=
          (DensePoly.size_eq_zero_iff _).mp
            ((DensePoly.isZero_eq_true_iff _).mp ‹_›)
        exact (rawPoly_nil_eq_zero_iff f).mpr hp
      · split at hresult
        · cases hresult
          exfalso
          apply hf
          have hpZero : p = 0 := by
            apply (DensePoly.size_eq_zero_iff _).mp
            exact (DensePoly.isZero_eq_true_iff _).mp ‹_›
          exact (hpNe hpZero).elim
        · split at hresult
          · split at hresult
            · rename_i hinputZero hpZero hgcd hproduct
              cases hresult
              have hmappedList (xs : List (Array (Array Rat))) :
                  (xs.map fun factor => HexPolyMathlib.toPolynomial
                    (Factor.rawPoly [] factor)).map
                      (fun q => q.map
                        LevelSemantics.coeffRatEquiv.toRingHom) =
                    xs.map fun factor => HexPolyMathlib.toPolynomial
                      (Factor.toRatPoly factor) := by
                rw [List.map_map]
                apply List.map_congr_left
                intro factor hfactor
                exact LevelSemantics.map_rawPoly_nil factor
              apply Polynomial.map_injective
                LevelSemantics.coeffRatEquiv.toRingHom
                LevelSemantics.coeffRatEquiv.injective
              rw [polynomial_map_list_prod, hmappedList,
                map_monic_rawPoly_nil, if_neg hinputZero]
              have hpoly := congrArg HexPolyMathlib.toPolynomial hproduct
              rw [← Array.foldl_toList,
                ratFactorFoldl] at hpoly
              simpa using hpoly
            · cases hresult
          · cases hresult
  | cons level lower =>
      let hinv := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
        hinjective
      letI : Field (Arithmetic.Coeff (level :: lower)) :=
        Norm.coeffFieldPoly (level :: lower) hvalid hinjective hinv
      dsimp only
      simp only [Factor.factorSquarefree?] at hresult
      split at hresult
      · obtain ⟨pair, hfind, hresult⟩ := Option.bind_eq_some_iff.mp hresult
        obtain ⟨lowerFactors, hlower, hresult⟩ :=
          Option.bind_eq_some_iff.mp hresult
        split at hresult
        · rename_i hcheck
          cases hresult
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
          have hproduct := hcheck.2
          rw [← Array.foldl_toList] at hproduct
          have hpoly := congrArg HexPolyMathlib.toPolynomial hproduct
          rw [rawFactorFoldl (level :: lower) hvalid hinjective hinv] at hpoly
          simpa using hpoly
        · contradiction
      · contradiction

private theorem gcd_prod_associated {K : Type*} [Field K] [DecidableEq K]
    (P : Polynomial K) : ∀ qs : List (Polynomial K),
    Squarefree qs.prod →
    Associated (gcd P qs.prod)
      ((qs.map fun q => gcd P q).prod) := by
  intro qs
  induction qs with
  | nil =>
      intro hsquarefree
      simp
  | cons q qs ih =>
      intro hsquarefree
      have hparts := squarefree_mul_iff.mp hsquarefree
      have htail := ih hparts.2.2
      let gq := gcd P q
      let gt := gcd P qs.prod
      have hrel : IsRelPrime gq gt :=
        (hparts.1.of_dvd_left (gcd_dvd_right P q)).of_dvd_right
          (gcd_dvd_right P qs.prod)
      have hcop : IsCoprime gq gt := hrel.isCoprime
      have hforward : gcd P (q * qs.prod) ∣ gq * gt := by
        exact gcd_mul_dvd_mul_gcd P q qs.prod
      have hback : gq * gt ∣ gcd P (q * qs.prod) := by
        apply dvd_gcd
        · exact hcop.mul_dvd (gcd_dvd_left P q)
            (gcd_dvd_left P qs.prod)
        · exact mul_dvd_mul (gcd_dvd_right P q)
            (gcd_dvd_right P qs.prod)
      have hstep : Associated (gcd P (q * qs.prod))
          (gq * gt) := associated_of_dvd_dvd hforward hback
      simpa [gq, gt] using hstep.trans
        ((Associated.refl (gcd P q)).mul_mul htail)

private theorem prod_gcd_associated {K : Type*} [Field K] [DecidableEq K]
    (P : Polynomial K) (qs : List (Polynomial K))
    (hsquarefree : Squarefree qs.prod) (hdiv : P ∣ qs.prod) :
    Associated ((qs.map fun q => gcd P q).prod) P := by
  have h := (gcd_prod_associated P qs hsquarefree).symm
  have hgcd : gcd P qs.prod = normalize P :=
    gcd_eq_normalize (gcd_dvd_left P qs.prod) (dvd_gcd dvd_rfl hdiv)
  rw [hgcd] at h
  exact h.trans (associated_normalize P).symm

private theorem euclidean_gcd_associated_gcd {K : Type*} [Field K]
    [DecidableEq K]
    (a b : Polynomial K) :
    Associated (EuclideanDomain.gcd a b) (gcd a b) := by
  apply associated_of_dvd_dvd
  · apply dvd_gcd
    · exact EuclideanDomain.gcd_dvd_left a b
    · exact EuclideanDomain.gcd_dvd_right a b
  · apply EuclideanDomain.dvd_gcd
    · exact gcd_dvd_left a b
    · exact gcd_dvd_right a b

set_option maxHeartbeats 800000 in
private theorem recover_product_associated (level : Level)
    (lower : List Level) (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (component : Array (Array Rat)) (shift : Int)
    (lowerFactors : Array (Array (Array Rat)))
    (hcomponentNe : Factor.rawPoly (level :: lower) component ≠ 0) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    let delta := Arithmetic.Coeff.ofData (level :: lower) #[(shift : Rat)] *
      Factor.topGenerator level lower
    let shifted := Factor.rawPoly (level :: lower)
      (Factor.shiftTop level lower component shift)
    let lifted (lowerFactor : Array (Array Rat)) :=
      Factor.rawPoly (level :: lower)
        (Factor.embedLower level lower lowerFactor)
    Associated
      (Polynomial.taylor (-delta)
        ((Factor.recover level lower shift component lowerFactors).toList.map
          fun factor => HexPolyMathlib.toPolynomial
            (Factor.rawPoly (level :: lower) factor)).prod)
      ((lowerFactors.toList.map fun lowerFactor =>
        EuclideanDomain.gcd (HexPolyMathlib.toPolynomial shifted)
          (HexPolyMathlib.toPolynomial (lifted lowerFactor))).prod) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let delta := Arithmetic.Coeff.ofData (level :: lower) #[(shift : Rat)] *
    Factor.topGenerator level lower
  let shifted := Factor.rawPoly (level :: lower)
    (Factor.shiftTop level lower component shift)
  let lifted (lowerFactor : Array (Array Rat)) :=
    Factor.rawPoly (level :: lower)
      (Factor.embedLower level lower lowerFactor)
  let g (lowerFactor : Array (Array Rat)) :=
    DensePoly.gcd shifted (lifted lowerFactor)
  let common (lowerFactor : Array (Array Rat)) := Norm.monic (g lowerFactor)
  let pass (lowerFactor : Array (Array Rat)) :=
    0 < (common lowerFactor).degree?.getD 0
  let unshifted (lowerFactor : Array (Array Rat)) :=
    Factor.rawPoly (level :: lower)
      (Factor.shiftTop level lower (Factor.polyCoords (common lowerFactor))
        (-shift))
  let result (lowerFactor : Array (Array Rat)) :=
    Norm.monic (unshifted lowerFactor)
  let recovered (lowerFactor : Array (Array Rat)) :=
    Factor.polyCoords (result lowerFactor)
  dsimp only
  have hcomponentPolyNe : HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower) component) ≠ 0 := by
    intro hzero
    apply hcomponentNe
    apply (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff (level :: lower))).injective
    simpa using hzero
  have hshiftedPolyNe : HexPolyMathlib.toPolynomial shifted ≠ 0 := by
    change HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower component shift)) ≠ 0
    rw [toPolynomial_shiftTop level lower hvalid hinjectiveTop]
    intro hzero
    have hback := congrArg (Polynomial.taylor delta) hzero
    apply hcomponentPolyNe
    simpa [delta, Polynomial.taylor_taylor] using hback
  have hgNe (lowerFactor : Array (Array Rat)) : g lowerFactor ≠ 0 := by
    have hassociated := HexPolyMathlib.toPolynomial_gcd_associated
      shifted (lifted lowerFactor)
    have hgcdNe : EuclideanDomain.gcd
        (HexPolyMathlib.toPolynomial shifted)
        (HexPolyMathlib.toPolynomial (lifted lowerFactor)) ≠ 0 := by
      intro hzero
      exact hshiftedPolyNe
        (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
    have hpolyNe : HexPolyMathlib.toPolynomial (g lowerFactor) ≠ 0 :=
      hassociated.ne_zero_iff.mpr hgcdNe
    intro hzero
    apply hpolyNe
    simp [g, hzero]
  have hcommonPolyNe (lowerFactor : Array (Array Rat)) :
      HexPolyMathlib.toPolynomial (common lowerFactor) ≠ 0 :=
    (toPolynomial_monic_monic (level :: lower) hvalid hinjectiveTop hinvTop
      (g lowerFactor) (hgNe lowerFactor)).ne_zero
  have hcommonAssoc (lowerFactor : Array (Array Rat)) : Associated
      (HexPolyMathlib.toPolynomial (common lowerFactor))
      (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial shifted)
        (HexPolyMathlib.toPolynomial (lifted lowerFactor))) :=
    (toPolynomial_monic_associated (level :: lower) hvalid
      hinjectiveTop hinvTop (g lowerFactor) (hgNe lowerFactor)).trans
        (HexPolyMathlib.toPolynomial_gcd_associated shifted
          (lifted lowerFactor))
  have hunshiftedPoly (lowerFactor : Array (Array Rat)) :
      HexPolyMathlib.toPolynomial (unshifted lowerFactor) =
        Polynomial.taylor delta
          (HexPolyMathlib.toPolynomial (common lowerFactor)) := by
    change HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower (Factor.polyCoords (common lowerFactor))
          (-shift))) = _
    rw [toPolynomial_shiftTop level lower hvalid hinjectiveTop,
      rawPoly_polyCoords]
    have hdelta := shiftDelta_neg level lower hvalid hinjectiveTop shift
    simpa only [Int.cast_neg] using congrArg
      (fun c => Polynomial.taylor c
        (HexPolyMathlib.toPolynomial (common lowerFactor))) hdelta
  have hunshiftedNe (lowerFactor : Array (Array Rat)) :
      unshifted lowerFactor ≠ 0 := by
    intro hzero
    have hpolyZero : Polynomial.taylor delta
        (HexPolyMathlib.toPolynomial (common lowerFactor)) = 0 := by
      rw [← hunshiftedPoly lowerFactor, hzero]
      exact HexPolyMathlib.toPolynomial_zero
    have hback := congrArg (Polynomial.taylor (-delta)) hpolyZero
    apply hcommonPolyNe lowerFactor
    simpa [Polynomial.taylor_taylor] using hback
  have hpass (lowerFactor : Array (Array Rat))
      (_hpass : pass lowerFactor) : Associated
      (Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial (result lowerFactor)))
      (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial shifted)
        (HexPolyMathlib.toPolynomial (lifted lowerFactor))) := by
    have hnormalized := toPolynomial_monic_associated (level :: lower)
      hvalid hinjectiveTop hinvTop (unshifted lowerFactor)
        (hunshiftedNe lowerFactor)
    have hmapped := hnormalized.map
      (Polynomial.taylorEquiv (-delta)).toMonoidHom
    change Associated
      (Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial (Norm.monic (unshifted lowerFactor))))
      (Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial (unshifted lowerFactor))) at hmapped
    have htaylor : Associated
        (Polynomial.taylor (-delta)
          (HexPolyMathlib.toPolynomial (result lowerFactor)))
        (HexPolyMathlib.toPolynomial (common lowerFactor)) := by
      change Associated
        (Polynomial.taylor (-delta)
          (HexPolyMathlib.toPolynomial (Norm.monic (unshifted lowerFactor))))
        (HexPolyMathlib.toPolynomial (common lowerFactor))
      rw [hunshiftedPoly lowerFactor] at hmapped
      simpa [Polynomial.taylor_taylor] using hmapped
    exact htaylor.trans (hcommonAssoc lowerFactor)
  have hskip (lowerFactor : Array (Array Rat))
      (hskip : ¬ pass lowerFactor) : IsUnit
      (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial shifted)
        (HexPolyMathlib.toPolynomial (lifted lowerFactor))) := by
    apply (hcommonAssoc lowerFactor).isUnit_iff.mp
    apply Polynomial.isUnit_iff_degree_eq_zero.mpr
    rw [Polynomial.degree_eq_natDegree (hcommonPolyNe lowerFactor),
      HexPolyMathlib.natDegree_toPolynomial]
    have hdegree : (common lowerFactor).degree?.getD 0 = 0 :=
      Nat.eq_zero_of_not_pos hskip
    rw [hdegree]
    rfl
  have hfiltered := filterMap_prod_associated pass
    (fun lowerFactor => Polynomial.taylor (-delta)
      (HexPolyMathlib.toPolynomial (result lowerFactor)))
    (fun lowerFactor => EuclideanDomain.gcd
      (HexPolyMathlib.toPolynomial shifted)
      (HexPolyMathlib.toPolynomial (lifted lowerFactor)))
    hpass hskip lowerFactors.toList
  have hrecoverList :
      (Factor.recover level lower shift component lowerFactors).toList =
        lowerFactors.toList.filterMap (fun lowerFactor =>
          if pass lowerFactor then some (recovered lowerFactor) else none) := by
    have hfold := foldl_push_if_toList pass recovered
      lowerFactors.toList (#[] : Array (Array (Array Rat)))
    simpa only [Factor.recover, Array.foldl_toList, List.nil_append,
      shifted, lifted, g, common, pass, unshifted, result, recovered] using hfold
  rw [taylor_list_prod, hrecoverList]
  simpa [List.map_filterMap, Function.comp_def, recovered,
    rawPoly_polyCoords, delta, shifted, lifted] using hfiltered

private theorem recover_product_monic (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (component : Array (Array Rat)) (shift : Int)
    (lowerFactors : Array (Array (Array Rat))) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    (∀ factor ∈ Factor.recover level lower shift component lowerFactors,
      Irreducible (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor))) →
    ((Factor.recover level lower shift component lowerFactors).toList.map
      fun factor => HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor)).prod.Monic := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  dsimp only
  intro hsound
  let allFactors :=
    (Factor.recover level lower shift component lowerFactors).toList
  have go : ∀ factors : List (Array (Array Rat)),
      (∀ factor ∈ factors, factor ∈ allFactors) →
      (factors.map fun factor => HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor)).prod.Monic := by
    intro factors hmem
    induction factors with
    | nil => simp
    | cons factor factors ih =>
      rw [List.map_cons, List.prod_cons]
      have hfactorMem : factor ∈
          Factor.recover level lower shift component lowerFactors := by
        exact Array.mem_toList_iff.mp (hmem factor (by simp))
      obtain ⟨lowerFactor, hlowerFactor, hdegree, hrecovered⟩ :=
        recover_mem level lower shift component lowerFactors hfactorMem
      let shifted := Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower component shift)
      let lifted := Factor.rawPoly (level :: lower)
        (Factor.embedLower level lower lowerFactor)
      let common := Norm.monic (DensePoly.gcd shifted lifted)
      let unshifted := Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower (Factor.polyCoords common) (-shift))
      have hirreducible := hsound factor hfactorMem
      have hunshiftedNe : unshifted ≠ 0 := by
        intro hzero
        apply hirreducible.ne_zero
        rw [← hrecovered, rawPoly_polyCoords]
        change HexPolyMathlib.toPolynomial (Norm.monic unshifted) = 0
        rw [hzero]
        simp [Norm.monic]
      have hfactorMonic : (HexPolyMathlib.toPolynomial
          (Factor.rawPoly (level :: lower) factor)).Monic := by
        rw [← hrecovered, rawPoly_polyCoords]
        change (HexPolyMathlib.toPolynomial (Norm.monic unshifted)).Monic
        exact toPolynomial_monic_monic (level :: lower) hvalid
          hinjectiveTop hinvTop unshifted hunshiftedNe
      exact hfactorMonic.mul (ih (fun candidate hc =>
        hmem candidate (by simp [hc])))
  exact go allFactors (fun factor hfactor => hfactor)

set_option maxHeartbeats 800000 in
private theorem recover_product (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (component norm : Array (Array Rat)) (shift : Int)
    (lowerFactors : Array (Array (Array Rat))) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    Factor.rawPoly (level :: lower) component ≠ 0 →
    Squarefree (HexPolyMathlib.toPolynomial (Factor.rawPoly lower norm)) →
    norm = Norm.oneLevel level lower component shift →
    (∀ lowerFactor ∈ lowerFactors,
      Factor.polyCoords (Factor.rawPoly lower lowerFactor) = lowerFactor) →
    ((lowerFactors.toList.map fun lowerFactor =>
      HexPolyMathlib.toPolynomial
        (Factor.rawPoly lower lowerFactor)).prod =
      HexPolyMathlib.toPolynomial
        (Norm.monic (Factor.rawPoly lower norm))) →
    (∀ factor ∈ Factor.recover level lower shift component lowerFactors,
      Irreducible (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor))) →
    ((Factor.recover level lower shift component lowerFactors).toList.map
      fun factor => HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor)).prod =
      HexPolyMathlib.toPolynomial
        (Norm.monic (Factor.rawPoly (level :: lower) component)) := by
  classical
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  dsimp only
  intro hcomponentNe hnormSquarefree hnormEq hlowerCoords hlowerProduct
    hrecoverSound
  let φ := Norm.lowerHom level lower hvalid hinjectiveTop
  let lowerPolys := lowerFactors.toList.map fun lowerFactor =>
    HexPolyMathlib.toPolynomial (Factor.rawPoly lower lowerFactor)
  let shifted := Factor.rawPoly (level :: lower)
    (Factor.shiftTop level lower component shift)
  let lifted (lowerFactor : Array (Array Rat)) :=
    Factor.rawPoly (level :: lower)
      (Factor.embedLower level lower lowerFactor)
  let qs := lowerFactors.toList.map fun lowerFactor =>
    HexPolyMathlib.toPolynomial (lifted lowerFactor)
  let recoveredProduct :=
    ((Factor.recover level lower shift component lowerFactors).toList.map
      fun factor => HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor)).prod
  let delta := Arithmetic.Coeff.ofData (level :: lower) #[(shift : Rat)] *
    Factor.topGenerator level lower
  let ιLower := LevelSemantics.coeffHom lower hvalid.2.2
    hinjectiveLower hinvLower
  let ιTop := LevelSemantics.coeffHom (level :: lower) hvalid
    hinjectiveTop hinvTop
  letI : CharZero (Arithmetic.Coeff lower) :=
    { cast_injective := by
        intro m n hmn
        apply Nat.cast_injective (R := ℂ)
        have hmapped := congrArg ιLower hmn
        simpa only [map_natCast] using hmapped }
  letI : CharZero (Arithmetic.Coeff (level :: lower)) :=
    { cast_injective := by
        intro m n hmn
        apply Nat.cast_injective (R := ℂ)
        have hmapped := congrArg ιTop hmn
        simpa only [map_natCast] using hmapped }
  have hnormNe : Factor.rawPoly lower norm ≠ 0 := by
    intro hzero
    apply hnormSquarefree.ne_zero
    rw [hzero]
    exact HexPolyMathlib.toPolynomial_zero
  have hnormAssoc : Associated
      (HexPolyMathlib.toPolynomial
        (Norm.monic (Factor.rawPoly lower norm)))
      (HexPolyMathlib.toPolynomial (Factor.rawPoly lower norm)) :=
    toPolynomial_monic_associated lower hvalid.2.2 hinjectiveLower
      hinvLower (Factor.rawPoly lower norm) hnormNe
  have hnormMonicSquarefree : Squarefree
      (HexPolyMathlib.toPolynomial
        (Norm.monic (Factor.rawPoly lower norm))) :=
    hnormAssoc.squarefree_iff.mpr hnormSquarefree
  have hlifted (lowerFactor : Array (Array Rat))
      (hlowerFactor : lowerFactor ∈ lowerFactors) :
      HexPolyMathlib.toPolynomial (lifted lowerFactor) =
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly lower lowerFactor)).map φ := by
    let q := Factor.rawPoly lower lowerFactor
    have hcoords : Factor.polyCoords q = lowerFactor :=
      hlowerCoords lowerFactor hlowerFactor
    calc
      HexPolyMathlib.toPolynomial (lifted lowerFactor) =
          HexPolyMathlib.toPolynomial
            (Factor.rawPoly (level :: lower)
              (Factor.embedLower level lower (Factor.polyCoords q))) := by
        rw [hcoords]
      _ = (HexPolyMathlib.toPolynomial q).map
          (Norm.lowerHom level lower hvalid hinjectiveTop) := by
        rw [rawPoly_embedLower_polyCoords level lower hvalid hinjectiveTop,
          HexPolyMathlib.toPolynomial_ofPolynomial]
      _ = (HexPolyMathlib.toPolynomial
          (Factor.rawPoly lower lowerFactor)).map φ := rfl
  have hqs : qs.prod =
      (HexPolyMathlib.toPolynomial
        (Norm.monic (Factor.rawPoly lower norm))).map φ := by
    have hlist : qs = lowerPolys.map fun p => p.map φ := by
      dsimp only [qs, lowerPolys]
      rw [List.map_map]
      apply List.map_congr_left
      intro lowerFactor hlowerFactor
      exact hlifted lowerFactor (Array.mem_toList_iff.mp hlowerFactor)
    calc
      qs.prod = (lowerPolys.map fun p => p.map φ).prod :=
        congrArg List.prod hlist
      _ = lowerPolys.prod.map φ :=
        (polynomial_map_list_prod φ lowerPolys).symm
      _ = (HexPolyMathlib.toPolynomial
          (Norm.monic (Factor.rawPoly lower norm))).map φ := by
        rw [show lowerPolys.prod = HexPolyMathlib.toPolynomial
          (Norm.monic (Factor.rawPoly lower norm)) by
            exact hlowerProduct]
  have hqsSquarefree : Squarefree qs.prod := by
    rw [hqs]
    exact polynomial_squarefree_map φ hnormMonicSquarefree
  have hshiftedDvd : HexPolyMathlib.toPolynomial shifted ∣ qs.prod := by
    have hdiv := Norm.shifted_dvd_norm level lower hvalid hinjectiveTop
      component shift
    rw [← hnormEq] at hdiv
    have hnormDvdMonic :
        (HexPolyMathlib.toPolynomial (Factor.rawPoly lower norm)).map φ ∣
          (HexPolyMathlib.toPolynomial
            (Norm.monic (Factor.rawPoly lower norm))).map φ := by
      obtain ⟨u, hu⟩ := hnormAssoc.symm.dvd
      refine ⟨u.map φ, ?_⟩
      rw [hu, Polynomial.map_mul]
    rw [hqs]
    exact hdiv.trans hnormDvdMonic
  have hgcdProduct := prod_gcd_associated
    (HexPolyMathlib.toPolynomial shifted) qs hqsSquarefree hshiftedDvd
  have hgcdBridge : Associated
      ((lowerFactors.toList.map fun lowerFactor =>
        EuclideanDomain.gcd (HexPolyMathlib.toPolynomial shifted)
          (HexPolyMathlib.toPolynomial (lifted lowerFactor))).prod)
      ((qs.map fun q => gcd (HexPolyMathlib.toPolynomial shifted) q).prod) := by
    have go : ∀ items : List
        (Polynomial (Arithmetic.Coeff (level :: lower))),
        Associated
          ((items.map fun q => EuclideanDomain.gcd
            (HexPolyMathlib.toPolynomial shifted) q).prod)
          ((items.map fun q => gcd
            (HexPolyMathlib.toPolynomial shifted) q).prod) := by
      intro items
      induction items with
      | nil => simp
      | cons q items ih =>
          simp only [List.map_cons, List.prod_cons]
          exact (euclidean_gcd_associated_gcd
            (HexPolyMathlib.toPolynomial shifted) q).mul_mul ih
    simpa [qs, List.map_map, Function.comp_def] using go qs
  have hrecoverAssoc := recover_product_associated level lower hvalid
    hinjectiveTop component shift lowerFactors hcomponentNe
  have hshiftedAssoc : Associated
      (Polynomial.taylor (-delta) recoveredProduct)
      (HexPolyMathlib.toPolynomial shifted) := by
    exact hrecoverAssoc.trans (hgcdBridge.trans hgcdProduct)
  have hshiftedEq : HexPolyMathlib.toPolynomial shifted =
      Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly (level :: lower) component)) := by
    exact toPolynomial_shiftTop level lower hvalid hinjectiveTop
      component shift
  rw [hshiftedEq] at hshiftedAssoc
  have hback := hshiftedAssoc.map
    (Polynomial.taylorEquiv delta).toMonoidHom
  change Associated
    (Polynomial.taylor delta
      (Polynomial.taylor (-delta) recoveredProduct))
    (Polynomial.taylor delta
      (Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly (level :: lower) component)))) at hback
  have hrecoveredAssoc : Associated recoveredProduct
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) component)) := by
    simpa [Polynomial.taylor_taylor] using hback
  have hrecoveredMonic : recoveredProduct.Monic :=
    recover_product_monic level lower hvalid hinjectiveTop component shift
      lowerFactors hrecoverSound
  have hcomponentMonic := toPolynomial_monic_monic (level :: lower)
    hvalid hinjectiveTop hinvTop (Factor.rawPoly (level :: lower) component)
      hcomponentNe
  have hcomponentAssoc := toPolynomial_monic_associated (level :: lower)
    hvalid hinjectiveTop hinvTop (Factor.rawPoly (level :: lower) component)
      hcomponentNe
  exact Polynomial.eq_of_monic_of_associated hrecoveredMonic hcomponentMonic
    (hrecoveredAssoc.trans hcomponentAssoc.symm)

private theorem normalizedRatFactorFoldl (factors : List ZPoly)
    (init : DensePoly Rat) :
    HexPolyMathlib.toPolynomial
        (factors.foldl (fun product factor => product *
          DensePoly.scale factor.toRatPoly.leadingCoeff⁻¹
            factor.toRatPoly) init) =
      HexPolyMathlib.toPolynomial init *
        (factors.map normalizedRatFactor).prod := by
  induction factors generalizing init with
  | nil => simp
  | cons factor factors ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.prod_cons, normalizedRatFactor,
        HexPolyMathlib.toPolynomial_mul]
      ring

private theorem factorRat_product (p : DensePoly Rat) (hp : p ≠ 0)
    (hpMonic : (HexPolyMathlib.toPolynomial p).Monic) :
    let integer := ZPoly.ratPolyPrimitivePart p
    let rawFactors := (ZPoly.factorize integer).factors.flatMap fun entry =>
      Array.replicate entry.2 entry.1
    let factors := rawFactors.map fun factor =>
      let q := ZPoly.toRatPoly factor
      let q := DensePoly.scale q.leadingCoeff⁻¹ q
      Factor.ofRatPoly q
    factors.foldl
      (fun product factor => product * Factor.toRatPoly factor) 1 = p := by
  let integer := ZPoly.ratPolyPrimitivePart p
  have hintegerNe : integer ≠ 0 := by
    intro hzero
    obtain ⟨unit, hunit⟩ :=
      ZPoly.ratPolyPrimitivePart_rational_associate p
    apply hp
    rw [hunit]
    have hprimitiveZero :
        (ZPoly.ratPolyPrimitivePart p).toRatPoly = 0 := by
      rw [← show integer = ZPoly.ratPolyPrimitivePart p from rfl, hzero]
      exact ZPoly.toRatPoly_zero
    rw [hprimitiveZero]
    simp
  let rawFactors := (ZPoly.factorize integer).factors.flatMap fun entry =>
    Array.replicate entry.2 entry.1
  let normalized (factor : ZPoly) :=
    DensePoly.scale factor.toRatPoly.leadingCoeff⁻¹ factor.toRatPoly
  let factors := rawFactors.map fun factor => Factor.ofRatPoly (normalized factor)
  have hfold : HexPolyMathlib.toPolynomial
      (factors.foldl
        (fun product factor => product * Factor.toRatPoly factor) 1) =
      (rawFactors.toList.map normalizedRatFactor).prod := by
    rw [← Array.foldl_toList]
    simp only [factors, Array.toList_map]
    have hnormalized :
        ∀ init : DensePoly Rat,
        (List.map (fun factor => Factor.ofRatPoly (normalized factor))
          rawFactors.toList).foldl
            (fun product factor => product * Factor.toRatPoly factor) init =
          rawFactors.toList.foldl
            (fun product factor => product * normalized factor) init := by
      intro init
      induction rawFactors.toList generalizing init with
      | nil => rfl
      | cons factor tail ih =>
          rw [List.map_cons, List.foldl_cons, toRatPoly_ofRatPoly]
          exact ih _
    rw [hnormalized 1, normalizedRatFactorFoldl rawFactors.toList]
    simp
  obtain ⟨hnormalizedMonic, hnormalizedAssociated⟩ :=
    factorize_normalized_product integer hintegerNe
  have hrawList : rawFactors.toList =
      (ZPoly.factorize integer).factors.toList.flatMap
        (fun entry => List.replicate entry.2 entry.1) := by
    simp [rawFactors]
  rw [← hrawList] at hnormalizedMonic hnormalizedAssociated
  obtain ⟨unit, hunit⟩ :=
    ZPoly.ratPolyPrimitivePart_rational_associate p
  have hunitNe : unit ≠ 0 := by
    intro hzero
    apply hp
    apply (HexPolyMathlib.equiv (R := Rat)).injective
    rw [hunit, hzero]
    simp
  have hpAssociated : Associated (HexPolyMathlib.toPolynomial p)
      (HexPolyZMathlib.toPolyℚ integer) := by
    have hunitPoly := congrArg HexPolyMathlib.toPolynomial hunit
    rw [HexPolyMathlib.toPolynomial_scale,
      HexPolyZMathlib.toPolynomial_toRatPoly] at hunitPoly
    rw [hunitPoly]
    exact associated_unit_mul_left _ _
      (Polynomial.isUnit_C.mpr hunitNe.isUnit)
  change factors.foldl
    (fun product factor => product * Factor.toRatPoly factor) 1 = p
  apply (HexPolyMathlib.equiv (R := Rat)).injective
  change HexPolyMathlib.toPolynomial
      (factors.foldl
        (fun product factor => product * Factor.toRatPoly factor) 1) =
    HexPolyMathlib.toPolynomial p
  rw [hfold]
  exact Polynomial.eq_of_monic_of_associated hnormalizedMonic hpMonic
    (hnormalizedAssociated.trans hpAssociated.symm)

private theorem gcd_derivative_size_le_one_of_separable
    (p : DensePoly Rat)
    (hseparable : (HexPolyMathlib.toPolynomial p).Separable) :
    (DensePoly.gcd p (DensePoly.derivative p)).size ≤ 1 := by
  let g := DensePoly.gcd p (DensePoly.derivative p)
  let G := EuclideanDomain.gcd (HexPolyMathlib.toPolynomial p)
    (HexPolyMathlib.toPolynomial p).derivative
  have hassociated : Associated (HexPolyMathlib.toPolynomial g) G := by
    simpa only [g, G, HexPolyMathlib.toPolynomial_derivative] using
      HexPolyMathlib.toPolynomial_gcd_associated p (DensePoly.derivative p)
  have hGunit : IsUnit G := by
    change IsUnit (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial p)
      (HexPolyMathlib.toPolynomial p).derivative)
    rw [EuclideanDomain.gcd_isUnit_iff]
    exact hseparable
  have hgunit : IsUnit (HexPolyMathlib.toPolynomial g) :=
    hassociated.isUnit_iff.mpr hGunit
  rw [HexPolyZMathlib.size_le_one_iff_natDegree_eq_zero]
  exact Polynomial.natDegree_eq_zero_of_isUnit hgunit

/-- The rational base factorizer is total on the separable inputs supplied by
Yun decomposition. -/
private theorem factorRat_isSome (input : DensePoly Rat)
    (hseparable : (HexPolyMathlib.toPolynomial input).Separable) :
    (Factor.factorRat? input).isSome := by
  have hinputNe : input ≠ 0 := by
    intro hzero
    apply hseparable.ne_zero
    rw [hzero, HexPolyMathlib.toPolynomial_zero]
  have hinputZero : input.isZero = false := by
    rw [DensePoly.isZero_eq_false_iff]
    exact Nat.pos_of_ne_zero fun hsize =>
      hinputNe ((DensePoly.size_eq_zero_iff input).mp hsize)
  let p := DensePoly.scale input.leadingCoeff⁻¹ input
  have hpNe : p ≠ 0 := by
    intro hzero
    have hpoly := congrArg HexPolyMathlib.toPolynomial hzero
    change HexPolyMathlib.toPolynomial
        (DensePoly.scale input.leadingCoeff⁻¹ input) =
      HexPolyMathlib.toPolynomial 0 at hpoly
    rw [HexPolyMathlib.toPolynomial_scale,
      HexPolyMathlib.toPolynomial_zero] at hpoly
    have hleadingNe : input.leadingCoeff ≠ 0 :=
      DensePoly.leadingCoeff_ne_zero_of_pos_size input
        ((DensePoly.isZero_eq_false_iff input).mp hinputZero)
    have hinputPoly : HexPolyMathlib.toPolynomial input = 0 :=
      (mul_eq_zero.mp hpoly).resolve_left
        (Polynomial.C_ne_zero.mpr (inv_ne_zero hleadingNe))
    apply hinputNe
    apply (HexPolyMathlib.equiv (R := Rat)).injective
    change HexPolyMathlib.toPolynomial input =
      HexPolyMathlib.toPolynomial (0 : DensePoly Rat)
    rw [HexPolyMathlib.toPolynomial_zero]
    exact hinputPoly
  have hpZero : p.isZero = false := by
    rw [DensePoly.isZero_eq_false_iff]
    exact Nat.pos_of_ne_zero fun hsize =>
      hpNe ((DensePoly.size_eq_zero_iff p).mp hsize)
  have hpMonic : (HexPolyMathlib.toPolynomial p).Monic := by
    exact toPolynomial_scale_inv_monic input hinputNe
  have hpSeparable : (HexPolyMathlib.toPolynomial p).Separable := by
    exact (scale_inv_associated input hinputNe).symm.separable hseparable
  have hgcd := gcd_derivative_size_le_one_of_separable p hpSeparable
  have hproduct := factorRat_product p hpNe hpMonic
  dsimp only at hproduct
  simp only [Factor.factorRat?, hinputZero, Bool.false_eq_true, if_false]
  rw [show DensePoly.scale input.leadingCoeff⁻¹ input = p from rfl]
  simp only [hpZero, hgcd, if_pos]
  rw [hproduct]
  simp

section Yun

variable {levels : List Level}
variable (hvalid : LevelsValid levels)
variable (hinjective : LevelSemantics.DenoteInjective levels)
variable (hinv : ∀ a : Arithmetic.Coeff levels,
  LevelSemantics.coeffDenote levels a⁻¹ =
    (LevelSemantics.coeffDenote levels a)⁻¹)

include hvalid hinjective hinv

private theorem rawPolynomial_monic_associated
    (f : DensePoly (Arithmetic.Coeff levels))
    (hf : Norm.rawPolynomial levels f ≠ 0) :
    Associated (Norm.rawPolynomial levels (Norm.monic f))
      (Norm.rawPolynomial levels f) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let ι := LevelSemantics.coeffHom levels hvalid hinjective hinv
  have hfSource : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    apply hf
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    change (HexPolyMathlib.toPolynomial f).map ι = 0
    rw [hzero, Polynomial.map_zero]
  have hsource := toPolynomial_monic_associated levels hvalid hinjective
    hinv f (by
      intro hzero
      apply hfSource
      rw [hzero, HexPolyMathlib.toPolynomial_zero])
  have hmapped := Polynomial.associated_map_map ι hsource
  rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv,
    ← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
  change Associated
    ((HexPolyMathlib.toPolynomial (Norm.monic f)).map ι)
    ((HexPolyMathlib.toPolynomial f).map ι)
  exact hmapped

omit hvalid hinjective hinv in
private theorem rootMultiplicity_associated_complex
    {f g : Polynomial ℂ} (h : Associated f g) (z : ℂ) :
    f.rootMultiplicity z = g.rootMultiplicity z := by
  rw [← Polynomial.count_roots, ← Polynomial.count_roots, h.roots_eq]

omit hvalid hinjective hinv in
private theorem rootMultiplicity_gcd_complex
    (f g : Polynomial ℂ) (hf : f ≠ 0) (hg : g ≠ 0) (z : ℂ) :
    (EuclideanDomain.gcd f g).rootMultiplicity z =
      min (f.rootMultiplicity z) (g.rootMultiplicity z) := by
  have hgcd : EuclideanDomain.gcd f g ≠ 0 := by
    intro h
    exact hf (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  apply le_antisymm
  · exact le_min
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hf
        (EuclideanDomain.gcd_dvd_left f g) z)
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hg
        (EuclideanDomain.gcd_dvd_right f g) z)
  · rw [Polynomial.le_rootMultiplicity_iff hgcd]
    apply EuclideanDomain.dvd_gcd
    · rw [← Polynomial.le_rootMultiplicity_iff hf]
      exact min_le_left _ _
    · rw [← Polynomial.le_rootMultiplicity_iff hg]
      exact min_le_right _ _

private theorem monicGcd_dvd
    (f g : DensePoly (Arithmetic.Coeff levels))
    (hf : f ≠ 0) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    Norm.monic (DensePoly.gcd f g) ∣ f ∧
      Norm.monic (DensePoly.gcd f g) ∣ g := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let raw := HexPolyMathlib.toPolynomial (DensePoly.gcd f g)
  let normalized := EuclideanDomain.gcd
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
  have hfPoly : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    apply hf
    apply (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff levels)).injective
    simpa using hzero
  have hrawNormalized : Associated raw normalized :=
    HexPolyMathlib.toPolynomial_gcd_associated f g
  have hnormalized : normalized ≠ 0 := by
    intro hzero
    exact hfPoly (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hraw : raw ≠ 0 := fun hzero =>
    hnormalized (hrawNormalized.eq_zero_iff.mp hzero)
  have hmonicRaw : Associated
      (HexPolyMathlib.toPolynomial (Norm.monic (DensePoly.gcd f g))) raw :=
    toPolynomial_monic_associated levels hvalid hinjective hinv
      (DensePoly.gcd f g) (by
        intro hzero
        apply hraw
        simp [raw, hzero])
  have hmonicNormalized := hmonicRaw.trans hrawNormalized
  constructor <;> rw [← HexPolyMathlib.toPolynomial_dvd_iff]
  · exact hmonicNormalized.dvd.trans
      (EuclideanDomain.gcd_dvd_left _ _)
  · exact hmonicNormalized.dvd.trans
      (EuclideanDomain.gcd_dvd_right _ _)

private theorem rawPolynomial_monicGcd_ne_zero
    (f g : DensePoly (Arithmetic.Coeff levels))
    (hf : Norm.rawPolynomial levels f ≠ 0) :
    Norm.rawPolynomial levels (Norm.monic (DensePoly.gcd f g)) ≠ 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hfSource : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    apply hf
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    change (HexPolyMathlib.toPolynomial f).map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) = 0
    rw [hzero, Polynomial.map_zero]
  let sourceGcd := EuclideanDomain.gcd
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
  have hsourceGcd : sourceGcd ≠ 0 := by
    intro hzero
    exact hfSource (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hrawSource : Associated
      (HexPolyMathlib.toPolynomial (DensePoly.gcd f g)) sourceGcd :=
    HexPolyMathlib.toPolynomial_gcd_associated f g
  have hraw : DensePoly.gcd f g ≠ 0 := by
    intro hzero
    apply hsourceGcd
    apply hrawSource.eq_zero_iff.mp
    rw [hzero, HexPolyMathlib.toPolynomial_zero]
  have hsourceNe := toPolynomial_monic_associated levels hvalid hinjective
    hinv (DensePoly.gcd f g) hraw |>.ne_zero_iff.mpr (by
      intro hzero
      apply hsourceGcd
      exact hrawSource.eq_zero_iff.mp hzero)
  rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
  change (HexPolyMathlib.toPolynomial
    (Norm.monic (DensePoly.gcd f g))).map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) ≠ 0
  exact (Polynomial.map_ne_zero_iff
    (LevelSemantics.coeffHom levels hvalid hinjective hinv).injective).mpr
      hsourceNe

private theorem rootMultiplicity_monicGcd
    (f g : DensePoly (Arithmetic.Coeff levels))
    (hf : Norm.rawPolynomial levels f ≠ 0)
    (hg : Norm.rawPolynomial levels g ≠ 0) (z : ℂ) :
    (Norm.rawPolynomial levels
      (Norm.monic (DensePoly.gcd f g))).rootMultiplicity z =
      min ((Norm.rawPolynomial levels f).rootMultiplicity z)
        ((Norm.rawPolynomial levels g).rootMultiplicity z) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let sourceGcd := EuclideanDomain.gcd
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
  let targetGcd := EuclideanDomain.gcd
    (Norm.rawPolynomial levels f) (Norm.rawPolynomial levels g)
  have hfSource : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    apply hf
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    change (HexPolyMathlib.toPolynomial f).map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) = 0
    rw [hzero, Polynomial.map_zero]
  have hsourceGcd : sourceGcd ≠ 0 := by
    intro hzero
    exact hfSource (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hrawSource : Associated
      (HexPolyMathlib.toPolynomial (DensePoly.gcd f g)) sourceGcd :=
    HexPolyMathlib.toPolynomial_gcd_associated f g
  have hraw : DensePoly.gcd f g ≠ 0 := by
    intro hzero
    apply hsourceGcd
    apply hrawSource.eq_zero_iff.mp
    rw [hzero, HexPolyMathlib.toPolynomial_zero]
  have hmonicSource : Associated
      (HexPolyMathlib.toPolynomial (Norm.monic (DensePoly.gcd f g)))
      sourceGcd :=
    (toPolynomial_monic_associated levels hvalid hinjective hinv
      (DensePoly.gcd f g) hraw).trans hrawSource
  let ι := LevelSemantics.coeffHom levels hvalid hinjective hinv
  have hmapped : Associated
      (Norm.rawPolynomial levels (Norm.monic (DensePoly.gcd f g)))
      (sourceGcd.map ι) := by
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    change Associated
      ((HexPolyMathlib.toPolynomial
        (Norm.monic (DensePoly.gcd f g))).map ι)
      (sourceGcd.map ι)
    exact Polynomial.associated_map_map ι hmonicSource
  have hmapGcd : sourceGcd.map ι = targetGcd := by
    change (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial f)
      (HexPolyMathlib.toPolynomial g)).map ι =
      EuclideanDomain.gcd (Norm.rawPolynomial levels f)
        (Norm.rawPolynomial levels g)
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv,
      ← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    change (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial f)
      (HexPolyMathlib.toPolynomial g)).map ι =
      EuclideanDomain.gcd
        ((HexPolyMathlib.toPolynomial f).map ι)
        ((HexPolyMathlib.toPolynomial g).map ι)
    exact (Polynomial.gcd_map (p := HexPolyMathlib.toPolynomial f)
      (q := HexPolyMathlib.toPolynomial g) ι).symm
  calc
    (Norm.rawPolynomial levels
        (Norm.monic (DensePoly.gcd f g))).rootMultiplicity z =
        (sourceGcd.map ι).rootMultiplicity z :=
      rootMultiplicity_associated_complex hmapped z
    _ = targetGcd.rootMultiplicity z := by rw [hmapGcd]
    _ = min ((Norm.rawPolynomial levels f).rootMultiplicity z)
        ((Norm.rawPolynomial levels g).rootMultiplicity z) :=
      rootMultiplicity_gcd_complex _ _ hf hg z

private theorem rawPolynomial_div_mul
    (dividend divisor : DensePoly (Arithmetic.Coeff levels))
    (hdivisor : divisor ∣ dividend) :
    Norm.rawPolynomial levels (dividend / divisor) *
        Norm.rawPolynomial levels divisor =
      Norm.rawPolynomial levels dividend := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hmod : dividend % divisor = 0 :=
    DensePoly.mod_eq_zero_of_dvd dividend divisor hdivisor
  have hreconstruct := DensePoly.div_mul_add_mod dividend divisor
  rw [hmod] at hreconstruct
  have hsource := congrArg HexPolyMathlib.toPolynomial hreconstruct
  simp only [HexPolyMathlib.toPolynomial_add,
    HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_zero,
    add_zero] at hsource
  let ι := LevelSemantics.coeffHom levels hvalid hinjective hinv
  have hmapped := congrArg (Polynomial.map ι) hsource
  rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv,
    ← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv,
    ← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
  change (HexPolyMathlib.toPolynomial (dividend / divisor)).map ι *
      (HexPolyMathlib.toPolynomial divisor).map ι =
    (HexPolyMathlib.toPolynomial dividend).map ι
  simpa only [Polynomial.map_mul] using hmapped

private theorem rawPolynomial_div_ne_zero
    (dividend divisor : DensePoly (Arithmetic.Coeff levels))
    (hdivisor : divisor ∣ dividend)
    (hdividend : Norm.rawPolynomial levels dividend ≠ 0) :
    Norm.rawPolynomial levels (dividend / divisor) ≠ 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  intro hquotient
  have hreconstruct := rawPolynomial_div_mul hvalid hinjective hinv
    dividend divisor hdivisor
  rw [hquotient, zero_mul] at hreconstruct
  exact hdividend hreconstruct.symm

private theorem rootMultiplicity_monicDiv
    (dividend divisor : DensePoly (Arithmetic.Coeff levels))
    (hdivisor : divisor ∣ dividend)
    (hdividend : Norm.rawPolynomial levels dividend ≠ 0) (z : ℂ) :
    (Norm.rawPolynomial levels
      (Norm.monic (dividend / divisor))).rootMultiplicity z =
      (Norm.rawPolynomial levels dividend).rootMultiplicity z -
        (Norm.rawPolynomial levels divisor).rootMultiplicity z := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hquotient := rawPolynomial_div_ne_zero hvalid hinjective hinv
    dividend divisor hdivisor hdividend
  have hmonic := rawPolynomial_monic_associated hvalid hinjective hinv
    (dividend / divisor) hquotient
  rw [rootMultiplicity_associated_complex hmonic z]
  have hreconstruct := rawPolynomial_div_mul hvalid hinjective hinv
    dividend divisor hdivisor
  have hproduct : Norm.rawPolynomial levels (dividend / divisor) *
      Norm.rawPolynomial levels divisor ≠ 0 := by simpa [hreconstruct]
  have hmultiplicity := Polynomial.rootMultiplicity_mul (x := z) hproduct
  rw [hreconstruct] at hmultiplicity
  omega

private theorem rawPolynomial_monicDiv_ne_zero
    (dividend divisor : DensePoly (Arithmetic.Coeff levels))
    (hdivisor : divisor ∣ dividend)
    (hdividend : Norm.rawPolynomial levels dividend ≠ 0) :
    Norm.rawPolynomial levels (Norm.monic (dividend / divisor)) ≠ 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hquotient := rawPolynomial_div_ne_zero hvalid hinjective hinv
    dividend divisor hdivisor hdividend
  exact (rawPolynomial_monic_associated hvalid hinjective hinv
    (dividend / divisor) hquotient).ne_zero_iff.mpr hquotient

private structure YunInvariant (z : ℂ) (r k : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels)) : Prop where
  w_ne : Norm.rawPolynomial levels w ≠ 0
  repeated_ne : Norm.rawPolynomial levels repeated ≠ 0
  w_multiplicity : (Norm.rawPolynomial levels w).rootMultiplicity z =
    if k ≤ r then 1 else 0
  repeated_multiplicity :
    (Norm.rawPolynomial levels repeated).rootMultiplicity z = r - k

private theorem YunInvariant.step (z : ℂ) (r k : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels))
    (invariant : YunInvariant z r k w repeated) :
    let shared := Norm.monic (DensePoly.gcd w repeated)
    let nextRepeated := Norm.monic (repeated / shared)
    YunInvariant z r (k + 1) shared nextRepeated := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let shared := Norm.monic (DensePoly.gcd w repeated)
  let nextRepeated := Norm.monic (repeated / shared)
  have hwDense : w ≠ 0 := by
    intro hzero
    apply invariant.w_ne
    rw [hzero, Norm.rawPolynomial_zero]
  have hdivisors := monicGcd_dvd hvalid hinjective hinv w repeated hwDense
  have hsharedNe : Norm.rawPolynomial levels shared ≠ 0 :=
    rawPolynomial_monicGcd_ne_zero hvalid hinjective hinv
      w repeated invariant.w_ne
  have hnextNe : Norm.rawPolynomial levels nextRepeated ≠ 0 :=
    rawPolynomial_monicDiv_ne_zero hvalid hinjective hinv
      repeated shared hdivisors.2 invariant.repeated_ne
  have hsharedMultiplicity :
      (Norm.rawPolynomial levels shared).rootMultiplicity z =
        min ((Norm.rawPolynomial levels w).rootMultiplicity z)
          ((Norm.rawPolynomial levels repeated).rootMultiplicity z) :=
    rootMultiplicity_monicGcd hvalid hinjective hinv w repeated
      invariant.w_ne invariant.repeated_ne z
  have hnextMultiplicity :
      (Norm.rawPolynomial levels nextRepeated).rootMultiplicity z =
        (Norm.rawPolynomial levels repeated).rootMultiplicity z -
          (Norm.rawPolynomial levels shared).rootMultiplicity z :=
    rootMultiplicity_monicDiv hvalid hinjective hinv repeated shared
      hdivisors.2 invariant.repeated_ne z
  refine ⟨hsharedNe, hnextNe, ?_, ?_⟩
  · rw [hsharedMultiplicity, invariant.w_multiplicity,
      invariant.repeated_multiplicity]
    by_cases hk : k ≤ r <;> by_cases hnext : k + 1 ≤ r <;>
      simp [hk, hnext] <;> omega
  · rw [hnextMultiplicity, invariant.repeated_multiplicity,
      hsharedMultiplicity, invariant.w_multiplicity,
      invariant.repeated_multiplicity]
    by_cases hk : k ≤ r <;> simp [hk] <;> omega

private theorem YunInvariant.component (z : ℂ) (r k : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels))
    (invariant : YunInvariant z r k w repeated) :
    let shared := Norm.monic (DensePoly.gcd w repeated)
    let component := Norm.monic (w / shared)
    (Norm.rawPolynomial levels component).rootMultiplicity z =
      if k = r then 1 else 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let shared := Norm.monic (DensePoly.gcd w repeated)
  let component := Norm.monic (w / shared)
  have hwDense : w ≠ 0 := by
    intro hzero
    apply invariant.w_ne
    rw [hzero, Norm.rawPolynomial_zero]
  have hdivisors := monicGcd_dvd hvalid hinjective hinv w repeated hwDense
  change (Norm.rawPolynomial levels component).rootMultiplicity z =
    if k = r then 1 else 0
  rw [rootMultiplicity_monicDiv hvalid hinjective hinv w shared
      hdivisors.1 invariant.w_ne z,
    rootMultiplicity_monicGcd hvalid hinjective hinv w repeated
      invariant.w_ne invariant.repeated_ne z,
    invariant.w_multiplicity, invariant.repeated_multiplicity]
  by_cases hk : k ≤ r
  · by_cases heq : k = r
    · simp [heq]
    · simp [hk, heq]
      omega
  · have heq : k ≠ r := by omega
    simp [hk, heq]

private theorem YunInvariant.init
    (f : DensePoly (Arithmetic.Coeff levels))
    (hf : Norm.rawPolynomial levels f ≠ 0)
    (hdegree : (Norm.rawPolynomial levels f).natDegree ≠ 0) (z : ℂ) :
    let normalized := Norm.monic f
    let repeated := Norm.monic
      (DensePoly.gcd normalized (Norm.derivative levels normalized))
    let distinct := Norm.monic (normalized / repeated)
    YunInvariant z
      ((Norm.rawPolynomial levels f).rootMultiplicity z) 1
      distinct repeated := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let normalized := Norm.monic f
  let repeated := Norm.monic
    (DensePoly.gcd normalized (Norm.derivative levels normalized))
  let distinct := Norm.monic (normalized / repeated)
  have hnormalizedAssoc := rawPolynomial_monic_associated hvalid
    hinjective hinv f hf
  have hnormalizedNe : Norm.rawPolynomial levels normalized ≠ 0 :=
    hnormalizedAssoc.ne_zero_iff.mpr hf
  have hnormalizedMultiplicity :
      (Norm.rawPolynomial levels normalized).rootMultiplicity z =
        (Norm.rawPolynomial levels f).rootMultiplicity z :=
    rootMultiplicity_associated_complex hnormalizedAssoc z
  have hnormalizedDegree :
      (Norm.rawPolynomial levels normalized).natDegree ≠ 0 := by
    have hdegreeEq := Polynomial.degree_eq_degree_of_associated
      hnormalizedAssoc
    have hnatDegreeEq := Polynomial.natDegree_eq_of_degree_eq hdegreeEq
    intro hzero
    apply hdegree
    rw [← hnatDegreeEq, hzero]
  have hderivativeNe : Norm.rawPolynomial levels
      (Norm.derivative levels normalized) ≠ 0 := by
    rw [Norm.rawPolynomial_derivative]
    exact Polynomial.derivative_ne_zero.mpr hnormalizedDegree
  have hrepeatedNe : Norm.rawPolynomial levels repeated ≠ 0 :=
    rawPolynomial_monicGcd_ne_zero hvalid hinjective hinv normalized
      (Norm.derivative levels normalized) hnormalizedNe
  have hnormalizedDense : normalized ≠ 0 := by
    intro hzero
    apply hnormalizedNe
    rw [hzero, Norm.rawPolynomial_zero]
  have hdivisor : repeated ∣ normalized :=
    (monicGcd_dvd hvalid hinjective hinv normalized
      (Norm.derivative levels normalized) hnormalizedDense).1
  have hdistinctNe : Norm.rawPolynomial levels distinct ≠ 0 :=
    rawPolynomial_monicDiv_ne_zero hvalid hinjective hinv normalized
      repeated hdivisor hnormalizedNe
  have hrepeatedMultiplicity :
      (Norm.rawPolynomial levels repeated).rootMultiplicity z =
        (Norm.rawPolynomial levels f).rootMultiplicity z - 1 := by
    rw [rootMultiplicity_monicGcd hvalid hinjective hinv normalized
        (Norm.derivative levels normalized) hnormalizedNe hderivativeNe z,
      Norm.rawPolynomial_derivative, hnormalizedMultiplicity]
    by_cases hroot :
        (Norm.rawPolynomial levels f).rootMultiplicity z = 0
    · simp [hroot]
    · have hpositive : 0 <
          (Norm.rawPolynomial levels normalized).rootMultiplicity z := by
        omega
      have hisRoot : (Norm.rawPolynomial levels normalized).IsRoot z :=
        (Polynomial.rootMultiplicity_pos hnormalizedNe).mp hpositive
      rw [Polynomial.derivative_rootMultiplicity_of_root hisRoot,
        hnormalizedMultiplicity]
      omega
  refine ⟨hdistinctNe, hrepeatedNe, ?_, hrepeatedMultiplicity⟩
  rw [rootMultiplicity_monicDiv hvalid hinjective hinv normalized repeated
      hdivisor hnormalizedNe z,
    hnormalizedMultiplicity, hrepeatedMultiplicity]
  by_cases hpositive : 1 ≤
      (Norm.rawPolynomial levels f).rootMultiplicity z <;>
    simp [hpositive] <;> omega

/-- A nonzero interpreted polynomial with a root has positive executable
degree. Keeping this transport separate prevents the recursive Yun proof from
re-elaborating the coefficient-field construction at every induction step. -/
private theorem natDegree_rawPolynomial
    (f : DensePoly (Arithmetic.Coeff levels)) :
    (Norm.rawPolynomial levels f).natDegree = f.degree?.getD 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
  change ((HexPolyMathlib.toPolynomial f).map
    (LevelSemantics.coeffHom levels hvalid hinjective hinv)).natDegree = _
  rw [Polynomial.natDegree_map_eq_of_injective
      (LevelSemantics.coeffHom levels hvalid hinjective hinv).injective,
    HexPolyMathlib.natDegree_toPolynomial]

private theorem rawPolynomial_eq_map
    (f : DensePoly (Arithmetic.Coeff levels)) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    Norm.rawPolynomial levels f =
      (HexPolyMathlib.toPolynomial f).map
        (LevelSemantics.coeffHom levels hvalid hinjective hinv) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
  rfl

private theorem degree_pos_of_rawPolynomial_root
    (f : DensePoly (Arithmetic.Coeff levels))
    (hf : Norm.rawPolynomial levels f ≠ 0) {z : ℂ}
    (hroot : (Norm.rawPolynomial levels f).IsRoot z) :
    0 < f.degree?.getD 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hdegree := Polynomial.degree_pos_of_root hf hroot
  have hnatDegree : 0 < (Norm.rawPolynomial levels f).natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr hdegree
  rw [natDegree_rawPolynomial hvalid hinjective hinv] at hnatDegree
  exact hnatDegree

private theorem mem_yunAux_of_mem
    (w repeated : DensePoly (Arithmetic.Coeff levels)) (k fuel : Nat)
    (out : Array (Array (Array Rat) × Nat)) {entry}
    (hentry : entry ∈ out.toList) :
    entry ∈ (Factor.yunAux levels w repeated k fuel out).toList := by
  induction fuel generalizing w repeated k out with
  | zero => simpa [Factor.yunAux] using hentry
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact hentry
      · dsimp only
        split
        · apply ih
          rw [Array.toList_push, List.mem_append]
          exact Or.inl hentry
        · exact ih _ _ _ _ hentry

private theorem yunAux_sound (z : ℂ) (r : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels)) (k fuel : Nat)
    (out : Array (Array (Array Rat) × Nat))
    (invariant : YunInvariant z r k w repeated)
    (hOut : ∀ entry ∈ out.toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).IsRoot z → entry.2 = r) :
    ∀ entry ∈ (Factor.yunAux levels w repeated k fuel out).toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).IsRoot z → entry.2 = r := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction fuel generalizing w repeated k out with
  | zero => simpa [Factor.yunAux] using hOut
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact hOut
      · dsimp only
        let shared := Norm.monic (DensePoly.gcd w repeated)
        let component := Norm.monic (w / shared)
        let nextRepeated := Norm.monic (repeated / shared)
        have hwDense : w ≠ 0 := by
          intro hzero
          apply invariant.w_ne
          rw [hzero, Norm.rawPolynomial_zero]
        have hdivisors := monicGcd_dvd hvalid hinjective hinv
          w repeated hwDense
        have hcomponentNe : Norm.rawPolynomial levels component ≠ 0 :=
          rawPolynomial_monicDiv_ne_zero hvalid hinjective hinv
            w shared hdivisors.1 invariant.w_ne
        have hcomponentMultiplicity :
            (Norm.rawPolynomial levels component).rootMultiplicity z =
              if k = r then 1 else 0 :=
          invariant.component hvalid hinjective hinv z r k w repeated
        have hcomponentSound :
            (Norm.rawPolynomial levels component).IsRoot z → k = r := by
          intro hroot
          have hpositive :=
            (Polynomial.rootMultiplicity_pos hcomponentNe).mpr hroot
          rw [hcomponentMultiplicity] at hpositive
          by_cases heq : k = r
          · exact heq
          · simp [heq] at hpositive
        have hnextInvariant : YunInvariant z r (k + 1)
            shared nextRepeated :=
          invariant.step hvalid hinjective hinv z r k w repeated
        split
        · apply ih shared nextRepeated (k + 1) _ hnextInvariant
          intro entry hentry
          rw [Array.toList_push, List.mem_append,
            List.mem_singleton] at hentry
          rcases hentry with hentry | rfl
          · exact hOut entry hentry
          · rw [rawPoly_polyCoords]
            intro hroot
            exact hcomponentSound hroot
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant hOut

private theorem yunAux_rootMultiplicity_le_one (z : ℂ) (r : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels)) (k fuel : Nat)
    (out : Array (Array (Array Rat) × Nat))
    (invariant : YunInvariant z r k w repeated)
    (hOut : ∀ entry ∈ out.toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).rootMultiplicity z ≤ 1) :
    ∀ entry ∈ (Factor.yunAux levels w repeated k fuel out).toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).rootMultiplicity z ≤ 1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction fuel generalizing w repeated k out with
  | zero => simpa [Factor.yunAux] using hOut
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact hOut
      · dsimp only
        let shared := Norm.monic (DensePoly.gcd w repeated)
        let component := Norm.monic (w / shared)
        let nextRepeated := Norm.monic (repeated / shared)
        have hcomponentMultiplicity :
            (Norm.rawPolynomial levels component).rootMultiplicity z =
              if k = r then 1 else 0 :=
          invariant.component hvalid hinjective hinv z r k w repeated
        have hnextInvariant : YunInvariant z r (k + 1)
            shared nextRepeated :=
          invariant.step hvalid hinjective hinv z r k w repeated
        split
        · apply ih shared nextRepeated (k + 1) _ hnextInvariant
          intro entry hentry
          rw [Array.toList_push, List.mem_append,
            List.mem_singleton] at hentry
          rcases hentry with hentry | rfl
          · exact hOut entry hentry
          · rw [rawPoly_polyCoords, hcomponentMultiplicity]
            split <;> omega
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant hOut

set_option maxHeartbeats 1200000 in
private theorem yunAux_complete (z : ℂ) (r : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels)) (k fuel : Nat)
    (out : Array (Array (Array Rat) × Nat))
    (invariant : YunInvariant z r k w repeated)
    (hindex : k ≤ r) (hfuel : r < k + fuel) :
    ∃ entry ∈ (Factor.yunAux levels w repeated k fuel out).toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).IsRoot z ∧ entry.2 = r := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction fuel generalizing w repeated k out with
  | zero => omega
  | succ fuel ih =>
      have hnotOne : w ≠ 1 := by
        intro hone
        have hmultiplicity := invariant.w_multiplicity
        rw [hone, Norm.rawPolynomial_one levels hvalid hinjective hinv,
          if_pos hindex] at hmultiplicity
        have honeMultiplicity :
            Polynomial.rootMultiplicity z (1 : Polynomial ℂ) = 0 := by
          simpa only [Polynomial.C_1] using
            Polynomial.rootMultiplicity_C (1 : ℂ) z
        omega
      rw [Factor.yunAux, if_neg hnotOne]
      dsimp only
      let shared := Norm.monic (DensePoly.gcd w repeated)
      let component := Norm.monic (w / shared)
      let nextRepeated := Norm.monic (repeated / shared)
      have hwDense : w ≠ 0 := by
        intro hzero
        apply invariant.w_ne
        rw [hzero, Norm.rawPolynomial_zero]
      have hdivisors := monicGcd_dvd hvalid hinjective hinv
        w repeated hwDense
      have hcomponentNe : Norm.rawPolynomial levels component ≠ 0 :=
        rawPolynomial_monicDiv_ne_zero hvalid hinjective hinv
          w shared hdivisors.1 invariant.w_ne
      have hcomponentMultiplicity :
          (Norm.rawPolynomial levels component).rootMultiplicity z =
            if k = r then 1 else 0 :=
        invariant.component hvalid hinjective hinv z r k w repeated
      by_cases heq : k = r
      · have hpositive : 0 <
            (Norm.rawPolynomial levels component).rootMultiplicity z := by
          rw [hcomponentMultiplicity]
          simp [heq]
        have hroot : (Norm.rawPolynomial levels component).IsRoot z :=
          (Polynomial.rootMultiplicity_pos hcomponentNe).mp hpositive
        have hdegree : 0 < component.degree?.getD 0 :=
          degree_pos_of_rawPolynomial_root hvalid hinjective hinv component
            hcomponentNe hroot
        rw [if_pos hdegree]
        refine ⟨(Factor.polyCoords component, k), ?_, ?_, heq⟩
        · apply mem_yunAux_of_mem hvalid hinjective hinv
          simp [component, shared]
        · rw [rawPoly_polyCoords]
          exact hroot
      · have hnextInvariant : YunInvariant z r (k + 1)
            shared nextRepeated :=
          invariant.step hvalid hinjective hinv z r k w repeated
        have hnextIndex : k + 1 ≤ r := by omega
        have hnextFuel : r < k + 1 + fuel := by omega
        split
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant
            hnextIndex hnextFuel
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant
            hnextIndex hnextFuel

private theorem yunAux_positive
    (w repeated : DensePoly (Arithmetic.Coeff levels))
    (multiplicity fuel : Nat) (out : Array (Array (Array Rat) × Nat))
    (hMultiplicity : 0 < multiplicity)
    (hOut : ∀ component ∈ out.toList,
      0 < (Factor.rawPoly levels component.1).degree?.getD 0 ∧
        0 < component.2) :
    ∀ component ∈
      (Factor.yunAux levels w repeated multiplicity fuel out).toList,
      0 < (Factor.rawPoly levels component.1).degree?.getD 0 ∧
        0 < component.2 := by
  induction fuel generalizing w repeated multiplicity out with
  | zero => simpa [Factor.yunAux] using hOut
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact hOut
      · dsimp only
        split
        · apply ih
          · omega
          · intro component hcomponent
            rw [Array.toList_push, List.mem_append,
              List.mem_singleton] at hcomponent
            rcases hcomponent with hcomponent | rfl
            · exact hOut component hcomponent
            · rw [rawPoly_polyCoords]
              exact ⟨by assumption, hMultiplicity⟩
        · apply ih
          · omega
          · exact hOut

omit hvalid hinjective hinv in
private theorem yunAux_multiplicities
    (w repeated : DensePoly (Arithmetic.Coeff levels))
    (multiplicity fuel : Nat) (out : Array (Array (Array Rat) × Nat))
    (hpairwise : out.toList.Pairwise fun a b => a.2 < b.2)
    (hOut : ∀ entry ∈ out.toList, entry.2 < multiplicity) :
    ((Factor.yunAux levels w repeated multiplicity fuel out).toList.Pairwise
        fun a b => a.2 < b.2) ∧
      ∀ entry ∈
        (Factor.yunAux levels w repeated multiplicity fuel out).toList,
        entry.2 < multiplicity + fuel := by
  induction fuel generalizing w repeated multiplicity out with
  | zero =>
      refine ⟨by simpa [Factor.yunAux] using hpairwise, ?_⟩
      simpa [Factor.yunAux] using hOut
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact ⟨hpairwise, fun entry hentry => by
          have := hOut entry hentry
          omega⟩
      · dsimp only
        split
        · have hresult := ih
            (Norm.monic (DensePoly.gcd w repeated))
            (Norm.monic (repeated /
              Norm.monic (DensePoly.gcd w repeated)))
            (multiplicity + 1)
            (out.push (Factor.polyCoords
              (Norm.monic (w / Norm.monic (DensePoly.gcd w repeated))),
              multiplicity)) (by
            rw [Array.toList_push, List.pairwise_append]
            refine ⟨hpairwise, by simp, ?_⟩
            intro a ha b hb
            have hb' : b = (Factor.polyCoords
                (Norm.monic (w / Norm.monic (DensePoly.gcd w repeated))),
                multiplicity) := by
              simpa only [List.mem_singleton] using hb
            rw [hb']
            exact hOut a ha) (by
            intro entry hentry
            rw [Array.toList_push, List.mem_append,
              List.mem_singleton] at hentry
            rcases hentry with hentry | rfl
            · have := hOut entry hentry
              omega
            · omega)
          refine ⟨hresult.1, ?_⟩
          intro entry hentry
          have := hresult.2 entry hentry
          omega
        · have hresult := ih
            (Norm.monic (DensePoly.gcd w repeated))
            (Norm.monic (repeated /
              Norm.monic (DensePoly.gcd w repeated)))
            (multiplicity + 1) out hpairwise (by
            intro entry hentry
            have := hOut entry hentry
            omega)
          refine ⟨hresult.1, ?_⟩
          intro entry hentry
          have := hresult.2 entry hentry
          omega

private theorem yunAux_monic
    (w repeated : DensePoly (Arithmetic.Coeff levels))
    (multiplicity fuel : Nat) (out : Array (Array (Array Rat) × Nat))
    (hOut : ∀ entry ∈ out.toList,
      (Factor.rawPoly levels entry.1).leadingCoeff = 1) :
    ∀ entry ∈
      (Factor.yunAux levels w repeated multiplicity fuel out).toList,
      (Factor.rawPoly levels entry.1).leadingCoeff = 1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction fuel generalizing w repeated multiplicity out with
  | zero => simpa [Factor.yunAux] using hOut
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact hOut
      · dsimp only
        let shared := Norm.monic (DensePoly.gcd w repeated)
        let component := Norm.monic (w / shared)
        split
        · rename_i hdegree
          apply ih
          intro entry hentry
          rw [Array.toList_push, List.mem_append,
            List.mem_singleton] at hentry
          rcases hentry with hentry | rfl
          · exact hOut entry hentry
          · rw [rawPoly_polyCoords]
            have hcomponentNe : component ≠ 0 := by
              intro hzero
              have hdegreeZero : component.degree?.getD 0 = 0 := by
                rw [hzero]
                simp
              have hdegreeComponent : 0 < component.degree?.getD 0 := by
                simpa [component, shared] using hdegree
              omega
            have hquotientNe : w / shared ≠ 0 := by
              intro hzero
              apply hcomponentNe
              simp [component, hzero, Norm.monic]
            rw [← HexPolyMathlib.leadingCoeff_toPolynomial]
            exact (toPolynomial_monic_monic levels hvalid hinjective hinv
              (w / shared) hquotientNe).leadingCoeff
        · exact ih _ _ _ _ hOut

omit hvalid hinjective hinv in
private theorem rootMultiplicity_le_natDegree_complex
    (f : Polynomial ℂ) (hf : f ≠ 0) (z : ℂ) :
    f.rootMultiplicity z ≤ f.natDegree := by
  have hdegree := Polynomial.natDegree_le_of_dvd
    (Polynomial.pow_rootMultiplicity_dvd f z) hf
  simpa using hdegree

/-- Every root of an emitted tower Yun component is a root of the input with
the component's stored multiplicity. -/
private theorem yun_sound
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0)
    (z : ℂ) (entry : Array (Array Rat) × Nat)
    (hentry : entry ∈ (Factor.yunRaw levels f).toList)
    (hroot : (Norm.rawPolynomial levels
      (Factor.rawPoly levels entry.1)).IsRoot z) :
    entry.2 = (Norm.rawPolynomial levels
      (Factor.rawPoly levels f)).rootMultiplicity z := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  have hdegreeP : 0 < p.degree?.getD 0 := hdegree
  have hnatDegree : (Norm.rawPolynomial levels p).natDegree ≠ 0 := by
    rw [natDegree_rawPolynomial hvalid hinjective hinv]
    omega
  have hpNe : Norm.rawPolynomial levels p ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hnatDegree
    exact hnatDegree rfl
  let normalized := Norm.monic p
  let repeated := Norm.monic
    (DensePoly.gcd normalized (Norm.derivative levels normalized))
  let distinct := Norm.monic (normalized / repeated)
  have invariant : YunInvariant z
      ((Norm.rawPolynomial levels p).rootMultiplicity z) 1
      distinct repeated :=
    YunInvariant.init hvalid hinjective hinv p hpNe hnatDegree z
  unfold Factor.yunRaw at hentry
  rw [if_neg (by omega : p.degree?.getD 0 ≠ 0)] at hentry
  exact yunAux_sound hvalid hinjective hinv z
    ((Norm.rawPolynomial levels p).rootMultiplicity z)
    distinct repeated 1 (p.size + 1) #[] invariant (by simp)
    entry hentry hroot

/-- Every root of a positive-degree tower polynomial occurs in an emitted Yun
component at its exact multiplicity. -/
private theorem yun_complete
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0)
    (z : ℂ)
    (hroot : (Norm.rawPolynomial levels
      (Factor.rawPoly levels f)).IsRoot z) :
    ∃ entry ∈ (Factor.yunRaw levels f).toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).IsRoot z ∧
      entry.2 = (Norm.rawPolynomial levels
        (Factor.rawPoly levels f)).rootMultiplicity z := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  have hdegreeP : 0 < p.degree?.getD 0 := hdegree
  have hnatDegree : (Norm.rawPolynomial levels p).natDegree ≠ 0 := by
    rw [natDegree_rawPolynomial hvalid hinjective hinv]
    omega
  have hpNe : Norm.rawPolynomial levels p ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hnatDegree
    exact hnatDegree rfl
  let r := (Norm.rawPolynomial levels p).rootMultiplicity z
  have hindex : 1 ≤ r :=
    (Polynomial.rootMultiplicity_pos hpNe).mpr hroot
  have hmultiplicityDegree : r ≤
      (Norm.rawPolynomial levels p).natDegree :=
    rootMultiplicity_le_natDegree_complex _ hpNe z
  have hsize : 0 < p.size := by
    by_contra hzero
    have hsizeZero : p.size = 0 := by omega
    have hpZero : p = 0 := (DensePoly.size_eq_zero_iff p).mp hsizeZero
    rw [hpZero] at hdegreeP
    simp at hdegreeP
  have hdenseDegree : p.degree?.getD 0 = p.size - 1 := by
    rw [DensePoly.degree?_eq_some_of_pos_size p hsize]
    rfl
  have hdegreeEq : (Norm.rawPolynomial levels p).natDegree =
      p.degree?.getD 0 :=
    natDegree_rawPolynomial hvalid hinjective hinv p
  have hfuel : r < 1 + (p.size + 1) := by omega
  let normalized := Norm.monic p
  let repeated := Norm.monic
    (DensePoly.gcd normalized (Norm.derivative levels normalized))
  let distinct := Norm.monic (normalized / repeated)
  have invariant : YunInvariant z r 1 distinct repeated :=
    YunInvariant.init hvalid hinjective hinv p hpNe hnatDegree z
  have hcomplete := yunAux_complete hvalid hinjective hinv z r
    distinct repeated 1 (p.size + 1) #[] invariant hindex hfuel
  unfold Factor.yunRaw
  rw [if_neg (by omega : p.degree?.getD 0 ≠ 0)]
  exact hcomplete

/-- Every emitted Yun component has only simple roots over `ℂ`. -/
private theorem yun_rootMultiplicity_le_one
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0)
    (entry : Array (Array Rat) × Nat)
    (hentry : entry ∈ (Factor.yunRaw levels f).toList) (z : ℂ) :
    (Norm.rawPolynomial levels
      (Factor.rawPoly levels entry.1)).rootMultiplicity z ≤ 1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  have hdegreeP : 0 < p.degree?.getD 0 := hdegree
  have hnatDegree : (Norm.rawPolynomial levels p).natDegree ≠ 0 := by
    rw [natDegree_rawPolynomial hvalid hinjective hinv]
    omega
  have hpNe : Norm.rawPolynomial levels p ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hnatDegree
    exact hnatDegree rfl
  let r := (Norm.rawPolynomial levels p).rootMultiplicity z
  let normalized := Norm.monic p
  let repeated := Norm.monic
    (DensePoly.gcd normalized (Norm.derivative levels normalized))
  let distinct := Norm.monic (normalized / repeated)
  have invariant : YunInvariant z r 1 distinct repeated :=
    YunInvariant.init hvalid hinjective hinv p hpNe hnatDegree z
  unfold Factor.yunRaw at hentry
  rw [if_neg (by omega : p.degree?.getD 0 ≠ 0)] at hentry
  exact yunAux_rootMultiplicity_le_one hvalid hinjective hinv z r
    distinct repeated 1 (p.size + 1) #[] invariant (by simp)
    entry hentry

/-- Every emitted tower Yun component has positive degree and positive stored
multiplicity. -/
private theorem yun_positive
    (f : Array (Array Rat)) (component : Array (Array Rat) × Nat)
    (hcomponent : component ∈ (Factor.yunRaw levels f).toList) :
    0 < (Factor.rawPoly levels component.1).degree?.getD 0 ∧
      0 < component.2 := by
  simp only [Factor.yunRaw] at hcomponent
  split at hcomponent
  · simp at hcomponent
  · exact yunAux_positive hvalid hinjective hinv _ _ 1
      ((Factor.rawPoly levels f).size + 1) #[] Nat.one_pos
      (by simp) component hcomponent

/-- Yun emits components in strictly increasing multiplicity order. -/
private theorem yun_multiplicities
    (f : Array (Array Rat)) :
    (Factor.yunRaw levels f).toList.Pairwise fun a b => a.2 < b.2 := by
  simp only [Factor.yunRaw]
  split
  · simp
  · exact (yunAux_multiplicities
      (levels := levels) _ _ 1 ((Factor.rawPoly levels f).size + 1) #[]
      (by simp) (by simp)).1

/-- Every tower Yun component is monic in executable coordinates. -/
private theorem yun_monic
    (f : Array (Array Rat)) (component : Array (Array Rat) × Nat)
    (hcomponent : component ∈ (Factor.yunRaw levels f).toList) :
    (Factor.rawPoly levels component.1).leadingCoeff = 1 := by
  simp only [Factor.yunRaw] at hcomponent
  split at hcomponent
  · simp at hcomponent
  · exact yunAux_monic hvalid hinjective hinv _ _ 1
      ((Factor.rawPoly levels f).size + 1) #[] (by simp)
      component hcomponent

/-- Every tower Yun component passes the executable squarefreeness test. -/
private theorem yun_squarefree
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0)
    (component : Array (Array Rat) × Nat)
    (hcomponent : component ∈ (Factor.yunRaw levels f).toList) :
    Norm.isSquarefree levels component.1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let P := Norm.rawPolynomial levels
    (Factor.rawPoly levels component.1)
  have hcomponentDegree :=
    (yun_positive hvalid hinjective hinv f component hcomponent).1
  have hPNe : P ≠ 0 := by
    intro hzero
    have hnatDegree : P.natDegree = 0 := by simp [hzero]
    have htransport := natDegree_rawPolynomial hvalid hinjective hinv
      (Factor.rawPoly levels component.1)
    rw [← htransport] at hcomponentDegree
    exact (Nat.ne_of_gt hcomponentDegree) hnatDegree
  have hnodup : P.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro z
    rw [Polynomial.count_roots]
    exact yun_rootMultiplicity_le_one hvalid hinjective hinv f hdegree
      component hcomponent z
  have hseparable : P.Separable :=
    (Polynomial.nodup_roots_iff_of_splits hPNe
      (IsAlgClosed.splits P)).mp hnodup
  exact (Norm.isSquarefree_iff levels hvalid hinjective hinv
    component.1).mpr hseparable.squarefree

/-- Distinct tower Yun components pass the executable coprimality test. -/
private theorem yun_coprime
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0)
    (a b : Array (Array Rat) × Nat)
    (ha : a ∈ (Factor.yunRaw levels f).toList)
    (hb : b ∈ (Factor.yunRaw levels f).toList)
    (hmultiplicity : a.2 < b.2) :
    (DensePoly.gcd (Factor.rawPoly levels a.1)
      (Factor.rawPoly levels b.1)).size ≤ 1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let pa := Factor.rawPoly levels a.1
  let pb := Factor.rawPoly levels b.1
  let g := DensePoly.gcd pa pb
  by_contra hsize
  have hsizeG : ¬g.size ≤ 1 := hsize
  have hsize' : 1 < g.size := by omega
  have hgSize : 0 < g.size := by omega
  have hgDegree : 0 < g.degree?.getD 0 := by
    rw [DensePoly.degree?_eq_some_of_pos_size g hgSize]
    simp only [Option.getD_some]
    omega
  have htargetDegree : 0 < (Norm.rawPolynomial levels g).natDegree := by
    rw [natDegree_rawPolynomial hvalid hinjective hinv]
    exact hgDegree
  have hdegreeComplex : 0 < (Norm.rawPolynomial levels g).degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp htargetDegree
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (Norm.rawPolynomial levels g) (ne_of_gt hdegreeComplex)
  have hgAssociated : Associated (HexPolyMathlib.toPolynomial g)
      (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial pa)
        (HexPolyMathlib.toPolynomial pb)) :=
    HexPolyMathlib.toPolynomial_gcd_associated pa pb
  have hgDvdA : HexPolyMathlib.toPolynomial g ∣
      HexPolyMathlib.toPolynomial pa :=
    hgAssociated.dvd.trans (EuclideanDomain.gcd_dvd_left _ _)
  have hgDvdB : HexPolyMathlib.toPolynomial g ∣
      HexPolyMathlib.toPolynomial pb :=
    hgAssociated.dvd.trans (EuclideanDomain.gcd_dvd_right _ _)
  have htargetDvdA : Norm.rawPolynomial levels g ∣
      Norm.rawPolynomial levels pa := by
    rw [rawPolynomial_eq_map hvalid hinjective hinv,
      rawPolynomial_eq_map hvalid hinjective hinv]
    exact Polynomial.map_dvd
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) hgDvdA
  have htargetDvdB : Norm.rawPolynomial levels g ∣
      Norm.rawPolynomial levels pb := by
    rw [rawPolynomial_eq_map hvalid hinjective hinv,
      rawPolynomial_eq_map hvalid hinjective hinv]
    exact Polynomial.map_dvd
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) hgDvdB
  have hrootA : (Norm.rawPolynomial levels pa).IsRoot z :=
    hz.dvd htargetDvdA
  have hrootB : (Norm.rawPolynomial levels pb).IsRoot z :=
    hz.dvd htargetDvdB
  have haMultiplicity := yun_sound hvalid hinjective hinv f hdegree
    z a ha hrootA
  have hbMultiplicity := yun_sound hvalid hinjective hinv f hdegree
    z b hb hrootB
  omega

omit hvalid hinjective hinv in
private theorem rootMultiplicity_pow_complex
    (P : Polynomial ℂ) (hP : P ≠ 0) (n : Nat) (z : ℂ) :
    (P ^ n).rootMultiplicity z = n * P.rootMultiplicity z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul
        (mul_ne_zero (_root_.pow_ne_zero n hP) hP), ih]
      simp [Nat.succ_mul]

omit hvalid hinjective hinv in
private theorem rootMultiplicity_list_prod_complex
    (polys : List (Polynomial ℂ))
    (hnonzero : ∀ P ∈ polys, P ≠ 0) (z : ℂ) :
    polys.prod.rootMultiplicity z =
      (polys.map fun P => P.rootMultiplicity z).sum := by
  induction polys with
  | nil => simp
  | cons P polys ih =>
      have hP : P ≠ 0 := hnonzero P (by simp)
      have htail : ∀ Q ∈ polys, Q ≠ 0 := by
        intro Q hQ
        exact hnonzero Q (by simp [hQ])
      have htailProd : polys.prod ≠ 0 :=
        List.prod_ne_zero (by
          intro hzeroMem
          exact htail 0 hzeroMem rfl)
      rw [List.prod_cons, Polynomial.rootMultiplicity_mul
        (mul_ne_zero hP htailProd), ih htail]
      simp

private theorem rawPolynomial_polyPow
    (f : DensePoly (Arithmetic.Coeff levels)) (n : Nat) :
    Norm.rawPolynomial levels (Factor.polyPow f n) =
      Norm.rawPolynomial levels f ^ n := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [Factor.polyPow, Norm.rawPolynomial_one levels hvalid
          hinjective hinv]
      · rw [Factor.polyPow, if_neg hn]
        have hhalf : n / 2 < n :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
        dsimp only
        by_cases heven : n % 2 = 0
        · rw [if_pos heven,
            Norm.rawPolynomial_mul levels hvalid hinjective hinv,
            ih (n / 2) hhalf]
          rw [← pow_add]
          congr 1
          omega
        · rw [if_neg heven,
            Norm.rawPolynomial_mul levels hvalid hinjective hinv,
            Norm.rawPolynomial_mul levels hvalid hinjective hinv,
            ih (n / 2) hhalf]
          rw [← pow_add, ← pow_succ]
          congr 1
          omega

private theorem rawPolynomial_yunFold
    (components : List (Array (Array Rat) × Nat))
    (acc : DensePoly (Arithmetic.Coeff levels)) :
    Norm.rawPolynomial levels
        (components.foldl (fun product component =>
          product * Factor.polyPow
            (Factor.rawPoly levels component.1) component.2) acc) =
      (components.map fun component =>
        Norm.rawPolynomial levels
          (Factor.rawPoly levels component.1) ^ component.2).prod *
        Norm.rawPolynomial levels acc := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction components generalizing acc with
  | nil => simp
  | cons component components ih =>
      rw [List.foldl_cons, ih,
        Norm.rawPolynomial_mul levels hvalid hinjective hinv,
        rawPolynomial_polyPow hvalid hinjective hinv]
      simp only [List.map_cons, List.prod_cons]
      ring

private theorem yunMultiplicity_sum
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0) (z : ℂ)
    (components : List (Array (Array Rat) × Nat))
    (hcomponents : ∀ entry ∈ components,
      entry ∈ (Factor.yunRaw levels f).toList)
    (hpairwise : components.Pairwise fun a b => a.2 < b.2)
    (hcomplete :
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels f)).IsRoot z →
      ∃ entry ∈ components,
        (Norm.rawPolynomial levels
          (Factor.rawPoly levels entry.1)).IsRoot z) :
    (components.map fun entry => entry.2 *
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).rootMultiplicity z).sum =
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels f)).rootMultiplicity z := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let input := Norm.rawPolynomial levels (Factor.rawPoly levels f)
  have hinputNe : input ≠ 0 := by
    intro hzero
    have hnat : input.natDegree = 0 := by simp [hzero]
    have htransport := natDegree_rawPolynomial hvalid hinjective hinv
      (Factor.rawPoly levels f)
    rw [← htransport] at hdegree
    exact (Nat.ne_of_gt hdegree) hnat
  induction components with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      by_contra hr
      have hr' : input.rootMultiplicity z ≠ 0 := by
        intro hzero
        apply hr
        change 0 = input.rootMultiplicity z
        exact hzero.symm
      have hrPositive : 0 < input.rootMultiplicity z :=
        Nat.pos_of_ne_zero hr'
      have hroot : input.IsRoot z :=
        (Polynomial.rootMultiplicity_pos hinputNe).mp hrPositive
      rcases hcomplete hroot with ⟨entry, hentry, _⟩
      simp at hentry
  | cons entry components ih =>
      have hentryMem : entry ∈ (Factor.yunRaw levels f).toList :=
        hcomponents entry (by simp)
      have htailMem : ∀ tail ∈ components,
          tail ∈ (Factor.yunRaw levels f).toList := by
        intro tail htail
        exact hcomponents tail (by simp [htail])
      have hentryDegree :=
        (yun_positive hvalid hinjective hinv f entry hentryMem).1
      have hentryNe : Norm.rawPolynomial levels
          (Factor.rawPoly levels entry.1) ≠ 0 := by
        intro hzero
        have hnat : (Norm.rawPolynomial levels
          (Factor.rawPoly levels entry.1)).natDegree = 0 := by simp [hzero]
        rw [← natDegree_rawPolynomial hvalid hinjective hinv] at hentryDegree
        exact (Nat.ne_of_gt hentryDegree) hnat
      have hsimple := yun_rootMultiplicity_le_one hvalid hinjective hinv
        f hdegree entry hentryMem z
      rw [List.pairwise_cons] at hpairwise
      by_cases hzero : (Norm.rawPolynomial levels
          (Factor.rawPoly levels entry.1)).rootMultiplicity z = 0
      · simp only [List.map_cons, hzero, mul_zero, List.sum_cons, zero_add]
        apply ih htailMem hpairwise.2
        intro hroot
        rcases hcomplete hroot with ⟨witness, hwitness, hwitnessRoot⟩
        rw [List.mem_cons] at hwitness
        rcases hwitness with rfl | hwitness
        · have hpositive :=
            (Polynomial.rootMultiplicity_pos hentryNe).mpr hwitnessRoot
          omega
        · exact ⟨witness, hwitness, hwitnessRoot⟩
      · have hpositive : 0 < (Norm.rawPolynomial levels
            (Factor.rawPoly levels entry.1)).rootMultiplicity z :=
          Nat.pos_of_ne_zero hzero
        have hroot : (Norm.rawPolynomial levels
            (Factor.rawPoly levels entry.1)).IsRoot z :=
          (Polynomial.rootMultiplicity_pos hentryNe).mp hpositive
        have hlabel := yun_sound hvalid hinjective hinv f hdegree z
          entry hentryMem hroot
        have hmultiplicity : (Norm.rawPolynomial levels
            (Factor.rawPoly levels entry.1)).rootMultiplicity z = 1 := by
          omega
        have htailZero : (components.map fun tail => tail.2 *
            (Norm.rawPolynomial levels
              (Factor.rawPoly levels tail.1)).rootMultiplicity z).sum = 0 := by
          rw [List.sum_eq_zero_iff_forall_eq_nat]
          intro value hvalue
          simp only [List.mem_map] at hvalue
          obtain ⟨tail, htail, rfl⟩ := hvalue
          by_cases htailZero : (Norm.rawPolynomial levels
              (Factor.rawPoly levels tail.1)).rootMultiplicity z = 0
          · simp [htailZero]
          · have htailEntry := htailMem tail htail
            have htailDegree :=
              (yun_positive hvalid hinjective hinv f tail htailEntry).1
            have htailNe : Norm.rawPolynomial levels
                (Factor.rawPoly levels tail.1) ≠ 0 := by
              intro hzeroPoly
              have hnat : (Norm.rawPolynomial levels
                (Factor.rawPoly levels tail.1)).natDegree = 0 := by
                simp [hzeroPoly]
              rw [← natDegree_rawPolynomial hvalid hinjective hinv]
                at htailDegree
              exact (Nat.ne_of_gt htailDegree) hnat
            have htailRoot : (Norm.rawPolynomial levels
                (Factor.rawPoly levels tail.1)).IsRoot z :=
              (Polynomial.rootMultiplicity_pos htailNe).mp
                (Nat.pos_of_ne_zero htailZero)
            have htailLabel := yun_sound hvalid hinjective hinv f hdegree z
              tail htailEntry htailRoot
            have hlt := hpairwise.1 tail htail
            omega
        simp only [List.map_cons, List.sum_cons, hmultiplicity, mul_one,
          htailZero, add_zero, hlabel]

private theorem yun_rawPolynomial_monic
    (f : Array (Array Rat))
    (entry : Array (Array Rat) × Nat)
    (hentry : entry ∈ (Factor.yunRaw levels f).toList) :
    (Norm.rawPolynomial levels
      (Factor.rawPoly levels entry.1)).Monic := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hsource : (HexPolyMathlib.toPolynomial
      (Factor.rawPoly levels entry.1)).Monic := by
    rw [Polynomial.Monic.def, HexPolyMathlib.leadingCoeff_toPolynomial,
      yun_monic hvalid hinjective hinv f entry hentry]
  rw [rawPolynomial_eq_map hvalid hinjective hinv]
  exact hsource.map
    (LevelSemantics.coeffHom levels hvalid hinjective hinv)

/-- The powered product of all tower Yun components reconstructs the monic
input exactly. -/
private theorem yun_product
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0) :
    Factor.yunProduct levels (Factor.yunRaw levels f) =
      Factor.polyCoords (Norm.monic (Factor.rawPoly levels f)) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  let components := (Factor.yunRaw levels f).toList
  let polys := components.map fun entry =>
    Norm.rawPolynomial levels (Factor.rawPoly levels entry.1) ^ entry.2
  let product := polys.prod
  let normalized := Norm.rawPolynomial levels (Norm.monic p)
  have hdegreeP : 0 < p.degree?.getD 0 := hdegree
  have hpNe : p ≠ 0 := by
    intro hzero
    rw [hzero] at hdegreeP
    simp at hdegreeP
  have hinputNe : Norm.rawPolynomial levels p ≠ 0 := by
    intro hzero
    have hnat : (Norm.rawPolynomial levels p).natDegree = 0 := by
      simp [hzero]
    rw [natDegree_rawPolynomial hvalid hinjective hinv] at hnat
    omega
  have hcomponentMonic : ∀ entry ∈ components,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).Monic := by
    intro entry hentry
    exact yun_rawPolynomial_monic hvalid hinjective hinv f entry hentry
  have hcomponentNe : ∀ entry ∈ components,
      Norm.rawPolynomial levels (Factor.rawPoly levels entry.1) ≠ 0 := by
    intro entry hentry
    exact (hcomponentMonic entry hentry).ne_zero
  have hpolysMonic : ∀ P ∈ polys, P.Monic := by
    intro P hP
    simp only [polys, List.mem_map] at hP
    obtain ⟨entry, hentry, rfl⟩ := hP
    exact (hcomponentMonic entry hentry).pow entry.2
  have hproductMonic : product.Monic := by
    change polys.prod.Monic
    have listProductMonic : ∀ (items : List (Polynomial ℂ)),
        (∀ P ∈ items, P.Monic) → items.prod.Monic := by
      intro items hitems
      induction items with
      | nil => simp
      | cons P items ih =>
          rw [List.prod_cons]
          exact (hitems P (by simp)).mul
            (ih (fun Q hQ => hitems Q (by simp [hQ])))
    exact listProductMonic polys hpolysMonic
  have hnormalizedMonic : normalized.Monic := by
    have hsourceMonic := toPolynomial_monic_monic levels hvalid hinjective
      hinv p hpNe
    change (Norm.rawPolynomial levels (Norm.monic p)).Monic
    rw [rawPolynomial_eq_map hvalid hinjective hinv]
    exact hsourceMonic.map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv)
  have hpolysNe : ∀ P ∈ polys, P ≠ 0 := by
    intro P hP
    exact (hpolysMonic P hP).ne_zero
  have hmultiplicity (z : ℂ) : product.rootMultiplicity z =
      normalized.rootMultiplicity z := by
    have hsum := yunMultiplicity_sum hvalid hinjective hinv f hdegree z
      components (by intro entry hentry; exact hentry)
      (yun_multiplicities hvalid hinjective hinv f) (by
        intro hroot
        obtain ⟨entry, hentry, hentryRoot, _⟩ :=
          yun_complete hvalid hinjective hinv f hdegree z hroot
        exact ⟨entry, hentry, hentryRoot⟩)
    calc
      product.rootMultiplicity z =
          (polys.map fun P => P.rootMultiplicity z).sum :=
        rootMultiplicity_list_prod_complex polys hpolysNe z
      _ = (components.map fun entry => entry.2 *
          (Norm.rawPolynomial levels
            (Factor.rawPoly levels entry.1)).rootMultiplicity z).sum := by
        congr 1
        simp only [polys, List.map_map, Function.comp_apply]
        apply List.map_congr_left
        intro entry hentry
        exact rootMultiplicity_pow_complex _
          (hcomponentNe entry hentry) entry.2 z
      _ = (Norm.rawPolynomial levels p).rootMultiplicity z := hsum
      _ = normalized.rootMultiplicity z :=
        (rootMultiplicity_associated_complex
          (rawPolynomial_monic_associated hvalid hinjective hinv p hinputNe)
          z).symm
  have hroots : product.roots = normalized.roots := by
    apply Multiset.ext.mpr
    intro z
    rw [Polynomial.count_roots, Polynomial.count_roots]
    exact hmultiplicity z
  have hsemantic : product = normalized := by
    rw [(IsAlgClosed.splits product).eq_prod_roots_of_monic hproductMonic,
      (IsAlgClosed.splits normalized).eq_prod_roots_of_monic
        hnormalizedMonic, hroots]
  let fold := components.foldl (fun result entry =>
    result * Factor.polyPow (Factor.rawPoly levels entry.1) entry.2) 1
  have hfoldSemantic : Norm.rawPolynomial levels fold = product := by
    dsimp only [fold]
    rw [rawPolynomial_yunFold hvalid hinjective hinv,
      Norm.rawPolynomial_one levels hvalid hinjective hinv, mul_one]
  have hfold : fold = Norm.monic p := by
    apply Norm.rawPolynomial_injective levels hvalid hinjective hinv
    rw [hfoldSemantic]
    exact hsemantic
  unfold Factor.yunProduct
  rw [← Array.foldl_toList]
  change Factor.polyCoords fold = Factor.polyCoords (Norm.monic p)
  rw [hfold]

/-- The executable Yun decomposition always passes its full internal
certificate check. -/
theorem checkYun_yunRaw
    (f : Array (Array Rat)) :
    Factor.checkYun levels f (Factor.yunRaw levels f) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  by_cases hdegreeZero : p.degree?.getD 0 = 0
  · simp [Factor.checkYun, Factor.yunRaw, p, hdegreeZero]
  · have hdegree : 0 < p.degree?.getD 0 :=
      Nat.pos_of_ne_zero hdegreeZero
    let components := Factor.yunRaw levels f
    have hmultiplicities :
        Factor.yunMultiplicitiesIncrease components := by
      simp only [Factor.yunMultiplicitiesIncrease, decide_eq_true_eq]
      exact yun_multiplicities hvalid hinjective hinv f
    have hpositiveMonic : components.all (fun component =>
        0 < component.2 &&
          let factor := Factor.rawPoly levels component.1
          0 < factor.degree?.getD 0 && factor.leadingCoeff = 1) := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro component hcomponent
      have hcomponent' : component ∈
          (Factor.yunRaw levels f).toList := by
        apply Array.mem_toList_iff.mpr
        simpa only [components] using hcomponent
      have hpositive := yun_positive hvalid hinjective hinv f component
        hcomponent'
      have hmonic := yun_monic hvalid hinjective hinv f component hcomponent'
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hpositive.2, hpositive.1, hmonic⟩
    have hcoprime : Factor.yunPairwiseCoprime levels components := by
      simp only [Factor.yunPairwiseCoprime, decide_eq_true_eq]
      have pairwiseCoprime : ∀
          (items : List (Array (Array Rat) × Nat)),
          (∀ entry ∈ items, entry ∈ components.toList) →
          (items.Pairwise fun a b => a.2 < b.2) →
          items.Pairwise fun a b =>
            (DensePoly.gcd (Factor.rawPoly levels a.1)
              (Factor.rawPoly levels b.1)).size ≤ 1 := by
        intro items hitems hpairwise
        induction items with
        | nil => simp
        | cons entry items ih =>
            rw [List.pairwise_cons] at hpairwise ⊢
            constructor
            · intro other hother
              exact yun_coprime hvalid hinjective hinv f hdegree entry other
                (hitems entry (by simp))
                (hitems other (by simp [hother]))
                (hpairwise.1 other hother)
            · exact ih (fun other hother =>
                hitems other (by simp [hother])) hpairwise.2
      exact pairwiseCoprime components.toList (by
        intro entry hentry
        exact hentry) (yun_multiplicities hvalid hinjective hinv f)
    have hsquarefree : components.all (fun component =>
        Norm.isSquarefree levels component.1) := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro component hcomponent
      have hcomponent' : component ∈
          (Factor.yunRaw levels f).toList := by
        apply Array.mem_toList_iff.mpr
        simpa only [components] using hcomponent
      exact yun_squarefree hvalid hinjective hinv f hdegree component
        hcomponent'
    have hproduct : Factor.yunProduct levels components =
        Factor.polyCoords (Norm.monic p) :=
      yun_product hvalid hinjective hinv f hdegree
    simp only [Factor.checkYun, p, hdegreeZero, if_false,
      Bool.and_eq_true]
    exact ⟨⟨⟨⟨hmultiplicities, hpositiveMonic⟩, hcoprime⟩,
      hsquarefree⟩, decide_eq_true hproduct⟩

end Yun

set_option maxHeartbeats 1200000 in
theorem factorSquarefree_isSome :
    ∀ (levels : List Level) (hvalid : LevelsValid levels)
      (hinjective : LevelSemantics.DenoteInjective levels)
      (f : Array (Array Rat)),
      Norm.isSquarefree levels f →
      0 < (Factor.rawPoly levels f).degree?.getD 0 →
      (Factor.factorSquarefree? levels f).isSome := by
  intro levels
  induction levels with
  | nil =>
      intro hvalid hinjective f hcheck hdegree
      have hvalidEq : hvalid = (trivial : LevelsValid []) :=
        Subsingleton.elim _ _
      have hinjectiveEq : hinjective = LevelSemantics.DenoteInjective.nil :=
        Subsingleton.elim _ _
      subst hvalid
      subst hinjective
      letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil
      let ι := LevelSemantics.coeffHom [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil
      letI : CharZero (Arithmetic.Coeff []) :=
        { cast_injective := by
            intro m n hmn
            apply Nat.cast_injective (R := ℂ)
            have hmapped := congrArg ι hmn
            simpa only [map_natCast] using hmapped }
      have hsquarefree := squarefree_toPolynomial_of_check [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil f hcheck
      have hseparable :=
        (PerfectField.separable_iff_squarefree.mpr hsquarefree).map
          (f := LevelSemantics.coeffRatEquiv.toRingHom)
      rw [LevelSemantics.map_rawPoly_nil] at hseparable
      exact factorRat_isSome (Factor.toRatPoly f) hseparable
  | cons level lower ih =>
      intro hvalid hinjectiveTop f hcheck hdegree
      let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
      let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
        hinjectiveLower
      let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
        hinjectiveTop
      letI : Field (Arithmetic.Coeff lower) :=
        Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
      letI : Field (Arithmetic.Coeff (level :: lower)) :=
        Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
      have harrayDegree : 0 < f.size - 1 :=
        array_degree_pos_of_raw_degree_pos (level :: lower) f hdegree
      have hrawSquarefree := (Norm.isSquarefree_iff (level :: lower)
        hvalid hinjectiveTop hinvTop f).mp hcheck
      have hfindSome := Norm.findSquarefreeShift_isSome_of_injective
        level lower hvalid hinjectiveTop f harrayDegree hrawSquarefree
      obtain ⟨pair, hfind⟩ := Option.isSome_iff_exists.mp hfindSome
      rcases pair with ⟨shift, norm⟩
      have hnormCheck : Norm.isSquarefree lower norm :=
        findSquarefreeShift_squarefree level lower f hfind
      have hnormSquarefree : Squarefree
          (HexPolyMathlib.toPolynomial (Factor.rawPoly lower norm)) :=
        squarefree_toPolynomial_of_check lower hvalid.2.2 hinjectiveLower
          hinvLower norm hnormCheck
      have hnormEq : norm = Norm.oneLevel level lower f shift :=
        findSquarefreeShift_norm level lower f hfind
      have hnormDegree : 0 < (Factor.rawPoly lower norm).degree?.getD 0 := by
        rw [hnormEq]
        exact oneLevel_degree_pos level lower hvalid hinjectiveTop f shift
          hdegree (by simpa [hnormEq] using hnormSquarefree)
      have hlowerSome := ih hvalid.2.2 hinjectiveLower norm hnormCheck
        hnormDegree
      obtain ⟨lowerFactors, hlower⟩ :=
        Option.isSome_iff_exists.mp hlowerSome
      let factors := Factor.recover level lower shift f lowerFactors
      have hlowerSound : ∀ lowerFactor ∈ lowerFactors,
          Factor.polyCoords (Factor.rawPoly lower lowerFactor) = lowerFactor ∧
            Irreducible (HexPolyMathlib.toPolynomial
              (Factor.rawPoly lower lowerFactor)) := by
        exact factorSquarefree_mem_sound lower hvalid.2.2 hinjectiveLower norm
          hlower
      have htragerSquarefree : Squarefree
          (HexPolyMathlib.toPolynomial
            (tragerNorm level lower
              (Factor.rawPoly (level :: lower)
                (Factor.shiftTop level lower f shift)))) := by
        rw [tragerNorm_shiftTop level lower hvalid hinjectiveTop, ← hnormEq]
        exact hnormSquarefree
      have hfactorsSound : ∀ factor ∈ factors,
          Factor.polyCoords (Factor.rawPoly (level :: lower) factor) = factor ∧
            Irreducible (HexPolyMathlib.toPolynomial
              (Factor.rawPoly (level :: lower) factor)) := by
        exact recover_mem_sound level lower hvalid hinjectiveTop f shift
          lowerFactors htragerSquarefree hlowerSound
      have hnormNe : Factor.rawPoly lower norm ≠ 0 := by
        intro hzero
        apply hnormSquarefree.ne_zero
        rw [hzero, HexPolyMathlib.toPolynomial_zero]
      have hlowerProduct := factorSquarefree_product lower hvalid.2.2
        hinjectiveLower norm hnormNe hlower
      have hfNe : Factor.rawPoly (level :: lower) f ≠ 0 := by
        intro hzero
        rw [hzero] at hdegree
        simp at hdegree
      have hfactorsProduct :
          (factors.toList.map fun factor => HexPolyMathlib.toPolynomial
            (Factor.rawPoly (level :: lower) factor)).prod =
            HexPolyMathlib.toPolynomial
              (Norm.monic (Factor.rawPoly (level :: lower) f)) := by
        exact recover_product level lower hvalid hinjectiveTop f norm shift
          lowerFactors hfNe hnormSquarefree hnormEq
            (fun lowerFactor hlowerFactor =>
              (hlowerSound lowerFactor hlowerFactor).1)
            hlowerProduct
            (fun factor hfactor => (hfactorsSound factor hfactor).2)
      have hfactorsDegree : factors.all (fun factor =>
          0 < (Factor.rawPoly (level :: lower) factor).degree?.getD 0) =
          true := by
        rw [Array.all_eq_true_iff_forall_mem]
        intro factor hfactor
        have hirreducible := (hfactorsSound factor hfactor).2
        have hnatDegree :
            (HexPolyMathlib.toPolynomial
              (Factor.rawPoly (level :: lower) factor)).natDegree ≠ 0 := by
          intro hzero
          apply hirreducible.not_isUnit
          apply Polynomial.isUnit_iff_degree_eq_zero.mpr
          rw [Polynomial.degree_eq_natDegree hirreducible.ne_zero, hzero]
          rfl
        rw [HexPolyMathlib.natDegree_toPolynomial] at hnatDegree
        exact decide_eq_true (Nat.pos_of_ne_zero hnatDegree)
      have hproduct : factors.foldl
          (fun product factor =>
            product * Factor.rawPoly (level :: lower) factor) 1 =
          Norm.monic (Factor.rawPoly (level :: lower) f) := by
        apply (HexPolyMathlib.equiv
          (R := Arithmetic.Coeff (level :: lower))).injective
        change HexPolyMathlib.toPolynomial
            (factors.foldl (fun product factor =>
              product * Factor.rawPoly (level :: lower) factor) 1) =
          HexPolyMathlib.toPolynomial
            (Norm.monic (Factor.rawPoly (level :: lower) f))
        rw [← Array.foldl_toList,
          rawFactorFoldl (level :: lower) hvalid hinjectiveTop hinvTop,
          hfactorsProduct]
        simp
      have hresult : Factor.factorSquarefree? (level :: lower) f =
          some factors := by
        simp only [Factor.factorSquarefree?, hcheck, if_true]
        rw [hfind]
        change (do
          let lowerFactors ← Factor.factorSquarefree? lower norm
          let factors' := Factor.recover level lower shift f lowerFactors
          let p := Norm.monic (Factor.rawPoly (level :: lower) f)
          let product := factors'.foldl (fun product factor =>
            product * Factor.rawPoly (level :: lower) factor) 1
          if factors'.all (fun factor =>
              0 < (Factor.rawPoly (level :: lower) factor).degree?.getD 0) &&
              product = p then some factors' else none) = some factors
        rw [hlower]
        change (if factors.all (fun factor =>
            0 < (Factor.rawPoly (level :: lower) factor).degree?.getD 0) &&
            factors.foldl (fun product factor =>
              product * Factor.rawPoly (level :: lower) factor) 1 =
              Norm.monic (Factor.rawPoly (level :: lower) f) then
            some factors else none) = some factors
        rw [hfactorsDegree, hproduct]
        simp
      exact Option.isSome_iff_exists.mpr ⟨factors, hresult⟩

private theorem list_foldlM_isSome {A B : Type*}
    {step : B → A → Option B} {items : List A} (init : B)
    (hstep : ∀ state item, item ∈ items → (step state item).isSome) :
    (items.foldlM step init).isSome := by
  induction items generalizing init with
  | nil => simp
  | cons item items ih =>
      obtain ⟨next, hnext⟩ := Option.isSome_iff_exists.mp
        (hstep init item (by simp))
      rw [List.foldlM_cons, hnext]
      exact ih next fun state tail htail =>
        hstep state tail (by simp [htail])

private theorem array_foldlM_isSome {A B : Type*}
    {step : B → A → Option B} {items : Array A} (init : B)
    (hstep : ∀ state item, item ∈ items.toList →
      (step state item).isSome) :
    (items.foldlM step init).isSome := by
  rw [← Array.foldlM_toList]
  exact list_foldlM_isSome init hstep

private theorem ratListLess_iff : ∀ a b : List Rat,
    Factor.ratListLess a b = true ↔ a < b := by
  intro a
  induction a with
  | nil =>
      intro b
      cases b <;> simp [Factor.ratListLess, List.lt_iff_lex_lt]
  | cons a as ih =>
      intro b
      cases b with
      | nil => simp [Factor.ratListLess, List.lt_iff_lex_lt]
      | cons b bs =>
          by_cases hab : a < b
          · rw [Factor.ratListLess, if_pos hab]
            constructor
            · intro _
              exact List.Lex.rel hab
            · intro _
              rfl
          · rw [Factor.ratListLess, if_neg hab]
            by_cases hba : b < a
            · rw [if_pos hba]
              constructor
              · intro hfalse
                contradiction
              · intro hlt
                exact ((not_le_of_gt hba) (List.head_le_of_lt hlt)).elim
            · rw [if_neg hba]
              have heq : a = b :=
                le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
              subst b
              rw [ih]
              constructor
              · exact List.Lex.cons
              · intro hlt
                cases hlt with
                | rel haa => exact (lt_irrefl a haa).elim
                | cons htail => exact htail

private theorem flattenList_injective : Function.Injective
    (fun f : List (Array Rat) =>
      f.flatMap fun coefficient =>
        (coefficient.size : Rat) :: coefficient.toList) := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons coefficient tail => simp at h
  | cons coefficient tail ih =>
      intro b h
      cases b with
      | nil => simp at h
      | cons other rest =>
          simp only [List.flatMap_cons, List.cons_append] at h
          have hhead : (coefficient.size : Rat) = other.size :=
            (List.cons.inj h).1
          have htail := (List.cons.inj h).2
          have hsize : coefficient.size = other.size := by
            exact_mod_cast hhead
          have hlength : coefficient.toList.length = other.toList.length := by
            simpa using hsize
          obtain ⟨hcoefficient, hrest⟩ :=
            List.append_inj htail hlength
          have harray : coefficient = other :=
            Array.toList_inj.mp hcoefficient
          subst other
          have htailEq : tail = rest := ih hrest
          subst rest
          rfl

private theorem flattenPoly_injective :
    Function.Injective Factor.flattenPoly := by
  intro a b h
  apply Array.toList_inj.mp
  apply flattenList_injective
  simpa only [Factor.flattenPoly] using h

private theorem factorLess_iff (a b : Array (Array Rat)) :
    Factor.factorLess a b = true ↔
      Factor.flattenPoly a < Factor.flattenPoly b := by
  exact ratListLess_iff _ _

private theorem factor_eq_of_not_less {a b : Array (Array Rat)}
    (hab : Factor.factorLess a b ≠ true)
    (hba : Factor.factorLess b a ≠ true) : a = b := by
  apply flattenPoly_injective
  apply le_antisymm
  · exact le_of_not_gt fun hlt => hba ((factorLess_iff b a).mpr hlt)
  · exact le_of_not_gt fun hlt => hab ((factorLess_iff a b).mpr hlt)

private theorem factorLess_trans {a b c : Array (Array Rat)}
    (hab : Factor.factorLess a b = true)
    (hbc : Factor.factorLess b c = true) :
    Factor.factorLess a c = true :=
  (factorLess_iff a c).mpr
    (lt_trans ((factorLess_iff a b).mp hab)
      ((factorLess_iff b c).mp hbc))

private def FactorEntryLess
    (a b : Array (Array Rat) × Nat) : Prop :=
  Factor.factorLess a.1 b.1 = true

private theorem insertFactor_fst_mem
    (factor entry : Array (Array Rat) × Nat) :
    ∀ factors : List (Array (Array Rat) × Nat),
      entry ∈ Factor.insertFactor factor factors →
      entry.1 = factor.1 ∨
        ∃ original ∈ factors, entry.1 = original.1 := by
  intro factors
  induction factors with
  | nil =>
      intro hentry
      have heq : entry = factor := by
        simpa [Factor.insertFactor] using hentry
      subst entry
      exact Or.inl rfl
  | cons head tail ih =>
      intro hentry
      by_cases hfactor : Factor.factorLess factor.1 head.1 = true
      · rw [Factor.insertFactor, if_pos hfactor] at hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · exact Or.inl rfl
        · exact Or.inr ⟨entry, hentry, rfl⟩
      · rw [Factor.insertFactor, if_neg hfactor] at hentry
        by_cases hhead : Factor.factorLess head.1 factor.1 = true
        · rw [if_pos hhead] at hentry
          rcases List.mem_cons.mp hentry with hentryHead | hentry
          · subst entry
            exact Or.inr ⟨head, by simp, rfl⟩
          · rcases ih hentry with hfactorEq | ⟨original, horiginal, heq⟩
            · exact Or.inl hfactorEq
            · exact Or.inr ⟨original, by simp [horiginal], heq⟩
        · rw [if_neg hhead] at hentry
          rcases List.mem_cons.mp hentry with hentry | hentry
          · subst entry
            exact Or.inr ⟨head, by simp, rfl⟩
          · exact Or.inr ⟨entry, by simp [hentry], rfl⟩

private theorem insertFactor_pairwise
    (factor : Array (Array Rat) × Nat) :
    ∀ factors : List (Array (Array Rat) × Nat),
      factors.Pairwise FactorEntryLess →
      (Factor.insertFactor factor factors).Pairwise FactorEntryLess := by
  intro factors
  induction factors with
  | nil => simp [Factor.insertFactor]
  | cons head tail ih =>
      intro hsorted
      have hhead := (List.pairwise_cons.mp hsorted).1
      have htail := (List.pairwise_cons.mp hsorted).2
      by_cases hfactor : Factor.factorLess factor.1 head.1 = true
      · rw [Factor.insertFactor, if_pos hfactor,
          List.pairwise_cons]
        refine ⟨?_, hsorted⟩
        intro other hother
        rcases List.mem_cons.mp hother with rfl | hother
        · exact hfactor
        · exact factorLess_trans hfactor (hhead other hother)
      · rw [Factor.insertFactor, if_neg hfactor]
        by_cases hheadFactor : Factor.factorLess head.1 factor.1 = true
        · rw [if_pos hheadFactor, List.pairwise_cons]
          refine ⟨?_, ih htail⟩
          intro other hother
          rcases insertFactor_fst_mem factor other tail hother with
            hfactorEq | ⟨original, horiginal, horiginalEq⟩
          · unfold FactorEntryLess
            rw [hfactorEq]
            exact hheadFactor
          · unfold FactorEntryLess
            rw [horiginalEq]
            exact hhead original horiginal
        · rw [if_neg hheadFactor, List.pairwise_cons]
          refine ⟨?_, htail⟩
          intro other hother
          exact hhead other hother

private theorem foldl_insertFactor_pairwise
    (items state : List (Array (Array Rat) × Nat))
    (hstate : state.Pairwise FactorEntryLess) :
    (items.foldl (fun out factor => Factor.insertFactor factor out) state).Pairwise
      FactorEntryLess := by
  induction items generalizing state with
  | nil => simpa using hstate
  | cons factor items ih =>
      rw [List.foldl_cons]
      exact ih _ (insertFactor_pairwise factor state hstate)

private theorem canonicalFactors_pairwise
    (factors : Array (Array (Array Rat) × Nat)) :
    (Factor.canonicalFactors factors).toList.Pairwise FactorEntryLess := by
  simpa [Factor.canonicalFactors] using
    foldl_insertFactor_pairwise factors.toList [] (by simp)

private theorem canonicalFactors_sorted
    (factors : Array (Array (Array Rat) × Nat)) :
    Factor.factorsSorted (Factor.canonicalFactors factors) = true := by
  simp only [Factor.factorsSorted, decide_eq_true_eq]
  exact canonicalFactors_pairwise factors

private theorem insertFactor_preserves
    (P : Array (Array Rat) → Prop)
    (factor : Array (Array Rat) × Nat) (hfactor : P factor.1)
    (factors : List (Array (Array Rat) × Nat))
    (hfactors : ∀ entry ∈ factors, P entry.1) :
    ∀ entry ∈ Factor.insertFactor factor factors, P entry.1 := by
  intro entry hentry
  rcases insertFactor_fst_mem factor entry factors hentry with
    hfactorEq | ⟨original, horiginal, horiginalEq⟩
  · rw [hfactorEq]
    exact hfactor
  · rw [horiginalEq]
    exact hfactors original horiginal

private theorem foldl_insertFactor_preserves
    (P : Array (Array Rat) → Prop)
    (items state : List (Array (Array Rat) × Nat))
    (hitems : ∀ entry ∈ items, P entry.1)
    (hstate : ∀ entry ∈ state, P entry.1) :
    ∀ entry ∈ items.foldl
      (fun out factor => Factor.insertFactor factor out) state,
      P entry.1 := by
  induction items generalizing state with
  | nil => simpa using hstate
  | cons factor items ih =>
      rw [List.foldl_cons]
      apply ih
      · intro entry hentry
        exact hitems entry (by simp [hentry])
      · exact insertFactor_preserves P factor
          (hitems factor (by simp)) state hstate

private theorem canonicalFactors_preserves
    (P : Array (Array Rat) → Prop)
    (factors : Array (Array (Array Rat) × Nat))
    (hfactors : ∀ entry ∈ factors, P entry.1) :
    ∀ entry ∈ Factor.canonicalFactors factors, P entry.1 := by
  intro entry hentry
  apply foldl_insertFactor_preserves P factors.toList []
  · intro original horiginal
    exact hfactors original (Array.mem_toList_iff.mp horiginal)
  · simp
  · simpa [Factor.canonicalFactors] using hentry

private theorem insertFactor_positive
    (factor : Array (Array Rat) × Nat) (hfactor : 0 < factor.2)
    (factors : List (Array (Array Rat) × Nat))
    (hfactors : ∀ entry ∈ factors, 0 < entry.2) :
    ∀ entry ∈ Factor.insertFactor factor factors, 0 < entry.2 := by
  induction factors with
  | nil => simpa [Factor.insertFactor] using hfactor
  | cons head tail ih =>
      intro entry hentry
      have hhead : 0 < head.2 := hfactors head (by simp)
      have htail : ∀ original ∈ tail, 0 < original.2 := by
        intro original horiginal
        exact hfactors original (by simp [horiginal])
      by_cases hfactorHead : Factor.factorLess factor.1 head.1 = true
      · rw [Factor.insertFactor, if_pos hfactorHead] at hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · exact hfactor
        · exact hfactors entry hentry
      · rw [Factor.insertFactor, if_neg hfactorHead] at hentry
        by_cases hheadFactor : Factor.factorLess head.1 factor.1 = true
        · rw [if_pos hheadFactor] at hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact hhead
          · exact ih htail entry hentry
        · rw [if_neg hheadFactor] at hentry
          rcases List.mem_cons.mp hentry with hentry | hentry
          · subst entry
            omega
          · exact htail entry hentry

private theorem foldl_insertFactor_positive
    (items state : List (Array (Array Rat) × Nat))
    (hitems : ∀ entry ∈ items, 0 < entry.2)
    (hstate : ∀ entry ∈ state, 0 < entry.2) :
    ∀ entry ∈ items.foldl
      (fun out factor => Factor.insertFactor factor out) state,
      0 < entry.2 := by
  induction items generalizing state with
  | nil => simpa using hstate
  | cons factor items ih =>
      rw [List.foldl_cons]
      apply ih
      · intro entry hentry
        exact hitems entry (by simp [hentry])
      · exact insertFactor_positive factor (hitems factor (by simp))
          state hstate

private theorem canonicalFactors_positive
    (factors : Array (Array (Array Rat) × Nat))
    (hfactors : ∀ entry ∈ factors, 0 < entry.2) :
    ∀ entry ∈ Factor.canonicalFactors factors, 0 < entry.2 := by
  intro entry hentry
  apply foldl_insertFactor_positive factors.toList []
  · intro original horiginal
    exact hfactors original (Array.mem_toList_iff.mp horiginal)
  · simp
  · simpa [Factor.canonicalFactors] using hentry

private theorem insertFactor_prod {M : Type*} [CommMonoid M]
    (value : Array (Array Rat) → M)
    (factor : Array (Array Rat) × Nat) :
    ∀ factors : List (Array (Array Rat) × Nat),
      ((Factor.insertFactor factor factors).map fun entry =>
        value entry.1 ^ entry.2).prod =
      (factors.map fun entry => value entry.1 ^ entry.2).prod *
        value factor.1 ^ factor.2 := by
  intro factors
  induction factors with
  | nil => simp [Factor.insertFactor]
  | cons head tail ih =>
      by_cases hfactorHead : Factor.factorLess factor.1 head.1 = true
      · simp [Factor.insertFactor, hfactorHead, mul_assoc, mul_comm,
          mul_left_comm]
      · by_cases hheadFactor : Factor.factorLess head.1 factor.1 = true
        · simp [Factor.insertFactor, hfactorHead, hheadFactor, ih,
            mul_assoc, mul_comm, mul_left_comm]
        · have heq : head.1 = factor.1 :=
            factor_eq_of_not_less hheadFactor hfactorHead
          have hirrefl :
              Factor.factorLess factor.1 factor.1 ≠ true := by
            intro hless
            exact (lt_irrefl _ ((factorLess_iff factor.1 factor.1).mp
              hless))
          simp [Factor.insertFactor, heq, hirrefl,
            pow_add, mul_assoc, mul_comm, mul_left_comm]

private theorem foldl_insertFactor_prod {M : Type*} [CommMonoid M]
    (value : Array (Array Rat) → M)
    (items state : List (Array (Array Rat) × Nat)) :
    ((items.foldl (fun out factor => Factor.insertFactor factor out) state).map
        fun entry => value entry.1 ^ entry.2).prod =
      (state.map fun entry => value entry.1 ^ entry.2).prod *
        (items.map fun entry => value entry.1 ^ entry.2).prod := by
  induction items generalizing state with
  | nil => simp
  | cons factor items ih =>
      rw [List.foldl_cons, ih, insertFactor_prod]
      simp only [List.map_cons, List.prod_cons]
      ac_rfl

private theorem canonicalFactors_prod {M : Type*} [CommMonoid M]
    (value : Array (Array Rat) → M)
    (factors : Array (Array (Array Rat) × Nat)) :
    ((Factor.canonicalFactors factors).toList.map fun entry =>
        value entry.1 ^ entry.2).prod =
      (factors.toList.map fun entry => value entry.1 ^ entry.2).prod := by
  simpa [Factor.canonicalFactors] using
    foldl_insertFactor_prod value factors.toList []

private theorem factorRat_mem_monic (input : DensePoly Rat)
    {factors : Array (Array (Array Rat))}
    (hresult : Factor.factorRat? input = some factors) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    ∀ factor ∈ factors,
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly [] factor)).Monic := by
  letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  intro factor hfactor
  simp only [Factor.factorRat?] at hresult
  split at hresult
  · cases hresult
    simp at hfactor
  · split at hresult
    · cases hresult
      simp at hfactor
    · split at hresult
      · split at hresult
        · cases hresult
          rename_i hinputZero hpZero hgcd hproduct
          obtain ⟨rawFactor, hrawFactor, rfl⟩ := Array.mem_map.mp hfactor
          have hrawList := Array.mem_toList_iff.mpr hrawFactor
          simp only [Array.toList_flatMap, List.mem_flatMap] at hrawList
          obtain ⟨entry, hentryList, hrawReplicate⟩ := hrawList
          have hrawEq : rawFactor = entry.1 := by
            have hrep : entry.2 ≠ 0 ∧ rawFactor = entry.1 := by
              simpa using hrawReplicate
            exact hrep.2
          subst rawFactor
          have hentry : entry ∈
              (ZPoly.factorize
                (ZPoly.ratPolyPrimitivePart
                  (DensePoly.scale input.leadingCoeff⁻¹ input))).factors :=
            Array.mem_toList_iff.mp hentryList
          have hentryNe : entry.1 ≠ 0 :=
            (HexBerlekampZassenhausMathlib.factorize_irreducible_of_nonUnit
              (ZPoly.ratPolyPrimitivePart
                (DensePoly.scale input.leadingCoeff⁻¹ input))
              entry hentry).not_zero
          let q := DensePoly.scale entry.1.toRatPoly.leadingCoeff⁻¹
            entry.1.toRatPoly
          have hqMonic : (HexPolyMathlib.toPolynomial q).Monic :=
            toPolynomial_scale_inv_monic entry.1.toRatPoly
              (toRatPoly_ne_zero hentryNe)
          apply Polynomial.monic_of_injective
            (f := LevelSemantics.coeffRatEquiv.toRingHom)
            LevelSemantics.coeffRatEquiv.injective
          rw [LevelSemantics.map_rawPoly_nil, toRatPoly_ofRatPoly]
          exact hqMonic
        · cases hresult
      · cases hresult

private theorem factorSquarefree_mem_monic
    (levels : List Level) (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat)) {factors : Array (Array (Array Rat))}
    (hresult : Factor.factorSquarefree? levels f = some factors) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    ∀ factor ∈ factors,
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly levels factor)).Monic := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  dsimp only
  intro factor hfactor
  cases levels with
  | nil =>
      exact factorRat_mem_monic (Factor.toRatPoly f) hresult factor hfactor
  | cons level lower =>
      have hfull := hresult
      simp only [Factor.factorSquarefree?] at hresult
      split at hresult
      · rename_i hinputSquarefree
        obtain ⟨pair, hfind, hresult⟩ :=
          Option.bind_eq_some_iff.mp hresult
        rcases pair with ⟨shift, norm⟩
        obtain ⟨lowerFactors, hlower, hresult⟩ :=
          Option.bind_eq_some_iff.mp hresult
        split at hresult
        · cases hresult
          obtain ⟨lowerFactor, hlowerFactor, hdegree, hrecovered⟩ :=
            recover_mem level lower shift f lowerFactors hfactor
          let common := Norm.monic
            (DensePoly.gcd
              (Factor.rawPoly (level :: lower)
                (Factor.shiftTop level lower f shift))
              (Factor.rawPoly (level :: lower)
                (Factor.embedLower level lower lowerFactor)))
          let unshifted := Factor.rawPoly (level :: lower)
            (Factor.shiftTop level lower (Factor.polyCoords common) (-shift))
          have hrawEq : Factor.rawPoly (level :: lower) factor =
              Norm.monic unshifted := by
            rw [← hrecovered, rawPoly_polyCoords]
          have hirreducible :=
            (factorSquarefree_mem_sound (level :: lower) hvalid hinjective f
              hfull factor hfactor).2
          have hunshifted : unshifted ≠ 0 := by
            intro hzero
            apply hirreducible.ne_zero
            rw [hrawEq, hzero]
            simp [Norm.monic]
          rw [hrawEq]
          exact toPolynomial_monic_monic (level :: lower) hvalid
            hinjective hinv unshifted hunshifted
        · contradiction
      · contradiction

private theorem foldl_push_labeled
    (factors : Array (Array (Array Rat)))
    (state : Array (Array (Array Rat) × Nat)) (multiplicity : Nat) :
    factors.foldl
      (fun out factor => out.push (factor, multiplicity)) state =
      state ++ factors.map fun factor => (factor, multiplicity) := by
  rw [Array.foldl_push_eq_append (stop := factors.size) rfl]

private theorem list_prod_pow {M : Type*} [CommMonoid M]
    (items : List M) (n : Nat) :
    (items.map fun item => item ^ n).prod = items.prod ^ n := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      exact (_root_.mul_pow item items.prod n).symm

private theorem labeled_prod_pow {A M : Type*} [CommMonoid M]
    (value : A → M) (items : List A) (n : Nat) :
    ((items.map fun item => (item, n)).map fun entry =>
      value entry.1 ^ entry.2).prod = (items.map value).prod ^ n := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp only [List.map_cons, List.prod_cons, ih, Prod.fst, Prod.snd]
      exact (_root_.mul_pow (value item) (List.map value items).prod n).symm

private theorem factorFold_sound
    (levels : List Level) (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat))
    (components : List (Array (Array Rat) × Nat))
    (hcomponents : ∀ component ∈ components,
      component ∈ (Factor.yunRaw levels f).toList)
    (state out : Array (Array (Array Rat) × Nat))
    (hfold : components.foldlM (Factor.appendComponent? levels) state =
      some out) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    (∀ entry ∈ state,
      Factor.polyCoords (Factor.rawPoly levels entry.1) = entry.1 ∧
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels entry.1)).Monic ∧
        Irreducible (HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels entry.1)) ∧
        0 < entry.2) →
    (∀ entry ∈ out,
      Factor.polyCoords (Factor.rawPoly levels entry.1) = entry.1 ∧
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels entry.1)).Monic ∧
        Irreducible (HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels entry.1)) ∧
        0 < entry.2) ∧
      (out.toList.map fun entry =>
        HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels entry.1) ^ entry.2).prod =
        (state.toList.map fun entry =>
          HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1) ^ entry.2).prod *
          (components.map fun component =>
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels component.1) ^ component.2).prod := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  dsimp only
  intro hstate
  induction components generalizing state with
  | nil =>
      simp only [List.foldlM_nil, Option.pure_def,
        Option.some.injEq] at hfold
      subst out
      exact ⟨hstate, by simp⟩
  | cons component components ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨next, hnext, htail⟩ :=
        Option.bind_eq_some_iff.mp hfold
      simp only [Factor.appendComponent?] at hnext
      obtain ⟨irreducibles, hirreducibles, hnext⟩ :=
        Option.bind_eq_some_iff.mp hnext
      rw [foldl_push_labeled] at hnext
      simp only [Option.pure_def, Option.some.injEq] at hnext
      subst next
      have hcomponentMem : component ∈
          (Factor.yunRaw levels f).toList :=
        hcomponents component (by simp)
      have hpositive := yun_positive hvalid hinjective hinv f component
        hcomponentMem
      have hrawNe : Factor.rawPoly levels component.1 ≠ 0 := by
        intro hzero
        rw [hzero] at hpositive
        simp at hpositive
      have hcomponentMonic :
          (HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels component.1)).Monic := by
        rw [Polynomial.Monic.def,
          HexPolyMathlib.leadingCoeff_toPolynomial]
        exact yun_monic hvalid hinjective hinv f component hcomponentMem
      have hnormalized :
          Norm.monic (Factor.rawPoly levels component.1) =
            Factor.rawPoly levels component.1 :=
        monic_eq_self levels hvalid hinjective hinv _ hcomponentMonic
      have hirreducibleProduct :
          (irreducibles.toList.map fun factor =>
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels factor)).prod =
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels component.1) := by
        rw [← hnormalized]
        exact factorSquarefree_product levels hvalid hinjective component.1
          hrawNe hirreducibles
      have hnextSound : ∀ entry ∈
          state ++ irreducibles.map fun factor => (factor, component.2),
          Factor.polyCoords (Factor.rawPoly levels entry.1) = entry.1 ∧
            (HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels entry.1)).Monic ∧
            Irreducible (HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels entry.1)) ∧
            0 < entry.2 := by
        intro entry hentry
        rw [Array.mem_append] at hentry
        rcases hentry with hentry | hentry
        · exact hstate entry hentry
        · obtain ⟨factor, hfactor, rfl⟩ := Array.mem_map.mp hentry
          have hsound := factorSquarefree_mem_sound levels hvalid hinjective
            component.1 hirreducibles factor hfactor
          have hmonic := factorSquarefree_mem_monic levels hvalid hinjective
            component.1 hirreducibles factor hfactor
          exact ⟨hsound.1, hmonic, hsound.2, hpositive.2⟩
      have hnextProduct :
          ((state ++ irreducibles.map fun factor =>
              (factor, component.2)).toList.map fun entry =>
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels entry.1) ^ entry.2).prod =
            (state.toList.map fun entry =>
              HexPolyMathlib.toPolynomial
                (Factor.rawPoly levels entry.1) ^ entry.2).prod *
              HexPolyMathlib.toPolynomial
                (Factor.rawPoly levels component.1) ^ component.2 := by
        rw [Array.toList_append, Array.toList_map, List.map_append,
          List.prod_append]
        congr 1
        have hlabels := labeled_prod_pow
          (fun factor : Array (Array Rat) =>
            HexPolyMathlib.toPolynomial (Factor.rawPoly levels factor))
          irreducibles.toList component.2
        rw [hirreducibleProduct] at hlabels
        exact hlabels
      have htailComponents : ∀ tail ∈ components,
          tail ∈ (Factor.yunRaw levels f).toList := by
        intro tail htailMem
        exact hcomponents tail (by simp [htailMem])
      have hind := ih htailComponents
        (state ++ irreducibles.map fun factor => (factor, component.2))
        htail hnextSound
      refine ⟨hind.1, ?_⟩
      rw [hind.2, hnextProduct]
      simp only [List.map_cons, List.prod_cons]
      ring

/-- The complete raw Yun/Trager factorization pipeline cannot fail when
coefficient denotation is injective. -/
theorem factorRaw_isSome (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat)) :
    (Factor.factorRaw? levels f).isSome := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let components := Factor.yunRaw levels f
  have hcheck : Factor.checkYun levels f components :=
    checkYun_yunRaw hvalid hinjective hinv f
  let step := fun (out : Array (Array (Array Rat) × Nat))
      (component : Array (Array Rat) × Nat) => do
    let irreducibles ← Factor.factorSquarefree? levels component.1
    pure <| irreducibles.foldl
      (fun (out : Array (Array (Array Rat) × Nat))
        (factor : Array (Array Rat)) => out.push (factor, component.2)) out
  have hfold : (components.foldlM step #[]).isSome := by
    apply array_foldlM_isSome #[]
    intro out component hcomponent
    have hsquarefree := yun_squarefree hvalid hinjective hinv f
      (by
        by_cases hzero : (Factor.rawPoly levels f).degree?.getD 0 = 0
        · have hempty : components = #[] := by
            simp [components, Factor.yunRaw, hzero]
          rw [hempty] at hcomponent
          simp at hcomponent
        · exact Nat.pos_of_ne_zero hzero)
      component hcomponent
    have hdegree :=
      (yun_positive hvalid hinjective hinv f component hcomponent).1
    have hsome := factorSquarefree_isSome levels hvalid hinjective
      component.1 hsquarefree hdegree
    obtain ⟨irreducibles, hirreducibles⟩ :=
      Option.isSome_iff_exists.mp hsome
    exact Option.isSome_iff_exists.mpr ⟨irreducibles.foldl
      (fun (out : Array (Array (Array Rat) × Nat))
        (factor : Array (Array Rat)) => out.push (factor, component.2)) out, by
      simp only [step]
      rw [hirreducibles]
      rfl⟩
  obtain ⟨factors, hfactors⟩ := Option.isSome_iff_exists.mp hfold
  unfold Factor.factorRaw?
  dsimp only
  rw [show Factor.checkYun levels f (Factor.yunRaw levels f) = true by
    simpa only [components] using hcheck]
  change (do
    let factors' ← components.foldlM step #[]
    some (Factor.RawFactorization.mk
      (Factor.rawPoly levels f).leadingCoeff.data
      (Factor.canonicalFactors factors'))).isSome
  rw [hfactors]
  simp

theorem isIrreducible_nil_iff (f : Array (Array Rat)) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    Factor.isIrreducible [] f ↔
      (Factor.rawPoly [] f).leadingCoeff = 1 ∧
        Irreducible (HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)) := by
  letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  constructor
  · intro hcheck
    have hcheckRaw := hcheck
    simp only [Factor.isIrreducible, Bool.and_eq_true] at hcheck
    exact ⟨of_decide_eq_true hcheck.1.1.2,
      LevelSemantics.isIrreducible_nil_toMathlib f hcheckRaw⟩
  · rintro ⟨hmonic, hirreducible⟩
    have hdegree : 0 < (Factor.rawPoly [] f).degree?.getD 0 := by
      have hne := hirreducible.ne_zero
      have hnatDegree :
          (HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)).natDegree ≠ 0 := by
        intro hzero
        apply hirreducible.not_isUnit
        apply Polynomial.isUnit_iff_degree_eq_zero.mpr
        rw [Polynomial.degree_eq_natDegree hne, hzero]
        rfl
      rw [HexPolyMathlib.natDegree_toPolynomial] at hnatDegree
      omega
    have hsquarefree : Norm.isSquarefree [] f := by
      apply (Norm.isSquarefree_iff [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil f).mpr
      letI : CharZero (Arithmetic.Coeff []) :=
        { cast_injective := by
            intro m n hmn
            apply Nat.cast_injective (R := ℂ)
            have hmapped := congrArg
              (LevelSemantics.coeffHom [] trivial
                LevelSemantics.DenoteInjective.nil
                LevelSemantics.coeffDenote_inv_nil) hmn
            simpa using hmapped }
      have hseparable := hirreducible.separable
      have hmapped := hseparable.map
        (f := LevelSemantics.coeffHom [] trivial
          LevelSemantics.DenoteInjective.nil
          LevelSemantics.coeffDenote_inv_nil)
      rw [← Norm.rawPolynomialHom_apply [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil]
      exact hmapped.squarefree
    let raw := Factor.toRatPoly f
    let primitive := ZPoly.ratPolyPrimitivePart raw
    have hirreducibleRaw :
        Irreducible (HexPolyMathlib.toPolynomial raw) := by
      have hmapped := (MulEquiv.irreducible_iff
        (f := (Polynomial.mapEquiv
          LevelSemantics.coeffRatEquiv).toMulEquiv)).mpr hirreducible
      change Irreducible
        ((HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)).map
          LevelSemantics.coeffRatEquiv.toRingHom) at hmapped
      rw [LevelSemantics.map_rawPoly_nil] at hmapped
      exact hmapped
    obtain ⟨unit, hunit⟩ :=
      ZPoly.ratPolyPrimitivePart_rational_associate raw
    have hunitNe : unit ≠ 0 := by
      intro hzero
      apply hirreducibleRaw.ne_zero
      rw [hunit, hzero]
      simp
    have hassociate : HexPolyMathlib.toPolynomial raw =
        Polynomial.C unit * HexPolyZMathlib.toPolyℚ primitive := by
      rw [hunit, HexPolyMathlib.toPolynomial_scale,
        HexPolyZMathlib.toPolynomial_toRatPoly]
    have hirreducibleRat :
        Irreducible (HexPolyZMathlib.toPolyℚ primitive) := by
      rw [hassociate, mul_comm] at hirreducibleRaw
      exact (irreducible_mul_isUnit
        (Polynomial.isUnit_C.mpr hunitNe.isUnit)).mp hirreducibleRaw
    have hprimitiveNe : primitive ≠ 0 := by
      intro hzero
      apply hirreducibleRat.ne_zero
      rw [hzero]
      change (HexPolyZMathlib.toPolynomial 0).map
        (Int.castRingHom ℚ) = 0
      rw [HexPolyZMathlib.toPolynomial_zero, Polynomial.map_zero]
    have hprimitive :
        (HexPolyZMathlib.toPolynomial primitive).IsPrimitive :=
      HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive primitive
        (ZPoly.ratPolyPrimitivePart_primitive raw
          (HexPolyZMathlib.content_ne_zero primitive hprimitiveNe))
    have hirreducibleInt :
        Irreducible (HexPolyZMathlib.toPolynomial primitive) :=
      (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
        hprimitive).mpr hirreducibleRat
    have hchecker : ZPoly.isIrreducible primitive = true :=
      (ZPoly.isIrreducible_iff primitive).mpr
        ((ZPoly.Irreducible_iff_polynomialIrreducible primitive).mpr
          hirreducibleInt)
    simp only [Factor.isIrreducible, Bool.and_eq_true]
    exact ⟨⟨⟨of_decide_eq_true (by simpa using hdegree),
      of_decide_eq_true (by simpa using hmonic)⟩, hsquarefree⟩, hchecker⟩

private theorem list_eq_singleton_of_prod_irreducible
    {R : Type*} [CommMonoidWithZero R] (items : List R)
    (hnonunit : ∀ item ∈ items, ¬ IsUnit item)
    (hprod : Irreducible items.prod) : ∃ item, items = [item] := by
  cases items with
  | nil =>
      simpa using hprod.not_isUnit
  | cons item tail =>
      cases tail with
      | nil => exact ⟨item, rfl⟩
      | cons next rest =>
          exfalso
          rcases hprod.isUnit_or_isUnit rfl with hitem | htail
          · exact (hnonunit item (by simp)) hitem
          · have hnextDvd : next ∣ (next :: rest).prod := by
              exact dvd_mul_right next rest.prod
            have hnextUnit : IsUnit next :=
              isUnit_iff_dvd_one.mpr
                (hnextDvd.trans (isUnit_iff_dvd_one.mp htail))
            exact (hnonunit next (by simp)) hnextUnit

/-- With coefficient-denotation injectivity supplied explicitly, the recursive
Boolean checker is exactly monic polynomial irreducibility.  This generic form
breaks the logical cycle used when validating the tower itself. -/
theorem isIrreducible_iff_of_injective (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat)) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    Factor.isIrreducible levels f ↔
      (Factor.rawPoly levels f).leadingCoeff = 1 ∧
        Irreducible (HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels f)) := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  cases levels with
  | nil =>
      have hvalidEq : hvalid = (trivial : LevelsValid []) :=
        Subsingleton.elim _ _
      have hinjectiveEq : hinjective = LevelSemantics.DenoteInjective.nil :=
        Subsingleton.elim _ _
      subst hvalid
      subst hinjective
      exact isIrreducible_nil_iff f
  | cons level lower =>
      constructor
      · intro hchecker
        have hparts := hchecker
        simp only [Factor.isIrreducible, Bool.and_eq_true] at hparts
        refine ⟨of_decide_eq_true hparts.1.1.2, ?_⟩
        split at hparts
        · rename_i factors hresult
          have hfactors : factors =
              #[Factor.polyCoords (Factor.rawPoly (level :: lower) f)] :=
            of_decide_eq_true hparts.2
          have hmember : Factor.polyCoords
              (Factor.rawPoly (level :: lower) f) ∈ factors := by
            rw [hfactors]
            simp
          have hsound := factorSquarefree_mem_sound (level :: lower) hvalid
            hinjective f hresult _ hmember
          rw [rawPoly_polyCoords] at hsound
          exact hsound.2
        · simp at hparts
      · rintro ⟨hmonic, hirreducible⟩
        have hdegree :
            0 < (Factor.rawPoly (level :: lower) f).degree?.getD 0 := by
          have hnatDegree : (HexPolyMathlib.toPolynomial
              (Factor.rawPoly (level :: lower) f)).natDegree ≠ 0 := by
            intro hzero
            apply hirreducible.not_isUnit
            apply Polynomial.isUnit_iff_degree_eq_zero.mpr
            rw [Polynomial.degree_eq_natDegree hirreducible.ne_zero, hzero]
            rfl
          rw [HexPolyMathlib.natDegree_toPolynomial] at hnatDegree
          exact Nat.pos_of_ne_zero hnatDegree
        let ι := LevelSemantics.coeffHom (level :: lower) hvalid
          hinjective hinv
        letI : CharZero (Arithmetic.Coeff (level :: lower)) :=
          { cast_injective := by
              intro m n hmn
              apply Nat.cast_injective (R := ℂ)
              have hmapped := congrArg ι hmn
              simpa only [map_natCast] using hmapped }
        have hsquarefree : Norm.isSquarefree (level :: lower) f := by
          apply (Norm.isSquarefree_iff (level :: lower) hvalid hinjective
            hinv f).mpr
          have hseparable := hirreducible.separable.map (f := ι)
          rw [← Norm.rawPolynomialHom_apply (level :: lower) hvalid
            hinjective hinv]
          exact hseparable.squarefree
        have hsome := factorSquarefree_isSome (level :: lower) hvalid
          hinjective f hsquarefree hdegree
        obtain ⟨factors, hresult⟩ := Option.isSome_iff_exists.mp hsome
        have hsound : ∀ factor ∈ factors,
            Factor.polyCoords
                (Factor.rawPoly (level :: lower) factor) = factor ∧
              Irreducible (HexPolyMathlib.toPolynomial
                (Factor.rawPoly (level :: lower) factor)) :=
          factorSquarefree_mem_sound (level :: lower) hvalid hinjective f
            hresult
        have hfNe : Factor.rawPoly (level :: lower) f ≠ 0 := by
          intro hzero
          apply hirreducible.ne_zero
          rw [hzero, HexPolyMathlib.toPolynomial_zero]
        have hproduct := factorSquarefree_product (level :: lower) hvalid
          hinjective f hfNe hresult
        have hmonicPoly : (HexPolyMathlib.toPolynomial
            (Factor.rawPoly (level :: lower) f)).Monic := by
          rw [Polynomial.Monic.def,
            HexPolyMathlib.leadingCoeff_toPolynomial, hmonic]
        rw [monic_eq_self (level :: lower) hvalid hinjective hinv _
          hmonicPoly] at hproduct
        have hsingleton := list_eq_singleton_of_prod_irreducible
          (factors.toList.map fun factor => HexPolyMathlib.toPolynomial
            (Factor.rawPoly (level :: lower) factor))
          (by
            intro factor hfactor
            simp only [List.mem_map] at hfactor
            obtain ⟨rawFactor, hrawFactor, rfl⟩ := hfactor
            exact (hsound rawFactor
              (Array.mem_toList_iff.mp hrawFactor)).2.not_isUnit)
          (by simpa [hproduct] using hirreducible)
        obtain ⟨factorPoly, hfactorPolys⟩ := hsingleton
        have hfactorsSize : factors.size = 1 := by
          have hlength := congrArg List.length hfactorPolys
          simpa using hlength
        obtain ⟨factor, hfactor⟩ : ∃ factor, factors = #[factor] := by
          have hzeroLt : 0 < factors.size := by omega
          refine ⟨factors[0], ?_⟩
          apply Array.ext
          · simp [hfactorsSize]
          · intro i hi₁ hi₂
            have hi : i = 0 := by simpa [hfactorsSize] using hi₁
            subst i
            simp
        have hfactorMem : factor ∈ factors := by rw [hfactor]; simp
        have hfactorEq : factor =
            Factor.polyCoords (Factor.rawPoly (level :: lower) f) := by
          have hpolyEq : HexPolyMathlib.toPolynomial
              (Factor.rawPoly (level :: lower) factor) =
              HexPolyMathlib.toPolynomial
                (Factor.rawPoly (level :: lower) f) := by
            rw [hfactor] at hproduct
            simpa using hproduct
          have hrawEq : Factor.rawPoly (level :: lower) factor =
              Factor.rawPoly (level :: lower) f :=
            (HexPolyMathlib.equiv
              (R := Arithmetic.Coeff (level :: lower))).injective hpolyEq
          rw [← (hsound factor hfactorMem).1, hrawEq]
        have hfactors : factors =
            #[Factor.polyCoords (Factor.rawPoly (level :: lower) f)] := by
          rw [hfactor, hfactorEq]
        simp only [Factor.isIrreducible, Bool.and_eq_true]
        refine ⟨⟨⟨decide_eq_true hdegree, decide_eq_true hmonic⟩,
          hsquarefree⟩, ?_⟩
        rw [hresult]
        exact decide_eq_true hfactors

private theorem toPolynomial_polyPow (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : DensePoly (Arithmetic.Coeff levels)) (n : Nat) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    HexPolyMathlib.toPolynomial (Factor.polyPow f n) =
      HexPolyMathlib.toPolynomial f ^ n := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [Factor.polyPow]
      · rw [Factor.polyPow, if_neg hn]
        have hhalf : n / 2 < n :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
        dsimp only
        by_cases heven : n % 2 = 0
        · rw [if_pos heven, HexPolyMathlib.toPolynomial_mul,
            ih (n / 2) hhalf]
          rw [← pow_add]
          congr 1
          omega
        · rw [if_neg heven, HexPolyMathlib.toPolynomial_mul,
            HexPolyMathlib.toPolynomial_mul, ih (n / 2) hhalf]
          rw [← pow_add, ← pow_succ]
          congr 1
          omega

private theorem toPolynomial_factorFold (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (entries : List (Array (Array Rat) × Nat))
    (acc : DensePoly (Arithmetic.Coeff levels)) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    HexPolyMathlib.toPolynomial
        (entries.foldl (fun product entry =>
          product * Factor.polyPow
            (Factor.rawPoly levels entry.1) entry.2) acc) =
      HexPolyMathlib.toPolynomial acc *
        (entries.map fun entry =>
          HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1) ^ entry.2).prod := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  dsimp only
  induction entries generalizing acc with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, ih, HexPolyMathlib.toPolynomial_mul,
        toPolynomial_polyPow levels hvalid hinjective]
      simp only [List.map_cons, List.prod_cons]
      ring

private theorem leadingCoeff_mul_monic (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (p : DensePoly (Arithmetic.Coeff levels)) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    Polynomial.C p.leadingCoeff *
        HexPolyMathlib.toPolynomial (Norm.monic p) =
      HexPolyMathlib.toPolynomial p := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  dsimp only
  rw [Norm.monic]
  split
  · rename_i hzero
    have hpzero : p = 0 :=
      (DensePoly.size_eq_zero_iff p).mp
        ((DensePoly.isZero_eq_true_iff p).mp hzero)
    subst p
    simp
  · rename_i hnonzero
    rw [HexPolyMathlib.toPolynomial_scale, ← mul_assoc,
      ← Polynomial.C_mul]
    have hlc : p.leadingCoeff ≠ 0 :=
      DensePoly.leadingCoeff_ne_zero_of_pos_size p
        ((DensePoly.isZero_eq_false_iff p).mp
          (Bool.eq_false_of_not_eq_true hnonzero))
    rw [mul_inv_cancel₀ hlc]
    simp

private theorem C_leadingCoeff_eq_of_degreeZero (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (p : DensePoly (Arithmetic.Coeff levels))
    (hdegree : p.degree?.getD 0 = 0) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    DensePoly.C p.leadingCoeff = p := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  dsimp only
  apply (HexPolyMathlib.equiv
    (R := Arithmetic.Coeff levels)).injective
  change HexPolyMathlib.toPolynomial (DensePoly.C p.leadingCoeff) =
    HexPolyMathlib.toPolynomial p
  rw [HexPolyMathlib.toPolynomial_C]
  have hnat : (HexPolyMathlib.toPolynomial p).natDegree = 0 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    exact hdegree
  calc
    Polynomial.C p.leadingCoeff =
        Polynomial.C (HexPolyMathlib.toPolynomial p).leadingCoeff := by
      rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    _ = Polynomial.C ((HexPolyMathlib.toPolynomial p).coeff 0) := by
      rw [Polynomial.leadingCoeff, hnat]
    _ = HexPolyMathlib.toPolynomial p :=
      (Polynomial.eq_C_of_natDegree_eq_zero hnat).symm

private theorem factorRaw_sorted (levels : List Level)
    (f : Array (Array Rat)) {raw : Factor.RawFactorization}
    (hresult : Factor.factorRaw? levels f = some raw) :
    Factor.factorsSorted raw.factors = true := by
  simp only [Factor.factorRaw?] at hresult
  split at hresult
  · obtain ⟨factors, _, hresult⟩ := Option.bind_eq_some_iff.mp hresult
    cases hresult
    exact canonicalFactors_sorted factors
  · contradiction

/-- Every raw candidate produced by the complete Yun/Trager pipeline passes
the executable certificate replay, provided the input coordinate array is in
the canonical image of `rawPoly`. -/
theorem factorRaw_check (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat))
    (hcanonical :
      Factor.polyCoords (Factor.rawPoly levels f) = f)
    {raw : Factor.RawFactorization}
    (hresult : Factor.factorRaw? levels f = some raw) :
    Factor.check levels f raw.scalar raw.factors = true := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  have hresult' := hresult
  simp only [Factor.factorRaw?] at hresult'
  split at hresult'
  · obtain ⟨factors, hfold, hraw⟩ :=
      Option.bind_eq_some_iff.mp hresult'
    have hfoldList :
        (Factor.yunRaw levels f).toList.foldlM
          (Factor.appendComponent? levels) #[] = some factors := by
      rw [Array.foldlM_toList]
      exact hfold
    have hsound := factorFold_sound levels hvalid hinjective f
      (Factor.yunRaw levels f).toList
      (by intro component hcomponent; exact hcomponent)
      #[] factors hfoldList (by simp)
    have hpre := hsound.1
    have hpreProduct :
        (factors.toList.map fun entry =>
          HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1) ^ entry.2).prod =
          ((Factor.yunRaw levels f).toList.map fun component =>
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels component.1) ^ component.2).prod := by
      simpa using hsound.2
    cases hraw
    have hproperties : ∀ entry ∈ Factor.canonicalFactors factors,
        Factor.polyCoords (Factor.rawPoly levels entry.1) = entry.1 ∧
          (HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1)).Monic ∧
          Irreducible (HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1)) := by
      apply canonicalFactors_preserves
        (fun factor =>
          Factor.polyCoords (Factor.rawPoly levels factor) = factor ∧
            (HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels factor)).Monic ∧
            Irreducible (HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels factor)))
      intro entry hentry
      have h := hpre entry hentry
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    have hpositive : ∀ entry ∈ Factor.canonicalFactors factors,
        0 < entry.2 :=
      canonicalFactors_positive factors fun entry hentry =>
        (hpre entry hentry).2.2.2
    have hcoords :
        (Factor.canonicalFactors factors).all (fun entry =>
          Factor.polyCoords (Factor.rawPoly levels entry.1) =
            entry.1) = true := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro entry hentry
      exact decide_eq_true (hproperties entry hentry).1
    have hchecks :
        (Factor.canonicalFactors factors).all (fun entry =>
          0 < entry.2 && Factor.isIrreducible levels entry.1) = true := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro entry hentry
      simp only [Bool.and_eq_true]
      refine ⟨decide_eq_true (hpositive entry hentry), ?_⟩
      apply (isIrreducible_iff_of_injective levels hvalid hinjective
        entry.1).mpr
      have hentrySound := hproperties entry hentry
      refine ⟨?_, hentrySound.2.2⟩
      simpa only [Polynomial.Monic.def,
        HexPolyMathlib.leadingCoeff_toPolynomial] using hentrySound.2.1
    have hcanonicalProduct :
        ((Factor.canonicalFactors factors).toList.map fun entry =>
          HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1) ^ entry.2).prod =
          ((Factor.yunRaw levels f).toList.map fun component =>
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels component.1) ^ component.2).prod :=
      (canonicalFactors_prod
        (fun factor => HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels factor)) factors).trans hpreProduct
    have hreconstruct : Factor.factorProduct levels
        p.leadingCoeff.data (Factor.canonicalFactors factors) = f := by
      by_cases hdegree : p.degree?.getD 0 = 0
      · have hcomponents : Factor.yunRaw levels f = #[] := by
          simp [Factor.yunRaw, p, hdegree]
        have hfactors : factors = #[] := by
          rw [hcomponents] at hfold
          simpa using hfold
        subst factors
        change Factor.polyCoords
          (DensePoly.C (Arithmetic.Coeff.ofData levels
            p.leadingCoeff.data)) = f
        rw [LevelSemantics.coeff_ofData_data,
          C_leadingCoeff_eq_of_degreeZero levels hvalid hinjective p
            hdegree,
          hcanonical]
      · have hdegreePositive : 0 < p.degree?.getD 0 :=
          Nat.pos_of_ne_zero hdegree
        have hyun := yun_product hvalid hinjective hinv f hdegreePositive
        have hyunDense := congrArg (Factor.rawPoly levels) hyun
        unfold Factor.yunProduct at hyunDense
        simp only [rawPoly_polyCoords] at hyunDense
        rw [← Array.foldl_toList] at hyunDense
        have hcomponentProduct :
            ((Factor.yunRaw levels f).toList.map fun component =>
              HexPolyMathlib.toPolynomial
                (Factor.rawPoly levels component.1) ^ component.2).prod =
              HexPolyMathlib.toPolynomial (Norm.monic p) := by
          have hsemantic := toPolynomial_factorFold levels hvalid hinjective
            (Factor.yunRaw levels f).toList
            (1 : DensePoly (Arithmetic.Coeff levels))
          simp only [HexPolyMathlib.toPolynomial_one, one_mul] at hsemantic
          rw [← hsemantic]
          exact congrArg HexPolyMathlib.toPolynomial hyunDense
        unfold Factor.factorProduct
        rw [← hcanonical]
        apply congrArg Factor.polyCoords
        apply (HexPolyMathlib.equiv
          (R := Arithmetic.Coeff levels)).injective
        change HexPolyMathlib.toPolynomial
            ((Factor.canonicalFactors factors).foldl
              (fun product factor => product * Factor.polyPow
                (Factor.rawPoly levels factor.1) factor.2)
              (DensePoly.C (Arithmetic.Coeff.ofData levels
                p.leadingCoeff.data))) =
          HexPolyMathlib.toPolynomial p
        rw [← Array.foldl_toList,
          toPolynomial_factorFold levels hvalid hinjective,
          HexPolyMathlib.toPolynomial_C,
          LevelSemantics.coeff_ofData_data,
          hcanonicalProduct, hcomponentProduct]
        exact leadingCoeff_mul_monic levels hvalid hinjective p
    simp only [Factor.check, Bool.and_eq_true]
    exact ⟨⟨⟨hcoords, decide_eq_true hreconstruct⟩,
      canonicalFactors_sorted factors⟩, hchecks⟩
  · contradiction

private theorem relation_eq_rawPoly (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    Arithmetic.Coeff.relation level lower =
      Factor.rawPoly lower (level.polynomial lower) := by
  rw [Arithmetic.Coeff.relation, Factor.rawPoly, Level.polynomial]
  congr 1
  rw [Array.map_push]
  have hbase :
      ((List.range level.degree).map fun i =>
        Arithmetic.Coeff.ofData lower
          (level.defining.getD i #[])).toArray =
        level.defining.map (Arithmetic.Coeff.ofData lower) := by
    apply Array.ext
    · simp [hvalid.1.2]
    · intro i hi₁ hi₂
      have hi : i < level.degree := by simpa [hvalid.1.2] using hi₂
      have hidefining : i < level.defining.size := by
        simpa [hvalid.1.2] using hi
      simp [Array.getD, hi, hidefining]
  rw [hbase]
  have hone : Arithmetic.Coeff.ofData lower
      (Arithmetic.fixedCoeffs (levelsDim lower) #[1]) =
        (1 : Arithmetic.Coeff lower) := by
    exact LevelSemantics.coeff_ofData_data lower
      (1 : Arithmetic.Coeff lower)
  rw [hone]

/-- Structural validity plus the recursive checker certificates imply
injectivity of raw coefficient denotation at every tower depth. -/
theorem denoteInjective_of_valid : ∀ (levels : List Level),
    LevelsValid levels → LevelSemantics.DenoteInjective levels := by
  intro levels
  induction levels with
  | nil =>
      intro hvalid
      exact LevelSemantics.DenoteInjective.nil
  | cons level lower ih =>
      intro hvalid
      have hinjectiveLower := ih hvalid.2.2
      let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
        hinjectiveLower
      letI : Field (Arithmetic.Coeff lower) :=
        Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
      have hrelation : Irreducible (HexPolyMathlib.toPolynomial
          (Arithmetic.Coeff.relation level lower)) := by
        cases hvalid.2.1 with
        | rational hrat =>
            have hlower : lower = [] := hrat.1
            subst lower
            exact LevelSemantics.relation_irreducible_rational level
              hvalid.1 hrat
        | relative _ hchecker _ =>
            have hraw := (isIrreducible_iff_of_injective lower hvalid.2.2
              hinjectiveLower (level.polynomial lower)).mp hchecker
            rw [relation_eq_rawPoly level lower hvalid]
            exact hraw.2
      exact LevelSemantics.DenoteInjective.cons level lower hvalid
        (LevelSemantics.separates_of_irreducible level lower hvalid
          hinjectiveLower hinvLower hrelation)

end Hex.NumberTower
