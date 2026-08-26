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

/-- Rebuilding a raw dense polynomial from its flattened coordinate arrays is
the identity: `Factor.polyCoords` is a section of `Factor.rawPoly`. -/
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

/-- The executable top-generator shift is composition with the affine
polynomial `X - c * α` over the extended coefficient field. -/
theorem rawPoly_shiftTop (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (c : Int) :
    Factor.rawPoly (level :: lower) (Factor.shiftTop level lower f c) =
      DensePoly.compose (Factor.rawPoly (level :: lower) f)
        (DensePoly.ofCoeffs
          #[-(Arithmetic.Coeff.ofData (level :: lower) #[(c : Rat)] *
                Factor.topGenerator level lower), 1]) := by
  rw [Factor.shiftTop, rawPoly_polyCoords]

/-- Shifted coordinate arrays are already canonical: rebuilding and
re-flattening a `Factor.shiftTop` output returns it unchanged. -/
theorem polyCoords_rawPoly_shiftTop (level : Level)
    (lower : List Level) (f : Array (Array Rat)) (c : Int) :
    Factor.polyCoords
        (Factor.rawPoly (level :: lower)
          (Factor.shiftTop level lower f c)) =
      Factor.shiftTop level lower f c := by
  rw [Factor.shiftTop, rawPoly_polyCoords]

/-- Rebuilding an `embedLower` output reads its coefficients through the
canonical coordinate injection into the extended tower. -/
theorem rawPoly_embedLower (level : Level) (lower : List Level)
    (f : Array (Array Rat)) :
    Factor.rawPoly (level :: lower) (Factor.embedLower level lower f) =
      DensePoly.ofCoeffs
        (f.map fun coefficient =>
          Arithmetic.Coeff.ofData (level :: lower) coefficient) := by
  rw [Factor.embedLower, rawPoly_polyCoords]

/-- Zero-padding lower-tower coordinate data into the extended tower agrees
with the bundled lower-coefficient embedding {name}`Norm.lowerHom`. -/
theorem ofData_lower_eq_lowerHom (level : Level) (lower : List Level)
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

/-- Lifting a lower-tower polynomial by `embedLower` is, semantically,
coefficientwise mapping through {name}`Norm.lowerHom`. -/
theorem rawPoly_embedLower_polyCoords (level : Level)
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

/-- The two-coefficient array `#[-delta, 1]` interprets to the affine
polynomial `X - C delta`. -/
theorem toPolynomial_affine {K : Type*} [Field K]
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

/-- Negating the integer shift negates the shift delta `c * α`, so opposite
shifts translate by opposite amounts. -/
theorem shiftDelta_neg (level : Level) (lower : List Level)
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

/-- Shifting by the top generator preserves irreducibility: translation by a
fixed element is a ring automorphism of the polynomial ring. -/
theorem irreducible_shiftTop_iff (level : Level)
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

/-- The zero shift is the identity on rebuilt polynomials. -/
theorem rawPoly_shiftTop_zero (level : Level) (lower : List Level)
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
def tragerNorm (level : Level) (lower : List Level)
    (f : DensePoly (Arithmetic.Coeff (level :: lower))) :
    DensePoly (Arithmetic.Coeff lower) :=
  Factor.rawPoly lower
    (Norm.oneLevel level lower (Factor.polyCoords f) 0)

/-- Norming after an executable shift agrees with the shifted one-level
resultant `Norm.oneLevel … c`, identifying the two routes to the shifted
Trager norm. -/
theorem tragerNorm_shiftTop (level : Level) (lower : List Level)
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

/-- The one-level Trager norm is multiplicative. -/
theorem tragerNorm_mul (level : Level) (lower : List Level)
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

/-- The norm of a polynomial lifted from the lower tower is its
`level.degree`-th power: every conjugate of the top generator contributes the
same factor. -/
theorem tragerNorm_lift (level : Level) (lower : List Level)
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

/-- The one-level Trager norm preserves divisibility of interpreted
polynomials. -/
theorem tragerNorm_dvd (level : Level) (lower : List Level)
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

/-- The Trager norm of a nonconstant polynomial is nonconstant: a unit norm
would force the input itself to be a unit. -/
theorem tragerNorm_not_isUnit (level : Level) (lower : List Level)
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

/-- Monic normalisation only rescales by a unit: the interpretation of
`Norm.monic f` is associated to the interpretation of `f`. -/
theorem toPolynomial_monic_associated (levels : List Level)
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

/-- The monic normalisation of a nonzero executable polynomial interprets to
a monic polynomial. -/
theorem toPolynomial_monic_monic (levels : List Level)
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

/-- Monic normalisation fixes polynomials that already interpret to monic
polynomials. -/
theorem monic_eq_self (levels : List Level)
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

/-- Core counting argument for gcd recovery: a product of two nonunits cannot
simultaneously divide a squarefree polynomial and a power of one irreducible,
since both its irreducible factors would collapse onto that irreducible and
square it inside the squarefree divisor. -/
theorem not_two_nonunits_of_squarefree_primePower
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

/-- Irreducibility of one recovered gcd: when the Trager norm of `P` is
squarefree and `q` is an irreducible lower factor, any nonconstant monic gcd
of `P` with the lift of `q` is irreducible, because its norm divides both the
squarefree norm of `P` and the prime power `q ^ level.degree`. -/
theorem recoveredCommon_irreducible (level : Level)
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

/-- Irreducibility survives un-shifting and renormalising: the recovered
factor produced from one accepted lower factor interprets to an irreducible
polynomial over the extended tower. -/
theorem recoveredFactor_irreducible (level : Level)
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

/-- Any shift accepted by the bounded search passes the executable
squarefreeness check on its one-level norm. -/
theorem findSquarefreeShiftAux_squarefree (level : Level)
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

/-- The norm returned by the bounded search is the one-level resultant at the
returned shift. -/
theorem findSquarefreeShiftAux_norm (level : Level)
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

/-- A successful `Norm.findSquarefreeShift` returns a norm passing the
executable squarefreeness check. -/
theorem findSquarefreeShift_squarefree (level : Level)
    (lower : List Level) (f : Array (Array Rat))
    {shift : Int} {norm : Array (Array Rat)}
    (h : Norm.findSquarefreeShift level lower f = some (shift, norm)) :
    Norm.isSquarefree lower norm := by
  exact findSquarefreeShiftAux_squarefree level lower f 0
    (Norm.tragerShiftCount level.degree (f.size - 1)) h

/-- A successful `Norm.findSquarefreeShift` returns the one-level resultant
at the returned shift. -/
theorem findSquarefreeShift_norm (level : Level)
    (lower : List Level) (f : Array (Array Rat))
    {shift : Int} {norm : Array (Array Rat)}
    (h : Norm.findSquarefreeShift level lower f = some (shift, norm)) :
    norm = Norm.oneLevel level lower f shift := by
  exact findSquarefreeShiftAux_norm level lower f 0
    (Norm.tragerShiftCount level.degree (f.size - 1)) h

/-- Positive rebuilt degree forces the flattened coefficient array to have at
least two entries. -/
theorem array_degree_pos_of_raw_degree_pos (levels : List Level)
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

/-- A squarefree one-level norm of a nonconstant input is itself
nonconstant, so the recursion below the top level receives a genuine
factorization problem. -/
theorem oneLevel_degree_pos (level : Level) (lower : List Level)
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

/-- The executable squarefreeness certificate is semantically sound: a
polynomial passing `Norm.isSquarefree` interprets to a squarefree polynomial
over the tower coefficient field. -/
theorem squarefree_toPolynomial_of_check (levels : List Level)
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

/-- Membership inversion for a filtered push fold: an element of the result
is either in the initial accumulator or the image of a passing input. -/
theorem mem_foldl_push_if {α β : Type*}
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

/-- A filtered push fold materialises as the initial accumulator followed by
a `filterMap` over the inputs. -/
theorem foldl_push_if_toList {α β : Type*}
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

/-- Dropping unit contributions preserves the product up to a unit: if
passing items have associated images and failing items map to units, the
filtered product is associated to the full product. -/
theorem filterMap_prod_associated {K α : Type*} [Field K]
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

/-- Taylor translation distributes over a list product. -/
theorem taylor_list_prod {K : Type*} [CommRing K]
    (c : K) : ∀ ps : List (Polynomial K),
    Polynomial.taylor c ps.prod =
      (ps.map (Polynomial.taylor c)).prod := by
  intro ps
  induction ps with
  | nil => simp
  | cons p ps ih => simp [Polynomial.taylor_mul, ih]

/-- Squarefreeness transfers along field embeddings in characteristic zero,
via separability. -/
theorem polynomial_squarefree_map {K L : Type*}
    [Field K] [Field L] [CharZero K] [CharZero L]
    (f : K →+* L) {p : Polynomial K} (hp : Squarefree p) :
    Squarefree (p.map f) :=
  PerfectField.separable_iff_squarefree.mp
    ((PerfectField.separable_iff_squarefree.mpr hp).map (f := f))

/-- Membership inversion for `Factor.recover`: every recovered factor arises
from some lower factor whose lifted gcd with the shifted component is
nonconstant, by un-shifting and renormalising that gcd. -/
theorem recover_mem (level : Level) (lower : List Level)
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

/-- Every factor produced by `Factor.recover` from canonical irreducible
lower factors is canonical and interprets to an irreducible polynomial over
the extended tower. -/
theorem recover_mem_sound (level : Level) (lower : List Level)
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

/-- Wrapping rational coefficients as singleton coordinate arrays and reading
them back is the identity. -/
theorem toRatPoly_ofRatPoly (f : DensePoly Rat) :
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

/-- Over the empty tower, `ofRatPoly` outputs canonical coordinate arrays:
rebuilding and re-flattening them is the identity for nonzero inputs. -/
theorem polyCoords_rawPoly_ofRatPoly (f : DensePoly Rat)
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

/-- Rescaling a nonzero rational polynomial by the inverse of its leading
coefficient interprets to a monic polynomial. -/
theorem toPolynomial_scale_inv_monic (f : DensePoly Rat)
    (hf : f ≠ 0) :
    (HexPolyMathlib.toPolynomial
      (DensePoly.scale f.leadingCoeff⁻¹ f)).Monic := by
  rw [HexPolyMathlib.toPolynomial_scale, Polynomial.Monic.def,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    HexPolyMathlib.leadingCoeff_toPolynomial]
  exact inv_mul_cancel₀ (DensePoly.leadingCoeff_ne_zero_of_pos_size f
    (Nat.pos_of_ne_zero fun hsize =>
      hf ((DensePoly.size_eq_zero_iff f).mp hsize)))

/-- Rescaling by the inverse leading coefficient changes the interpretation
only by a unit. -/
theorem scale_inv_associated (f : DensePoly Rat) (hf : f ≠ 0) :
    Associated
      (HexPolyMathlib.toPolynomial (DensePoly.scale f.leadingCoeff⁻¹ f))
      (HexPolyMathlib.toPolynomial f) := by
  rw [HexPolyMathlib.toPolynomial_scale]
  exact associated_unit_mul_left _ _
    (Polynomial.isUnit_C.mpr
      (inv_ne_zero (DensePoly.leadingCoeff_ne_zero_of_pos_size f
        (Nat.pos_of_ne_zero fun hsize =>
          hf ((DensePoly.size_eq_zero_iff f).mp hsize)))).isUnit)

/-- The monic rational polynomial obtained from an integer factor by reading
it rationally and dividing by its leading coefficient. -/
@[expose]
noncomputable def normalizedRatFactor (f : ZPoly) : Polynomial Rat :=
  HexPolyMathlib.toPolynomial <|
    DensePoly.scale f.toRatPoly.leadingCoeff⁻¹ f.toRatPoly

/-- The rational reading of a nonzero integer polynomial is nonzero. -/
theorem toRatPoly_ne_zero {f : ZPoly} (hf : f ≠ 0) :
    f.toRatPoly ≠ 0 := by
  intro hzero
  have hmapped := congrArg HexPolyMathlib.toPolynomial hzero
  rw [HexPolyZMathlib.toPolynomial_toRatPoly,
    HexPolyMathlib.toPolynomial_zero] at hmapped
  exact HexPolyZMathlib.toPolyℚ_ne_zero hf hmapped

/-- The product of monically rescaled integer factors is monic and
associated to the product of their plain rational readings. -/
theorem normalizedRatFactors_monic_associated
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

/-- The executable integer factor power reads rationally as the polynomial
power. -/
theorem factorPower_toPolyℚ (f : ZPoly) (n : Nat) :
    HexPolyZMathlib.toPolyℚ (Hex.Factorization.factorPower f n) =
      HexPolyZMathlib.toPolyℚ f ^ n := by
  rw [HexPolyZMathlib.toPolyℚ, HexPolyZMathlib.toPolyℚ,
    ← Polynomial.map_pow,
    ← HexBerlekampZassenhausMathlib.factorPower_toPolynomial]

/-- Rational reading of integer polynomials is multiplicative. -/
theorem toPolyℚ_mul (f g : ZPoly) :
    HexPolyZMathlib.toPolyℚ (f * g) =
      HexPolyZMathlib.toPolyℚ f * HexPolyZMathlib.toPolyℚ g := by
  rw [HexPolyZMathlib.toPolyℚ, HexPolyZMathlib.toPolynomial_mul,
    Polynomial.map_mul]

/-- The executable fold multiplying labelled integer factor powers reads
rationally as the initial value times the multiplicity-expanded product of
the factors. -/
theorem factorizationProduct_toPolyℚ_foldl
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

/-- A `Hex.Factorization` reads rationally as its scalar times the
multiplicity-expanded product of its factors. -/
theorem factorizationProduct_toPolyℚ (factorization : Hex.Factorization) :
    HexPolyZMathlib.toPolyℚ factorization.product =
      Polynomial.C (factorization.scalar : Rat) *
        (factorization.factors.toList.flatMap fun entry =>
          List.replicate entry.2 (HexPolyZMathlib.toPolyℚ entry.1)).prod := by
  rw [Hex.Factorization.product_eq_foldl_factorPower,
    ← Array.foldl_toList, factorizationProduct_toPolyℚ_foldl,
    HexPolyZMathlib.toPolyℚ, HexPolyZMathlib.toPolynomial_C,
    Polynomial.map_C]
  congr 2

/-- Monically rescaling the multiplicity-expanded Berlekamp-Zassenhaus
factors of a nonzero integer polynomial yields a monic product associated to
its rational reading. -/
theorem factorize_normalized_product (f : ZPoly) (hf : f ≠ 0) :
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

/-- Each Berlekamp-Zassenhaus factor stays irreducible after monic rational
rescaling: primitivity transfers integer irreducibility to `ℚ` by Gauss's
lemma, and rescaling is associated. -/
theorem normalizedRatFactor_irreducible (integer : ZPoly)
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

/-- The empty-tower coordinate encoding of a monically rescaled
Berlekamp-Zassenhaus factor interprets to an irreducible polynomial. -/
theorem rawRatFactor_irreducible (integer : ZPoly)
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
/-- Every multiplicity-expanded, monically rescaled Berlekamp-Zassenhaus
factor is a canonical coordinate array interpreting to an irreducible
polynomial over the empty tower. -/
theorem generatedRatFactors_sound (integer : ZPoly)
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
/-- Base-case soundness of the rational factorizer: every factor returned by
`Factor.factorRat?` is canonical and interprets to an irreducible
polynomial. -/
theorem factorRat_mem_sound (input : DensePoly Rat)
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

/-- Soundness of the squarefree-component factorizer at every tower height:
each returned factor is a canonical coordinate array interpreting to an
irreducible polynomial, by induction through the recursive one-level Trager
step with the Berlekamp-Zassenhaus base case. -/
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

end Hex.NumberTower
