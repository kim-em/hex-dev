/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.Convert
public import HexResultant
public meta import HexNumberField.Convert
public meta import HexResultant

public section

/-!
Factorization-lazy arithmetic for algebraic roots.

Binary operations form their integer eliminants with bivariate resultants,
discard multiplicities by primitive square-free normalization, and select the
desired root using a certified operation ball at the eliminant's separation
depth. Negation reflects both the polynomial and its root certificate directly.
-/
namespace Hex

namespace ZPoly

/-- Regard an integer polynomial in `y` as a polynomial in `y` whose
coefficients are constant polynomials in a second variable `t`. -/
@[expose]
def liftOuter (p : ZPoly) : DensePoly ZPoly :=
  DensePoly.ofCoeffs (p.toArray.map DensePoly.C)

/-- Coefficients of the outer lift are the corresponding constant
polynomials. -/
@[simp] theorem coeff_liftOuter (p : ZPoly) (n : Nat) :
    p.liftOuter.coeff n = DensePoly.C (p.coeff n) := by
  unfold liftOuter
  rw [DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?,
    Array.getElem?_map]
  by_cases hn : n < p.size
  · have hnArray : n < p.toArray.size := by simpa using hn
    rw [Array.getElem?_eq_getElem hnArray]
    simp only [Option.map_some, Option.getD_some]
    congr 1
    rw [Array.getElem_eq_getD (Zero.zero : Int), DensePoly.toArray_getD]
  · have hnArray : p.toArray.size ≤ n := by simpa using Nat.le_of_not_gt hn
    rw [Array.getElem?_eq_none hnArray]
    simp only [Option.map_none, Option.getD_none]
    have hpcoeff : p.coeff n = 0 :=
      DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hn)
    rw [hpcoeff]
    rfl

/-- The eliminant whose roots are pairwise sums of roots of `p` and `q`. -/
@[expose]
def addEliminant (p q : ZPoly) : ZPoly :=
  let y : DensePoly ZPoly := DensePoly.monomial 1 1
  let t : DensePoly ZPoly := DensePoly.C ZPoly.X
  DensePoly.resultant p.liftOuter (DensePoly.compose q.liftOuter (t - y))

/-- The polynomial `y^degree(q) q(t/y)`, viewed as a polynomial in `y`
with coefficients in `Int[t]`. -/
@[expose]
def mulSubstitute (q : ZPoly) : DensePoly ZPoly :=
  let n := q.degree?.getD 0
  DensePoly.ofCoeffs <| ((List.range (n + 1)).map fun j =>
    DensePoly.monomial (n - j) (q.coeff (n - j))).toArray

/-- The eliminant whose roots are pairwise products of roots of `p` and `q`. -/
@[expose]
def mulEliminant (p q : ZPoly) : ZPoly :=
  DensePoly.resultant p.liftOuter q.mulSubstitute

/-- Remove the largest power of `X` dividing an integer polynomial. -/
@[expose]
def removeX (p : ZPoly) : ZPoly :=
  DensePoly.ofCoeffs (p.toArray.reverse.popWhile (· == 0)).reverse

/-- Reverse coefficients, automatically trimming the degree drop caused by
an original zero constant coefficient. -/
@[expose]
def reciprocal (p : ZPoly) : ZPoly :=
  DensePoly.ofCoeffs p.toArray.reverse

/-- Negating roots preserves primitive normalization. -/
theorem negRoots_primitive (p : ZPoly) (h : Primitive p) :
    Primitive (negRoots p) := by
  rw [negRoots_eq_reflect h]
  exact primitive_normalizePrimitiveSign (primitive_dilate_neg_one h)

/-- Negating roots preserves positive leading normalization. -/
theorem negRoots_lc_pos (p : ZPoly) (hprim : Primitive p)
    (h : 0 < p.leadingCoeff) :
    0 < (negRoots p).leadingCoeff := by
  rw [negRoots_eq_reflect hprim]
  apply leadingCoeff_normalizePrimitiveSign_pos_of_ne_zero
  apply dilate_neg_one_ne_zero
  intro hp
  rw [hp] at h
  simp at h

/-- Negating roots preserves positive degree. -/
theorem negRoots_degree_pos (p : ZPoly) (hprim : Primitive p)
    (h : 0 < p.degree?.getD 0) :
    0 < (negRoots p).degree?.getD 0 := by
  rw [negRoots_eq_reflect hprim, degree?_normalizePrimitiveSign,
    degree?_dilate_neg_one]
  exact h

/-- Negating roots preserves squarefreeness. -/
theorem negRoots_simple (p : ZPoly) (hprim : Primitive p)
    (h : HasOnlySimpleRoots p) :
    HasOnlySimpleRoots (negRoots p) := by
  rw [negRoots_eq_reflect hprim]
  exact ZPoly.squareFreeRat_normalizePrimitiveSign _
    (ZPoly.squareFreeRat_dilate_neg_one p h)

/-- The Mahler precision is invariant under reflection and unit
normalization. -/
theorem mahlerPrec_negRoots (p : ZPoly) (h : Primitive p) :
    mahlerPrec (negRoots p) = mahlerPrec p := by
  unfold mahlerPrec
  rw [negRoots_eq_reflect h, degree?_normalizePrimitiveSign,
    degree?_dilate_neg_one, coeffAbsMax_normalizePrimitiveSign,
    coeffAbsMax_dilate_neg_one]

end ZPoly

namespace DyadicComplexBall

/-- Reflection of a complex ball. -/
@[expose]
def neg (b : DyadicComplexBall) : DyadicComplexBall :=
  ⟨-b.re, -b.im, b.radius⟩

/-- Minkowski difference of complex balls. -/
@[expose]
def sub (a b : DyadicComplexBall) : DyadicComplexBall :=
  a.add b.neg

/-- Checked reciprocal enclosure. The centre reciprocal is rounded downward
coordinatewise; three ulps cover both coordinate errors and the downward
rounding of the radial distortion bound. -/
@[expose]
def inv? (b : DyadicComplexBall) (prec : Int) : Option DyadicComplexBall :=
  let c : GaussDyadic := (b.re, b.im)
  let lower := GaussDyadic.lo c
  if b.radius < lower then
    let norm := GaussDyadic.normSq c
    let denom := (lower - b.radius) * lower
    let ulp := Dyadic.ofIntWithPrec 1 prec
    let re := (b.re.toRat / norm.toRat).toDyadic prec
    let im := ((-b.im.toRat) / norm.toRat).toDyadic prec
    let distortion := (b.radius.toRat / denom.toRat).toDyadic prec
    some ⟨re, im, distortion + ulp + ulp + ulp⟩
  else
    none

end DyadicComplexBall

/-- Reflect a refined isolation while preserving its root certificate and
separation precision. -/
@[expose]
def RefinedIsolation.neg {p : ZPoly} (r : RefinedIsolation p)
    (hprim : ZPoly.Primitive p) : RefinedIsolation p.negRoots :=
  ⟨⟨r.1.square.neg, .neg hprim r.1.witness⟩, by
    rw [ZPoly.mahlerPrec_negRoots p hprim]
    exact r.2⟩

namespace AlgebraicRoot

/-- Normalize an eliminant, isolate all of its distinct roots, and retain the
root meeting the supplied certified operation ball. -/
@[expose]
def ofEliminant? (raw : ZPoly)
    (ballAt : Int → Option DyadicComplexBall) : Option AlgebraicRoot := do
  let p := ZPoly.squareFreeCore raw
  if hprim : ZPoly.content p = 1 then
    if hpos : 0 < p.leadingCoeff then
      if hdegree : 0 < p.degree?.getD 0 then
        if hsimple : HasOnlySimpleRoots p then do
          let prec : Int := separationDepth p
          let ball ← ballAt prec
          let isolations ← isolate p hsimple prec
          let refined ← isolations.mapM DyadicRootIsolation.toRefined?
          match refined.toList.filter fun r => r.1.square.meetsBall ball with
          | [matching] =>
              some
                { p
                  prim := hprim
                  pos_lc := hpos
                  pos_degree := hdegree
                  squarefree := hsimple
                  x := SimpleRoot.mk matching
                  rep := matching
                  rep_mk := rfl }
          | _ => none
        else
          none
      else
        none
    else
      none
  else
    none

/-- Certificate-free negation by reflection. -/
@[expose]
def neg (a : AlgebraicRoot) : AlgebraicRoot :=
  let rep := a.rep.neg a.prim
  { p := a.p.negRoots
    prim := ZPoly.negRoots_primitive a.p a.prim
    pos_lc := ZPoly.negRoots_lc_pos a.p a.prim a.pos_lc
    pos_degree := ZPoly.negRoots_degree_pos a.p a.prim a.pos_degree
    squarefree := ZPoly.negRoots_simple a.p a.prim a.squarefree
    x := SimpleRoot.mk rep
    rep
    rep_mk := rfl }

/-- Checked lazy sum through the addition eliminant. -/
@[expose]
def add? (a b : AlgebraicRoot) : Option AlgebraicRoot :=
  ofEliminant? (ZPoly.addEliminant a.p b.p) fun prec => do
    let target := prec + 4
    let ar ← a.rep.refineTo? target
    let br ← b.rep.refineTo? target
    some (ar.1.1.square.toBall.add br.1.1.square.toBall)

/-- Total lazy sum. -/
@[expose]
def add (a b : AlgebraicRoot) : AlgebraicRoot :=
  (a.add? b).getD
    (Hex.panicWith AlgebraicNumber.zero.toRoot
      "AlgebraicRoot.add: certification failed")

/-- Checked lazy difference. -/
@[expose]
def sub? (a b : AlgebraicRoot) : Option AlgebraicRoot :=
  a.add? b.neg

/-- Total lazy difference. -/
@[expose]
def sub (a b : AlgebraicRoot) : AlgebraicRoot :=
  (a.sub? b).getD
    (Hex.panicWith AlgebraicNumber.zero.toRoot
      "AlgebraicRoot.sub: certification failed")

/-- Guard bits for multiplication-ball amplification. -/
@[expose]
def mulGuardBits (a b : AlgebraicRoot) : Nat :=
  8 + QAdjoin.rootBits a.rep.1.square + QAdjoin.rootBits b.rep.1.square

/-- Guard bits for reciprocal-ball amplification. For a nonzero root of the
primitive integer polynomial `p`, reciprocal Cauchy gives
`|a| ≥ 1 / (1 + coeffAbsMax p)`. Doubling the bit bound pays for the
`|a|⁻²` distortion in inversion; sixteen further bits cover the strict
nonzero guard and dyadic rounding. -/
@[expose]
def invGuardBits (a : AlgebraicRoot) : Nat :=
  2 * Hex.ceilLog2 (ZPoly.coeffAbsMax a.p + 1) + 16

/-- Checked lazy product through the product eliminant. -/
@[expose]
def mul? (a b : AlgebraicRoot) : Option AlgebraicRoot :=
  if a.isZero || b.isZero then
    some AlgebraicNumber.zero.toRoot
  else
    let raw := (ZPoly.mulEliminant a.p b.p).removeX
    ofEliminant? raw fun prec => do
      let target := prec + (mulGuardBits a b : Int)
      let ar ← a.rep.refineTo? target
      let br ← b.rep.refineTo? target
      some (ar.1.1.square.toBall.mul br.1.1.square.toBall)

/-- Total lazy product. -/
@[expose]
def mul (a b : AlgebraicRoot) : AlgebraicRoot :=
  (a.mul? b).getD
    (Hex.panicWith AlgebraicNumber.zero.toRoot
      "AlgebraicRoot.mul: certification failed")

/-- Checked lazy inverse through coefficient reversal. -/
@[expose]
def inv? (a : AlgebraicRoot) : Option AlgebraicRoot :=
  if a.isZero then
    some AlgebraicNumber.zero.toRoot
  else
    ofEliminant? a.p.reciprocal fun prec => do
      let target := prec + (invGuardBits a : Int)
      let ar ← a.rep.refineTo? target
      ar.1.1.square.toBall.inv? target

/-- Total lazy inverse, with `inv 0 = 0`. -/
@[expose]
def inv (a : AlgebraicRoot) : AlgebraicRoot :=
  a.inv?.getD
    (Hex.panicWith AlgebraicNumber.zero.toRoot
      "AlgebraicRoot.inv: certification failed")

/-- Checked lazy quotient. -/
@[expose]
def div? (a b : AlgebraicRoot) : Option AlgebraicRoot := do
  let bInv ← b.inv?
  a.mul? bInv

/-- Total lazy quotient. -/
@[expose]
def div (a b : AlgebraicRoot) : AlgebraicRoot :=
  (a.div? b).getD
    (Hex.panicWith AlgebraicNumber.zero.toRoot
      "AlgebraicRoot.div: certification failed")

end AlgebraicRoot

namespace AlgebraicNumber

@[expose] def add (a b : AlgebraicNumber) : AlgebraicNumber :=
  (a.toRoot.add b.toRoot).exact

@[expose] def sub (a b : AlgebraicNumber) : AlgebraicNumber :=
  (a.toRoot.sub b.toRoot).exact

@[expose] def mul (a b : AlgebraicNumber) : AlgebraicNumber :=
  (a.toRoot.mul b.toRoot).exact

@[expose] def neg (a : AlgebraicNumber) : AlgebraicNumber :=
  a.toRoot.neg.exact

@[expose] def inv (a : AlgebraicNumber) : AlgebraicNumber :=
  a.toRoot.inv.exact

@[expose] def div (a b : AlgebraicNumber) : AlgebraicNumber :=
  (a.toRoot.div b.toRoot).exact

instance : Add AlgebraicNumber := ⟨add⟩
instance : Sub AlgebraicNumber := ⟨sub⟩
instance : Mul AlgebraicNumber := ⟨mul⟩
instance : Neg AlgebraicNumber := ⟨neg⟩
instance : Inv AlgebraicNumber := ⟨inv⟩
instance : Div AlgebraicNumber := ⟨div⟩

end AlgebraicNumber

/-! Compiled eliminant-shape checks. -/

#guard
    let p : ZPoly := DensePoly.ofList [-2, 0, 1]
    ZPoly.addEliminant p p = DensePoly.ofList [0, 0, -8, 0, 1] &&
      ZPoly.mulEliminant p p = DensePoly.ofList [16, 0, -8, 0, 1] &&
      ZPoly.reciprocal p = DensePoly.ofList [1, 0, -2]

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def sqrtTwoRoot (hsimple : HasOnlySimpleRoots sqrtTwoPoly) :
    AlgebraicRoot where
  p := sqrtTwoPoly
  prim := by rfl
  pos_lc := by decide
  pos_degree := by decide
  squarefree := hsimple
  x := SimpleRoot.mk sqrtTwoRep
  rep := sqrtTwoRep
  rep_mk := rfl

#guard
    if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
      let a := sqrtTwoRoot hsimple
      match a.add? a, a.sub? a, a.mul? a, a.inv?, a.div? a with
      | some sum, some difference, some product, some inverse, some quotient =>
          sum.p = DensePoly.ofList [0, -8, 0, 1] && !sum.isZero &&
            difference.p = DensePoly.ofList [0, -8, 0, 1] && difference.isZero &&
            product.p = DensePoly.ofList [-4, 0, 1] &&
              decide (0 < product.rep.1.square.re) &&
            inverse.p = DensePoly.ofList [-1, 0, 2] &&
              decide (0 < inverse.rep.1.square.re) &&
            quotient.p = DensePoly.ofList [-1, 0, 1] &&
              decide (0 < quotient.rep.1.square.re)
      | _, _, _, _, _ => false
    else
      false

private def tinyRootDen : Int := (2 : Int) ^ 60

private def tinyRootPoly : ZPoly := DensePoly.ofList [-1, tinyRootDen]

private def tinyRootSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 1 60, 0, 70⟩

private def tinyRootRep : RefinedIsolation tinyRootPoly :=
  ⟨⟨tinyRootSquare, .ofWitness (by decide)⟩, by decide⟩

private def tinyRoot (hsimple : HasOnlySimpleRoots tinyRootPoly) :
    AlgebraicRoot where
  p := tinyRootPoly
  prim := by rfl
  pos_lc := by decide
  pos_degree := by decide
  squarefree := hsimple
  x := SimpleRoot.mk tinyRootRep
  rep := tinyRootRep
  rep_mk := rfl

-- Regression for reciprocal precision depending on root magnitude rather than
-- only degree: the old fixed degree-one budget returned `none` here.
#guard
    if hsimple : HasOnlySimpleRoots tinyRootPoly then
      match (tinyRoot hsimple).inv? with
      | some inverse =>
          inverse.p = DensePoly.ofList [-tinyRootDen, 1] &&
            decide (0 < inverse.rep.1.square.re)
      | none => false
    else
      false

end Hex
