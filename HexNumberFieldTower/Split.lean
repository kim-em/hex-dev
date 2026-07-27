/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Factor
public meta import HexNumberFieldTower.Factor

public section

/-!
# Adjoining roots and splitting tower polynomials

The fixed embedding of a tower is evaluated recursively in mixed-radix order.
Factor selection uses the bounded evaluation-disambiguation machinery from
`HexNumberField`: a wrong conjugate factor is rejected by a certified ball,
while exactly one factor of the candidate's enclosing polynomial is retained.
-/
namespace Hex.NumberTower

namespace Evaluation

open Arithmetic

/-- Evaluate raw mixed-radix coordinates at the absolute roots stored by a
top-first level list. The result remains factorization-lazy. -/
@[expose]
def evalCoords? : (levels : List Level) → Array Rat → Option AlgebraicRoot
  | [], data => do
      let value ← AlgebraicPoly.Common.rational? (data.getD 0 0)
      some value.toRoot
  | level :: lower, data => do
      let lowerDim := levelsDim lower
      let coefficients ← (List.range level.degree).mapM fun i =>
        evalCoords? lower (block data i lowerDim)
      coefficients.reverse.foldlM
        (fun acc coefficient => do
          let product ← acc.mul? level.root
          product.add? coefficient)
        AlgebraicNumber.zero.toRoot

/-- Evaluate a fixed tower element in its chosen absolute embedding. -/
@[expose]
def evalElem? (T : NumberTower) (a : Elem T) : Option AlgebraicRoot :=
  evalCoords? T.levels.toList (coeffs a)

/-- Exact lazy Horner evaluation of a tower polynomial at an absolute
candidate root. -/
@[expose]
def evalPoly? (T : NumberTower) (f : Poly T) (candidate : AlgebraicRoot) :
    Option AlgebraicRoot := do
  f.toArray.reverse.toList.foldlM
    (fun acc coefficient => do
      let product ← acc.mul? candidate
      let value ← evalElem? T coefficient
      product.add? value)
    AlgebraicNumber.zero.toRoot

/-- Integer magnitude majorant for raw coordinates under every embedding of
the stored level polynomials. -/
@[expose]
def coordsMajorant : (levels : List Level) → Array Rat → Nat
  | [], data => QAdjoin.ratAbsCeil (data.getD 0 0)
  | level :: lower, data =>
      let lowerDim := levelsDim lower
      let rootBound := 2 ^ cauchyExp level.root.p + 1
      (List.range level.degree).foldr
        (fun i acc =>
          acc * rootBound + coordsMajorant lower (block data i lowerDim))
        0

/-- Integer magnitude majorant for a fixed tower element. -/
@[expose]
def elemMajorant (T : NumberTower) (a : Elem T) : Nat :=
  coordsMajorant T.levels.toList (coeffs a)

/-- Certified ball Horner evaluation at the tower's fixed embedding and one
absolute candidate root. Each exact coefficient is refined far enough to
supply the common `2^-prec` input-error unit consumed by `evalMajorant`. -/
@[expose]
def evalBall? (T : NumberTower) (f : Poly T) (candidate : AlgebraicRoot)
    (prec : Nat) : Option DyadicComplexBall := do
  let candidate' ← candidate.rep.refineTo? ((prec : Int) + 1)
  let z := candidate'.1.1.square.toBall
  let coefficientBalls ← f.toArray.mapM fun coefficient => do
    let value ← evalElem? T coefficient
    let refined ← value.rep.refineTo? ((prec : Int) + 1)
    some refined.1.1.square.toBall
  match coefficientBalls.back? with
  | none => some DyadicComplexBall.zero
  | some top =>
      some <| coefficientBalls.foldr
        (fun coefficient acc => coefficient.add (z.mul acc))
        top (start := coefficientBalls.size - 1)

/-- Decide, with the prescribed finite precision endpoint, whether a tower
polynomial vanishes at an absolute candidate root. -/
@[expose]
def vanishesAt? (T : NumberTower) (f : Poly T)
    (candidate : AlgebraicRoot) : Option Bool := do
  let evaluation ← evalPoly? T f candidate
  retainZero? evaluation.p
    (Disambiguation.evalMajorant f (elemMajorant T) candidate.p)
    (evalBall? T f candidate)

end Evaluation

/-- Lift an integer polynomial coefficientwise to a tower polynomial. -/
@[expose]
def liftZPoly (T : NumberTower) (p : ZPoly) : Poly T :=
  DensePoly.ofCoeffs <| p.toArray.map fun (coefficient : Int) =>
    ofRat T (coefficient : Rat)

/-- Retain the unique multiplicity-one irreducible factor that vanishes at the
specified absolute root under the tower's fixed embedding. -/
@[expose]
def selectFactor? (T : NumberTower) (candidate : AlgebraicRoot)
    (factors : Array (Poly T × Nat)) : Option (Poly T) := do
  let selected ← factors.foldlM (fun selected entry => do
    if entry.2 = 1 then
      let keep ← Evaluation.vanishesAt? T entry.1 candidate
      if keep then some (selected.push entry.1) else some selected
    else
      none) #[]
  match selected.toList with
  | [factor] => some factor
  | _ => none

/-! Compiled fixed-embedding selection regression. -/

private def selectSqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def selectSqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def selectSqrtTwoRep : RefinedIsolation selectSqrtTwoPoly :=
  ⟨⟨selectSqrtTwoSquare, by decide⟩, by decide⟩

private def selectSqrtTwoRoot : SimpleRoot selectSqrtTwoPoly :=
  SimpleRoot.mk selectSqrtTwoRep

-- The quotient alone admits both conjugate linear factors. Evaluation at the
-- stored positive root must retain `X - sqrt(2)` and reject `X + sqrt(2)`.
#guard
    if hirred : ZPoly.isIrreducible selectSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible selectSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots selectSqrtTwoPoly then
        let extension := ofQAdjoin (x := selectSqrtTwoRoot)
          hsimple selectSqrtTwoRep rfl
        let input := liftZPoly extension.tower selectSqrtTwoPoly
        match Evaluation.evalElem? extension.tower extension.gen,
            factor? extension.tower input with
        | some evaluated, some factorization =>
            match QAdjoin.Roots.sameValue? evaluated extension.root,
                selectFactor? extension.tower extension.root
                  factorization.factors with
            | some true, some selected =>
                factorization.factors.size = 2 &&
                  selected.degree?.getD 0 = 1 &&
                  coeffs (selected.coeff 0) = #[0, -1] &&
                  Evaluation.vanishesAt? extension.tower selected
                    extension.root = some true
            | _, _ => false
        | _, _ => false
      else
        false
    else
      false

end Hex.NumberTower
