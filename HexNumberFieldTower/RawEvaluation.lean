/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.FactorRaw
public meta import HexNumberFieldTower.FactorRaw

public section

/-!
# Fixed-embedding evaluation for raw tower coordinates

This module gives the certified tower wrapper an executable check that a level
relation vanishes at its stored absolute generator.
-/
namespace Hex.NumberTower.RawEvaluation

open Arithmetic

/-- Evaluate raw mixed-radix coordinates at the absolute roots stored by a
top-first level list. -/
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

/-- Exact lazy Horner evaluation of a raw tower polynomial at an absolute
candidate root. -/
@[expose]
def evalPoly? (levels : List Level) (f : Array (Array Rat))
    (candidate : AlgebraicRoot) : Option AlgebraicRoot := do
  f.reverse.toList.foldlM
    (fun acc coefficient => do
      let product ← acc.mul? candidate
      let value ← evalCoords? levels coefficient
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

/-- Certified ball Horner evaluation for raw tower coefficients. -/
@[expose]
def evalBall? (levels : List Level) (f : Array (Array Rat))
    (candidate : AlgebraicRoot) (prec : Nat) : Option DyadicComplexBall := do
  let candidate' ← candidate.rep.refineTo? ((prec : Int) + 1)
  let z := candidate'.1.1.square.toBall
  let coefficientBalls ← f.mapM fun coefficient => do
    let value ← evalCoords? levels coefficient
    let refined ← value.rep.refineTo? ((prec : Int) + 1)
    some refined.1.1.square.toBall
  match coefficientBalls.back? with
  | none => some DyadicComplexBall.zero
  | some top =>
      some <| coefficientBalls.foldr
        (fun coefficient acc => coefficient.add (z.mul acc))
        top (start := coefficientBalls.size - 1)

/-- Decide at the prescribed finite precision endpoint whether a raw tower
polynomial vanishes at an absolute candidate root. -/
@[expose]
def vanishesAt? (levels : List Level) (f : Array (Array Rat))
    (candidate : AlgebraicRoot) : Option Bool := do
  let evaluation ← evalPoly? levels f candidate
  let polynomial := Factor.rawPoly levels f
  retainZero? evaluation.p
    (Disambiguation.evalMajorant polynomial
      (fun coefficient => coordsMajorant levels coefficient.data) candidate.p)
    (evalBall? levels f candidate)

end Hex.NumberTower.RawEvaluation
