/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast
public meta import HexPoly.Dense
public meta import HexPolyFast.Plan
public meta import HexPolyFast.Karatsuba
public meta import HexPolyFast.Reverse
public meta import HexPolyFast.Cyclic
public meta import HexPolyFast.Reciprocal
public meta import HexPolyFast.Division
public meta import HexPolyFast.Tree
public meta import HexPolyFast.Multipoint
public meta import HexPolyFast.Interpolation

public section

/-!
# Fast polynomial core conformance

Oracle: the independent `DensePoly.mul` schoolbook implementation.
Mode: always.

The initial suite covers full and specialized-square Karatsuba recursion,
cutoff zero, odd splits, normalized trailing zeros, strongly unbalanced
blocking, arbitrary slices, and the guarded polynomial/series reversal bridge.
-/

namespace HexPolyFast.Conformance

open Hex Hex.DensePoly

private def a : DensePoly Int :=
  ofList [3, -2, 0, 5, 1, -7, 4]

private def b : DensePoly Int :=
  ofList [-1, 6, 2, 0, -3]

private def trailing : DensePoly Int :=
  ofList [3, -2, 0, 5, 1, -7, 4, 0, 0]

private def long : DensePoly Int :=
  ofList ((List.range 65).map fun i => Int.ofNat i - 17)

private def short : DensePoly Int := ofList [2, -3]

#guard mulKaratsuba 0 a b = a * b
#guard mulKaratsuba 2 a b = a * b
#guard mulKaratsuba 3 trailing b = trailing * b
#guard squareKaratsuba 0 a = a * a
#guard squareKaratsuba 3 a = a * a
#guard mulKaratsuba 2 long short = long * short
#guard mulKaratsuba 2 short long = short * long

private def plan : MulPlan Int := karatsubaPlan 2

#guard mulWith plan a b = a * b
#guard squareWith plan a = a * a
#guard mulSlice plan 2 4 a b = schoolbookSlice 2 4 a b
#guard mulSlice plan 50 4 a b = 0

#guard (reverseSeries (C (1 : Int)) 2).coeffs.toArray.toList = [1, 0]
#guard (polyOfSeries (reverseSeries a a.size)).coeff 0 = a.coeff 6
#guard (polyOfSeries (reverseSeries a a.size)).coeff 3 = a.coeff 3
#guard (polyOfSeries (reverseSeries a a.size)).coeff 6 = a.coeff 0
#guard (polyOfSeries (reverseSeries a a.size)).coeff 7 = 0

#guard mulCyclic (karatsubaPlan 2) 3 (by omega)
    (ofList [1, 2, 3] : DensePoly Int) (ofList [4, 5]) = ofList [19, 13, 22]
#guard mulNegacyclic (karatsubaPlan 2) 3 (by omega)
    (ofList [1, 2, 3] : DensePoly Int) (ofList [4, 5]) = ofList [-11, 13, 22]
#guard mulCyclic? (karatsubaPlan 2) 0 a b = none

private def unitSeries : TSeries Int 8 :=
  TSeries.ofFn fun i => [1, 2, -1, 3, 0, -2, 4, 1].getD i 0

#guard seriesMulUpTo plan 5 unitSeries unitSeries =
  TSeries.mulUpTo 5 unitSeries unitSeries
#guard reciprocalWith plan unitSeries 1 = TSeries.invOfUnit unitSeries 1
#guard unitSeries * reciprocalWith plan unitSeries 1 = 1

private def monicDivisor : DensePoly Int := ofList [2, -3, 1]

private theorem monicDivisor_monic : Monic monicDivisor := by
  rfl

#guard divModMonicWith plan a monicDivisor monicDivisor_monic =
  divModMonic a monicDivisor monicDivisor_monic
#guard divModMonicWith plan (monicDivisor * b) monicDivisor
    monicDivisor_monic = (b, 0)
#guard divModMonicWith plan (ofList [4, -1]) monicDivisor
    monicDivisor_monic = (0, ofList [4, -1])
#guard divModMonicWith plan a (C (1 : Int)) (by rfl) = (a, 0)

private def ratA : DensePoly Rat :=
  ofList [3, -2, 0, 5, 1, -7, 4]

private def ratB : DensePoly Rat := ofList [2, -3, 5]

#guard divModWith (karatsubaPlan 2) ratA ratB = divMod ratA ratB
#guard divModWith (karatsubaPlan 2) ratA 0 = (0, ratA)
#guard divModWith (karatsubaPlan 2) (ratA * ratB) ratB = (ratA, 0)

private def treeLeaves : Array (DensePoly Int) :=
  #[ofList [1, 1], ofList [2, 1], ofList [3, 1], ofList [4, 1], ofList [5, 1]]

private def tree : ProductTree Int := ProductTree.build plan treeLeaves

#guard tree.leaves = treeLeaves
#guard tree.levelCount = 4
#guard tree.root = treeLeaves.foldl (fun acc p => acc * p) 1
#guard (tree.level? 0).map Array.size = some 5
#guard (tree.level? 1).map Array.size = some 3
#guard (tree.level? 2).map Array.size = some 2
#guard (tree.level? 3).map Array.size = some 1
#guard tree.nodeProduct? 1 0 = some (treeLeaves.getD 0 0 * treeLeaves.getD 1 0)
#guard tree.nodeProduct? 1 2 = some (treeLeaves.getD 4 0)

private def evalPoints : Array Int := #[-3, 0, 2, 5, 9]
private def evalPlan : EvalPlan Int := EvalPlan.build plan evalPoints
private def evalPoly : DensePoly Int := ofList [7, -4, 3, 2, -1]

#guard evalPlan.size = evalPoints.size
#guard evalPlan.points = evalPoints
#guard evalPlan.tree.leaves = evalPoints.map (fun x => ofList [0 - x, 1])
#guard evalPlan.evalImpl evalPoly = evalPoints.map (evalPoly.eval ·)
#guard evalPlan.evalImpl (ofList [1, 2, 3, 4, 5, 6, 7]) =
  evalPoints.map ((ofList [1, 2, 3, 4, 5, 6, 7] : DensePoly Int).eval ·)
#guard (EvalPlan.build plan (#[] : Array Int)).evalImpl evalPoly = #[]
#guard tree.nodeProduct? 3 0 = some tree.root
#guard tree.nodeProduct? 4 0 = none

private def interpPoints : Array Rat := #[-1, 0, 2]
private def interpValues : Array Rat := #[6, 3, 3]
private def interpPoly : DensePoly Rat := ofList [3, -2, 1]

#guard (InterpPlan.build? (karatsubaPlan 2) interpPoints).isSome
#guard (InterpPlan.build? (karatsubaPlan 2) (#[1, 2, 1] : Array Rat)).isNone
#guard match InterpPlan.build? (karatsubaPlan 2) interpPoints with
  | none => false
  | some interpolation => interpolation.interpolate? #[6, 3] = none
#guard match InterpPlan.build? (karatsubaPlan 2) interpPoints with
  | none => false
  | some interpolation => interpolation.interpolate? interpValues = some interpPoly
#guard match InterpPlan.build? (karatsubaPlan 2) interpPoints with
  | none => false
  | some interpolation =>
      match interpolation.interpolate? interpValues with
      | none => false
      | some p => interpolation.evalPlan.evalImpl p = interpValues
#guard match InterpPlan.build? (karatsubaPlan 2) (#[] : Array Rat) with
  | none => false
  | some interpolation => interpolation.interpolate? #[] = some 0

end HexPolyFast.Conformance
