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

end HexPolyFast.Conformance
