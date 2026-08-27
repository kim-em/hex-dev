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
public meta import HexPolyFast.RemainderTree
public meta import HexPolyFast.HalfGcd
public meta import HexPolyFast.Pade

public section

/-!
# Fast polynomial core conformance

Oracle: established `DensePoly`/`TSeries` specifications in this module, plus
the exact Python/FLINT checker for every emitted JSONL result.
Mode: always.

Covered operations: multiplication plans, full/square/low/slice/middle
products, cyclic and negacyclic products, polynomial/series reversal,
truncated multiplication and reciprocal, one-shot and cached division,
product and remainder trees, multipoint evaluation and interpolation,
gcd/extended gcd, and homogeneous/normalized Padé approximation.  The emitted
cross-library stream additionally covers the coefficient-owner NTT, CRT-NTT,
and KS1/KS2/KS3/KS4 entry points named by the library SPEC.

Covered properties: agreement with the established operations, clipped-window
semantics, quotient/remainder reconstruction, cyclic output bounds, reciprocal
identity, product-tree roots, pointwise evaluation/interpolation round trips,
Bézout identities, and Padé degree/congruence contracts.

Covered edge cases: empty and constant operands, normalized clipped outputs,
cutoff and odd-split boundaries, balanced through 64:1 inputs, empty and
out-of-range windows, zero cyclic length, zero and exact division, cached-plan
capacity, empty/singleton/odd trees, empty and duplicate point sets, mismatched
values, zero gcd inputs and reversed degrees, and unit/nonunit/empty Padé data.
-/

namespace HexPolyFast.Conformance

open Hex Hex.DensePoly

private def a : DensePoly Int :=
  ofList [3, -2, 0, 5, 1, -7, 4]

private def b : DensePoly Int :=
  ofList [-1, 6, 2, 0, -3]

private def cancellingLeft : DensePoly Int := ofList [1, 1]

private def cancellingRight : DensePoly Int := ofList [1, -1]

private def long : DensePoly Int :=
  ofList ((List.range 65).map fun i => Int.ofNat i - 17)

private def short : DensePoly Int := ofList [2, -3]

private def ratioUnder2Left : DensePoly Int :=
  ofList ((List.range 128).map fun i => Int.ofNat (i % 17) - 8)

private def ratioUnder2Right : DensePoly Int :=
  ofList ((List.range 80).map fun i => Int.ofNat (i % 19) - 9)

#guard mulKaratsuba 0 a b = a * b
#guard mulKaratsuba 2 a b = a * b
#guard mulKaratsuba 3 cancellingLeft cancellingRight = cancellingLeft * cancellingRight
#guard squareKaratsuba 0 a = a * a
#guard squareKaratsuba 3 a = a * a
#guard mulKaratsuba 2 long short = long * short
#guard mulKaratsuba 2 short long = short * long
#guard mulKaratsuba 32 ratioUnder2Left ratioUnder2Right =
  ratioUnder2Left * ratioUnder2Right

private def plan : MulPlan Int := karatsubaPlan 2

#guard mulWith (schoolbookPlan : MulPlan Int) a b = a * b
#guard mulWith (schoolbookPlan : MulPlan Int) 0 b = 0
#guard mulWith (schoolbookPlan : MulPlan Int) cancellingLeft cancellingRight =
  cancellingLeft * cancellingRight
#guard mulWith plan a b = a * b
#guard mulWith plan 0 b = 0
#guard mulWith plan cancellingLeft cancellingRight = cancellingLeft * cancellingRight
#guard squareWith plan a = a * a
#guard squareWith plan 0 = 0
#guard squareWith plan cancellingLeft = cancellingLeft * cancellingLeft
#guard mulLow plan 4 a b = schoolbookSlice 0 4 a b
#guard mulLow plan 0 a b = 0
#guard mulLow plan 100 a b = a * b
#guard mulSlice plan 2 4 a b = schoolbookSlice 2 4 a b
#guard mulSlice plan 50 4 a b = 0
#guard mulSlice plan 0 100 0 a = 0
#guard mulSlice plan 0 100 a 0 = 0
#guard mulSlice plan 0 2 long b = schoolbookSlice 0 2 long b
#guard mulSlice plan 0 2 cancellingLeft cancellingRight = C 1
#guard (mulSlice plan 0 2 cancellingLeft cancellingRight).size = 1
#guard mulMiddleChecked plan a b =
  schoolbookSlice (b.size - 1) (a.size - b.size + 1) a b
#guard mulMiddleChecked plan b a = mulMiddleChecked plan a b
#guard mulMiddleChecked plan 0 a = 0
#guard mulMiddle plan a b (by decide) (by decide) =
  schoolbookSlice (b.size - 1) (a.size - b.size + 1) a b
#guard mulMiddle plan a (C 2) (by decide) (by decide) =
  schoolbookSlice 0 a.size a (C 2)
#guard mulMiddle plan a short (by decide) (by decide) =
  schoolbookSlice (short.size - 1) (a.size - short.size + 1) a short

#guard (reverseSeries (C (1 : Int)) 2).coeffs.toArray.toList = [1, 0]
#guard (polyOfSeries (reverseSeries a a.size)).coeff 0 = a.coeff 6
#guard (polyOfSeries (reverseSeries a a.size)).coeff 3 = a.coeff 3
#guard (polyOfSeries (reverseSeries a a.size)).coeff 6 = a.coeff 0
#guard (polyOfSeries (reverseSeries a a.size)).coeff 7 = 0

#guard mulCyclic (karatsubaPlan 2) 3 (by omega)
    (ofList [1, 2, 3] : DensePoly Int) (ofList [4, 5]) = ofList [19, 13, 22]
#guard mulNegacyclic (karatsubaPlan 2) 3 (by omega)
    (ofList [1, 2, 3] : DensePoly Int) (ofList [4, 5]) = ofList [-11, 13, 22]
#guard mulCyclic (karatsubaPlan 2) 3 (by omega)
    (ofList [1, 2, 3, 4, 5, 6, 7] : DensePoly Int) (C 1) =
      ofList [12, 7, 9]
#guard mulNegacyclic (karatsubaPlan 2) 3 (by omega)
    (ofList [1, 2, 3, 4, 5, 6, 7] : DensePoly Int) (C 1) =
      ofList [4, -3, -3]
#guard mulCyclic plan 1 (by omega) a b = C ((a * b).coeffs.toList.sum)
#guard mulNegacyclic plan 1 (by omega) (C 7) (C (-2)) = C (-14)
#guard mulCyclic? plan 3 a b = some (mulCyclic plan 3 (by omega) a b)
#guard mulCyclic? plan 1 a b = some (mulCyclic plan 1 (by omega) a b)
#guard mulCyclic? (karatsubaPlan 2) 0 a b = none
#guard mulNegacyclic? plan 3 a b = some (mulNegacyclic plan 3 (by omega) a b)
#guard mulNegacyclic? plan 1 a b = some (mulNegacyclic plan 1 (by omega) a b)
#guard mulNegacyclic? plan 0 a b = none
#guard (mulCyclic plan 3 (by omega) a b).size ≤ 3
#guard (mulNegacyclic plan 3 (by omega) a b).size ≤ 3

private def unitSeries : TSeries Int 8 :=
  TSeries.ofFn fun i => [1, 2, -1, 3, 0, -2, 4, 1].getD i 0

#guard seriesMulUpTo plan 5 unitSeries unitSeries =
  TSeries.mulUpTo 5 unitSeries unitSeries
#guard seriesMulUpTo (karatsubaPlan 0) 5 unitSeries unitSeries =
  TSeries.mulUpTo 5 unitSeries unitSeries
#guard seriesMulUpTo (karatsubaPlan 2) 0 unitSeries unitSeries =
  TSeries.mulUpTo 0 unitSeries unitSeries
#guard seriesMulUpTo (karatsubaPlan 2) 8 unitSeries unitSeries =
  unitSeries * unitSeries
private def emptySeries : TSeries Int 0 := TSeries.ofFn fun _ => 7
#guard seriesMulUpTo (karatsubaPlan 2) 0 emptySeries emptySeries = emptySeries
#guard reciprocalWith plan unitSeries 1 = TSeries.invOfUnit unitSeries 1
#guard unitSeries * reciprocalWith plan unitSeries 1 = 1

private def alternateUnitSeries : TSeries Int 8 :=
  TSeries.ofFn fun i => [1, -1, 2, 0, 3, 1, -2, 4].getD i 0

#guard reciprocalWith plan alternateUnitSeries 1 =
  TSeries.invOfUnit alternateUnitSeries 1
#guard alternateUnitSeries * reciprocalWith plan alternateUnitSeries 1 = 1
#guard reciprocalWith plan emptySeries 1 = emptySeries

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

private def exactRatDividend : DensePoly Rat := ratA * ratB

private def smallRatDividend : DensePoly Rat := ofList [1, -1]

private def ratCapacity : Nat :=
  max (quotientLength ratA ratB)
    (max (quotientLength exactRatDividend ratB)
      (quotientLength smallRatDividend ratB))

private def cachedRatPlan : DivPlan Rat :=
  DivPlan.ofNonzero (karatsubaPlan 2) ratB (by decide) ratCapacity

private def cachedMonicPlan : DivPlan Int :=
  DivPlan.ofMonic plan monicDivisor monicDivisor_monic (by decide)
    (quotientLength a monicDivisor)

private theorem ratA_capacity :
    quotientLength ratA cachedRatPlan.divisor ≤ cachedRatPlan.capacity := by
  simp only [cachedRatPlan, DivPlan.divisor_ofNonzero,
    DivPlan.capacity_ofNonzero]
  exact Nat.le_max_left _ _

private theorem exactRat_capacity :
    quotientLength exactRatDividend cachedRatPlan.divisor ≤
      cachedRatPlan.capacity := by
  simp only [cachedRatPlan, DivPlan.divisor_ofNonzero,
    DivPlan.capacity_ofNonzero]
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

private theorem smallRat_capacity :
    quotientLength smallRatDividend cachedRatPlan.divisor ≤
      cachedRatPlan.capacity := by
  simp only [cachedRatPlan, DivPlan.divisor_ofNonzero,
    DivPlan.capacity_ofNonzero]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

#guard divModWith (karatsubaPlan 2) ratA ratB = divMod ratA ratB
#guard divModWith (karatsubaPlan 2) ratA 0 = (0, ratA)
#guard divModWith (karatsubaPlan 2) exactRatDividend ratB = (ratA, 0)
#guard cachedRatPlan.divisor = ratB
#guard cachedRatPlan.capacity = ratCapacity
#guard cachedRatPlan.quotient ratA ratA_capacity = (divMod ratA ratB).1
#guard cachedRatPlan.quotient exactRatDividend exactRat_capacity = ratA
#guard cachedRatPlan.quotient smallRatDividend smallRat_capacity = 0
#guard cachedRatPlan.divMod ratA (by
    exact ratA_capacity) = divMod ratA ratB
#guard cachedRatPlan.divMod exactRatDividend (by
    exact exactRat_capacity) = (ratA, 0)
#guard cachedRatPlan.divMod smallRatDividend (by
    exact smallRat_capacity) = (0, smallRatDividend)
#guard cachedRatPlan.mod ratA (by
    exact ratA_capacity) = (divMod ratA ratB).2
#guard cachedRatPlan.mod exactRatDividend (by
    exact exactRat_capacity) = 0
#guard cachedRatPlan.mod smallRatDividend (by
    exact smallRat_capacity) = smallRatDividend
#guard let qr := cachedRatPlan.divMod ratA ratA_capacity
  qr.1 * ratB + qr.2 = ratA
#guard cachedMonicPlan.divisor = monicDivisor
#guard cachedMonicPlan.capacity = quotientLength a monicDivisor
#guard cachedMonicPlan.divMod a (by simp [cachedMonicPlan]) =
  divModMonic a monicDivisor monicDivisor_monic

private def treeLeaves : Array (DensePoly Int) :=
  #[ofList [1, 1], ofList [2, 1], ofList [3, 1], ofList [4, 1], ofList [5, 1]]

private def tree : ProductTree Int := ProductTree.build plan treeLeaves

private def emptyTree : ProductTree Int :=
  ProductTree.build plan (#[] : Array (DensePoly Int))

private def singletonTree : ProductTree Int :=
  ProductTree.build plan #[a]

#guard tree.leaves = treeLeaves
#guard tree.levelCount = 4
#guard tree.root = treeLeaves.foldl (fun acc p => acc * p) 1
#guard (tree.level? 0).map Array.size = some 5
#guard (tree.level? 1).map Array.size = some 3
#guard (tree.level? 2).map Array.size = some 2
#guard (tree.level? 3).map Array.size = some 1
#guard tree.nodeProduct? 1 0 = some (treeLeaves.getD 0 0 * treeLeaves.getD 1 0)
#guard tree.nodeProduct? 1 2 = some (treeLeaves.getD 4 0)
#guard emptyTree.leaves = #[]
#guard emptyTree.root = 1
#guard singletonTree.leaves = #[a]
#guard singletonTree.root = a

private def evalPoints : Array Int := #[-3, 0, 2, 5, 9]
private def evalPlan : EvalPlan Int := EvalPlan.build plan evalPoints
private def evalPoly : DensePoly Int := ofList [7, -4, 3, 2, -1]

#guard evalPlan.size = evalPoints.size
#guard evalPlan.points = evalPoints
#guard evalPlan.treeView.leaves = evalPoints.map (fun x => ofList [0 - x, 1])
#guard (EvalPlan.build plan (#[] : Array Int)).treeView.leaves = #[]
#guard (EvalPlan.build plan #[3]).treeView.leaves = #[ofList [-3, 1]]
#guard evalPlan.evalImpl evalPoly = evalPoints.map (evalPoly.eval ·)
#guard evalPlan.evalImpl (ofList [1, 2, 3, 4, 5, 6, 7]) =
  evalPoints.map ((ofList [1, 2, 3, 4, 5, 6, 7] : DensePoly Int).eval ·)
#guard (EvalPlan.build plan (#[] : Array Int)).evalImpl evalPoly = #[]
#guard (EvalPlan.build plan (#[] : Array Int)).evalImpl 0 = #[]
#guard tree.nodeProduct? 3 0 = some tree.root
#guard tree.nodeProduct? 4 0 = none

private def remainderLeaves : Array (MonicLeaf Int) :=
  #[{ poly := ofList [1, 1], monic := by rfl, ne := by decide },
    { poly := ofList [2, 1], monic := by rfl, ne := by decide },
    { poly := ofList [3, 1], monic := by rfl, ne := by decide },
    { poly := ofList [4, 1], monic := by rfl, ne := by decide },
    { poly := ofList [5, 1], monic := by rfl, ne := by decide }]

private def remainderTree : RemainderTree Int :=
  RemainderTree.build plan 2 remainderLeaves (by decide)

#guard remainderTree.leaves = treeLeaves
#guard remainderTree.remainders? a =
  some (remainderLeaves.map fun leaf => modByMonic a leaf.poly leaf.monic)
#guard (RemainderTree.build plan 1 remainderLeaves (by decide)).remainders? a = none
#guard (RemainderTree.build plan 0 (#[] : Array (MonicLeaf Int))
  (by decide)).remainders? a = some #[]

private def interpPoints : Array Rat := #[-1, 0, 2]
private def interpValues : Array Rat := #[6, 3, 3]
private def interpPoly : DensePoly Rat := ofList [3, -2, 1]

private def interpWidePoints : Array Rat := #[-4, -3, -2, -1, 0, 1, 2, 3]

private def interpWidePoly : DensePoly Rat := ofList [1, 2, 3, 4, 5, 6, 7, 8]

private def interpWideValues : Array Rat :=
  interpWidePoints.map (interpWidePoly.eval ·)

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
#guard match InterpPlan.build? (karatsubaPlan 2) interpWidePoints with
  | none => false
  | some interpolation =>
      interpolation.interpolate? interpWideValues = some interpWidePoly

private def ratPlan : MulPlan Rat := karatsubaPlan 2

private def xgcdAgrees (p q : DensePoly Rat) : Bool :=
  let actual := xgcdWith ratPlan p q
  let expected := xgcd p q
  actual.gcd == expected.gcd && actual.left == expected.left &&
    actual.right == expected.right

private def xgcdLeftAgrees (p q : DensePoly Rat) : Bool :=
  let actual := xgcdLeftWith ratPlan p q
  let expected := xgcdLeft p q
  actual.gcd == expected.gcd && actual.left == expected.left

#guard gcdWith ratPlan ratA ratB = gcd ratA ratB
#guard (xgcdWith ratPlan ratA ratB).gcd = (xgcd ratA ratB).gcd
#guard (xgcdWith ratPlan ratA ratB).left = (xgcd ratA ratB).left
#guard (xgcdWith ratPlan ratA ratB).right = (xgcd ratA ratB).right
#guard (xgcdLeftWith ratPlan ratA ratB).gcd = (xgcdLeft ratA ratB).gcd
#guard (xgcdLeftWith ratPlan ratA ratB).left = (xgcdLeft ratA ratB).left
#guard xgcdAgrees 0 0
#guard xgcdAgrees ratB ratA
#guard xgcdLeftAgrees 0 0
#guard xgcdLeftAgrees ratB ratA
#guard let result := xgcdWith ratPlan ratA ratB
  result.left * ratA + result.right * ratB = result.gcd
#guard let result := xgcdWith ratPlan ratB ratA
  result.left * ratB + result.right * ratA = result.gcd
#guard gcdWith ratPlan 0 0 = 0
#guard gcdWith ratPlan ratA 0 = gcd ratA 0
#guard gcdWith ratPlan 0 ratA = gcd 0 ratA
#guard gcdWith ratPlan ratB ratA = gcd ratB ratA

private def padeUnit : TSeries Rat 3 :=
  TSeries.ofFn fun _ => 1

private def padeNonunit : TSeries Rat 3 :=
  TSeries.ofFn fun i => if i = 2 then 1 else 0

private def padeEmpty : TSeries Rat 0 :=
  TSeries.ofFn fun _ => 0

private def padeWide : TSeries Rat 9 :=
  TSeries.ofFn fun i => [1, 2, -1, 3, 0, 4, -2, 1, 5].getD i 0

#guard let approx := padeHomogeneous ratPlan padeWide 4 4
  approx.p.size ≤ 5 ∧ approx.q.size ≤ 5 ∧ approx.q ≠ 0
#guard let approx := padeHomogeneous ratPlan padeWide 4 4
  (List.range 9).all fun i =>
    (approx.q * polyOfSeries padeWide - approx.p).coeff i == 0

#guard let approx := padeHomogeneous ratPlan padeUnit 1 1
  approx.p = C 1 ∧ approx.q = ofList [1, -1]
#guard let approx := padeHomogeneous ratPlan padeUnit 1 1
  approx.p.size ≤ 2 ∧ approx.q.size ≤ 2 ∧ approx.q ≠ 0
#guard let approx := padeHomogeneous ratPlan padeUnit 1 1
  (approx.q * polyOfSeries padeUnit - approx.p).coeff 0 = 0 ∧
    (approx.q * polyOfSeries padeUnit - approx.p).coeff 1 = 0 ∧
    (approx.q * polyOfSeries padeUnit - approx.p).coeff 2 = 0
#guard match pade? ratPlan padeUnit 1 1 with
  | none => false
  | some approx =>
      approx.p = C 1 ∧ approx.q = ofList [1, -1] ∧ approx.q.coeff 0 = 1
#guard (padeHomogeneous ratPlan padeNonunit 1 1).q.coeff 0 = 0
#guard let approx := padeHomogeneous ratPlan padeNonunit 1 1
  approx.p.size ≤ 2 ∧ approx.q.size ≤ 2 ∧ approx.q ≠ 0
#guard (pade? ratPlan padeNonunit 1 1).isNone
#guard match pade? ratPlan padeUnit 0 0 with
  | none => false
  | some approx => approx.p = C 1 ∧ approx.q = C 1 ∧ approx.q.coeff 0 = 1
#guard let approx := padeHomogeneous ratPlan padeEmpty 2 2
  approx.p.size ≤ 3 ∧ approx.q.size ≤ 3 ∧ approx.q ≠ 0
#guard match pade? ratPlan padeEmpty 2 2 with
  | none => false
  | some approx => approx.p = 0 ∧ approx.q = C 1 ∧ approx.q.coeff 0 = 1

end HexPolyFast.Conformance
