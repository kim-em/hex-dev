/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDet

/-!
Core conformance checks for `hex-det`.

Run this file through the conformance Lake target (not direct `lake env lean`):
the integer arm needs the native code generated for `HexArith.Int.exactDiv`.

Oracle: `scripts/oracle/matrix_flint.py` (`det` op, via the
`hexdet_emit_fixtures` stream) and `scripts/oracle/matrix_carriers.py` (`det`
records, via the `hexdet_emit_carrier_fixtures` stream)
Mode: always
Covered operations:
- `Hex.Det.det` and the route `Hex.Det.DetOps.run` reports
- `Hex.Det.runWith` at explicit recipes, forcing each available arm
Covered properties:
- dispatch agrees with the lower algorithm its recipe selects, on identical
  matrices, at every shipped carrier
- dispatch agrees with the Leibniz reference determinant at the small sizes
- the reported route is the small arm at `n ≤ 2` and the recipe's own arm above
Covered edge cases:
- empty, one-by-one and two-by-two inputs, row swaps, singular matrices, zero
  pivot columns, odd and even sizes
- nonconstant polynomial pivots, a ring with zero divisors through Berkowitz,
  and the trivial ring where `1 = 0`
-/

namespace Hex.DetConformance

open Hex Hex.Det

scoped instance : ZMod64.Bounds 101 := ⟨by decide, by decide⟩
scoped instance : ZMod64.PrimeModulus 101 :=
  ZMod64.primeModulusOfPrime (by decide)

/-- A ring with zero divisors: `2 * 3 = 0` modulo six. -/
scoped instance : ZMod64.Bounds 6 := ⟨by decide, by decide⟩

/-- The trivial ring, where `1 = 0`. -/
scoped instance : ZMod64.Bounds 1 := ⟨by decide, by decide⟩

/-- Build a square matrix from row data, padding short rows with zero. -/
private def square {R : Type} [Zero R] (n : Nat) (rows : Array (Array R)) :
    Matrix R n n :=
  Matrix.ofFn fun i j => (rows.getD i.val #[]).getD j.val 0

/-! # Integer dispatch

At `n ≤ 2` the lower algorithms are called directly, because dispatch always
runs its small arm there. Above that, dispatch is compared with the arm its
recipe selects and with explicitly forced recipes. -/

private def emptyInt : Matrix Int 0 0 := square 0 #[]

private def oneInt : Matrix Int 1 1 := square 1 #[#[7]]

private def twoInt : Matrix Int 2 2 := square 2 #[#[1, 2], #[3, 4]]

private def swapInt : Matrix Int 2 2 := square 2 #[#[3, 4], #[1, 2]]

private def singularTwoInt : Matrix Int 2 2 := square 2 #[#[1, 2], #[2, 4]]

private def pivotInt : Matrix Int 3 3 :=
  square 3 #[#[0, 2, 1], #[3, 0, 4], #[5, 6, 0]]

private def fourInt : Matrix Int 4 4 :=
  square 4 #[#[3, 1, 4, 1], #[5, 9, 2, 6], #[5, 3, 5, 8], #[9, 7, 9, 3]]

private def singularFourInt : Matrix Int 4 4 :=
  square 4 #[#[1, 2, 3, 4], #[2, 4, 6, 8], #[3, 3, 3, 3], #[5, 4, 3, 2]]

/-- A zero column forces the Bareiss pivot search to fail and return zero. -/
private def zeroColumnInt : Matrix Int 4 4 :=
  square 4 #[#[3, 0, 4, 1], #[5, 0, 2, 6], #[5, 0, 5, 8], #[9, 0, 9, 3]]

private def zeroInt : Matrix Int 4 4 := square 4 #[]

private def fiveInt : Matrix Int 5 5 :=
  square 5 #[#[2, 1, 0, 0, 1], #[1, 2, 1, 0, 0], #[0, 1, 2, 1, 0],
    #[0, 0, 1, 2, 1], #[1, 0, 0, 1, 2]]

/- Small sizes: dispatch against the Leibniz reference and against the lower
algorithms called directly. -/

#guard Hex.Det.det emptyInt = 1
#guard Hex.Det.det emptyInt = Matrix.det emptyInt
#guard Hex.Det.det oneInt = Matrix.det oneInt
#guard Hex.Det.det twoInt = Matrix.det twoInt
#guard Hex.Det.det swapInt = Matrix.det swapInt
#guard Hex.Det.det singularTwoInt = 0
#guard Hex.Det.det swapInt = -Hex.Det.det twoInt
#guard Hex.Det.det twoInt = Matrix.bareiss twoInt


/- Larger sizes: dispatch against its selected arm and against each explicitly
forced recipe. -/

#guard Hex.Det.det pivotInt = Matrix.bareiss pivotInt
#guard Hex.Det.det pivotInt = Matrix.det pivotInt
#guard Hex.Det.det fourInt = Matrix.bareiss fourInt
#guard Hex.Det.det singularFourInt = 0
#guard Hex.Det.det zeroColumnInt = 0
#guard Hex.Det.det zeroColumnInt = Matrix.det zeroColumnInt
#guard Hex.Det.det zeroInt = 0
#guard (runWith (Policy.berkowitz inferInstance) zeroColumnInt).value = 0
#guard Hex.Det.det fiveInt = Matrix.bareiss fiveInt

#guard (runWith (Policy.berkowitz inferInstance) fourInt).value = Hex.Det.det fourInt
#guard (runWith (quotientPolicy (R := Int)) fourInt).value = Hex.Det.det fourInt
#guard (runWith (Policy.integer id id IntArm.bareiss) fiveInt).value = Hex.Det.det fiveInt
#guard (runWith (Policy.berkowitz inferInstance) pivotInt).value = Matrix.det pivotInt

/- Routes. The small arm is reported exactly at the small sizes; every other run
reports the arm its recipe selects, once, with no transition. -/

#guard (DetOps.run emptyInt).route.selected = Arm.small
#guard (DetOps.run twoInt).route.completed = Arm.small
#guard (DetOps.run twoInt).route.attempts = [Arm.small]
#guard (DetOps.run fourInt).route.selected = Arm.bareiss
#guard (DetOps.run fourInt).route.completed = Arm.bareiss
#guard (DetOps.run fourInt).route.attempts = [Arm.bareiss]
#guard (runWith (Policy.berkowitz (R := Int) inferInstance) fourInt).route.attempts =
  [Arm.berkowitz]
#guard (runWith (Policy.berkowitz (R := Int) inferInstance) twoInt).route.attempts =
  [Arm.small]

/-! # Rational dispatch -/

private def twoRat : Matrix Rat 2 2 := square 2 #[#[1 / 2, 2 / 3], #[3 / 4, 5 / 6]]

private def pivotRat : Matrix Rat 3 3 :=
  square 3 #[#[0, 2 / 3, 1], #[3 / 4, 0, 4 / 5], #[5 / 6, 6 / 7, 0]]

private def singularRat : Matrix Rat 3 3 :=
  square 3 #[#[1 / 2, 1, 3 / 2], #[1, 2, 3], #[2 / 3, 1, 4 / 3]]

#guard Hex.Det.det twoRat = Matrix.det twoRat
#guard Hex.Det.det pivotRat = Matrix.det pivotRat
#guard Hex.Det.det singularRat = 0
#guard Hex.Det.det pivotRat = Matrix.bareissWith Hex.exactDiv pivotRat
#guard (DetOps.run pivotRat).route.selected = Arm.bareiss
#guard (runWith (Policy.berkowitz (R := Rat) inferInstance) pivotRat).value =
  Hex.Det.det pivotRat

/-! # Prime-residue dispatch -/

private abbrev Fp := ZMod64 101

private def pivotFp : Matrix Fp 3 3 :=
  square 3 #[#[0, 2, 1], #[3, 0, 4], #[5, 6, 0]]

private def singularFp : Matrix Fp 3 3 :=
  square 3 #[#[1, 2, 3], #[2, 4, 6], #[7, 8, 9]]

#guard Hex.Det.det pivotFp = Matrix.det pivotFp
#guard Hex.Det.det singularFp = 0
#guard Hex.Det.det pivotFp = Matrix.bareissWith Hex.exactDiv pivotFp
#guard (runWith (Policy.berkowitz (R := Fp) inferInstance) pivotFp).value =
  Hex.Det.det pivotFp

/-! # Polynomial carriers

Nonconstant pivots exercise the recursive exact division: every division the
Bareiss recurrence performs here is by a polynomial of positive degree. -/

private def linear (a b : Int) : DensePoly Int := DensePoly.ofList [a, b]

private def polyInt : Matrix (DensePoly Int) 3 3 :=
  square 3 #[#[linear 1 1, linear 2 1, linear 0 1],
    #[linear 0 2, linear 1 3, linear 4 1],
    #[linear 3 1, linear 1 1, linear 2 5]]

private def linearRat (a b : Rat) : DensePoly Rat := DensePoly.ofList [a, b]

private def polyRat : Matrix (DensePoly Rat) 3 3 :=
  square 3 #[#[linearRat 1 (1 / 2), linearRat (2 / 3) 1, linearRat 0 1],
    #[linearRat 0 2, linearRat (1 / 5) 3, linearRat 4 1],
    #[linearRat 3 1, linearRat 1 1, linearRat (2 / 7) 5]]

private def linearFp (a b : Fp) : DensePoly Fp := DensePoly.ofList [a, b]

private def polyFp : Matrix (DensePoly Fp) 3 3 :=
  square 3 #[#[linearFp 1 1, linearFp 2 1, linearFp 0 1],
    #[linearFp 0 2, linearFp 1 3, linearFp 4 1],
    #[linearFp 3 1, linearFp 1 1, linearFp 2 5]]

#guard Hex.Det.det polyInt = Matrix.det polyInt
#guard Hex.Det.det polyRat = Matrix.det polyRat
#guard Hex.Det.det polyFp = Matrix.det polyFp
#guard Hex.Det.det polyInt = Matrix.bareissWith Hex.exactDiv polyInt
#guard (DetOps.run polyInt).route.selected = Arm.bareiss
#guard (DetOps.run polyRat).route.selected = Arm.bareiss
#guard (DetOps.run polyFp).route.selected = Arm.bareiss
#guard (runWith (Policy.berkowitz (R := DensePoly Int) inferInstance) polyInt).value =
  Hex.Det.det polyInt

private abbrev Mv (R : Type) [Zero R] := MvPoly 2 R Mono.grevlex

private def mvTerm (a : Int) (i j : Nat) : Mv Int :=
  MvPoly.ofTerms [(Vector.ofFn fun k => if k.val = 0 then i else j, a)]

private def mvInt : Matrix (Mv Int) 3 3 :=
  square 3 #[#[mvTerm 1 1 0 + mvTerm 2 0 1, mvTerm 1 0 1, mvTerm 3 0 0],
    #[mvTerm 2 0 0, mvTerm 1 1 1, mvTerm 1 0 1],
    #[mvTerm 1 0 0, mvTerm 4 1 0, mvTerm 1 2 0]]

#guard Hex.Det.det mvInt = Matrix.det mvInt
#guard (DetOps.run mvInt).route.selected = Arm.bareiss

/-! # Rings without an exact quotient

A ring with zero divisors and the trivial ring both fall to the Berkowitz
default, which needs no quotient and no nontriviality hypothesis. -/

private abbrev Zsix := ZMod64 6

private def zeroDivisorSix : Matrix Zsix 3 3 :=
  square 3 #[#[2, 3, 1], #[3, 2, 4], #[1, 1, 3]]

#guard Hex.Det.det zeroDivisorSix = Matrix.det zeroDivisorSix
#guard (DetOps.run zeroDivisorSix).route.selected = Arm.berkowitz
#guard (DetOps.run zeroDivisorSix).route.attempts = [Arm.berkowitz]

private abbrev Trivial := ZMod64 1

private def trivialThree : Matrix Trivial 3 3 :=
  square 3 #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]

#guard (1 : Trivial) = (0 : Trivial)
#guard Hex.Det.det trivialThree = Matrix.det trivialThree
#guard Hex.Det.det trivialThree = 0
#guard (DetOps.run trivialThree).route.selected = Arm.berkowitz

end Hex.DetConformance
