/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyFp.PrimeField
import HexResultant.ExactDiv
import HexMvGcd.Divide
import HexMvGcd.Instances
import HexBareiss.Fixtures
import HexBareiss

/-!
Core conformance checks for `hex-bareiss`.

Run this file through the conformance Lake target (not direct `lake env lean`):
the Bareiss guards need the native code generated for `Matrix.exactDiv`.

Oracle: `scripts/oracle/matrix_flint.py` (`bareiss` op, via the
`hexbareiss_emit_fixtures` stream), and `scripts/oracle/matrix_carriers.py`
(FLINT scalar / SymPy Berkowitz polynomial determinants through
`hexbareiss_emit_carrier_fixtures`)
Mode: always
Covered operations:
- the executable fraction-free Bareiss determinant `bareiss` and `bareissData`
- `bareissWith Hex.exactDiv` at Rat, ZMod64, dense and multivariate polynomials
- the common exact-quotient law with the specified carrier instances
Covered properties:
- committed Bareiss fixtures match their expected executable determinant values;
  the `bareiss = det` guards below are value-level fixture checks only, not a
  general theorem in the Mathlib-free layer
- `bareissData` records the determinant and the row-swap count
Covered edge cases:
- zero, singular, and pivoting (zero leading entry) inputs at the 2×2/3×3/6×6 bands
- determinant behaviour under elementary row operations on a 6×6 fixture
- empty/singleton matrices, modular reduction, and nonconstant polynomial pivots
-/

namespace Hex

namespace Matrix

private def baseInt : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, _ => 2
    | 1, 0 => 3
    | _, _ => 4

private def singularInt : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, _ => 2
    | 1, 0 => 2
    | _, _ => 4

private def pivotInt : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 0, 1 => 2
    | 0, _ => 1
    | 1, 0 => 3
    | 1, 1 => 0
    | 1, _ => 4
    | 2, 0 => 5
    | 2, 1 => 6
    | _, _ => 0

/- Bareiss fixture equality guards.

These evaluate committed examples against `Matrix.det` to catch runtime
regressions on representative nonsingular, singular, and pivoting inputs. They
do not expose or imply a general Mathlib-free bridge theorem of the forbidden
shape `Matrix.bareiss M = Matrix.det M`. -/

#guard Matrix.bareiss baseInt = Matrix.det baseInt
#guard Matrix.bareiss singularInt = 0
#guard Matrix.bareiss pivotInt = Matrix.det pivotInt
#guard (Matrix.bareissData singularInt).det = 0
#guard (Matrix.bareissData pivotInt).rowSwaps = 1

/- The generic coefficient path agrees with the retained integer surface and
also runs over a non-integer exact-division carrier. -/

#guard Matrix.bareissWith Hex.exactDiv baseInt = Matrix.bareiss baseInt
#guard (Matrix.bareissDataWith Hex.exactDiv pivotInt).det =
  (Matrix.bareissData pivotInt).det
#guard (Matrix.bareissDataWith Hex.exactDiv pivotInt).rowSwaps =
  (Matrix.bareissData pivotInt).rowSwaps

#synth Hex.ExactDivLaws Rat

private def baseRat : Matrix Rat 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1 / 2
    | 0, _ => 2 / 3
    | 1, 0 => 3 / 4
    | _, _ => 5 / 6

private def pivotRat : Matrix Rat 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 0, _ => 2 / 3
    | 1, 0 => 3 / 4
    | _, _ => 5 / 6

private def singularRat : Matrix Rat 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1 / 2
    | 0, _ => 2 / 3
    | 1, 0 => 1
    | _, _ => 4 / 3

private def emptyRat : Matrix Rat 0 0 := 0

private def singletonRat : Matrix Rat 1 1 :=
  Matrix.ofFn fun _ _ => 7 / 3

#guard Matrix.bareissWith Hex.exactDiv baseRat = Matrix.det baseRat
#guard Matrix.bareissWith Hex.exactDiv pivotRat = Matrix.det pivotRat
#guard Matrix.bareissWith Hex.exactDiv singularRat = Matrix.det singularRat
#guard Matrix.bareissWith Hex.exactDiv emptyRat = Matrix.det emptyRat
#guard Matrix.bareissWith Hex.exactDiv singletonRat = Matrix.det singletonRat

/-!
6×6 fixtures matching the SPEC `core` matrix-dimension band:

- `bigInt` — typical full-rank Int (entries `min i j + 1`); `det = 1`.
- `bigZeroInt` — edge zero matrix.
- `bigSingularInt` — adversarial singular Int with row 1 proportional to row 0.
- `bigPivotInt` — adversarial zero leading pivot (`M[0][0] = 0`), forcing one
  Bareiss row swap.
-/

private def bigInt : Matrix Int 6 6 :=
  Matrix.ofFn fun i j => (min i.val j.val + 1 : Int)

private def bigZeroInt : Matrix Int 6 6 := 0

private def bigSingularInt : Matrix Int 6 6 :=
  Matrix.ofFn fun i j =>
    if i.val = 1 then (2 : Int)
    else (min i.val j.val + 1 : Int)

private def bigPivotInt : Matrix Int 6 6 :=
  Matrix.ofFn fun i j =>
    if i.val = 0 ∧ j.val = 0 then (0 : Int)
    else (min i.val j.val + 1 : Int)

/- Bareiss executable-value guards for 6×6 fixtures.

These compare against known fixture values rather than stating any general
relationship between the Bareiss algorithm and Leibniz determinant. -/

#guard Matrix.bareiss bigInt = 1
#guard Matrix.bareiss bigZeroInt = 0
#guard Matrix.bareiss bigSingularInt = 0
#guard Matrix.bareiss bigPivotInt = -1
#guard (Matrix.bareissData bigPivotInt).rowSwaps = 1

#guard Matrix.bareiss (Matrix.rowSwap bigInt ⟨0, by decide⟩ ⟨5, by decide⟩) = -1
#guard Matrix.bareiss (Matrix.rowScale bigInt ⟨2, by decide⟩ 4) = 4
#guard Matrix.bareiss (Matrix.rowAdd bigInt ⟨0, by decide⟩ ⟨3, by decide⟩ 7) = 1

#guard Matrix.bareissWith Hex.exactDiv singularInt = Matrix.bareiss singularInt
#guard Matrix.bareissWith Hex.exactDiv pivotInt = Matrix.bareiss pivotInt
#guard Matrix.bareissWith Hex.exactDiv bigInt = Matrix.bareiss bigInt
#guard Matrix.bareissWith Hex.exactDiv bigZeroInt = Matrix.bareiss bigZeroInt
#guard Matrix.bareissWith Hex.exactDiv bigSingularInt = Matrix.bareiss bigSingularInt
#guard Matrix.bareissWith Hex.exactDiv bigPivotInt = Matrix.bareiss bigPivotInt
#guard Matrix.bareissWith Hex.exactDiv (Matrix.rowSwap bigInt ⟨0, by decide⟩ ⟨5, by decide⟩) =
  Matrix.bareiss (Matrix.rowSwap bigInt ⟨0, by decide⟩ ⟨5, by decide⟩)
#guard Matrix.bareissWith Hex.exactDiv (Matrix.rowScale bigInt ⟨2, by decide⟩ 4) =
  Matrix.bareiss (Matrix.rowScale bigInt ⟨2, by decide⟩ 4)
#guard Matrix.bareissWith Hex.exactDiv (Matrix.rowAdd bigInt ⟨0, by decide⟩ ⟨3, by decide⟩ 7) =
  Matrix.bareiss (Matrix.rowAdd bigInt ⟨0, by decide⟩ ⟨3, by decide⟩ 7)

end Matrix
end Hex

namespace Hex.BareissCarriers

instance : ZMod64.Bounds 101 := ⟨by decide, by decide⟩
instance : ZMod64.PrimeModulus 101 := ZMod64.primeModulusOfPrime (by decide)
abbrev Mod := ZMod64 101
abbrev Mv (n : Nat) (R : Type) [Zero R] := MvPoly n R Mono.grevlex

-- The same law term is instantiated with each provider below. Explicit
-- arguments avoid the opaque FpPoly ring dictionary exported by MvGcd.
set_option linter.unusedVariables false in
private theorem quotientLaw (R : Type) [Lean.Grind.CommRing R]
    [DecidableEq R] [Div R] [Hex.ExactDivLaws R] :
    ∀ a b : R, b ≠ 0 → Hex.exactDiv (a * b) b = a :=
  fun a b hb => Hex.exactDiv_mul_right a hb

example := @quotientLaw Rat _ _ _ Hex.instExactDivLawsField
example := @quotientLaw Mod _ _ _ Hex.instExactDivLawsField
example := @quotientLaw (DensePoly Rat) _ _ _ (Hex.instExactDivLawsDensePoly (R := Rat))
example := @quotientLaw (DensePoly Mod) _ _ _ (Hex.instExactDivLawsDensePoly (R := Mod))
example := @quotientLaw (DensePoly Int) _ _ _ (Hex.instExactDivLawsDensePoly (R := Int))
example (n : Nat) := @quotientLaw (Mv n Int) _ _ _ Hex.MvPoly.instExactDivLaws
example (n : Nat) := @quotientLaw (Mv n Rat) _ _ _ Hex.MvPoly.instExactDivLaws

/-- A tridiagonal matrix whose leading minors force nonconstant exact
quotients from step one onwards when `x` is a polynomial. -/
def tridiagonal {R : Type} [Zero R] [One R] [Add R] [Neg R]
    (n : Nat) (x : R) : Matrix R n n :=
  Matrix.ofFn fun i j =>
    if i.val = j.val then x + 1
    else if i.val + 1 = j.val then 1
    else if j.val + 1 = i.val then -1 else 0

/-- The same structural cases for every carrier, including both empty and
singleton matrices. Singular cases duplicate a row; swap cases force pivoting. -/
def cases {R : Type} [Zero R] [One R] [Add R] [Neg R] (x : R) :
    List (String × (n : Nat) × Matrix R n n) :=
  let m := tridiagonal 3 x
  [("empty", ⟨0, Matrix.ofFn fun _ _ => 0⟩),
   ("singleton", ⟨1, Matrix.ofFn fun _ _ => x⟩),
   ("ordinary", ⟨3, m⟩),
   ("swap", ⟨3, Matrix.ofFn fun i j =>
      if i.val = 0 then (if j.val = 1 then x else 0)
      else m[(i, j)]⟩),
   ("singular", ⟨3, Matrix.ofFn fun i j =>
      m[((if i.val = 1 then ⟨0, by decide⟩ else i), j)]⟩)]

def ratCases := cases (3 / 2 : Rat)
def modCases := cases (3 / 2 : Mod)
def denseRatCases := cases (DensePoly.ofList [1 / 2, 2 / 3] : DensePoly Rat)
def denseModCases := cases (DensePoly.ofList [102, 205] : DensePoly Mod)
def zpolyCases := cases (DensePoly.ofList [2, 2] : DensePoly Int)
def mvIntCases (n : Nat) (h : 2 ≤ n) :=
  let x : Mv n Int := MvPoly.X ⟨0, by omega⟩
  let y : Mv n Int := MvPoly.X ⟨1, by omega⟩
  let z := if hn : 2 < n then MvPoly.X ⟨2, hn⟩ else 1
  cases (2 * x * y + y * z + 1)
def mvRatCases (n : Nat) (h : 2 ≤ n) :=
  let x : Mv n Rat := MvPoly.X ⟨0, by omega⟩
  let y : Mv n Rat := MvPoly.X ⟨1, by omega⟩
  let z := if hn : 2 < n then MvPoly.X ⟨2, hn⟩ else 1
  cases (MvPoly.C (2 / 3) * x * y + y * z + 1)

def checkCases {R : Type} [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
    (cs : List (String × (n : Nat) × Matrix R n n)) : Bool :=
  cs.all fun (_, ⟨_, m⟩) => decide (Matrix.bareissWith Hex.exactDiv m = Matrix.det m)

#guard checkCases ratCases
#guard checkCases modCases
#guard checkCases denseRatCases
#guard checkCases denseModCases
#guard checkCases zpolyCases
#guard checkCases (mvIntCases 2 (by decide))
#guard checkCases (mvIntCases 3 (by decide))
#guard checkCases (mvRatCases 2 (by decide))
#guard checkCases (mvRatCases 3 (by decide))

-- Reduction creates a zero leading entry and a nonzero replacement pivot.
def reduction : Matrix Mod 3 3 := Matrix.ofFn fun i j =>
  ((#[#[101, 102, 0], #[202, 0, 103], #[304, 0, 1]] : Array (Array Mod)).getD i.val #[]).getD j.val 0
#guard Matrix.bareissWith Hex.exactDiv reduction = Matrix.det reduction
#guard (Matrix.bareissDataWith Hex.exactDiv reduction).rowSwaps = 2
#guard (304 : Mod) = 1

end Hex.BareissCarriers

#guard Hex.Matrix.bareissWith Hex.exactDiv Hex.BareissEmit.random4 = Hex.Matrix.bareiss Hex.BareissEmit.random4
#guard Hex.Matrix.bareissWith Hex.exactDiv Hex.BareissEmit.singular4Def1 = Hex.Matrix.bareiss Hex.BareissEmit.singular4Def1
#guard Hex.Matrix.bareissWith Hex.exactDiv Hex.BareissEmit.singular4Def2 = Hex.Matrix.bareiss Hex.BareissEmit.singular4Def2
#guard Hex.Matrix.bareissWith Hex.exactDiv Hex.BareissEmit.triangular4 = Hex.Matrix.bareiss Hex.BareissEmit.triangular4
#guard Hex.Matrix.bareissWith Hex.exactDiv Hex.BareissEmit.random6 = Hex.Matrix.bareiss Hex.BareissEmit.random6
#guard Hex.Matrix.bareissWith Hex.exactDiv Hex.BareissEmit.singular6Def1 = Hex.Matrix.bareiss Hex.BareissEmit.singular6Def1
#guard Hex.Matrix.bareissWith Hex.exactDiv Hex.BareissEmit.triangular6 = Hex.Matrix.bareiss Hex.BareissEmit.triangular6
#guard Hex.Matrix.bareissWith Hex.exactDiv Hex.BareissEmit.random8 = Hex.Matrix.bareiss Hex.BareissEmit.random8
#guard Hex.Matrix.bareissWith Hex.exactDiv Hex.BareissEmit.triangular8 = Hex.Matrix.bareiss Hex.BareissEmit.triangular8
