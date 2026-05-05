import HexMatrix.Bareiss
import HexMatrix.RREF

/-!
Core conformance checks for `hex-matrix`.

Oracle: none
Mode: always
Covered operations:
- dense matrix constructors and accessors (`ofFn`, `row`, `col`, `transpose`, `submatrix`)
- vector and matrix arithmetic (`dot`, `normSq`, `mulVec`, `mul`, `gramMatrix`)
- elementary row operations (`rowSwap`, `rowScale`, `rowAdd`)
- determinant APIs (`det`, `bareiss`, `bareissData`)
- row reduction and span APIs (`rref`, `spanCoeffs`, `spanContains`)
- nullspace basis extraction (`nullspace`)
Covered properties:
- transpose is involutive on committed fixtures
- identity matrices act as left and right multiplicative identities
- row operations satisfy the determinant laws promised by the SPEC
- `bareiss` agrees with `det` on committed nonsingular and singular inputs
- `rref` returns data whose transform matrix multiplies the input to the reported echelon form
- `spanCoeffs` witnesses row-span membership on a committed dependent-row example
- the committed nullspace basis vectors are annihilated by the source matrix
Covered edge cases:
- zero matrices and zero vectors
- identity matrices and full-rank square systems
- singular matrices with a zero determinant
- a pivoting Bareiss input whose leading entry is zero
- dependent rows producing nontrivial span and nullspace behavior
- empty pivot-column and empty nullspace outputs
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

private def zeroInt : Matrix Int 2 2 := 0

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

private def vecInt : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 5 else 6

private def rowOneInt : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 3 else 4

private def colZeroInt : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 1 else 3

private def unitSubmatrix : Matrix Int 1 1 :=
  Matrix.ofFn fun _ _ => 1

private def baseGramInt : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 5
    | 0, _ => 11
    | 1, 0 => 11
    | _, _ => 25

private def dependentRat : Matrix Rat 2 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 2
    | 0, _ => 3
    | 1, 0 => 2
    | 1, 1 => 4
    | _, _ => 6

private def dependentRref : Matrix Rat 2 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 2
    | 0, _ => 3
    | _, _ => 0

private def zeroRat23 : Matrix Rat 2 3 := 0

private def fullRat22 : Matrix Rat 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, _ => 2
    | 1, 0 => 3
    | _, _ => 5

private def spanVec : Vector Rat 3 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 1
    | 1 => 2
    | _ => 3

private def offSpanVec : Vector Rat 3 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 1
    | 1 => 0
    | _ => 0

private def zeroRat3 : Vector Rat 3 := Vector.ofFn fun _ => 0

private def zeroRat2 : Vector Rat 2 := Vector.ofFn fun _ => 0

private def spanCoeffsWitness : Vector Rat 2 :=
  Vector.ofFn fun i => if i.val = 0 then 1 else 0

private def dependentNullspace : Vector (Vector Rat 3) 2 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => Vector.ofFn fun j =>
        match j.val with
        | 0 => -2
        | 1 => 1
        | _ => 0
    | _ => Vector.ofFn fun j =>
        match j.val with
        | 0 => -3
        | 1 => 0
        | _ => 1

private def zeroNullspace : Vector (Vector Rat 3) 3 :=
  Vector.ofFn fun i =>
    Vector.ofFn fun j => if i = j then 1 else 0

private def emptyNullspace : Vector (Vector Rat 2) 0 :=
  Vector.ofFn fun i => nomatch i

#guard Matrix.row baseInt ⟨1, by decide⟩ = rowOneInt
#guard Matrix.col baseInt ⟨0, by decide⟩ = colZeroInt
#guard Matrix.submatrix baseInt ⟨0, by decide⟩ = unitSubmatrix
#guard Matrix.submatrix baseInt ⟨1, by decide⟩ = baseInt
#guard Matrix.intNormSq vecInt = 61
#guard Matrix.ratNormSq spanVec = 14
#guard Matrix.gramMatrix baseInt = baseGramInt
#guard (1 : Matrix Int 2 2) * baseInt = baseInt
#guard baseInt * (1 : Matrix Int 2 2) = baseInt
#guard Matrix.transpose (Matrix.transpose baseInt) = baseInt

/-- info: { toArray := #[{ toArray := #[1, 3], size_toArray := _ }, { toArray := #[2, 4], size_toArray := _ }],
  size_toArray := _ } -/
#guard_msgs in #eval Matrix.transpose baseInt

/-- info: { toArray := #[17, 39], size_toArray := _ } -/
#guard_msgs in #eval Matrix.mulVec baseInt vecInt

/-- info: { toArray := #[{ toArray := #[7, 10], size_toArray := _ }, { toArray := #[15, 22], size_toArray := _ }],
  size_toArray := _ } -/
#guard_msgs in #eval baseInt * baseInt

/-- info: { toArray := #[{ toArray := #[3, 4], size_toArray := _ }, { toArray := #[1, 2], size_toArray := _ }],
  size_toArray := _ } -/
#guard_msgs in #eval Matrix.rowSwap baseInt ⟨0, by decide⟩ ⟨1, by decide⟩

/-- info: { toArray := #[{ toArray := #[0, 2, 1], size_toArray := _ }, { toArray := #[-6, 0, -8], size_toArray := _ },
               { toArray := #[5, 6, 0], size_toArray := _ }],
  size_toArray := _ } -/
#guard_msgs in #eval Matrix.rowScale pivotInt ⟨1, by decide⟩ (-2)

/-- info: { toArray := #[{ toArray := #[0, 2, 1], size_toArray := _ }, { toArray := #[3, 0, 4], size_toArray := _ },
               { toArray := #[5, 12, 3], size_toArray := _ }],
  size_toArray := _ } -/
#guard_msgs in #eval Matrix.rowAdd pivotInt ⟨0, by decide⟩ ⟨2, by decide⟩ 3

#guard Matrix.rowSwap (Matrix.rowSwap baseInt ⟨0, by decide⟩ ⟨1, by decide⟩)
    ⟨0, by decide⟩ ⟨1, by decide⟩ = baseInt
#guard Matrix.det (1 : Matrix Int 2 2) = 1
#guard Matrix.det zeroInt = 0
#guard Matrix.det singularInt = 0
#guard Matrix.det (Matrix.rowSwap pivotInt ⟨0, by decide⟩ ⟨1, by decide⟩) = -Matrix.det pivotInt
#guard Matrix.det (Matrix.rowScale pivotInt ⟨1, by decide⟩ (-2)) = (-2) * Matrix.det pivotInt
#guard Matrix.det (Matrix.rowAdd pivotInt ⟨0, by decide⟩ ⟨2, by decide⟩ 3) = Matrix.det pivotInt
#guard Matrix.bareiss baseInt = Matrix.det baseInt
#guard Matrix.bareiss singularInt = 0
#guard Matrix.bareiss pivotInt = Matrix.det pivotInt
#guard (Matrix.bareissData singularInt).det = 0
#guard (Matrix.bareissData pivotInt).rowSwaps = 1

#guard let D := Matrix.rref dependentRat; D.rank = 1
#guard let D := Matrix.rref dependentRat; D.echelon = dependentRref
#guard let D := Matrix.rref dependentRat; D.transform * dependentRat = D.echelon
#guard let D := Matrix.rref zeroRat23; D.rank = 0
#guard let D := Matrix.rref zeroRat23; D.pivotCols = Vector.ofFn (fun i => nomatch i)
#guard let D := Matrix.rref fullRat22; D.rank = 2
#guard let D := Matrix.rref fullRat22; D.echelon = (1 : Matrix Rat 2 2)

#guard Matrix.spanCoeffs dependentRat spanVec = some spanCoeffsWitness
#guard Matrix.rowCombination dependentRat spanCoeffsWitness = spanVec
#guard Matrix.spanContains dependentRat spanVec
#guard Matrix.spanCoeffs dependentRat offSpanVec = none
#guard !(Matrix.spanContains dependentRat offSpanVec)
#guard Matrix.spanCoeffs zeroRat23 zeroRat3 = some zeroRat2

#guard (Matrix.nullspace dependentRat).toArray = dependentNullspace.toArray
#guard (Matrix.nullspace zeroRat23).toArray = zeroNullspace.toArray
#guard (Matrix.nullspace fullRat22).toArray = emptyNullspace.toArray
#guard dependentRat * dependentNullspace.get ⟨0, by decide⟩ = 0
#guard dependentRat * dependentNullspace.get ⟨1, by decide⟩ = 0

/-!
6×6 fixtures matching the SPEC `core` matrix-dimension band, with the
same typical / edge / adversarial structure as the 2×2 cases above:

- `bigInt` — typical full-rank Int (entries `min i j + 1`); factorises
  as `L·U` with unit lower- and upper-triangular all-ones, so
  `det = 1`. Dense enough that Bareiss exercises the inner update loop
  at every step.
- `bigZeroInt` — edge zero matrix.
- `bigSingularInt` — adversarial singular Int with row 1 proportional
  to row 0 (mirrors the `singularInt` 2×2 pattern at 6×6).
- `bigPivotInt` — adversarial zero leading pivot (`M[0][0] = 0`),
  forcing one Bareiss row swap (`bigInt` with the `(0,0)` entry
  cleared).
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

#guard Matrix.transpose (Matrix.transpose bigInt) = bigInt
#guard (1 : Matrix Int 6 6) * bigInt = bigInt

#guard Matrix.bareiss bigInt = 1
#guard Matrix.bareiss bigZeroInt = 0
#guard Matrix.bareiss bigSingularInt = 0
#guard Matrix.bareiss bigPivotInt = -1
#guard (Matrix.bareissData bigPivotInt).rowSwaps = 1

#guard Matrix.bareiss (Matrix.rowSwap bigInt ⟨0, by decide⟩ ⟨5, by decide⟩) = -1
#guard Matrix.bareiss (Matrix.rowScale bigInt ⟨2, by decide⟩ 4) = 4
#guard Matrix.bareiss (Matrix.rowAdd bigInt ⟨0, by decide⟩ ⟨3, by decide⟩ 7) = 1

end Matrix

end Hex
