import Hex.Conformance.Emit
import HexMatrix.Bareiss
import HexMatrix.RREF
import HexMatrix.Determinant

/-!
JSONL emit driver for the `hex-matrix` oracle.

`lake exe hexmatrix_emit_fixtures` writes one `matrix` fixture record
plus several `result` records per case to `stdout` (or to
`$HEX_FIXTURE_OUTPUT` when set).  The companion oracle driver
`scripts/oracle/matrix_flint.py` reads the same stream and re-runs each
operation through python-flint's `fmpz_mat` / `fmpq_mat`.

Cases are square integer matrices at dimensions 4×4, 6×6, and 8×8 in
three structural shapes:

* `random/*` — generic, deterministic "random-looking" full-rank
  matrices with bounded entry magnitudes;
* `singular/*` — rank-deficient matrices constructed by setting the
  last rows to integer combinations of earlier rows (deficiency 1, 2);
* `triangular/*` — upper-triangular matrices whose determinant is the
  product of the diagonal (so the expected `det` is independent of the
  Lean implementation).

For each case we emit results for the operations the oracle will
verify: `det` (Lean's combinatorial `Matrix.det`), `bareiss` (the
fraction-free Bareiss algorithm, expected to agree with `det` on every
fixture), `rank` (`Matrix.rref_rank` over `Q`), `rref` (the rational
reduced row echelon form), and `nullspace` (the rational basis of the
right kernel).  RREF / nullspace are computed after lifting the
integer entries to `Rat`.

Coordinate any future case-id additions with the `HexMatrix`
Conformance module so identical ids stay in sync.
-/

namespace Hex.MatrixEmit

open Hex.Conformance.Emit
open Hex
open Hex.Matrix

private def lib : String := "HexMatrix"

/-- A row of a matrix as a `List Int`. -/
private def matrixIntRows {n m : Nat} (M : Matrix Int n m) : List (List Int) :=
  M.toList.map (fun row => row.toList)

/-- Lift an integer matrix to a rational matrix entrywise. -/
private def intToRat {n m : Nat} (M : Matrix Int n m) : Matrix Rat n m :=
  M.map (fun row => row.map (fun x => ((x : Int) : Rat)))

private def jsonInt (n : Int) : String := toString n
private def jsonNat (n : Nat) : String := toString n

/-- A rational rendered as a `[num, den]` JSON pair (Lean keeps `Rat`
in lowest terms with positive denominator, so this is canonical). -/
private def ratValue (q : Rat) : String :=
  "[" ++ jsonInt q.num ++ "," ++ jsonNat q.den ++ "]"

private def ratArrayValue (xs : Array Rat) : String := Id.run do
  let mut out := "["
  let mut first := true
  for x in xs do
    if first then first := false else out := out.push ','
    out := out ++ ratValue x
  out.push ']'

private def ratMatrixValue {n m : Nat} (M : Matrix Rat n m) : String := Id.run do
  let mut out := "["
  let mut first := true
  for row in M.toArray do
    if first then first := false else out := out.push ','
    out := out ++ ratArrayValue row.toArray
  out.push ']'

private def intArrayValue (xs : Array Int) : String := Id.run do
  let mut out := "["
  let mut first := true
  for x in xs do
    if first then first := false else out := out.push ','
    out := out ++ jsonInt x
  out.push ']'

/-- `rref` value:
`{"rank":k,"pivotCols":[i...],"echelon":[[[num,den],...],...]}`. -/
private def rrefValue {n m : Nat} (D : RowEchelonData Rat n m) : String :=
  let cols : Array Int := D.pivotCols.toArray.map (fun c => Int.ofNat c.val)
  "{\"rank\":" ++ jsonNat D.rank ++
  ",\"pivotCols\":" ++ intArrayValue cols ++
  ",\"echelon\":" ++ ratMatrixValue D.echelon ++ "}"

/-- `nullspace` value: a JSON array of rational basis vectors. -/
private def basisValue {m : Nat} (B : Array (Vector Rat m)) : String := Id.run do
  let mut out := "["
  let mut first := true
  for v in B do
    if first then first := false else out := out.push ','
    out := out ++ ratArrayValue v.toArray
  out.push ']'

/-- Emit one fixture record plus the five result records the oracle
will cross-check. -/
private def emitSquare (n : Nat) (id : String) (M : Matrix Int n n) : IO Unit := do
  emitMatrixFixture lib id (matrixIntRows M)
  emitResult lib id "det"     (jsonInt (Matrix.det M))
  emitResult lib id "bareiss" (jsonInt (Matrix.bareiss M))
  let MQ := intToRat M
  let D : RowEchelonData Rat n n := Matrix.rref MQ
  emitResult lib id "rank"      (jsonNat D.rank)
  emitResult lib id "rref"      (rrefValue D)
  emitResult lib id "nullspace" (basisValue (Matrix.nullspace MQ).toArray)

/-- Build a square `Matrix Int n n` from a 2-D array of rows.  When
`rows.size ≠ n` or any row has fewer than `n` entries, missing entries
default to `0` (so the caller is responsible for shape-correct input). -/
private def mkSquare (n : Nat) (rows : Array (Array Int)) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    (rows.getD i.val #[]).getD j.val 0

/-! ## 4×4 fixtures -/

/-- Generic 4×4 with bounded entries: the integer matrix
`[[3,1,4,1],[5,9,2,6],[5,3,5,8],[9,7,9,3]]`. -/
private def random4 : Matrix Int 4 4 :=
  mkSquare 4 #[#[3, 1, 4, 1], #[5, 9, 2, 6], #[5, 3, 5, 8], #[9, 7, 9, 3]]

/-- 4×4 with rank deficiency 1: the last row is the sum of the first
two.  `det = 0`. -/
private def singular4Def1 : Matrix Int 4 4 :=
  mkSquare 4 #[#[2, 0, -1, 3], #[1, 5, 4, -2], #[0, 3, 7, 1],
               #[3, 5, 3, 1]]

/-- 4×4 with rank deficiency 2: rows 2 and 3 are integer combinations
of rows 0 and 1.  `det = 0`, nullity = 2. -/
private def singular4Def2 : Matrix Int 4 4 :=
  mkSquare 4 #[#[1, 2, 3, 4], #[2, 1, 0, -1],
               #[3, 3, 3, 3], #[5, 4, 3, 2]]

/-- 4×4 upper triangular with diagonal `[2, -3, 5, 7]`.  `det = -210`. -/
private def triangular4 : Matrix Int 4 4 :=
  mkSquare 4 #[#[2, 1, 4, 0], #[0, -3, 2, 1], #[0, 0, 5, 6], #[0, 0, 0, 7]]

/-! ## 6×6 fixtures -/

/-- Generic 6×6, bounded entries.  Computed `det = 4818` via Bareiss
locally; oracle will recompute. -/
private def random6 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[ 3,  1, -2,  4,  0,  1],
    #[ 0,  5,  1, -1,  3,  2],
    #[ 2, -1,  4,  0,  1,  3],
    #[ 1,  2,  0,  3, -2,  4],
    #[-1,  0,  2,  1,  4,  0],
    #[ 4,  3,  1,  2, -3,  5]
  ]

/-- 6×6 with rank deficiency 1 — the last row equals row 0 + row 1. -/
private def singular6Def1 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[ 1,  2,  3, -1,  0,  4],
    #[ 0,  1, -2,  3,  1,  2],
    #[ 4, -1,  0,  2,  3,  1],
    #[ 2,  3,  1,  0,  4, -1],
    #[ 1,  0,  4,  3, -2,  2],
    #[ 1,  3,  1,  2,  1,  6]   -- = row0 + row1
  ]

/-- 6×6 upper triangular with diagonal `[1, 2, 3, 4, 5, 6]`.
`det = 720`. -/
private def triangular6 : Matrix Int 6 6 :=
  mkSquare 6 #[
    #[1,  2, -1,  3,  0,  1],
    #[0,  2,  4, -2,  1,  3],
    #[0,  0,  3,  1,  2, -1],
    #[0,  0,  0,  4,  0,  2],
    #[0,  0,  0,  0,  5,  3],
    #[0,  0,  0,  0,  0,  6]
  ]

/-! ## 8×8 fixtures -/

/-- Generic 8×8 with small integer entries. -/
private def random8 : Matrix Int 8 8 :=
  mkSquare 8 #[
    #[ 2,  0,  1, -1,  3,  0,  4,  1],
    #[ 1,  3,  0,  2, -1,  4,  1,  0],
    #[ 0, -2,  3,  1,  4,  0,  2,  1],
    #[ 4,  1, -1,  2,  0,  3,  1,  2],
    #[-1,  2,  0,  1,  3,  1, -2,  4],
    #[ 3,  0,  2, -1,  1,  4,  0,  1],
    #[ 1,  4,  1,  0, -2,  2,  3,  0],
    #[ 0,  1,  3,  4,  1, -1,  2,  3]
  ]

/-- 8×8 upper triangular with diagonal `[1,1,2,2,3,3,4,4]`.  `det = 576`. -/
private def triangular8 : Matrix Int 8 8 :=
  mkSquare 8 #[
    #[1, 2, 0, 1, 3, -1, 0, 2],
    #[0, 1, 3, -2, 0, 1, 4, 0],
    #[0, 0, 2, 1, -1, 0, 3, 1],
    #[0, 0, 0, 2, 0, 4, -1, 0],
    #[0, 0, 0, 0, 3, 1, 0, 2],
    #[0, 0, 0, 0, 0, 3, 2, -1],
    #[0, 0, 0, 0, 0, 0, 4, 1],
    #[0, 0, 0, 0, 0, 0, 0, 4]
  ]

private def emitAll : IO Unit := do
  emitSquare 4 "random/4x4"        random4
  emitSquare 4 "singular/4x4-def1" singular4Def1
  emitSquare 4 "singular/4x4-def2" singular4Def2
  emitSquare 4 "triangular/4x4"    triangular4
  emitSquare 6 "random/6x6"        random6
  emitSquare 6 "singular/6x6-def1" singular6Def1
  emitSquare 6 "triangular/6x6"    triangular6
  emitSquare 8 "random/8x8"        random8
  emitSquare 8 "triangular/8x8"    triangular8

end Hex.MatrixEmit

def main : IO Unit :=
  Hex.MatrixEmit.emitAll
