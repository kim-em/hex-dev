import Hex.Conformance.Emit
import HexGramSchmidt

/-!
JSONL emit driver for the `hex-gram-schmidt` oracle.

`lake exe hexgramschmidt_emit_fixtures` writes one fixture record plus
two `result` records per case to `stdout` (or to `$HEX_FIXTURE_OUTPUT`
when set).  The companion oracle driver `scripts/oracle/gs_flint.py`
reads the same stream and re-runs the integer Gram-Schmidt
computations through python-flint's `fmpq_mat` for cross-check.

Operations cross-checked
------------------------

* `gram_det_vec` — `GramSchmidt.Int.gramDetVec` (the `n+1` leading
  Gram determinants `d₀=1, d₁, …, d_n`).  The oracle computes
  `det(B[:k] · B[:k]^T)` via `fmpq_mat`.
* `scaled_coeffs` — `GramSchmidt.Int.scaledCoeffs` (the integer
  matrix whose lower-triangular entry `(i, j)` for `j < i` equals
  `d_{j+1} · μ_{i,j}`, whose diagonal entry `i` equals `d_{i+1}`,
  and whose above-diagonal entries are zero).  The oracle computes
  the rational Gram-Schmidt coefficients `μ` via `fmpq_mat`,
  multiplies by the leading determinants, and verifies the integer
  result is identical.

Fixtures cover integer bases at dimensions 4, 6, and 8.  Each
dimension contributes one diagonal basis (where the Gram
determinants are products of squared diagonal entries and all
off-diagonal scaled coefficients are zero) plus one generic basis
with mixed-sign small entries.  The bounded magnitudes keep the
emitted scaled-coefficient matrices small enough that the JSONL
file stays diffable.

The fixture set is committed and intentionally small.  Coordinate
any future case-id additions with the `HexGramSchmidt` Conformance
module so identical ids stay in sync.
-/

namespace Hex.GramSchmidtEmit

open Hex.Conformance.Emit
open Hex.GramSchmidt

private def lib : String := "HexGramSchmidt"

/-- Build a `Matrix Int n m` from a list of rows, padding short rows
with `0`.  The row count is fixed by the type ascription, so any
extra rows in `rows` are silently ignored. -/
private def mkMatrix (n m : Nat) (rows : List (List Int)) : Matrix Int n m :=
  Matrix.ofFn fun i j => (rows.getD i.val []).getD j.val 0

private def vecToInts {n : Nat} (v : Vector Int n) : List Int :=
  v.toArray.toList

private def matToInts {n m : Nat} (b : Matrix Int n m) : List (List Int) :=
  b.toArray.toList.map vecToInts

private def natVecToInts {n : Nat} (v : Vector Nat n) : List Int :=
  v.toArray.toList.map (fun x => Int.ofNat x)

/-- Emit one case: `lattice` fixture + `gram_det_vec` + `scaled_coeffs`. -/
private def emitCase {n m : Nat} (case : String) (b : Matrix Int n m) : IO Unit := do
  emitLatticeFixture lib case (matToInts b)
  emitResult lib case "gram_det_vec"
    (intListValue (natVecToInts (Hex.GramSchmidt.Int.gramDetVec b)))
  emitResult lib case "scaled_coeffs"
    (intMatrixValue (matToInts (Hex.GramSchmidt.Int.scaledCoeffs b)))

/-- Diagonal `n×n` basis with diagonal entries `diag.getD i 0`. -/
private def diagMatrix (n : Nat) (diag : List Int) : Matrix Int n n :=
  Matrix.ofFn fun i j => if i = j then diag.getD i.val 0 else 0

private def dim4Identity : Matrix Int 4 4 := diagMatrix 4 [1, 1, 1, 1]

/-- Diagonal basis with squared norms `4, 9, 25, 49` →
Gram determinants `1, 4, 36, 900, 44100`. -/
private def dim4Diag : Matrix Int 4 4 := diagMatrix 4 [2, 3, 5, 7]

/-- Generic 4×4 integer basis with bounded entries. -/
private def dim4Typical : Matrix Int 4 4 := mkMatrix 4 4 [
  [ 2,  1,  0, -1],
  [ 1,  3,  2,  0],
  [ 0,  1,  4,  2],
  [-1,  0,  2,  5]
]

/-- Diagonal 6×6 basis with diagonal entries `1, 2, 3, 5, 7, 11`. -/
private def dim6Diag : Matrix Int 6 6 := diagMatrix 6 [1, 2, 3, 5, 7, 11]

/-- Generic 6×6 integer basis with bounded entries. -/
private def dim6Typical : Matrix Int 6 6 := mkMatrix 6 6 [
  [ 3,  1,  0, -1,  0,  2],
  [ 1,  2,  1,  0, -1,  0],
  [ 0,  1,  4,  2,  0,  1],
  [-1,  0,  2,  3,  1,  0],
  [ 0, -1,  0,  1,  5,  2],
  [ 2,  0,  1,  0,  2,  4]
]

/-- Diagonal 8×8 basis with diagonal entries `1, 1, 2, 2, 3, 3, 5, 5`. -/
private def dim8Diag : Matrix Int 8 8 := diagMatrix 8 [1, 1, 2, 2, 3, 3, 5, 5]

/-- Generic 8×8 integer basis with bounded entries. -/
private def dim8Typical : Matrix Int 8 8 := mkMatrix 8 8 [
  [ 2,  1,  0, -1,  0,  1,  0,  0],
  [ 1,  2,  1,  0, -1,  0,  1,  0],
  [ 0,  1,  3,  1,  0, -1,  0,  1],
  [-1,  0,  1,  3,  1,  0, -1,  0],
  [ 0, -1,  0,  1,  3,  1,  0, -1],
  [ 1,  0, -1,  0,  1,  3,  1,  0],
  [ 0,  1,  0, -1,  0,  1,  3,  1],
  [ 0,  0,  1,  0, -1,  0,  1,  3]
]

end Hex.GramSchmidtEmit

def main : IO Unit := do
  Hex.GramSchmidtEmit.emitCase "dim4/identity" Hex.GramSchmidtEmit.dim4Identity
  Hex.GramSchmidtEmit.emitCase "dim4/diag"     Hex.GramSchmidtEmit.dim4Diag
  Hex.GramSchmidtEmit.emitCase "dim4/typical"  Hex.GramSchmidtEmit.dim4Typical
  Hex.GramSchmidtEmit.emitCase "dim6/diag"     Hex.GramSchmidtEmit.dim6Diag
  Hex.GramSchmidtEmit.emitCase "dim6/typical"  Hex.GramSchmidtEmit.dim6Typical
  Hex.GramSchmidtEmit.emitCase "dim8/diag"     Hex.GramSchmidtEmit.dim8Diag
  Hex.GramSchmidtEmit.emitCase "dim8/typical"  Hex.GramSchmidtEmit.dim8Typical
