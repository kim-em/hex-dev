/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSmith
import HexMatrix.Notation

/-! Executable conformance guards for the Smith API. -/

namespace Hex.Matrix.Smith.Conformance

private def coprimeDiagonal : Matrix Int 2 2 := #m[2, 0; 0, 3]
private def chain : Matrix Int 3 3 := #m[2, 0, 0; 0, 4, 0; 0, 0, 8]
private def chainConjugate : Matrix Int 3 3 := #m[2, 2, 0; 0, 4, 4; 0, 0, 8]
private def rankOne : Matrix Int 3 2 := #m[2, 4; -2, -4; 4, 8]
private def rankDeficient : Matrix Int 3 3 := #m[2, 4, 6; 1, 2, 3; 0, 0, 0]
private def tall : Matrix Int 3 2 := #m[6, 9; 4, 7; -2, 1]
private def wide : Matrix Int 2 3 := #m[6, 4, -2; 9, 7, 1]
private def mixed : Matrix Int 2 2 := #m[-4, 6; 10, -14]
private def empty00 : Matrix Int 0 0 := 0
private def empty03 : Matrix Int 0 3 := 0
private def empty30 : Matrix Int 3 0 := 0

private def dataChecks (A : Matrix Int n m) : Bool :=
  let D := snfData A
  decide (D.left * A * D.right = diagMatrix D.diag n m) &&
    decide (D.left * D.leftInv = Matrix.identity n) &&
    decide (D.right * D.rightInv = Matrix.identity m) &&
    decide (snf A = diagMatrix D.diag n m)

private def certChecks (A : Matrix Int n m) : Bool :=
  let D := snfData A
  snfCert A D (D.left * A)

private def diagonalChecks (d : Vector Int r) : Bool :=
  let A := diagMatrix d r r
  let D := snfDiagonalData d
  let F := Smith.Diagonal.Compact.run (Smith.formAccumulator r r) d
  decide (D.left * A * D.right = diagMatrix D.diag r r) &&
    decide (D.left * D.leftInv = Matrix.identity r) &&
    decide (D.right * D.rightInv = Matrix.identity r) &&
    decide (diagMatrix F.values r r = snfDiagonal d) &&
    decide (snfDiagonal d = diagMatrix D.diag r r) &&
    decide (snfDiagonal d = snf A)

#guard snf empty00 = empty00
#guard snf empty03 = empty03
#guard snf empty30 = empty30
#guard (snf coprimeDiagonal).rows.toList = [#v[1, 0], #v[0, 6]]
#guard (invariantFactors coprimeDiagonal).toList = [1, 6]
#guard snf chain = chain
#guard (invariantFactors rankOne).toList = [2]
#guard snf chainConjugate = chain
#guard (snf tall).rows.toList = [#v[1, 0], #v[0, 6], #v[0, 0]]
#guard (snf wide).rows.toList = [#v[1, 0, 0], #v[0, 6, 0]]
#guard (invariantFactors mixed).toList = [2, 2]
#guard (invariantFactors (#m[-1] : Matrix Int 1 1)).toList = [1]
#guard snf (snf mixed) = snf mixed
#guard abelianStructure (#m[2, 0; 0, 2] : Matrix Int 2 2) =
  { freeRank := 0, torsionFactors := #[2, 2] }
#guard abelianStructure (#m[1, 1; 0, 2] : Matrix Int 2 2) =
  { freeRank := 0, torsionFactors := #[2] }

#guard dataChecks empty00
#guard dataChecks empty03
#guard dataChecks empty30
#guard dataChecks (0 : Matrix Int 2 2)
#guard dataChecks rankOne
#guard dataChecks rankDeficient
#guard dataChecks coprimeDiagonal
#guard dataChecks chain
#guard dataChecks chainConjugate
#guard dataChecks tall
#guard dataChecks wide
#guard dataChecks mixed
#guard dataChecks (#m[-1] : Matrix Int 1 1)
#guard dataChecks (#m[1, 0; 0, -2] : Matrix Int 2 2)
#guard dataChecks (#m[2, 0; 0, 2] : Matrix Int 2 2)
#guard dataChecks (#m[1, 1; 0, 2] : Matrix Int 2 2)

#guard certChecks empty00
#guard certChecks coprimeDiagonal
#guard certChecks rankDeficient
#guard certChecks tall
#guard certChecks wide
#guard certChecks mixed

#guard snfDiagonal #v[2, 3] = snf coprimeDiagonal
#guard (snfDiagonal #v[0, 2]).rows.toList = [#v[2, 0], #v[0, 0]]
#guard (snfDiagonal #v[-2, 0]).rows.toList = [#v[2, 0], #v[0, 0]]
#guard (snfDiagonal #v[0, 0]).rows.toList = [#v[0, 0], #v[0, 0]]
#guard (snfDiagonal #v[-6, 15, 10]).rows.toList =
  [#v[1, 0, 0], #v[0, 30, 0], #v[0, 0, 30]]

#guard diagonalChecks #v[2, 3]
#guard diagonalChecks #v[0, 2]
#guard diagonalChecks #v[-2, 0]
#guard diagonalChecks #v[0, 0]
#guard diagonalChecks #v[-6, 15, 10]

#guard let D := snfData coprimeDiagonal
  D.left * coprimeDiagonal * D.right = diagMatrix D.diag 2 2
#guard let D := snfData coprimeDiagonal
  D.left * D.leftInv = Matrix.identity 2
#guard let D := snfData coprimeDiagonal
  D.right * D.rightInv = Matrix.identity 2
#guard let D := snfData tall
  D.left * tall * D.right = diagMatrix D.diag 3 2
#guard let D := snfData tall
  D.left * D.leftInv = Matrix.identity 3
#guard let D := snfData tall
  D.right * D.rightInv = Matrix.identity 2
#guard let D := snfDiagonalData #v[-6, 15, 10]
  D.left * diagMatrix #v[-6, 15, 10] 3 3 * D.right = diagMatrix D.diag 3 3
#guard let D := snfDiagonalData #v[-6, 15, 10]
  D.left * D.leftInv = Matrix.identity 3
#guard let D := snfDiagonalData #v[-6, 15, 10]
  D.right * D.rightInv = Matrix.identity 3

private def system : Matrix Int 2 2 := #m[2, 1; 0, 0]
private def soluble : Vector Int 2 := #v[4, 2]
private def obstructed : Vector Int 2 := #v[2, 0]

#guard (snfData system).right ≠ Matrix.identity 2

example : ∃ x, vecMul x system = soluble :=
  (solvable_iff_dvd (snfData_isSNF system) soluble).2 (by decide)

example : ¬ ∃ x, vecMul x system = obstructed := by
  intro h
  have hdvd := (solvable_iff_dvd (snfData_isSNF system) obstructed).1 h
  revert hdvd
  decide

end Hex.Matrix.Smith.Conformance
