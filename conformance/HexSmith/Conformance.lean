/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSmith
import HexMatrix.Notation

/-!
# Smith conformance

Oracle: python-flint's `fmpz_mat.snf`, in `if_available` mode through
`scripts/oracle/matrix_flint.py`; CI installs python-flint. The oracle compares
only the canonical Smith matrix. Transform matrices are non-unique and are
checked independently in Lean.

Covered operations: `snf`, `snfRank`, `snfData`, `invariantFactors`,
`snfDiagonal`, `snfDiagonalData`, `abelianStructure`, `isSNFShape`, and
`snfCert`. The noncomputable specification function `detDivisor` has no runtime
surface; its all-index characterisation is exercised through the compiled
correctness and uniqueness theorems rather than an evaluator fixture.

Covered properties: agreement of form-only and transform-producing paths;
left/right transform equations and inverse identities; positive divisibility
chains; diagonal-fast-path agreement with the general path; idempotence;
certificate acceptance and malformed-certificate rejection; Smith/Hermite rank
agreement; lattice-index/invariant-factor agreement; solvability and
zero-tail rejection; and removal of unit factors from abelian presentations.

Covered edge cases: `0 × 0`, `0 × m`, and `n × 0`; the zero matrix; rank one
and rank deficiency; tall and wide matrices; mixed signs and units; a negative
final diagonal stage; an already-normal six-entry chain; diagonal inputs that
need gcd/lcm repair; diagonal zeros and negatives; nontrivial left/right
transforms; solvable and unsolvable systems; and presentations with torsion,
unit relations, and a free summand.
-/

namespace Hex.Matrix.Smith.Conformance

private def coprimeDiagonal : Matrix Int 2 2 := #m[2, 0; 0, 3]
private def chain : Matrix Int 3 3 := #m[2, 0, 0; 0, 4, 0; 0, 0, 8]
private def chainConjugate : Matrix Int 3 3 := #m[2, 2, 0; 0, 4, 4; 0, 0, 8]
private def rankOne : Matrix Int 3 2 := #m[2, 4; -2, -4; 4, 8]
private def rankDeficient : Matrix Int 3 3 := #m[2, 4, 6; 1, 2, 3; 0, 0, 0]
private def tall : Matrix Int 3 2 := #m[6, 9; 4, 7; -2, 1]
private def wide : Matrix Int 2 3 := #m[6, 4, -2; 9, 7, 1]
private def mixed : Matrix Int 2 2 := #m[-4, 6; 10, -14]
private def chainSix : Matrix Int 6 6 :=
  #m[1, 0, 0, 0, 0, 0;
     0, 2, 0, 0, 0, 0;
     0, 0, 4, 0, 0, 0;
     0, 0, 0, 8, 0, 0;
     0, 0, 0, 0, 16, 0;
     0, 0, 0, 0, 0, 32]
private def empty00 : Matrix Int 0 0 := 0
private def empty03 : Matrix Int 0 3 := 0
private def empty30 : Matrix Int 3 0 := 0

#check snf
#check snfRank
#check snfData
#check invariantFactors
#check snfDiagonal
#check snfDiagonalData
#check abelianStructure
#check detDivisor
#check isSNFShape
#check snfCert

private def dataChecks (A : Matrix Int n m) : Bool :=
  let D := snfData A
  decide (D.left * A * D.right = diagMatrix D.diag n m) &&
    decide (D.left * D.leftInv = Matrix.identity n) &&
    decide (D.right * D.rightInv = Matrix.identity m) &&
    decide (snf A = diagMatrix D.diag n m)

private def certChecks (A : Matrix Int n m) : Bool :=
  let D := snfData A
  snfCert A D (D.left * A)

private def certRejectsCorruptInverse (A : Matrix Int n m) : Bool :=
  let D := snfData A
  let bad : SmithData n m := { D with leftInv := 0 }
  !(snfCert A bad (bad.left * A))

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
#guard snf chainSix = chainSix
#guard snfRank empty03 = 0
#guard snfRank rankOne = 1
#guard snfRank chainSix = 6
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
#guard abelianStructure empty03 = { freeRank := 3, torsionFactors := #[] }
#guard abelianStructure (#m[2, 0, 0] : Matrix Int 1 3) =
  { freeRank := 2, torsionFactors := #[2] }

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
#guard dataChecks chainSix
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
#guard certRejectsCorruptInverse coprimeDiagonal

/- The shape checker is exercised directly on empty, typical valid, and
adversarial invalid-chain data, rather than only as a conjunct of `snfCert`. -/
#guard isSNFShape (snfData empty00)
#guard isSNFShape (snfData chainSix)
#guard !(isSNFShape
  ({ rank := 2
     diag := #v[2, 3]
     left := Matrix.identity 2
     leftInv := Matrix.identity 2
     right := Matrix.identity 2
     rightInv := Matrix.identity 2 } : SmithData 2 2))

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

/- Agreement with the independent Hermite rank path and Hermite-owned lattice
index, on empty, full-rank, rectangular, and deficient inputs. -/
#guard snfRank empty03 = hnfRank empty03
#guard snfRank coprimeDiagonal = hnfRank coprimeDiagonal
#guard snfRank rankDeficient = hnfRank rankDeficient
#guard latticeIndex coprimeDiagonal =
  (invariantFactors coprimeDiagonal).foldl (fun acc d => acc * d.natAbs) 1
#guard latticeIndex tall =
  (invariantFactors tall).foldl (fun acc d => acc * d.natAbs) 1
#guard latticeIndex rankDeficient = 0

private def system : Matrix Int 2 2 := #m[2, 1; 0, 0]
private def soluble : Vector Int 2 := #v[4, 2]
private def obstructed : Vector Int 2 := #v[2, 0]
private def zeroTarget : Vector Int 2 := 0

#guard (snfData system).right ≠ Matrix.identity 2

example : ∃ x, vecMul x system = soluble :=
  (solvable_iff_dvd (snfData_isSNF system) soluble).2 (by decide)

example : ¬ ∃ x, vecMul x system = obstructed := by
  intro h
  have hdvd := (solvable_iff_dvd (snfData_isSNF system) obstructed).1 h
  revert hdvd
  decide

example : ∃ x, vecMul x system = zeroTarget :=
  (solvable_iff_dvd (snfData_isSNF system) zeroTarget).2 (by decide)

end Hex.Matrix.Smith.Conformance
