/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexHermite
import HexMatrix.Notation

/-!
# Hermite conformance

Oracle: python-flint's `fmpz_mat.hnf`, in `always` mode through
`scripts/oracle/matrix_flint.py`. The external oracle covers `hnf` and the HNF
component of `hnfData`; the transform is checked independently by `U * A = H`
because a valid transform is not unique.

Covered operations: `isHNFForm`, `hnf`, `hnfRank`, `hnfBasis`, `hnfData`,
`hnfWithInv`, `latticeCoeffs`, `latticeContains`, `kernelBasis`, `pivots`,
`latticeIndex`, and `hnfCert`.

Covered properties: canonical form and idempotence; transform equality; both
inverse identities; positive, leading, below-zero, and reduced-above pivot
clauses; determinant/pivot-product agreement; lattice membership soundness and
residual rejection; kernel soundness and bounded independence; and certificate
acceptance plus rejection of malformed data.

Covered edge cases: `0 × 0`, `0 × m`, and `n × 0`; zero and zero-left
matrices; tall, wide, rank-deficient, duplicated, and negated rows; negative
pivot inputs including a negative final pivot; an already-canonical form; a
pivot of one; different row presentations of the same lattice; and a vector
that passes pivot divisibility but fails the residual check. The external
fixture set additionally includes the deterministic `20 × 20` growth case.
-/

namespace Hex.Matrix.Hermite.Conformance

private def negativeLast : Matrix Int 2 2 := #m[1, 0; 0, -1]
private def rankDeficient : Matrix Int 3 2 := #m[2, 4; -2, -4; 4, 8]
private def rectangular : Matrix Int 3 2 := #m[6, 9; 4, 7; -2, 1]
private def zeroLeft : Matrix Int 2 3 := #m[0, 4, 6; 0, -2, 8]
private def tall : Matrix Int 4 2 := #m[2, 0; 0, 3; 4, 6; -2, 3]
private def wide : Matrix Int 2 4 := #m[-6, 9, -3, 12; 4, -7, 5, -2]
private def alreadyHNF : Matrix Int 3 3 := #m[2, 1, 0; 0, 3, 2; 0, 0, 0]
private def pivotOne : Matrix Int 3 3 := #m[3, -2, 7; 2, -1, 4; 5, -3, 11]
private def diagonal : Matrix Int 2 2 := #m[2, 0; 0, 3]
private def unimodular : Matrix Int 2 2 := #m[1, 2; 0, 1]
private def sameLattice2 : Matrix Int 2 2 := #m[2, 0; 0, 3]
private def sameLattice3 : Matrix Int 3 2 := #m[2, 0; 0, 3; 2, 3]
private def empty00 : Matrix Int 0 0 := 0
private def empty03 : Matrix Int 0 3 := 0
private def empty30 : Matrix Int 3 0 := 0

#check isHNFForm
#check hnf
#check hnfRank
#check hnfBasis
#check hnfData
#check hnfWithInv
#check latticeCoeffs
#check latticeContains
#check kernelBasis
#check pivots
#check latticeIndex
#check hnfCert

/- Form computation: empty shapes, typical rectangular input, sign handling,
rank deficiency, a left zero column, and idempotence. Expected matrices are
hand-derived row-HNF values. -/
#guard hnf empty00 = empty00
#guard hnf empty03 = empty03
#guard hnf empty30 = empty30
#guard hnf negativeLast = Matrix.identity 2
#guard (hnf rankDeficient).rows.toList = [#v[2, 4], #v[0, 0], #v[0, 0]]
#guard (hnf rectangular).rows.toList = [#v[2, 2], #v[0, 3], #v[0, 0]]
#guard (hnf zeroLeft).rows.toList = [#v[0, 2, 14], #v[0, 0, 22]]
#guard hnf alreadyHNF = alreadyHNF
#guard hnf (hnf rectangular) = hnf rectangular

/- The rank-profiled candidate itself, rather than only its guarded fallback,
passes the complete HNF shape checker on every structural fixture family. -/
private def principalPasses (A : Matrix Int n m) : Bool :=
  let result := Hermite.principalRun (Hermite.formAccumulator n) A
  isHNFForm result.matrix result.pivots.length result.pivotVector

#guard principalPasses empty00
#guard principalPasses empty03
#guard principalPasses empty30
#guard principalPasses negativeLast
#guard principalPasses rankDeficient
#guard principalPasses rectangular
#guard principalPasses zeroLeft
#guard principalPasses tall
#guard principalPasses wide
#guard principalPasses alreadyHNF
#guard principalPasses pivotOne

/- Rank and basis observers, including equal lattices presented with different
numbers of rows. -/
#guard hnfRank empty03 = 0
#guard hnfRank rankDeficient = 1
#guard hnfRank rectangular = 2
#guard hnfRank wide = 2
#guard (hnfBasis rankDeficient).rows.toList = [#v[2, 4]]
#guard (hnfBasis rectangular).rows.toList = [#v[2, 2], #v[0, 3]]
#guard (hnfBasis sameLattice2).rows.toList = (hnfBasis sameLattice3).rows.toList

/- The executable shape checker covers the complete conjunction of leading
pivots, positive pivots, zeros below, and reduced nonnegative entries above. -/
#guard let D := hnfData rectangular
  isHNFForm D.echelon D.rank D.pivotCols
#guard let D := hnfData zeroLeft
  isHNFForm D.echelon D.rank D.pivotCols
#guard let D := hnfData pivotOne
  isHNFForm D.echelon D.rank D.pivotCols
#guard !(isHNFForm negativeLast 2 #v[0, 1])

/- Transform-only and transform-with-inverse paths. -/
#guard let D := hnfData rectangular
  D.transform * rectangular = D.echelon
#guard let D := hnfData rankDeficient
  D.transform * rankDeficient = D.echelon
#guard let D := hnfData wide
  D.transform * wide = D.echelon
#guard let D := hnfWithInv rectangular
  D.rowData.transform * rectangular = D.rowData.echelon &&
    D.inverse * D.rowData.transform = Matrix.identity 3 &&
    D.rowData.transform * D.inverse = Matrix.identity 3
#guard let D := hnfWithInv rankDeficient
  D.inverse * D.rowData.transform = Matrix.identity 3 &&
    D.rowData.transform * D.inverse = Matrix.identity 3
#guard let D := hnfWithInv diagonal
  D.inverse * D.rowData.transform = Matrix.identity 2 &&
    D.rowData.transform * D.inverse = Matrix.identity 2

/- Lattice solving checks a typical member, a zero member, a pivot-divisible
residual non-member, and the Boolean wrapper on the same classes. -/
#guard latticeCoeffs rectangular #v[2, 2] = some #v[1, -1, 0]
#guard latticeCoeffs rectangular #v[0, 0] = some #v[0, 0, 0]
#guard latticeCoeffs (#m[1, 0] : Matrix Int 1 2) #v[0, 1] = none
#guard latticeContains rectangular #v[2, 2]
#guard latticeContains rectangular #v[0, 0]
#guard !(latticeContains (#m[1, 0] : Matrix Int 1 2) #v[0, 1])

/- Kernel rows annihilate the matrix on rank-deficient, tall, and full-rank
inputs. For the two-row kernel of `rankDeficient`, enumerate coefficients in
`{-1,0,1}` and reject every nonzero combination that maps to zero. -/
#guard kernelBasis rankDeficient * rankDeficient = 0
#guard kernelBasis tall * tall = 0
#guard kernelBasis diagonal * diagonal = 0
private def boundedKernelIndependent : Bool :=
  let K := kernelBasis rankDeficient
  match K.rows.toList with
  | [u, v] =>
      ([-1, 0, 1].flatMap fun a => [-1, 0, 1].map fun b => (a, b)).all fun p =>
        if p.1 = 0 && p.2 = 0 then true
        else (Vector.ofFn (fun i => p.1 * u[i] + p.2 * v[i]) : Vector Int 3) != 0
  | _ => false
#guard boundedKernelIndependent

/- Pivot observers and finite-index convention. -/
#guard (pivots rectangular).toList = [2, 3]
#guard (pivots diagonal).toList = [2, 3]
#guard (pivots rankDeficient).toList = [2]
#guard latticeIndex diagonal = 6
#guard latticeIndex rankDeficient = 0
#guard latticeIndex unimodular = 1
#guard (pivots diagonal).foldl (fun a b => a * b) 1 = (Matrix.det diagonal).natAbs
#guard (pivots unimodular).foldl (fun a b => a * b) 1 =
  (Matrix.det unimodular).natAbs

private def certifies {n m : Nat} (A : Matrix Int n m) : Bool :=
  let D := hnfWithInv A
  hnfCert A D.rowData.echelon D.rowData.transform D.inverse
    D.rowData.rank D.rowData.pivotCols

#guard certifies rectangular
#guard certifies rankDeficient
#guard certifies diagonal
#guard !(hnfCert diagonal negativeLast (Matrix.identity 2) (Matrix.identity 2)
  2 #v[0, 1])
#guard !(hnfCert diagonal diagonal (Matrix.identity 2) (Matrix.identity 2)
  1 #v[0])
#guard !(hnfCert diagonal diagonal (#m[1, 1; 0, 1]) (Matrix.identity 2)
  2 #v[0, 1])

end Hex.Matrix.Hermite.Conformance
