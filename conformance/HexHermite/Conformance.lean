/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexHermite
import HexMatrix.Notation

/-! Executable conformance guards for the Hermite API. -/

namespace Hex.Matrix.Hermite.Conformance

private def negativeLast : Matrix Int 2 2 := #m[1, 0; 0, -1]
private def rankDeficient : Matrix Int 3 2 := #m[2, 4; -2, -4; 4, 8]
private def rectangular : Matrix Int 3 2 := #m[6, 9; 4, 7; -2, 1]
private def zeroLeft : Matrix Int 2 3 := #m[0, 4, 6; 0, -2, 8]
private def empty00 : Matrix Int 0 0 := 0
private def empty03 : Matrix Int 0 3 := 0
private def empty30 : Matrix Int 3 0 := 0

#guard hnf empty00 = empty00
#guard hnf empty03 = empty03
#guard hnf empty30 = empty30
#guard hnf negativeLast = Matrix.identity 2
#guard (hnf rankDeficient).rows.toList = [#v[2, 4], #v[0, 0], #v[0, 0]]
#guard (hnf rectangular).rows.toList = [#v[2, 2], #v[0, 3], #v[0, 0]]
#guard (hnf zeroLeft).rows.toList = [#v[0, 2, 14], #v[0, 0, 22]]
#guard hnfRank rankDeficient = 1
#guard hnf (hnf rectangular) = hnf rectangular

#guard let D := hnfWithInv rectangular
  D.rowData.transform * rectangular = D.rowData.echelon
#guard let D := hnfWithInv rectangular
  D.inverse * D.rowData.transform = Matrix.identity 3
#guard let D := hnfWithInv rectangular
  D.rowData.transform * D.inverse = Matrix.identity 3

#guard latticeCoeffs rectangular #v[2, 2] = some #v[1, -1, 0]
#guard latticeCoeffs (#m[1, 0] : Matrix Int 1 2) #v[0, 1] = none
#guard latticeContains rectangular #v[2, 2]
#guard !(latticeContains (#m[1, 0] : Matrix Int 1 2) #v[0, 1])
#guard kernelBasis rankDeficient * rankDeficient = 0
#guard (pivots rectangular).toList = [2, 3]
#guard latticeIndex (#m[2, 0; 0, 3] : Matrix Int 2 2) = 6

end Hex.Matrix.Hermite.Conformance
