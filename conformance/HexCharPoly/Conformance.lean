/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexCharPoly.Fixtures

/-!
Executable characteristic-polynomial conformance checks.

The fixture snapshot is cross-checked against python-flint by
`scripts/oracle/matrix_flint.py`. These guards additionally exercise
Cayley--Hamilton and document why annihilation alone is not a certificate.
-/

namespace Hex.CharPolyConformance

open Hex.CharPolyFixtures

private def satisfiesCayleyHamilton (c : Case) : Bool :=
  Hex.Matrix.evalMatrix (Hex.Matrix.charPoly c.matrix) c.matrix == 0

#guard satisfiesCayleyHamilton empty
#guard satisfiesCayleyHamilton scalar
#guard satisfiesCayleyHamilton zero2
#guard satisfiesCayleyHamilton diagonal3
#guard satisfiesCayleyHamilton nilpotent4
#guard satisfiesCayleyHamilton upper4
#guard satisfiesCayleyHamilton lower4
#guard satisfiesCayleyHamilton blockTriangular4
#guard satisfiesCayleyHamilton transposeOriginal
#guard satisfiesCayleyHamilton transposeImage
#guard satisfiesCayleyHamilton similarityOriginal
#guard satisfiesCayleyHamilton similarityConjugate
#guard satisfiesCayleyHamilton repeatedJordan4
#guard satisfiesCayleyHamilton random6
#guard satisfiesCayleyHamilton random7
#guard satisfiesCayleyHamilton random8
#guard satisfiesCayleyHamilton large5

private def falseCertificate : Hex.DensePoly Int :=
  Hex.DensePoly.ofCoeffs #[0, -1, 1]

#guard Hex.Matrix.evalMatrix falseCertificate zero2.matrix == 0
#guard Hex.Matrix.charPoly zero2.matrix != falseCertificate

end Hex.CharPolyConformance
