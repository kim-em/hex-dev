/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexCharPoly.Fixtures
import HexCharPoly.Carriers

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

namespace Hex.CharPolyCarriers
open Hex

local instance [ZMod64.Bounds p] : Zero (ZMod64 p) := ⟨0⟩

-- Pin direct instantiation, including the additional MvPoly equality classes.
example (A : Matrix (DensePoly Int) n n) : DensePoly (DensePoly Int) := A.charPoly
example (A : Matrix (DensePoly Rat) n n) : DensePoly (DensePoly Rat) := A.charPoly
example [ZMod64.Bounds p] (A : Matrix (DensePoly (ZMod64 p)) n n) :
    DensePoly (DensePoly (ZMod64 p)) := A.charPoly
example [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (A : Matrix (MV arity R) n n) : DensePoly (MV arity R) := A.charPoly
example (A : Matrix (RationalFn Rat) n n) : DensePoly (RationalFn Rat) := A.charPoly

private def checkCarrier [Lean.Grind.CommRing R] [DecidableEq R]
    (entry : Nat → Nat → R) : Bool := Id.run do
  for (shape, n) in shapes do
    let A := matrix entry shape n
    let p := A.charPoly
    if p.coeff n != 1 then return false
    if n > 0 && p.coeff (n - 1) != -A.trace then return false
    if shape == "singular" && p.coeff 0 != 0 then return false
    if shape == "diagonal" || shape == "triangular" then
      let expected := (List.finRange n).foldl (fun q i =>
        q * DensePoly.ofCoeffs #[-A.rows[i][i], 1]) (1 : DensePoly R)
      if p != expected then return false
  return true

#guard checkCarrier (denseEntry id 2)
#guard checkCarrier (denseEntry ratScalar 2)
#guard checkCarrier (denseEntry (fun z => (z : Mod)) 2)
#guard checkCarrier (mvEntry id 2 4)
#guard checkCarrier (mvEntry id 3 6)
#guard checkCarrier (mvEntry ratScalar 2 4)
#guard checkCarrier (mvEntry ratScalar 3 6)
#guard checkCarrier (ratFnEntry 1)

end Hex.CharPolyCarriers
