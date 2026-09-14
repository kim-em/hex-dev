/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRank.Fixtures

/-!
Oracle: SymPy fraction-field rank through `matrix_carriers.py`.
Mode: always.
Covered operations: `genericCert`, `genericRank`, `genericCert?`, `checkRank`.
Covered properties: expected generic ranks and rejection of malformed certificates.
Covered edge cases: zero and empty rectangular matrices, repeated expressions,
rational coefficients, and polynomials vanishing at every finite-field point.
-/

namespace Hex.GenericRank.Conformance
open Hex Fixtures

private def checked {k : Nat} {C : Type} [Lean.Grind.CommRing C] [DecidableEq C]
    [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C] [LawfulGcdOps C] (c : Case k C) : Bool :=
  let cert := genericCert c.matrix
  cert.rank == c.expected && genericRank c.matrix == c.expected &&
    Hex.Matrix.checkRank c.matrix cert && (genericCert? c.matrix).isSome &&
    !Hex.Matrix.checkRank c.matrix { cert with denom := 0 }

#guard (cases (MvPoly.X 0 : Poly 2 Int) (MvPoly.X 1) (MvPoly.X 0 + MvPoly.X 1)).all checked
#guard (cases (MvPoly.X 0 : Poly 3 Int) (MvPoly.X 1) (MvPoly.X 2)).all checked
#guard (cases (MvPoly.C (1/2) * MvPoly.X 0 : Poly 2 Rat)
  (MvPoly.C (2/3) * MvPoly.X 1) (MvPoly.X 0 + MvPoly.X 1)).all checked
#guard (cases (MvPoly.C (1/2) * MvPoly.X 0 : Poly 3 Rat)
  (MvPoly.C (2/3) * MvPoly.X 1) (MvPoly.X 2)).all checked

set_option maxRecDepth 100000 in
private instance : ZMod64.PrimeModulus 2147483647 := ⟨by decide⟩
private instance : ZMod64.Bounds 2147483647 := ⟨by decide, by decide⟩

private instance : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
private instance : ZMod64.PrimeModulus 3 := ⟨by decide⟩
#guard (cases (MvPoly.X 0 : Poly 2 (ZMod64 3)) (MvPoly.X 1)
  (MvPoly.X 0 + MvPoly.X 1)).all checked
#guard (cases (MvPoly.X 0 : Poly 3 (ZMod64 3)) (MvPoly.X 1) (MvPoly.X 2)).all checked
#guard checked (⟨"frobenius", 1, 1,
  ofRows 1 1 #[#[(MvPoly.X 0 : Poly 1 (ZMod64 3)) ^ 3 - MvPoly.X 0]], 1⟩)

#guard (cases (MvPoly.C 1073741823 * MvPoly.X 0 : Poly 2 (ZMod64 2147483647))
  (MvPoly.C 2147483646 * MvPoly.X 1) (MvPoly.X 0 + MvPoly.X 1)).all checked

end Hex.GenericRank.Conformance
