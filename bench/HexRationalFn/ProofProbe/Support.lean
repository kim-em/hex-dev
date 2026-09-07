/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn.Cert

public section

namespace Hex.RationalFn.ProofProbe
open DensePoly

@[expose] def p : DensePoly Rat := #p[1, 1]
@[expose] def q : DensePoly Rat := #p[2, 1]

/-- Literal degree-5 Bezout witnesses; preparation is not replayed. -/
@[expose] def cert4 : Cert Rat :=
  ⟨#p[1, 1], #p[2, 1], #p[1, 3, 3, 3, 3, 1], #p[0, -2, -2, -2, -2, -1]⟩

/-- Literal degree-17 Bezout witnesses; preparation is not replayed. -/
@[expose] def cert16 : Cert Rat :=
  ⟨#p[1, 1], #p[2, 1], #p[1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1], #p[0, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -1]⟩

/-- Literal degree-65 Bezout witnesses; preparation is not replayed. -/
@[expose] def cert64 : Cert Rat :=
  ⟨#p[1, 1], #p[2, 1], #p[1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1], #p[0, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -1]⟩

end Hex.RationalFn.ProofProbe

