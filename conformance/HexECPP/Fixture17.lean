/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Cert
meta import HexECPP.Cert

public section

/-! A complete small ECPP step, with an 11-point on `y² = x³ + 2x + 3` over `F₁₇`. -/

namespace Hex.ECPP.Fixture17

@[expose] def cert : Hex.ECPP.Cert :=
  .step 17 2 3 3 6 6 [10, 13, 3, 13] (.base (.small 11))

private def alternate : Hex.ECPP.Cert := .base (.small 2)

/-- A definition whose compiled behavior differs from its exposed body.
The explicit elaborator must reject it before evaluation. -/
@[implemented_by alternate, expose]
def disguised : Hex.ECPP.Cert := cert

end Hex.ECPP.Fixture17

#guard Hex.ECPP.checkAt 17 Hex.ECPP.Fixture17.cert
