/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Compact

/-! # Frozen module certificate

This is the public, exposed source shape produced by certificate export.
Replaying it requires no native search or GP import.
-/

namespace Hex.ECPP.Tests

/-- A frozen elliptic step proving 17, with an explicit terminal certificate. -/
@[expose] public def certificate : Hex.ECPP.Cert :=
  ecpp_cert% "[[17,7,1,2,[3,6]]]" using (.small 11)

end Hex.ECPP.Tests
