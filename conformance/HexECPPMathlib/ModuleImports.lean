/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPPMathlib

/-! Kernel replay through the module-system umbrella and compact decoder.
The protocol tests additionally import certificates written by the exporters.
-/

namespace Hex.ECPP.ModuleImports

@[expose] public def explicitCert : Hex.ECPP.Cert :=
  .step 17 2 3 3 6 6 [10, 13, 3, 13] (.base (.small 11))

example : _root_.Nat.Prime 17 := by
  ecpp using explicitCert

-- Ordinary module declarations are private by default. The compact decoder's
-- auxiliary data must remain exposed even in this context.
example : _root_.Nat.Prime 17 := by
  ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)

private def hiddenCert : Hex.ECPP.Cert := .base (.small 17)

/-- error: ecpp: `Hex.ECPP.ModuleImports.hiddenCert` is not an exposed data definition -/
#guard_msgs in
example : _root_.Nat.Prime 17 := by
  ecpp using hiddenCert

end Hex.ECPP.ModuleImports
