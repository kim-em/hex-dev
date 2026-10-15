/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.Diagnostics.Nested.Fractions
public meta import HexSignDet.Dag
public meta import HexSignDet.Replay

public section

namespace Hex.SignDetTheory.Diagnostics.Nested.N1.Certificates
open Hex.SignDet

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Check all four supplied nonunit fraction normalization certificates. -/
theorem checked : (RationalFn.check Fractions.firstCert.num Fractions.firstCert.den Fractions.firstCert &&
    RationalFn.check Fractions.secondCert.num Fractions.secondCert.den Fractions.secondCert &&
    RationalFn.check Fractions.squareCert.num Fractions.squareCert.den Fractions.squareCert &&
    RationalFn.check Fractions.sumCert.num Fractions.sumCert.den Fractions.sumCert) = true := by
  decide +kernel

/-- info: 'Hex.SignDetTheory.Diagnostics.Nested.N1.Certificates.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked

end Hex.SignDetTheory.Diagnostics.Nested.N1.Certificates
