/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ProofProbe.Nested.Fractions2
public meta import HexSignDet.Dag
public meta import HexSignDet.Replay

public section

namespace Hex.SignDetMathlib.ProofProbe.Nested.N2.Certificates
open Hex.SignDet

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Check all four supplied nonunit fraction normalization certificates. -/
theorem checked : (RationalFn.check Fractions2.firstCert.num Fractions2.firstCert.den Fractions2.firstCert &&
    RationalFn.check Fractions2.secondCert.num Fractions2.secondCert.den Fractions2.secondCert &&
    RationalFn.check Fractions2.squareCert.num Fractions2.squareCert.den Fractions2.squareCert &&
    RationalFn.check Fractions2.sumCert.num Fractions2.sumCert.den Fractions2.sumCert) = true := by
  decide +kernel

/-- info: 'Hex.SignDetMathlib.ProofProbe.Nested.N2.Certificates.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked

-- The external runner reads this inventory.
#print axioms checked
end Hex.SignDetMathlib.ProofProbe.Nested.N2.Certificates
