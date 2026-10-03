/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Tests.Certificate
import HexECPPMathlib.Native

/-! # Public module replay and native suggestion regression -/

namespace Hex.ECPP.Tests

/-- An importing module kernel-replays the exported certificate shape. -/
public theorem frozenPrime : _root_.Nat.Prime 17 := by
  ecpp using certificate

/-- info: 'Hex.ECPP.Tests.frozenPrime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frozenPrime

/-- info: Try this:
  [apply] ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)
-/
#guard_msgs in
example : _root_.Nat.Prime 17 := by primality? (method := ecpp)

example : _root_.Nat.Prime 17 := by
  ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)

end Hex.ECPP.Tests
