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

/-- info: Try this:
  [apply] ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)
-/
#guard_msgs in
example : _root_.Nat.Prime 17 := by primality? (method := ecpp) (seed := 3)

/-- info: Try this:
  [apply] ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)
-/
#guard_msgs in
example : _root_.Nat.Prime 17 := by primality? (method := ecpp) (bits := 256)

/-- info: Try this:
  [apply] ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)
-/
#guard_msgs in
example : _root_.Nat.Prime 17 := by primality? (method := ecpp) (bits := 512) (seed := 3)

run_cmd do
  let parsed := Lean.Parser.runParserCategory (← Lean.getEnv) `tactic
    "primality? (method := ecpp) (seed := 0) (bits := 512)"
  match parsed with
  | .error _ => pure ()
  | .ok _ => throwError "the bits policy must precede the seed"

/-- error: native ECPP: bits must be 256 or 512 -/
#guard_msgs in
example : _root_.Nat.Prime 17 := by primality? (method := ecpp) (bits := 513)

/-- error: native ECPP: no certificate; stopped at Hex.ECPP.Resource.inputBits; unresolved subject 115792089237316195423570985008687907853269984665640564039457584007913129639936; seed 0 -/
#guard_msgs in
example : _root_.Nat.Prime (2 ^ 256) := by primality? (method := ecpp)

/-- error: native ECPP: no certificate; stopped at Hex.ECPP.Resource.inputBits; unresolved subject 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096; seed 0 -/
#guard_msgs in
example : _root_.Nat.Prime 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by primality? (method := ecpp) (bits := 512)

end Hex.ECPP.Tests
