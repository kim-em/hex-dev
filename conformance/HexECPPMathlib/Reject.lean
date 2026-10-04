/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPPMathlib.Elab
public import HexECPP.Fixture65
public import HexECPP.Fixture17

public section

/-! The explicit bridge rejects computations, substitution, and bad data. -/

/-- error: ecpp: `Hex.ECPP.Fixture17.disguised` has a compiled implementation; use constructor data -/
#guard_msgs in
example : Nat.Prime 17 := by
  ecpp using Hex.ECPP.Fixture17.disguised

example : Nat.Prime 17 := by
  ecpp using (let c := Hex.ECPP.Fixture17.cert; c)

example : True := by
  fail_if_success
    have : Nat.Prime 18446744073709551629 := by
      ecpp using ((fun c => c) Hex.ECPP.Fixture65.cert)
  trivial

example : True := by
  fail_if_success
    have : Nat.Prime 18446744073709551631 := by
      ecpp using Hex.ECPP.Fixture65.cert
  trivial

example : True := by
  fail_if_success
    have : Nat.Prime 35 := by
      ecpp using (Hex.ECPP.Cert.step 35 0 3 1 2 17 [0]
        (.base (.small 13)))
  trivial
