/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.Elab
import HexECPP.Fixture65

/-! The explicit bridge rejects computations, substitution, and bad data. -/

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
