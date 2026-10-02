/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.Elab
import HexECPP.Fixture65
import HexECPP.Fixture17

open Lean Elab Command

/-!
Bridge conformance. Oracle: the Lean kernel; mode: always.
Covered operation: unconditional `Nat.Prime` proof production from exposed
ECPP data. The 65-bit fixture exercises an ECPP step and a checked
Pocklington terminal certificate in a fresh module.
-/

example : Nat.Prime 18446744073709551629 := by
  ecpp using Hex.ECPP.Fixture65.cert

example : Nat.Prime 17 := by
  ecpp using Hex.ECPP.Fixture17.cert

example : Nat.Prime 13 := by
  apply Hex.ECPP.natPrime_of_checkAt
    (cert := .base (.small 13))
  decide

elab "check_ecpp_conversion" : command => do
  let answer ← liftTermElabM <| Hex.ECPP.convertSupplied "13"
  match answer with
  | .ok cert =>
      unless Hex.ECPP.checkAt 13 cert do
        throwError "ECPP endpoint conversion did not return a checked certificate"
  | .error error =>
      throwError "ECPP endpoint conversion failed: {repr error}"

check_ecpp_conversion
