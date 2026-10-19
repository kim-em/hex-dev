/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPTheory.Elab
import HexECPP.Fixture65
import HexECPP.Fixture17

open Lean Elab Command

/-!
Bridge conformance. Oracle: the Lean kernel; mode: always.
Covered operations: explicit `ecpp using`, supplied endpoint conversion;
sibling modules cover compact decoding, both native/PARI suggestion routes,
source export and process execution. Properties: unconditional primality from
raw checker acceptance, subject binding and prime-divisor/group correspondence.
Cases: ordinary 17/65-bit proofs and base-only certificates; frozen 256/512-bit
replay, composite subjects 35/49 at prime divisors, corrupted witnesses,
hidden data, compiled replacements, nonclosed subjects and substitution,
32-node acceptance/33-node rejection, syntax and process exhaustion. Native
and PARI protocols replay exact generated suggestions and exports in fresh
modules, reject duplicate exports and replay with search/GP absent. Process
checks cover cancellation, timeout and descendants retaining pipes.
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
