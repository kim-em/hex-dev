/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPTheory.Native

/-! Explicit opt-in dispatch, bounded exhaustion and unsupported goals. -/

/-- info: Try this:
  [apply] ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)
-/
#guard_msgs in
example : Nat.Prime 17 := by primality? (method := ecpp)

-- Replay the exact suggested text without invoking the producer.
example : Nat.Prime 17 := by
  ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)

/-- error: primality? (method := ecpp): expected a Nat.Prime or Hex.Nat.Prime goal -/
#guard_msgs in
example : True := by primality? (method := ecpp)

/-- error: native ECPP: no certificate; stopped at Hex.ECPP.Resource.screening; unresolved subject 9; seed 0 -/
#guard_msgs in
example : Nat.Prime 9 := by primality? (method := ecpp)

/-- error: native ECPP: no certificate; stopped at Hex.ECPP.Resource.factorWork; unresolved subject 17; seed 9 -/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Hex.ECPP.Native.generate 17 9 { maxFactorWork := 0 }

-- Explicit custom budgets through the supported ceiling are admitted.
run_cmd Lean.Elab.Command.liftTermElabM do
  let (_, cert) ← Hex.ECPP.Native.generate 17 0 { maxBits := 512 }
  unless Hex.ECPP.checkAt 17 cert do
    throwError "native generation changed the admitted subject"

/-- error: native ECPP: native production is admitted only through 512 bits -/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Hex.ECPP.Native.generate 17 0 { maxBits := 513 }
