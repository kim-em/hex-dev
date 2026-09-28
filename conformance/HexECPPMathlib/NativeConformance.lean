/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.Native

/-! Explicit opt-in dispatch, bounded exhaustion and unsupported goals. -/

/-- error: primality? (method := ecpp): expected a Nat.Prime or Hex.Nat.Prime goal -/
#guard_msgs in
example : True := by primality? (method := ecpp)

/-- error: native ECPP: exhausted Hex.ECPP.Resource.portfolio; unresolved subject 9; seed 0 -/
#guard_msgs in
example : Nat.Prime 9 := by primality? (method := ecpp)

/-- error: native ECPP: exhausted Hex.ECPP.Resource.factorWork; unresolved subject 17; seed 9 -/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Hex.ECPP.Native.generate 17 9 { maxFactorWork := 0 }

/-- error: native ECPP: native production is admitted only through 256 bits -/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Hex.ECPP.Native.generate 17 0 { maxBits := 512 }
