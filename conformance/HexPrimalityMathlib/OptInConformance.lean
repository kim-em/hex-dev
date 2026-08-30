/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-!
Fresh-module checks for the explicit Hex `Nat.Prime` `norm_num` policy.
The canonical `Conformance` module imports this one and checks that the
opt-in attribute erasure does not cross that import boundary.
-/

open Hex.PrimalityTactic

use_hex_primality_norm_num

example : natPrimeCertThreshold = 16777216 := rfl
example : Nat.Prime 16777121 := by norm_num       -- last tested prime below the threshold
example : Nat.Prime 16777259 := by norm_num       -- first prime above the threshold
example : ¬ Nat.Prime 16777216 := by norm_num     -- the threshold itself
example : Nat.Prime 2147483647 := by norm_num     -- certificate-backed positive proof
example : Nat.Prime 9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177 := by
  norm_num                                          -- exact 512-bit ceiling
example : ¬ Nat.Prime 2147483649 := by norm_num   -- validated factor proof
example : ¬ Nat.Prime 3215031751 := by norm_num   -- strong pseudoprime to bases 2, 3, 5, 7
example : ¬ Nat.Prime 0 := by norm_num
example : ¬ Nat.Prime 1 := by norm_num

-- Bounded certificate production exhausts on this adversarial input. The
-- guarded trial alias must decline too: no large trial proof is attempted
-- after bounded Hex search is exhausted.
/--
error: unsolved goals
⊢ Nat.Prime
    11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123
-/
#guard_msgs in
example : Nat.Prime 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123 := by
  norm_num

/--
error: unsolved goals
⊢ Nat.Prime
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
-/
#guard_msgs in
example : Nat.Prime 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by
  norm_num

-- The input ceiling applies to negative goals too; the opt-in extension does
-- not silently recover Mathlib's unbounded trial decision above the ceiling.
/--
error: unsolved goals
⊢ ¬Nat.Prime
      13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
-/
#guard_msgs in
example : ¬ Nat.Prime 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by
  norm_num
