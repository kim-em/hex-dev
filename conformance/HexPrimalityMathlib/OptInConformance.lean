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
example : ¬ Nat.Prime 2147483649 := by norm_num   -- validated factor proof
example : ¬ Nat.Prime 3215031751 := by norm_num   -- strong pseudoprime to bases 2, 3, 5, 7
example : ¬ Nat.Prime 0 := by norm_num
example : ¬ Nat.Prime 1 := by norm_num

-- Bounded certificate production exhausts on this adversarial input. The
-- guarded trial alias must decline too: no large trial proof is attempted
-- after bounded Hex search is exhausted.
/--
error: unsolved goals
⊢ Nat.Prime 3317044064679887385961981
-/
#guard_msgs in
example : Nat.Prime 3317044064679887385961981 := by norm_num
