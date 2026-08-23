/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib.NormNum

/-!
Downstream tests for the certificate-backed `norm_num` extension, using
the opt-in pattern its module docstring documents: erasing Mathlib's
trial-division extension puts the certificate extension first, and the
re-registered alias keeps small numerals working.
-/

attribute [-norm_num] Mathlib.Meta.NormNum.evalNatPrime

example : Nat.Prime 2147483647 := by norm_num     -- certificate tier
example : ¬ Nat.Prime 2147483649 := by norm_num   -- rho factor witness
example : Nat.Prime 101 := by norm_num            -- alias (trial division)
example : ¬ Nat.Prime 100 := by norm_num
example : Nat.Prime 999983 := by norm_num         -- just below the threshold
example : ¬ Nat.Prime 0 := by norm_num
example : ¬ Nat.Prime 1 := by norm_num
