/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public section

/-!
Resource bounds for the explicitly opted-in Mathlib `norm_num` policy.
-/

namespace Hex.PrimalityTactic

/-- The measured opt-in `norm_num` crossover. Numerals below `2^24` use
trial division; 25-bit and larger numerals use bounded certificate search. -/
def natPrimeCertThreshold : Nat := 16777216

/-- Restart budget for the opt-in negative `Nat.Prime` route. One seeded draw
preserves useful small-factor coverage without multiplying the bounded
exhaustion cost. -/
def natPrimeRhoRestartBudget : Nat := 1

/-- Per-restart Brent cycle-step budget for the opt-in negative `Nat.Prime`
route. The fixed cap bounds work independently of input width while retaining
odd small-factor coverage through the supported 512-bit ceiling. -/
def natPrimeRhoStepBudget : Nat := 1 <<< 16

end Hex.PrimalityTactic
