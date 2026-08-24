/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public section

/-!
Proof-free exact division for integer algorithms.

Algorithms using this operation establish divisibility in their proof layer and
avoid carrying that proof on the executable value path.  The native attachment
uses Lean's GMP-backed exact quotient; the Lean definition remains Euclidean
division so it is transparent to proofs.
-/

namespace HexArith.Int

/-- Integer exact division without a proof argument on the value path. -/
@[expose, extern "lean_int_div_exact"]
def exactDiv (num denom : @& Int) : Int := num / denom

@[simp, grind =] theorem exactDiv_zero (denom : Int) : exactDiv 0 denom = 0 := by
  simp [exactDiv]

/-- Under the divisibility invariant, `exactDiv` agrees with `Int.divExact`. -/
theorem exactDiv_eq_divExact {num denom : Int} (h : denom ∣ num) :
    exactDiv num denom = Int.divExact num denom h := by
  simp [exactDiv, Int.divExact_eq_ediv]

end HexArith.Int
