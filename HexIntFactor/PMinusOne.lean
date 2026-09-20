/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.PMinusOne

public section

/-! The integer-factorization route uses the shared primality primitive
directly; this module is the named adapter boundary from the SPEC. -/

namespace Hex

namespace Nat

/-- Pollard `p - 1` stage 1 as an integer-factorization route. -/
def pMinusOneFactor (n base bound : Nat) : PMinusOneResult :=
  pMinusOneStage1 n base bound

/-- Counted adapter to the shared deterministic stage-1 attempt. -/
def pMinusOneFactorCounted (n base bound : Nat) (r : Rand) :
    PMinusOneAttempt :=
  pMinusOneStage1Counted n base bound r

/-- Every factor returned through the counted adapter is a proper divisor. -/
theorem pMinusOneFactorCounted_spec {n base bound d : Nat} {r : Rand}
    (h : (pMinusOneFactorCounted n base bound r).result = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  exact pMinusOneStage1Counted_spec h

/-- Every factor reported by the integer-factorization adapter is a proper
divisor of its subject. -/
theorem pMinusOneFactor_spec {n base bound d : Nat}
    (h : pMinusOneFactor n base bound = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n :=
  pMinusOneStage1_spec h

/-- Continue a saved stage-1 residue without repeating stage 1. -/
def pMinusOneStage2Counted (n x B₁ B₂ : Nat) (r : Rand) : PMinusOne.Run :=
  PMinusOne.stage2Counted n x B₁ B₂ r

/-- Standalone two-stage search, including its single stage-1 execution. -/
def pMinusOneSearchCounted (n a B₁ B₂ : Nat) (r : Rand) : PMinusOne.Run :=
  PMinusOne.searchCounted n a B₁ B₂ r

theorem pMinusOneStage2Counted_spec {n x B₁ B₂ d : Nat} {r : Rand}
    (h : (pMinusOneStage2Counted n x B₁ B₂ r).result = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := PMinusOne.stage2Counted_spec h

theorem pMinusOneSearchCounted_spec {n a B₁ B₂ d : Nat} {r : Rand}
    (h : (pMinusOneSearchCounted n a B₁ B₂ r).result = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n := PMinusOne.searchCounted_spec h

end Nat

end Hex
