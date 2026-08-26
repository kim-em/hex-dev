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

/-- Every factor reported by the integer-factorization adapter is a proper
divisor of its subject. -/
theorem pMinusOneFactor_spec {n base bound d : Nat}
    (h : pMinusOneFactor n base bound = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n :=
  pMinusOneStage1_spec h

end Nat

end Hex
