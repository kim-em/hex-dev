/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Search

public section

/-! Adapter boundary for the Brent-rho primitive shared with primality. -/

namespace Hex

namespace Nat

/-- Try the shared Brent-rho proper-factor search. -/
def rhoSplit? (n : Nat) (r : Rand) (fuel : Nat) :
    Except RhoFailure (Nat × Rand) :=
  rhoFactor? n r fuel

/-- Every rho adapter success is a proper divisor. -/
theorem rhoSplit?_spec {n : Nat} {r r' : Rand} {fuel d : Nat}
    (h : rhoSplit? n r fuel = .ok (d, r')) :
    1 < d ∧ d < n ∧ d ∣ n :=
  rhoFactor?_spec h

end Nat

end Hex
