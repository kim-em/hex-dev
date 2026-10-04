/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Hasse.Degree

/-!
# Hasse's bound over the prime fields used in a primality proof

For an elliptic curve over `ZMod p`, with `p` prime and `N` points, the
integer inequality `(p + 1 - N)² ≤ 4*p` implies
`N ≤ (√p + 1)²`. An ECPP certificate forces `N` to be at least the order
of its supplied point. Combining these bounds excludes a small prime
divisor of the integer being proved prime.
-/

@[expose] public section

namespace Hex.ECPP

open WeierstrassCurve

/-- The restricted integer Hasse inequality over the prime fields used by ECPP.
It holds in characteristics two and three as well, though ECPP checks exclude
those characteristics before constructing its short curve. -/
theorem hasse_sq_zmod (p : ℕ) [Fact p.Prime]
    (W : WeierstrassCurve (ZMod p)) [W.toAffine.IsElliptic] :
    ((p : ℤ) + 1 - (Fintype.card W.toAffine.Point : ℤ)) ^ 2 ≤ 4 * (p : ℤ) := by
  simpa only [ZMod.card] using hasse_sq W

end Hex.ECPP
