/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.Hasse.Degree

/-! # The restricted prime-field Hasse bound -/

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
