/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRationalFn.ProofProbe.Support

namespace Hex.RationalFn.ProofProbe

theorem replay4 : check p q cert4 = true := by
  decide +kernel

#print axioms replay4
end Hex.RationalFn.ProofProbe

