/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRationalFn.ProofProbe.Support

namespace Hex.RationalFn.ProofProbe

theorem reject64 : check p q { cert64 with s := cert64.s + 1 } = false := by
  decide +kernel

#print axioms reject64
end Hex.RationalFn.ProofProbe

