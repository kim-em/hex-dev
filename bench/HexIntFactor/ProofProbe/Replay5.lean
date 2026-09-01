/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.ProofProbe.Support
namespace Hex.IntFactor.ProofProbe
theorem replay5 : Hex.Nat.checkFactorization (replayCase 5) = true := by
  decide +kernel

#print axioms replay5
end Hex.IntFactor.ProofProbe
