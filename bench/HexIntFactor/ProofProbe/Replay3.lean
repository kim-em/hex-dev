/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.ProofProbe.Support
namespace Hex.IntFactor.ProofProbe
theorem replay3 : Hex.Nat.checkFactorization (replayCase 3) = true := by
  decide +kernel

#print axioms replay3
end Hex.IntFactor.ProofProbe
