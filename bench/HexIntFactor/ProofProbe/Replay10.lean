/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.ProofProbe.Support

public section
namespace Hex.IntFactor.ProofProbe
theorem replay10 : Hex.Nat.checkFactorization (replayCase 10) = true := by
  decide +kernel

/-- info: 'Hex.IntFactor.ProofProbe.replay10' depends on axioms: [propext] -/
#guard_msgs in
#print axioms replay10
end Hex.IntFactor.ProofProbe
