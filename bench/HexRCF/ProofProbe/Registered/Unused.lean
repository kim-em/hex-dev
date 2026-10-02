/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Registration
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public section

namespace Hex.RCF.ProofProbe.Registered

open RealCoefficients Hex.OrderedFn.Oracle

-- Neither exposed nor meta-imported by Support. Unused providers must not
-- require executable bodies or frozen-version reduction in a consuming module.
def unusedBounds (_ : Rat) : Bounds := ⟨-1, 1, by decide⟩

@[rcf_constant] def unusedRegistration : Registration (Real.sin 42) where
  version := 7
  approximation := unusedBounds
  containment δ _ := by
    simpa [Contains, unusedBounds] using
      And.intro (Real.neg_one_le_sin 42) (Real.sin_le_one 42)

end Hex.RCF.ProofProbe.Registered
