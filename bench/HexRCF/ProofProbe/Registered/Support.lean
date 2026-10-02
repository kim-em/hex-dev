/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import HexRCF.ProofProbe.Registered.Unused
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

namespace Hex.RCF.ProofProbe.Registered

open RealCoefficients Hex.OrderedFn.Oracle

-- Caller fixtures only: coarse containment, with no shrinking-width claim.
def piBounds (_ : Rat) : Bounds := ⟨3, mkRat 63 20, by decide⟩
def expBounds (_ : Rat) : Bounds := ⟨mkRat 27 10, mkRat 14 5, by decide⟩

@[rcf_constant] def piRegistration : Registration Real.pi where
  version := 1
  approximation := piBounds
  containment δ _ := by
    norm_num [Contains, piBounds, mkRat]
    constructor
    · exact Real.pi_gt_three.le
    · linarith [Real.pi_lt_d2]

@[rcf_constant] def expRegistration : Registration (Real.exp 1) where
  version := 1
  approximation := expBounds
  containment δ _ := by
    norm_num [Contains, expBounds, mkRat]
    constructor <;> linarith [Real.exp_one_gt_d9, Real.exp_one_lt_d9]

end Hex.RCF.ProofProbe.Registered
