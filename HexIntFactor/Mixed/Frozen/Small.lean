/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Mixed.Replay

@[expose] public section

namespace Hex.Nat.Mixed.Frozen

/-- A genuine small elliptic step for seventeen, with an eleven-order point. -/
def ecpp17 : Hex.ECPP.Cert :=
  .step 17 2 3 3 6 6 [10, 13, 3, 13] (.base (.small 11))

/-- Complete mixed factorization of thirty-four. -/
def small : Factorization := ⟨34, [⟨2, 1, .legacy (.small 2)⟩, ⟨17, 1, .ecpp ecpp17⟩]⟩

/-- Subject-bound kernel acceptance for the complete mixed example. -/
def small_checked : CheckedFactorization 34 := ⟨small, rfl, by decide +kernel⟩

/-- A listed seventeen also occurs in the residual, so its exponent is a lower bound. -/
def partialOverlap : PartialFactorization :=
  ⟨578, [⟨2, 1, .legacy (.small 2)⟩, ⟨17, 1, .ecpp ecpp17⟩], 17⟩

/-- Kernel acceptance does not assert that the residual is coprime to the list. -/
def partialOverlap_checked : CheckedPartialFactorization 578 :=
  ⟨partialOverlap, rfl, by decide +kernel⟩

end Hex.Nat.Mixed.Frozen
