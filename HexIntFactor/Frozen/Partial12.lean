/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Replay

public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[expose] def Hex.IntFactorFrozen.partial12 : Hex.Nat.PartialFactorization :=
  ⟨12, [⟨2, (Hex.Nat.PrimeCert.small 2)⟩], 3⟩

@[expose] def Hex.IntFactorFrozen.partial12_checked : Hex.Nat.CheckedPartialFactorization 12 :=
  ⟨Hex.IntFactorFrozen.partial12, rfl, by decide +kernel⟩
