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

@[expose] def Hex.IntFactorFrozen.case6 : Hex.Nat.PartialFactorization :=
  ⟨1000036000099, [], 1000036000099⟩

@[expose] def Hex.IntFactorFrozen.case6_checked : Hex.Nat.CheckedPartialFactorization 1000036000099 :=
  ⟨Hex.IntFactorFrozen.case6, rfl, by decide +kernel⟩
