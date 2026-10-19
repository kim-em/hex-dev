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

@[expose] def Hex.IntFactorFrozen.case2 : Hex.Nat.Factorization :=
  ⟨42535295865117307778430344311653531707, [⟨1, (Hex.Nat.PrimeCert.pock3Sieve 2305843009213693951 523073 1689203 523060 2 [(3, 0, (Hex.Nat.PrimeCert.small 2)), (3, 1, (Hex.Nat.PrimeCert.small 5)), (3, 0, (Hex.Nat.PrimeCert.small 13)), (3, 0, (Hex.Nat.PrimeCert.small 31)), (3, 0, (Hex.Nat.PrimeCert.small 41))])⟩, ⟨1, (Hex.Nat.PrimeCert.pock3 18446744073709551557 2290657 848337 2290655 [(2, 1, (Hex.Nat.PrimeCert.small 2)), (2, 0, (Hex.Nat.PrimeCert.small 11)), (2, 0, (Hex.Nat.PrimeCert.small 137)), (2, 0, (Hex.Nat.PrimeCert.small 547))])⟩]⟩

@[expose] def Hex.IntFactorFrozen.case2_checked : Hex.Nat.CheckedFactorization 42535295865117307778430344311653531707 :=
  ⟨Hex.IntFactorFrozen.case2, rfl, by decide +kernel⟩
