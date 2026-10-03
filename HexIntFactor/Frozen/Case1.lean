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

@[expose] def Hex.IntFactorFrozen.case1 : Hex.Nat.Factorization :=
  ⟨2136386824197929408955547135303871, [⟨1, (Hex.Nat.PrimeCert.pock3 926510094425921 253301 1806 253300 [(3, 5, (Hex.Nat.PrimeCert.small 2)), (2, 0, (Hex.Nat.PrimeCert.small 41)), (2, 0, (Hex.Nat.PrimeCert.small 193))])⟩, ⟨1, (Hex.Nat.PrimeCert.pock3Sieve 2305843009213693951 523073 1689203 523060 2 [(3, 0, (Hex.Nat.PrimeCert.small 2)), (3, 1, (Hex.Nat.PrimeCert.small 5)), (3, 0, (Hex.Nat.PrimeCert.small 13)), (3, 0, (Hex.Nat.PrimeCert.small 31)), (3, 0, (Hex.Nat.PrimeCert.small 41))])⟩]⟩

@[expose] def Hex.IntFactorFrozen.case1_checked : Hex.Nat.CheckedFactorization 2136386824197929408955547135303871 :=
  ⟨Hex.IntFactorFrozen.case1, rfl, by decide +kernel⟩
