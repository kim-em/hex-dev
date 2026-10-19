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

@[expose] def Hex.IntFactorFrozen.case5 : Hex.Nat.PartialFactorization :=
  ⟨57896044618658097711785492504343953926634992332820282019728792003956564819949, [], 57896044618658097711785492504343953926634992332820282019728792003956564819949⟩

@[expose] def Hex.IntFactorFrozen.case5_checked : Hex.Nat.CheckedPartialFactorization 57896044618658097711785492504343953926634992332820282019728792003956564819949 :=
  ⟨Hex.IntFactorFrozen.case5, rfl, by decide +kernel⟩
