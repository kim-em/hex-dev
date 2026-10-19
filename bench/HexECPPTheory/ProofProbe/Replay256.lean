/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPTheory.CompactFixtures

theorem result256 : Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564832381 := by
  ecpp using Hex.ECPP.CompactFixtures.cert256

#print axioms result256
