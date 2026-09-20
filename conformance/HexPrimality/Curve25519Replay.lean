/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality.Cert

namespace Hex.PrimalityConformance

-- The applied suggestion depends only on the checker-owning module.
theorem curve25519 : Hex.Nat.Prime (2 ^ 255 - 19) := by
  exact
    Hex.Nat.prime_of_checkPrimeAt (c :=
      Hex.Nat.PrimeCert.pock 57896044618658097711785492504343953926634992332820282019728792003956564819949
        [(2, 0,
            Hex.Nat.PrimeCert.pock3 74058212732561358302231226437062788676166966415465897661863160754340907
              2028478494862525422475607 22304740449229861598212 2028478494862525422475606
              [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 353),
                (2, 0, Hex.Nat.PrimeCert.small 57467),
                (2, 0,
                  Hex.Nat.PrimeCert.pock3 31757755568855353 4028945 289 4028944
                    [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 223),
                      (2, 0, Hex.Nat.PrimeCert.small 4153)])])])
      (by decide +kernel)

/-- info: 'Hex.PrimalityConformance.curve25519' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms curve25519

end Hex.PrimalityConformance

-- These suggestions come from a separate-module producer and a divisor sieve.
-- This module deliberately imports neither the producer nor the elaborator.
example : Hex.Nat.Prime 17 := by
  exact
    Hex.Nat.prime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock 17 [(3, 3, Hex.Nat.PrimeCert.small 2)])
      (by decide +kernel)

example : Hex.Nat.Prime 197 := by
  exact
    Hex.Nat.prime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve 197 1 6 0 2 [(2, 1, Hex.Nat.PrimeCert.small 2)])
      (by decide +kernel)

-- PrimeCert can use a sieve leaf for this prime. Hex uses a short subtree.
example : Hex.Nat.Prime 100003 :=
  Hex.Nat.prime_of_checkPrimeAt (c := .pock 100003 [(2, 0, .small 2381)])
    (by decide +kernel)
