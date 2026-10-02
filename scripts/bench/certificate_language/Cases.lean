/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import PrimeCert.Comparator.LanguageExtension
public import PrimeCert.SieveBase
public meta import PrimeCert.Meta.SieveLookup
public section

-- The imported extension contributes a proof, not a raw Hex certificate.
example : Nat.Prime 17 := prime_cert% [trial17 17]
-- Both repeated entries and zero exponents are accepted by this language.
example : Nat.Prime 17 := prime_cert% [small {2; 3}, pock (17, 3, 2 * 2 * 2 * 2 * 3 ^ 0)]
-- Reuse the proof of 17 as a named entry in a later step.
example : Nat.Prime 137 := prime_cert% [small 2, pock (17, 3, 2 ^ 4), pock (137, 3, 2 ^ 3 * 17)]
-- A pure power of two is expressible through the theorem API, although the
-- pinned pock3 surface grammar requires an odd-factor tail.
example : Nat.Prime 197 := PrimeCert.pocklington3_certK 197 2 2 2 [] .lt (by decide +kernel)
-- This explicit divisor bound exceeds Hex's cap, even though a smaller
-- bound also suffices for this prime. This is a witness-policy difference.
example : Nat.Prime 9223372036904058881 :=
  PrimeCert.pocklington3_certK 9223372036904058881 3 65 20 [] .lt (by decide +kernel)
-- This sieve leaf is above Hex's fixed table boundary.
example : Nat.Prime 100003 := prime_cert% [sieve 100003]
