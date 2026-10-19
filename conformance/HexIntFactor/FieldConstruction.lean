/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor

-- Standard import: automatic construction shares one finite attempt allowance.
-- Numerals isolate construction from power-expression normalization.
set_option maxHeartbeats 4000000

/-- info: Try this:
  [apply] exact Hex.Nat.prime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.small 7) (by decide +kernel)
-/
#guard_msgs in
example : Hex.Nat.Prime 7 := by
  primality?

/--
info: Try this:
  [apply] exact
    Hex.Nat.prime_of_checkPrimeAt (c :=
      Hex.Nat.PrimeCert.pock 115792089237316195423570985008687907853269984665640564039457584007908834671663
        [(2, 0,
            Hex.Nat.PrimeCert.pock 205115282021455665897114700593932402728804164701536103180137503955397371
              [(2, 0,
                  Hex.Nat.PrimeCert.pock3 255515944373312847190720520512484175977 185873736969223 6447496504
                    185873736969222
                    [(3, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 4423),
                      (2, 0, Hex.Nat.PrimeCert.small 41201), (2, 0, Hex.Nat.PrimeCert.small 96557)])])])
      (by decide +kernel)
-/
#guard_msgs in
example : Hex.Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  primality?

/--
info: Try this:
  [apply] exact
    Hex.Nat.prime_of_checkPrimeAt (c :=
      Hex.Nat.PrimeCert.pock
        39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
        [(2, 0,
            Hex.Nat.PrimeCert.pock3
              19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097
              4275967480674274557415086838890633 1992284194746136709604860560333145 4275967480674274557415086838890631
              [(3, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 8389),
                (2, 0, Hex.Nat.PrimeCert.small 38557),
                (2, 0, Hex.Nat.PrimeCert.pock 312289 [(2, 0, Hex.Nat.PrimeCert.small 3253)]),
                (2, 0,
                  Hex.Nat.PrimeCert.pock3 1357291859799823621 2562799 236783 2562798
                    [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 67),
                      (2, 0, Hex.Nat.PrimeCert.small 6317)])])])
      (by decide +kernel)
-/
#guard_msgs in
example : Hex.Nat.Prime
    39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 := by
  primality?

/--
info: Try this:
  [apply] exact
    Hex.Nat.prime_of_checkPrimeAt (c :=
      Hex.Nat.PrimeCert.pock3Sieve
        726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439
        200419688320257918107309753790586446759397775 4869360204515751591126894045814862955338309044
        200419688320257918107309753790586446759397677 14
        [(7, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 641), (2, 0, Hex.Nat.PrimeCert.small 18287),
          (2, 0,
            Hex.Nat.PrimeCert.pock 2916841 [(3, 0, Hex.Nat.PrimeCert.small 109), (2, 0, Hex.Nat.PrimeCert.small 223)]),
          (2, 0, Hex.Nat.PrimeCert.pock 6700417 [(3, 0, Hex.Nat.PrimeCert.small 17449)]),
          (2, 0,
            Hex.Nat.PrimeCert.pock 596242599987116128415063
              [(3, 0,
                  Hex.Nat.PrimeCert.pock 36131535570665139281
                    [(2, 0,
                        Hex.Nat.PrimeCert.pock3 34741861125639557 1257937 43047 1257936
                          [(2, 1, Hex.Nat.PrimeCert.small 2), (11, 2, Hex.Nat.PrimeCert.small 7),
                            (2, 0, Hex.Nat.PrimeCert.small 463)])])])])
      (by decide +kernel)
-/
#guard_msgs in
theorem interleavedCurve448 : Hex.Nat.Prime 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439 := by
  primality?

-- An open provider expression is rejected before even a table-prime search.
example (_factor : Hex.Nat.FactorSearch) : Hex.Nat.Prime 7 := by
  fail_if_success primality? (factor := _factor)
  primality

-- Standard HexIntFactor import; the explicit override still bypasses automatic
-- selection and honors an exhausted total allowance.
/--
error: primality?: certificate construction for 100003 exhausted after 0 attempts (seed 100003; maximum 521 bits, recursive depth 32, total attempts 0, factor fuel 1024, explicit factor provider Hex.Nat.ecmFactorSearch (its per-attempt bounds apply), witness bases [2, 3, 5, 7, 11, 13, 17] then 32 random candidates, at most 32 factors and 4096 subsets, sieve bound at most 64); unresolved obligation 100003
-/
#guard_msgs in
example : Hex.Nat.Prime 100003 := by
  primality? (factor := Hex.Nat.ecmFactorSearch) (maxAttempts := 0)

-- Standard HexIntFactor import: this 507-bit input also exhausts with the
-- interleaved provider. Its failure belongs only to the filtered field target.
/--
error: primality?: certificate construction for 325201940467712409581766354955805106229098916130042842589140035735389409205180013414465418744822299840352633258734186556814478386800626664214444960969771 exhausted after 642 attempts (seed 325201940467712409581766354955805106229098916130042842589140035735389409205180013414465418744822299840352633258734186556814478386800626664214444960969771; maximum 521 bits, recursive depth 32, total attempts 1024, factor fuel 1024, registered factor provider Hex.Nat.interleavedConstructionFactor (its per-attempt bounds apply), witness bases [2, 3, 5, 7, 11, 13, 17] then 32 random candidates, at most 32 factors and 4096 subsets, sieve bound at most 64; construction provider [Hex.Nat.interleavedConstructionFactor allocated 1024 attempts]); unresolved obligation 325201940467712409581766354955805106229098916130042842589140035735389409205180013414465418744822299840352633258734186556814478386800626664214444960969771
-/
#guard_msgs in
example : Hex.Nat.Prime 325201940467712409581766354955805106229098916130042842589140035735389409205180013414465418744822299840352633258734186556814478386800626664214444960969771 := by primality?

/-- info: 'interleavedCurve448' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interleavedCurve448

-- Independent corpus subjects exercise the adopted route through the tactic,
-- including cases that exhausted in the retained previous-policy comparison.
#guard_msgs (drop info) in
theorem interleaved256 : Hex.Nat.Prime
    98725064373667121382174855406017825356905878104171613528130501276369518782989 := by
  primality?

#guard_msgs (drop info) in
theorem interleaved384 : Hex.Nat.Prime
    34730152303213258661142885000258083991439860104379939165016045425256161811717519506874250341809730923130702070406751 := by
  primality?

#guard_msgs (drop info) in
theorem interleaved512 : Hex.Nat.Prime
    10133471647181947579896384650266844060713849090766027760095687469597152104840850612898432794360461807067553923683341850211950624196278029816845868121453607 := by
  primality?

/-- info: 'interleaved512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interleaved512
