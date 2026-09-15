/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexPrimality.Cert
public section

namespace Hex.PrimalityConformance.Curve448

-- Supplied root factors come from the pinned PrimeCert comparator. Hex's
-- bounded constructor checks that data and constructs the child certificates.
-- This fixture measures supplied-certificate replay, not factor-search coverage.
def certificate : Hex.Nat.PrimeCert :=
Hex.Nat.PrimeCert.pock3
  726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439
  523890102151522916311113076301980070234414163719
  3637867751654793328228610486390601899590
  523890102151522916311113076301980070234414163718
  [(7, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 641),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1469495262398780123809
      [(2, 0, Hex.Nat.PrimeCert.small 223),
       (3,
        0,
        Hex.Nat.PrimeCert.pock3
          3402277943
          2763
          380
          2762
          [(5, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 7),
           (2, 0, Hex.Nat.PrimeCert.small 151)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      167773885276849215533569
      22486179
      20805492
      22486175
      [(17, 8, Hex.Nat.PrimeCert.small 2), (3, 1, Hex.Nat.PrimeCert.small 7), (3, 0, Hex.Nat.PrimeCert.small 2531)])]

theorem result : Hex.Nat.Prime (2 ^ 448 - 2 ^ 224 - 1) :=
  Hex.Nat.prime_of_checkPrimeAt (c := certificate) (by decide +kernel)

/-- info: 'Hex.PrimalityConformance.Curve448.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

end Hex.PrimalityConformance.Curve448
