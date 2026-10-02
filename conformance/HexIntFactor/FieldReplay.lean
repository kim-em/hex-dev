/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality.Cert

/-! Ordinary checker replay of the exact ECM construction certificates. -/

namespace Hex.IntFactorFields

def secp256k1 : Hex.Nat.PrimeCert := Hex.Nat.PrimeCert.pock
  115792089237316195423570985008687907853269984665640564039457584007908834671663
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      205115282021455665897114700593932402728804164701536103180137503955397371
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          255515944373312847190720520512484175977
          185873736969223
          6447496504
          185873736969222
          [(3, 2, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 4423),
           (2, 0, Hex.Nat.PrimeCert.small 41201),
           (2, 0, Hex.Nat.PrimeCert.small 96557)])])]

example : Hex.Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 :=
  Hex.Nat.prime_of_checkPrimeAt (c := secp256k1) (by decide +kernel)

def p384 : Hex.Nat.PrimeCert := Hex.Nat.PrimeCert.pock
  39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097
      4275967480674274557415086838890633
      1992284194746136709604860560333145
      4275967480674274557415086838890631
      [(3, 3, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 8389),
       (2, 0, Hex.Nat.PrimeCert.small 38557),
       (2, 0, Hex.Nat.PrimeCert.pock 312289 [(2, 0, Hex.Nat.PrimeCert.small 3253)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          1357291859799823621
          2562799
          236783
          2562798
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 67),
           (2, 0, Hex.Nat.PrimeCert.small 6317)])])]

example : Hex.Nat.Prime 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 :=
  Hex.Nat.prime_of_checkPrimeAt (c := p384) (by decide +kernel)

def curve448 : Hex.Nat.PrimeCert := Hex.Nat.PrimeCert.pock3
  726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439
  54009879755274134901254563533313489965746040273
  11750363824128505328512224094510391536838
  54009879755274134901254563533313489965746040272
  [(7, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 18287),
   (2, 0, Hex.Nat.PrimeCert.pock 1466449 [(3, 0, Hex.Nat.PrimeCert.small 137), (2, 0, Hex.Nat.PrimeCert.small 223)]),
   (2, 0, Hex.Nat.PrimeCert.pock 2916841 [(3, 0, Hex.Nat.PrimeCert.small 109), (2, 0, Hex.Nat.PrimeCert.small 223)]),
   (2, 0, Hex.Nat.PrimeCert.pock 6700417 [(3, 0, Hex.Nat.PrimeCert.small 17449)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      167773885276849215533569
      22486179
      20805492
      22486175
      [(17, 8, Hex.Nat.PrimeCert.small 2), (3, 1, Hex.Nat.PrimeCert.small 7), (3, 0, Hex.Nat.PrimeCert.small 2531)])]

example : Hex.Nat.Prime 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439 :=
  Hex.Nat.prime_of_checkPrimeAt (c := curve448) (by decide +kernel)

end Hex.IntFactorFields
