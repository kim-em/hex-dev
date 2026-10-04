/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimalityMathlib.Prime

public section

/-! Frozen certificates from bounded factor-policy experiments. These probes
run no factor search: the Lean kernel replays the literal checker equations
and transports acceptance to Mathlib's primality predicate. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Hex.PrimalityFactorProbe

/-- Frozen holdout-512-ordinary-4 certificate from the random policy. -/
theorem case0 : _root_.Nat.Prime 8303243761314623153536298383293640890258824928930362945199766069795505229347391151296947598482864968712933522433529495861410413812952831043952026306423823 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  8303243761314623153536298383293640890258824928930362945199766069795505229347391151296947598482864968712933522433529495861410413812952831043952026306423823
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      231392247121855978133901766920235943779795090217764365202095841950595408010261529694920315912705259316767035574545980825506006625180389834577710157
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          263727278085898508909776859276785530295439768420955106495189836494449359368507512761372224758574088787986913
          403239302758865286702996050846888501
          969115179775050853745794979379854619
          403239302758865286702996050846888491
          2
          [(5, 4, Hex.Nat.PrimeCert.small 2),
           (2, 2, Hex.Nat.PrimeCert.small 3),
           (5, 0, Hex.Nat.PrimeCert.small 11),
           (2, 0, Hex.Nat.PrimeCert.small 17),
           (2, 0, Hex.Nat.PrimeCert.small 211),
           (2, 0, Hex.Nat.PrimeCert.small 2017),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              431325071899
              [(2, 0, Hex.Nat.PrimeCert.small 10889), (2, 0, Hex.Nat.PrimeCert.small 15461)]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3
              12437309001451
              37949
              13237
              37947
              [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 10837)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case0

/-- Frozen holdout-512-difficult-0 certificate from the random policy. -/
theorem case1 : _root_.Nat.Prime 7983226596738841058766325436315975273752711604126516516644200892341180092058466758226580125510711294302178552878759289723290167401444678034498033356114163 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  7983226596738841058766325436315975273752711604126516516644200892341180092058466758226580125510711294302178552878759289723290167401444678034498033356114163
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      6350026621933690113386201325499420177229374151571760086097788127770776076328881406780335094248779495090930898571905058477877334847597
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          182065818633715903389934318172758908668707966092882963494153075183581188211079735798695012717
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              1119031572209027825034916254932913431565573527312281693778835431145982732381
              418874734804052979745444422141
              10481356997698068
              418874734804052979745444422140
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.pock 5729747 [(2, 0, Hex.Nat.PrimeCert.small 7039)]),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  89769654379
                  [(2, 0, Hex.Nat.PrimeCert.small 347), (2, 0, Hex.Nat.PrimeCert.small 5981)]),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3Sieve
                  112298104307
                  1531
                  14293
                  1493
                  6
                  [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 991)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case1

/-- Frozen Curve25519 certificate from the efficient policy. -/
theorem case2 : _root_.Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  57896044618658097711785492504343953926634992332820282019728792003956564819949
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      74058212732561358302231226437062788676166966415465897661863160754340907
      2028478494862525422475607
      22304740449229861598212
      2028478494862525422475606
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 353),
       (2, 0, Hex.Nat.PrimeCert.small 57467),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          31757755568855353
          4028945
          289
          4028944
          [(5, 2, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 223),
           (2, 0, Hex.Nat.PrimeCert.small 4153)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case2

/-- Frozen P-256 certificate from the efficient policy. -/
theorem case3 : _root_.Nat.Prime 115792089210356248762697446949407573530086143415290314195533631308867097853951 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  115792089210356248762697446949407573530086143415290314195533631308867097853951
  128721914928032094605845043
  4905315401961533613775432
  128721914928032094605845042
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 257),
   (2, 0, Hex.Nat.PrimeCert.small 641),
   (2, 0, Hex.Nat.PrimeCert.small 1531),
   (2, 0, Hex.Nat.PrimeCert.small 65537),
   (2, 0, Hex.Nat.PrimeCert.pock 490463 [(2, 0, Hex.Nat.PrimeCert.small 53), (2, 0, Hex.Nat.PrimeCert.small 661)]),
   (2, 0, Hex.Nat.PrimeCert.pock 6700417 [(3, 0, Hex.Nat.PrimeCert.small 17449)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case3

/-- Frozen secp256k1 certificate from the efficient policy. -/
theorem case4 : _root_.Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
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
           (2, 0, Hex.Nat.PrimeCert.small 96557)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case4

/-- Frozen P-384 certificate from the efficient policy. -/
theorem case5 : _root_.Nat.Prime 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
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
           (2, 0, Hex.Nat.PrimeCert.small 6317)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case5

/-- Frozen Curve448 certificate from the efficient policy. -/
theorem case6 : _root_.Nat.Prime 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
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
      [(17, 8, Hex.Nat.PrimeCert.small 2), (3, 1, Hex.Nat.PrimeCert.small 7), (3, 0, Hex.Nat.PrimeCert.small 2531)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case6

/-- Frozen P-521 certificate from the efficient policy. -/
theorem case7 : _root_.Nat.Prime 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (3, 0, Hex.Nat.PrimeCert.small 3),
   (3, 1, Hex.Nat.PrimeCert.small 5),
   (3, 0, Hex.Nat.PrimeCert.small 11),
   (3, 0, Hex.Nat.PrimeCert.small 17),
   (3, 0, Hex.Nat.PrimeCert.small 31),
   (3, 0, Hex.Nat.PrimeCert.small 41),
   (3, 0, Hex.Nat.PrimeCert.small 53),
   (3, 0, Hex.Nat.PrimeCert.small 131),
   (3, 0, Hex.Nat.PrimeCert.small 157),
   (2, 0, Hex.Nat.PrimeCert.small 521),
   (3, 0, Hex.Nat.PrimeCert.small 1613),
   (3, 0, Hex.Nat.PrimeCert.small 2731),
   (3, 0, Hex.Nat.PrimeCert.small 8191),
   (3, 0, Hex.Nat.PrimeCert.small 42641),
   (3, 0, Hex.Nat.PrimeCert.small 51481),
   (3, 0, Hex.Nat.PrimeCert.small 61681),
   (3, 0, Hex.Nat.PrimeCert.pock 409891 [(3, 0, Hex.Nat.PrimeCert.small 1051)]),
   (3, 0, Hex.Nat.PrimeCert.pock 858001 [(3, 2, Hex.Nat.PrimeCert.small 5), (2, 0, Hex.Nat.PrimeCert.small 13)]),
   (3, 0, Hex.Nat.PrimeCert.pock 5746001 [(3, 1, Hex.Nat.PrimeCert.small 13), (3, 0, Hex.Nat.PrimeCert.small 17)]),
   (3, 0, Hex.Nat.PrimeCert.pock 7623851 [(3, 0, Hex.Nat.PrimeCert.small 37), (3, 0, Hex.Nat.PrimeCert.small 317)]),
   (3, 0, Hex.Nat.PrimeCert.pock 34110701 [(3, 0, Hex.Nat.PrimeCert.small 19), (3, 0, Hex.Nat.PrimeCert.small 1381)]),
   (3,
    0,
    Hex.Nat.PrimeCert.pock 2400573761 [(3, 0, Hex.Nat.PrimeCert.small 347), (3, 0, Hex.Nat.PrimeCert.small 1663)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case7

/-- Frozen holdout-512-ordinary-4 certificate from the efficient policy. -/
theorem case8 : _root_.Nat.Prime 8303243761314623153536298383293640890258824928930362945199766069795505229347391151296947598482864968712933522433529495861410413812952831043952026306423823 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  8303243761314623153536298383293640890258824928930362945199766069795505229347391151296947598482864968712933522433529495861410413812952831043952026306423823
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      231392247121855978133901766920235943779795090217764365202095841950595408010261529694920315912705259316767035574545980825506006625180389834577710157
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          263727278085898508909776859276785530295439768420955106495189836494449359368507512761372224758574088787986913
          205218844160758856953166020016070379
          1132564927445608386528059222182670429
          205218844160758856953166020016070356
          3
          [(5, 4, Hex.Nat.PrimeCert.small 2),
           (2, 2, Hex.Nat.PrimeCert.small 3),
           (2, 0, Hex.Nat.PrimeCert.small 17),
           (2, 0, Hex.Nat.PrimeCert.small 211),
           (2, 0, Hex.Nat.PrimeCert.small 2017),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              198269041
              [(2, 0, Hex.Nat.PrimeCert.small 151), (2, 0, Hex.Nat.PrimeCert.small 5471)]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              275311942584886861
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  55283522607407
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      8373753803
                      [(2,
                        0,
                        Hex.Nat.PrimeCert.pock
                          4186876901
                          [(2, 0, Hex.Nat.PrimeCert.small 83), (2, 0, Hex.Nat.PrimeCert.small 7529)])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case8

/-- Frozen holdout-512-difficult-0 certificate from the efficient policy. -/
theorem case9 : _root_.Nat.Prime 7983226596738841058766325436315975273752711604126516516644200892341180092058466758226580125510711294302178552878759289723290167401444678034498033356114163 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  7983226596738841058766325436315975273752711604126516516644200892341180092058466758226580125510711294302178552878759289723290167401444678034498033356114163
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      6350026621933690113386201325499420177229374151571760086097788127770776076328881406780335094248779495090930898571905058477877334847597
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          182065818633715903389934318172758908668707966092882963494153075183581188211079735798695012717
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              1119031572209027825034916254932913431565573527312281693778835431145982732381
              5238291556606449239293289
              15682955142102726053495642
              5238291556606449239293277
              2
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 5),
               (2, 0, Hex.Nat.PrimeCert.pock 580627 [(2, 0, Hex.Nat.PrimeCert.small 32257)]),
               (2, 0, Hex.Nat.PrimeCert.pock 5729747 [(2, 0, Hex.Nat.PrimeCert.small 7039)]),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  89769654379
                  [(2, 0, Hex.Nat.PrimeCert.small 347), (2, 0, Hex.Nat.PrimeCert.small 5981)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case9

/-- Frozen Curve448 certificate from the balanced policy. -/
theorem case10 : _root_.Nat.Prime 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439
  200419688320257918107309753790586446759397775
  4869360204515751591126894045814862955338309044
  200419688320257918107309753790586446759397677
  14
  [(7, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 641),
   (2, 0, Hex.Nat.PrimeCert.small 18287),
   (2, 0, Hex.Nat.PrimeCert.pock 2916841 [(3, 0, Hex.Nat.PrimeCert.small 109), (2, 0, Hex.Nat.PrimeCert.small 223)]),
   (2, 0, Hex.Nat.PrimeCert.pock 6700417 [(3, 0, Hex.Nat.PrimeCert.small 17449)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      596242599987116128415063
      [(3,
        0,
        Hex.Nat.PrimeCert.pock
          36131535570665139281
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              34741861125639557
              1257937
              43047
              1257936
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (11, 2, Hex.Nat.PrimeCert.small 7),
               (2, 0, Hex.Nat.PrimeCert.small 463)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case10

/-- Frozen P-521 certificate from the balanced policy. -/
theorem case11 : _root_.Nat.Prime 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (3, 0, Hex.Nat.PrimeCert.small 3),
   (3, 1, Hex.Nat.PrimeCert.small 5),
   (3, 0, Hex.Nat.PrimeCert.small 11),
   (3, 0, Hex.Nat.PrimeCert.small 17),
   (3, 0, Hex.Nat.PrimeCert.small 31),
   (3, 0, Hex.Nat.PrimeCert.small 41),
   (3, 0, Hex.Nat.PrimeCert.small 53),
   (3, 0, Hex.Nat.PrimeCert.small 131),
   (3, 0, Hex.Nat.PrimeCert.small 157),
   (2, 0, Hex.Nat.PrimeCert.small 521),
   (3, 0, Hex.Nat.PrimeCert.small 1613),
   (3, 0, Hex.Nat.PrimeCert.small 2731),
   (3, 0, Hex.Nat.PrimeCert.small 8191),
   (3, 0, Hex.Nat.PrimeCert.small 42641),
   (3, 0, Hex.Nat.PrimeCert.small 51481),
   (3, 0, Hex.Nat.PrimeCert.small 61681),
   (3, 0, Hex.Nat.PrimeCert.pock 409891 [(3, 0, Hex.Nat.PrimeCert.small 1051)]),
   (3, 0, Hex.Nat.PrimeCert.pock 858001 [(3, 2, Hex.Nat.PrimeCert.small 5), (2, 0, Hex.Nat.PrimeCert.small 13)]),
   (3, 0, Hex.Nat.PrimeCert.pock 5746001 [(3, 1, Hex.Nat.PrimeCert.small 13), (3, 0, Hex.Nat.PrimeCert.small 17)]),
   (3, 0, Hex.Nat.PrimeCert.pock 7623851 [(3, 0, Hex.Nat.PrimeCert.small 37), (3, 0, Hex.Nat.PrimeCert.small 317)]),
   (3, 0, Hex.Nat.PrimeCert.pock 34110701 [(3, 0, Hex.Nat.PrimeCert.small 19), (3, 0, Hex.Nat.PrimeCert.small 1381)]),
   (3,
    0,
    Hex.Nat.PrimeCert.pock 2400573761 [(3, 0, Hex.Nat.PrimeCert.small 347), (3, 0, Hex.Nat.PrimeCert.small 1663)]),
   (3,
    0,
    Hex.Nat.PrimeCert.pock
      108140989558681
      [(3, 0, Hex.Nat.PrimeCert.small 1433), (3, 0, Hex.Nat.PrimeCert.small 23609)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case11

/-- Frozen P-521 certificate from the baseline policy. -/
theorem case12 : _root_.Nat.Prime 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (3, 0, Hex.Nat.PrimeCert.small 3),
   (3, 1, Hex.Nat.PrimeCert.small 5),
   (3, 0, Hex.Nat.PrimeCert.small 11),
   (3, 0, Hex.Nat.PrimeCert.small 17),
   (3, 0, Hex.Nat.PrimeCert.small 31),
   (3, 0, Hex.Nat.PrimeCert.small 41),
   (3, 0, Hex.Nat.PrimeCert.small 53),
   (3, 0, Hex.Nat.PrimeCert.small 131),
   (3, 0, Hex.Nat.PrimeCert.small 157),
   (2, 0, Hex.Nat.PrimeCert.small 521),
   (3, 0, Hex.Nat.PrimeCert.small 1613),
   (3, 0, Hex.Nat.PrimeCert.small 2731),
   (3, 0, Hex.Nat.PrimeCert.small 8191),
   (3, 0, Hex.Nat.PrimeCert.small 42641),
   (3, 0, Hex.Nat.PrimeCert.small 51481),
   (3, 0, Hex.Nat.PrimeCert.small 61681),
   (3, 0, Hex.Nat.PrimeCert.pock 409891 [(3, 0, Hex.Nat.PrimeCert.small 1051)]),
   (3, 0, Hex.Nat.PrimeCert.pock 858001 [(3, 2, Hex.Nat.PrimeCert.small 5), (2, 0, Hex.Nat.PrimeCert.small 13)]),
   (3, 0, Hex.Nat.PrimeCert.pock 5746001 [(3, 1, Hex.Nat.PrimeCert.small 13), (3, 0, Hex.Nat.PrimeCert.small 17)]),
   (3, 0, Hex.Nat.PrimeCert.pock 7623851 [(3, 0, Hex.Nat.PrimeCert.small 37), (3, 0, Hex.Nat.PrimeCert.small 317)]),
   (3, 0, Hex.Nat.PrimeCert.pock 34110701 [(3, 0, Hex.Nat.PrimeCert.small 19), (3, 0, Hex.Nat.PrimeCert.small 1381)]),
   (3, 0, Hex.Nat.PrimeCert.pock 308761441 [(3, 0, Hex.Nat.PrimeCert.small 49481)]),
   (3,
    0,
    Hex.Nat.PrimeCert.pock 2400573761 [(3, 0, Hex.Nat.PrimeCert.small 347), (3, 0, Hex.Nat.PrimeCert.small 1663)]),
   (3,
    0,
    Hex.Nat.PrimeCert.pock
      108140989558681
      [(3, 0, Hex.Nat.PrimeCert.small 1433), (3, 0, Hex.Nat.PrimeCert.small 23609)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case12

/-- Frozen secp256k1 certificate from the random policy. -/
theorem case13 : _root_.Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  115792089237316195423570985008687907853269984665640564039457584007908834671663
  [(2, 0, Hex.Nat.PrimeCert.small 13441),
   (2,
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
           (2, 0, Hex.Nat.PrimeCert.small 96557)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityFactorProbe.case13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms case13


end Hex.PrimalityFactorProbe
