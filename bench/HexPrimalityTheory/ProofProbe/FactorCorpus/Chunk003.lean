/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimalityTheory.Prime

public section

/-! Exact frozen checker equations for factor-policy corpus outputs. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Frozen certificate for 61251725925704279270509400084229465806275684468119298220543292148396075762159. -/
theorem Hex.PrimalityCorpus.h6e9fe37477095b9024b8 : _root_.Nat.Prime 61251725925704279270509400084229465806275684468119298220543292148396075762159 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  61251725925704279270509400084229465806275684468119298220543292148396075762159
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      42177587031913781987275742121606756078067091438514246478558753030431787
      2539781020089015648628824881
      2320371113164870
      2539781020089015648628824880
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          2177868809
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              272233601
              [(2, 0, Hex.Nat.PrimeCert.small 241), (2, 0, Hex.Nat.PrimeCert.small 353)])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          692126426246108837
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              18700054745653
              9383
              175071
              9308
              15
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (3, 1, Hex.Nat.PrimeCert.small 3),
               (2, 0, Hex.Nat.PrimeCert.small 7),
               (2, 0, Hex.Nat.PrimeCert.small 29)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6e9fe37477095b9024b8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6e9fe37477095b9024b8

/-- Frozen certificate for 62561263508896193855979464402352831323862545750803235447661552118233145656581. -/
theorem Hex.PrimalityCorpus.ha4d4fb94d3325c6cbc52 : _root_.Nat.Prime 62561263508896193855979464402352831323862545750803235447661552118233145656581 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  62561263508896193855979464402352831323862545750803235447661552118233145656581
  270909227453785417324702503527
  41200107555446667
  270909227453785417324702503526
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      4040295288553
      8325
      54504
      8298
      6
      [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 761)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      53915729348340311
      287797
      719553
      287786
      3
      [(7, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 96779)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha4d4fb94d3325c6cbc52' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha4d4fb94d3325c6cbc52

/-- Frozen certificate for 63206298473639626075466602385140862799395462895317508646635585756810415352017. -/
theorem Hex.PrimalityCorpus.hec32f000976dded0fe13 : _root_.Nat.Prime 63206298473639626075466602385140862799395462895317508646635585756810415352017 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  63206298473639626075466602385140862799395462895317508646635585756810415352017
  34273665338504918233985423
  1836586533024491753618425
  34273665338504918233985422
  [(5, 3, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 312701 [(2, 0, Hex.Nat.PrimeCert.small 53), (2, 0, Hex.Nat.PrimeCert.small 59)]),
   (2, 0, Hex.Nat.PrimeCert.pock 485052193 [(2, 0, Hex.Nat.PrimeCert.small 269), (2, 0, Hex.Nat.PrimeCert.small 2087)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 54053243359 [(2, 0, Hex.Nat.PrimeCert.small 3089), (2, 0, Hex.Nat.PrimeCert.small 6299)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hec32f000976dded0fe13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hec32f000976dded0fe13

/-- Frozen certificate for 63482757460548766811117847474361978496543138881870312546571287090292794050619. -/
theorem Hex.PrimalityCorpus.h65ab9ad152f540b1ace2 : _root_.Nat.Prime 63482757460548766811117847474361978496543138881870312546571287090292794050619 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  63482757460548766811117847474361978496543138881870312546571287090292794050619
  1432015179394750214791253241
  47300181282442901429190
  1432015179394750214791253240
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 142037183 [(2, 0, Hex.Nat.PrimeCert.small 211), (2, 0, Hex.Nat.PrimeCert.small 6869)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      2883695799376769683
      [(2, 0, Hex.Nat.PrimeCert.small 337),
       (2, 0, Hex.Nat.PrimeCert.small 2887),
       (2, 0, Hex.Nat.PrimeCert.small 9967)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h65ab9ad152f540b1ace2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h65ab9ad152f540b1ace2

/-- Frozen certificate for 63482757460548766811117847474361978496543138881870312546571287090292794050619. -/
theorem Hex.PrimalityCorpus.ha30a0dd777c784d2a7e1 : _root_.Nat.Prime 63482757460548766811117847474361978496543138881870312546571287090292794050619 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  63482757460548766811117847474361978496543138881870312546571287090292794050619
  898849255121482779181399009
  60153795436312038893170
  898849255121482779181399008
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 11032969 [(2, 0, Hex.Nat.PrimeCert.small 9781)]),
   (2, 0, Hex.Nat.PrimeCert.pock 142037183 [(2, 0, Hex.Nat.PrimeCert.small 211), (2, 0, Hex.Nat.PrimeCert.small 6869)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      231769846003
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          38628307667
          5535
          1478
          5533
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 13),
           (2, 0, Hex.Nat.PrimeCert.small 139)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha30a0dd777c784d2a7e1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha30a0dd777c784d2a7e1

/-- Frozen certificate for 63802825834739587113637629164925761588153208639315328777257266467637278948319. -/
theorem Hex.PrimalityCorpus.h44659dcbe2bd50c39b48 : _root_.Nat.Prime 63802825834739587113637629164925761588153208639315328777257266467637278948319 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  63802825834739587113637629164925761588153208639315328777257266467637278948319
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      16154012786610786836135591781598751483838147160922623877119807959989771
      1350344034218678449730209
      766818869198572464982
      1350344034218678449730208
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 37551251 [(2, 0, Hex.Nat.PrimeCert.small 11), (2, 0, Hex.Nat.PrimeCert.small 2731)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          43213994492978207
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              21606997246489103
              66231
              588713
              66195
              4
              [(5, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 67733)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h44659dcbe2bd50c39b48' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h44659dcbe2bd50c39b48

/-- Frozen certificate for 63825282574570009928677218937799129600840977177668139621028178787142935522117. -/
theorem Hex.PrimalityCorpus.h344255de87fd45e2d874 : _root_.Nat.Prime 63825282574570009928677218937799129600840977177668139621028178787142935522117 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  63825282574570009928677218937799129600840977177668139621028178787142935522117
  21868190876198094794412833
  217817762553772594236267024
  21868190876198094794412793
  10
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (3, 0, Hex.Nat.PrimeCert.small 3),
   (2, 1, Hex.Nat.PrimeCert.small 71),
   (2, 0, Hex.Nat.PrimeCert.small 62191),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      3217431025586053
      10607
      264336
      10506
      4
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 1, Hex.Nat.PrimeCert.small 3),
       (2, 0, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.small 197)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h344255de87fd45e2d874' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h344255de87fd45e2d874

/-- Frozen certificate for 63942791304686956264049252444082067493025253751472847709137471677270954498641. -/
theorem Hex.PrimalityCorpus.h53e55a0e56f438bd8352 : _root_.Nat.Prime 63942791304686956264049252444082067493025253751472847709137471677270954498641 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  63942791304686956264049252444082067493025253751472847709137471677270954498641
  1717183416235886085421798380961
  5971339421467897
  1717183416235886085421798380960
  [(3, 3, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 681040183 [(2, 0, Hex.Nat.PrimeCert.small 10331), (2, 0, Hex.Nat.PrimeCert.small 10987)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      212349967468202913347
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          9408961381
          [(2, 0, Hex.Nat.PrimeCert.small 173), (2, 0, Hex.Nat.PrimeCert.small 1423)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h53e55a0e56f438bd8352' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h53e55a0e56f438bd8352

/-- Frozen certificate for 64071119972465830792846696197653781211277244437651815218044909841288451491521. -/
theorem Hex.PrimalityCorpus.h75d76e51668eb069effe : _root_.Nat.Prime 64071119972465830792846696197653781211277244437651815218044909841288451491521 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  64071119972465830792846696197653781211277244437651815218044909841288451491521
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      22236734703360352579407354212328784373870740838296367025319888887991
      40694109843090863387141
      8459015312390439188688
      40694109843090863387140
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 2, Hex.Nat.PrimeCert.small 3),
       (2, 1, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.small 331),
       (2, 0, Hex.Nat.PrimeCert.small 401),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          41803159525711
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              126676240987
              [(2, 0, Hex.Nat.PrimeCert.small 269), (2, 0, Hex.Nat.PrimeCert.small 4021)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h75d76e51668eb069effe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h75d76e51668eb069effe

/-- Frozen certificate for 64122721333534873949780038096702711708454548948915064683663203127053475343413. -/
theorem Hex.PrimalityCorpus.he8aff89a15bee1b77082 : _root_.Nat.Prime 64122721333534873949780038096702711708454548948915064683663203127053475343413 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  64122721333534873949780038096702711708454548948915064683663203127053475343413
  113775479925571973393693215
  1200676473705265371188431
  113775479925571973393693214
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 79),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      517119472403539776480901
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          1585769617919471869
          4643999
          55196
          4643998
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 173),
           (2, 0, Hex.Nat.PrimeCert.small 5477)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he8aff89a15bee1b77082' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he8aff89a15bee1b77082

/-- Frozen certificate for 65428036770633136109735440901398125643885186091953122414606704163968925054023. -/
theorem Hex.PrimalityCorpus.hf74653515cc985db47d2 : _root_.Nat.Prime 65428036770633136109735440901398125643885186091953122414606704163968925054023 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  65428036770633136109735440901398125643885186091953122414606704163968925054023
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      32714018385316568054867720450699062821942593045976561207303352081984462527011
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          23828592551032266248821442701703839014604045248551481737
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              1672258812782370743873616690251803030794707
              266665549876473079
              25479241
              266665549876473078
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.pock 67667651 [(2, 0, Hex.Nat.PrimeCert.small 79609)]),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  1338543233
                  [(2, 0, Hex.Nat.PrimeCert.small 883), (2, 0, Hex.Nat.PrimeCert.small 911)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hf74653515cc985db47d2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hf74653515cc985db47d2

/-- Frozen certificate for 65473292045859100894360006224176761723819530339472145078305710612389171719219. -/
theorem Hex.PrimalityCorpus.h92a82529889cda8d46bc : _root_.Nat.Prime 65473292045859100894360006224176761723819530339472145078305710612389171719219 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  65473292045859100894360006224176761723819530339472145078305710612389171719219
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      13120776162320911545623808898332144844877286267191623
      351543427895322323
      120957399873226855
      351543427895322321
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 1, Hex.Nat.PrimeCert.small 3),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          12938264910881333
          120979
          858393
          120950
          6
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 11),
           (2, 0, Hex.Nat.PrimeCert.small 1973)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h92a82529889cda8d46bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h92a82529889cda8d46bc

/-- Frozen certificate for 66095865409969963512769009351851786604618035736772789163052904321675213083493. -/
theorem Hex.PrimalityCorpus.hf5fb672c54805ab9e914 : _root_.Nat.Prime 66095865409969963512769009351851786604618035736772789163052904321675213083493 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  66095865409969963512769009351851786604618035736772789163052904321675213083493
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      10660089629697342728687775535904477280976067612366701719633403
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          497454179647704776983179107870174614473145363483
          199393423090822075
          6765216263839
          199393423090822074
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 337),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3
              284485938851987
              609745
              208
              609744
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.pock 413113 [(2, 0, Hex.Nat.PrimeCert.small 2459)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hf5fb672c54805ab9e914' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hf5fb672c54805ab9e914

/-- Frozen certificate for 66243588455299990673900461533040028184569126643346295493782783870967602100511. -/
theorem Hex.PrimalityCorpus.hd1b283a3b112b6a1923c : _root_.Nat.Prime 66243588455299990673900461533040028184569126643346295493782783870967602100511 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  66243588455299990673900461533040028184569126643346295493782783870967602100511
  141252317761273774562179695
  1540438885234476928001640
  141252317761273774562179694
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 113),
   (2, 0, Hex.Nat.PrimeCert.pock 14199043 [(2, 1, Hex.Nat.PrimeCert.small 13), (2, 0, Hex.Nat.PrimeCert.small 67)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      204322039
      1017
      318
      1015
      [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 283)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 223641277 [(2, 0, Hex.Nat.PrimeCert.small 1571), (2, 0, Hex.Nat.PrimeCert.small 11863)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd1b283a3b112b6a1923c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd1b283a3b112b6a1923c

/-- Frozen certificate for 66243588455299990673900461533040028184569126643346295493782783870967602100511. -/
theorem Hex.PrimalityCorpus.hf8d273bcf819a3a42a40 : _root_.Nat.Prime 66243588455299990673900461533040028184569126643346295493782783870967602100511 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  66243588455299990673900461533040028184569126643346295493782783870967602100511
  642289803190389623332473429
  276316724145668758416732
  642289803190389623332473428
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 107),
   (2, 0, Hex.Nat.PrimeCert.small 113),
   (2, 0, Hex.Nat.PrimeCert.pock 4508687 [(2, 0, Hex.Nat.PrimeCert.small 3539)]),
   (2, 0, Hex.Nat.PrimeCert.pock 14199043 [(2, 1, Hex.Nat.PrimeCert.small 13), (2, 0, Hex.Nat.PrimeCert.small 67)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 223641277 [(2, 0, Hex.Nat.PrimeCert.small 1571), (2, 0, Hex.Nat.PrimeCert.small 11863)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hf8d273bcf819a3a42a40' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hf8d273bcf819a3a42a40

/-- Frozen certificate for 66771796381955301037688595090742376045136159243768873973395568843327711906759. -/
theorem Hex.PrimalityCorpus.hd5f7aed471d524768bb9 : _root_.Nat.Prime 66771796381955301037688595090742376045136159243768873973395568843327711906759 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  66771796381955301037688595090742376045136159243768873973395568843327711906759
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      9232220615281264035455518172234009706453281898328289
      1274238885874143495
      2587032178401314
      1274238885874143494
      [(3, 4, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 1427),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          29252515785371
          38549
          34459
          38545
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 10301)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd5f7aed471d524768bb9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd5f7aed471d524768bb9

/-- Frozen certificate for 66781110955574635027625848199727876208785874294957488141064876847109811958041. -/
theorem Hex.PrimalityCorpus.ha731869d6cfada60dcec : _root_.Nat.Prime 66781110955574635027625848199727876208785874294957488141064876847109811958041 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  66781110955574635027625848199727876208785874294957488141064876847109811958041
  8025501018646437138398107
  416792702321016950265508820
  8025501018646437138397899
  33
  [(11, 2, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 3),
   (2, 0, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 19),
   (2, 0, Hex.Nat.PrimeCert.small 23),
   (2, 0, Hex.Nat.PrimeCert.small 37),
   (2, 0, Hex.Nat.PrimeCert.small 53),
   (2, 0, Hex.Nat.PrimeCert.small 59),
   (2, 0, Hex.Nat.PrimeCert.pock 1106527 [(2, 0, Hex.Nat.PrimeCert.small 223), (2, 0, Hex.Nat.PrimeCert.small 827)]),
   (2, 0, Hex.Nat.PrimeCert.pock 1333206631 [(2, 0, Hex.Nat.PrimeCert.small 127), (2, 0, Hex.Nat.PrimeCert.small 877)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha731869d6cfada60dcec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha731869d6cfada60dcec

/-- Frozen certificate for 67645435119419548695643915151480504171781015049651626834803014879352151529223. -/
theorem Hex.PrimalityCorpus.hdba5fa1e87dbd1e2014b : _root_.Nat.Prime 67645435119419548695643915151480504171781015049651626834803014879352151529223 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  67645435119419548695643915151480504171781015049651626834803014879352151529223
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      62763200977320230748007951472620163338313408753
      337329891928565
      17911739550818974
      337329891928352
      13
      [(3, 3, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 101),
       (2, 0, Hex.Nat.PrimeCert.small 641),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          1277818807
          287
          10909
          0
          30
          [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 1, Hex.Nat.PrimeCert.small 11)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hdba5fa1e87dbd1e2014b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hdba5fa1e87dbd1e2014b

/-- Frozen certificate for 67669116527397644956540083328620094677749524216304500955895596741016867607217. -/
theorem Hex.PrimalityCorpus.h0b585f353ee48901cb3e : _root_.Nat.Prime 67669116527397644956540083328620094677749524216304500955895596741016867607217 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  67669116527397644956540083328620094677749524216304500955895596741016867607217
  11218887823333015032604117
  18925930517033527419392550
  11218887823333015032604110
  [(3, 3, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 373),
   (2, 0, Hex.Nat.PrimeCert.small 3613),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      1960897345939288447
      14989333
      4210
      14989332
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          7629851
          97
          1525
          0
          17
          [(2, 0, Hex.Nat.PrimeCert.small 2), (3, 1, Hex.Nat.PrimeCert.small 5)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h0b585f353ee48901cb3e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h0b585f353ee48901cb3e

/-- Frozen certificate for 67735649059011715816390874437118330998300186416550926959768130056344855036207. -/
theorem Hex.PrimalityCorpus.h16206b4eee4d5392f209 : _root_.Nat.Prime 67735649059011715816390874437118330998300186416550926959768130056344855036207 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  67735649059011715816390874437118330998300186416550926959768130056344855036207
  121804226920098075443178863
  8150851142942722590786379
  121804226920098075443178862
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 1, Hex.Nat.PrimeCert.small 79),
   (2, 0, Hex.Nat.PrimeCert.small 97),
   (2, 0, Hex.Nat.PrimeCert.pock 25910939 [(2, 0, Hex.Nat.PrimeCert.small 12689)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      2054722161983
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          1453127413
          919
          223
          918
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 11),
           (2, 0, Hex.Nat.PrimeCert.small 41)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h16206b4eee4d5392f209' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h16206b4eee4d5392f209

/-- Frozen certificate for 67735649059011715816390874437118330998300186416550926959768130056344855036207. -/
theorem Hex.PrimalityCorpus.h6b07c1157f88493a36cc : _root_.Nat.Prime 67735649059011715816390874437118330998300186416550926959768130056344855036207 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  67735649059011715816390874437118330998300186416550926959768130056344855036207
  12542790639915326111981661
  110599487462800062892608411
  12542790639915326111981625
  5
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 1, Hex.Nat.PrimeCert.small 79),
   (2, 0, Hex.Nat.PrimeCert.pock 25910939 [(2, 0, Hex.Nat.PrimeCert.small 12689)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      54106540072133
      3733
      1252
      3731
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 36749)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6b07c1157f88493a36cc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6b07c1157f88493a36cc

/-- Frozen certificate for 67810831824474203578832566208401349448088639015989567126415699700911355082023. -/
theorem Hex.PrimalityCorpus.h1d1540ed61e11785fca6 : _root_.Nat.Prime 67810831824474203578832566208401349448088639015989567126415699700911355082023 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  67810831824474203578832566208401349448088639015989567126415699700911355082023
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      490144870432584919418236829098699331362936403577966239
      151686745443920577
      2412522378113552945
      151686745443920513
      7
      [(13, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 41771),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          3815106709697
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              3137423281
              [(2, 0, Hex.Nat.PrimeCert.small 661), (2, 0, Hex.Nat.PrimeCert.small 19777)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h1d1540ed61e11785fca6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h1d1540ed61e11785fca6

/-- Frozen certificate for 68031460617259647141281849225921830681135531660339821345109182658911985841303. -/
theorem Hex.PrimalityCorpus.hb5b2a9eb11acd9d74bf4 : _root_.Nat.Prime 68031460617259647141281849225921830681135531660339821345109182658911985841303 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  68031460617259647141281849225921830681135531660339821345109182658911985841303
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      504316130397584137356826868455027081256575205494377579274487
      42966009329233156085
      28835567747182902562
      42966009329233156082
      [(5, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 38609),
       (2, 0, Hex.Nat.PrimeCert.pock 225721 [(2, 2, Hex.Nat.PrimeCert.small 3), (2, 0, Hex.Nat.PrimeCert.small 19)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          5365147471
          [(2, 0, Hex.Nat.PrimeCert.small 2861), (2, 0, Hex.Nat.PrimeCert.small 3677)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb5b2a9eb11acd9d74bf4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb5b2a9eb11acd9d74bf4

/-- Frozen certificate for 68191123267404419179086053637008898662139090487986795377240823817248046281763. -/
theorem Hex.PrimalityCorpus.h0b76181ee91dc359abc2 : _root_.Nat.Prime 68191123267404419179086053637008898662139090487986795377240823817248046281763 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  68191123267404419179086053637008898662139090487986795377240823817248046281763
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      52501021822968376728861460917522215480442781870069270575563
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          14782455640863163506202859828591807473
          648148557029
          1383777566370
          648148557020
          [(5, 3, Hex.Nat.PrimeCert.small 2),
           (3, 2, Hex.Nat.PrimeCert.small 3),
           (2, 0, Hex.Nat.PrimeCert.small 13),
           (2, 0, Hex.Nat.PrimeCert.small 29),
           (2, 0, Hex.Nat.PrimeCert.small 2089),
           (2, 0, Hex.Nat.PrimeCert.small 6793)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h0b76181ee91dc359abc2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h0b76181ee91dc359abc2

/-- Frozen certificate for 68899775733077404339668791352000897017761205358037308697525763507569164337319. -/
theorem Hex.PrimalityCorpus.h20502803cf2ee02ea318 : _root_.Nat.Prime 68899775733077404339668791352000897017761205358037308697525763507569164337319 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  68899775733077404339668791352000897017761205358037308697525763507569164337319
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      480137141566982895039713217288367158015164967397137861212831311
      169920478701077405311
      890879826053371608754
      169920478701077405290
      2
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 5),
       (2, 0, Hex.Nat.PrimeCert.small 1549),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          33512488155031009
          51435
          10059
          51434
          [(7, 4, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 53),
           (2, 0, Hex.Nat.PrimeCert.small 761)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h20502803cf2ee02ea318' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h20502803cf2ee02ea318

/-- Frozen certificate for 69029289149441975054851220437269381120215618067919705148299482652798447014349. -/
theorem Hex.PrimalityCorpus.h20288c3f9f6511aaa753 : _root_.Nat.Prime 69029289149441975054851220437269381120215618067919705148299482652798447014349 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  69029289149441975054851220437269381120215618067919705148299482652798447014349
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      302760040129131469538821142268725355790419377490875899773243344968414241291
      4990651744690110758630507
      4021921954687110678800647
      4990651744690110758630503
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 263),
       (2, 0, Hex.Nat.PrimeCert.small 47441),
       (2, 0, Hex.Nat.PrimeCert.pock 4130647 [(2, 0, Hex.Nat.PrimeCert.small 52957)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          59519571851
          1187
          522
          1185
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2, 1, Hex.Nat.PrimeCert.small 5),
           (2, 0, Hex.Nat.PrimeCert.small 151)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h20288c3f9f6511aaa753' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h20288c3f9f6511aaa753

/-- Frozen certificate for 69212835738482849770431081983405833938052038844489389764766568158429525064843. -/
theorem Hex.PrimalityCorpus.h564b10a1690cff491295 : _root_.Nat.Prime 69212835738482849770431081983405833938052038844489389764766568158429525064843 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  69212835738482849770431081983405833938052038844489389764766568158429525064843
  105968505729301016062074761
  217251457374722568016048
  105968505729301016062074760
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 101),
   (2, 0, Hex.Nat.PrimeCert.small 673),
   (2, 0, Hex.Nat.PrimeCert.small 2273),
   (2, 0, Hex.Nat.PrimeCert.pock 2896969 [(2, 0, Hex.Nat.PrimeCert.small 6353)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      445848445969
      18307
      923
      18306
      [(7, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 971)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h564b10a1690cff491295' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h564b10a1690cff491295

/-- Frozen certificate for 70054902526615631165377356614326833169392505697141080176142079607601441213313. -/
theorem Hex.PrimalityCorpus.h8f98d194a51768ee5263 : _root_.Nat.Prime 70054902526615631165377356614326833169392505697141080176142079607601441213313 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  70054902526615631165377356614326833169392505697141080176142079607601441213313
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      17162457536313345048189305108066898174361151668044768397
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          1430204794692778754015775425672241514530095972337064033
          766851130012221937
          2847780629443792847
          766851130012221922
          4
          [(5, 4, Hex.Nat.PrimeCert.small 2),
           (2, 1, Hex.Nat.PrimeCert.small 3),
           (2, 0, Hex.Nat.PrimeCert.small 37),
           (2, 0, Hex.Nat.PrimeCert.pock 518387 [(2, 0, Hex.Nat.PrimeCert.small 23563)]),
           (2, 0, Hex.Nat.PrimeCert.pock 90715717 [(2, 0, Hex.Nat.PrimeCert.small 27691)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8f98d194a51768ee5263' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8f98d194a51768ee5263

/-- Frozen certificate for 70155229193280215080663627298141184749758211845401552735899274293111394891179. -/
theorem Hex.PrimalityCorpus.h94ea64ca26d81f4456a8 : _root_.Nat.Prime 70155229193280215080663627298141184749758211845401552735899274293111394891179 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  70155229193280215080663627298141184749758211845401552735899274293111394891179
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      5372269970895404155654350552637971208359252129875130203
      8131218687167996621
      555455965324
      8131218687167996620
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          1099535114343409192817
          [(2, 0, Hex.Nat.PrimeCert.small 13879),
           (2, 0, Hex.Nat.PrimeCert.pock 5598323 [(2, 0, Hex.Nat.PrimeCert.small 75653)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h94ea64ca26d81f4456a8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h94ea64ca26d81f4456a8

/-- Frozen certificate for 70845728524071296338339288134626548832348309227821074576047054921115179349831. -/
theorem Hex.PrimalityCorpus.h2081a15d3297d1b00dc1 : _root_.Nat.Prime 70845728524071296338339288134626548832348309227821074576047054921115179349831 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  70845728524071296338339288134626548832348309227821074576047054921115179349831
  41236529533213134092275527
  40785785894654651521614938
  41236529533213134092275523
  [(11, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 36473),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      80800850716450125713
      3301075
      12895069
      3301059
      4
      [(3, 3, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.small 89),
       (2, 0, Hex.Nat.PrimeCert.small 113)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h2081a15d3297d1b00dc1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h2081a15d3297d1b00dc1

/-- Frozen certificate for 70941574752559358741578748383011000571573677729977866949019449759146872391193. -/
theorem Hex.PrimalityCorpus.h63db01c282a36ecd487e : _root_.Nat.Prime 70941574752559358741578748383011000571573677729977866949019449759146872391193 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  70941574752559358741578748383011000571573677729977866949019449759146872391193
  793653688603917932876844867
  190070086223642602861367
  793653688603917932876844866
  [(3, 2, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 9582680893 [(2, 0, Hex.Nat.PrimeCert.small 3061), (2, 0, Hex.Nat.PrimeCert.small 6067)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      5635098547078277
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          45444343121599
          [(2, 0, Hex.Nat.PrimeCert.small 9133), (2, 0, Hex.Nat.PrimeCert.small 90863)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h63db01c282a36ecd487e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h63db01c282a36ecd487e

/-- Frozen certificate for 70952225104225201650747253874424856999315765468238574758893161455456192334251. -/
theorem Hex.PrimalityCorpus.h6e1bafcdf808d76f49b1 : _root_.Nat.Prime 70952225104225201650747253874424856999315765468238574758893161455456192334251 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  70952225104225201650747253874424856999315765468238574758893161455456192334251
  200872442865087968901766039
  2924342788268117891479968
  200872442865087968901766038
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 2, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 4261),
   (2, 0, Hex.Nat.PrimeCert.pock 64986641 [(2, 0, Hex.Nat.PrimeCert.small 19813)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1591029528083
      [(2, 0, Hex.Nat.PrimeCert.pock 2503327 [(2, 0, Hex.Nat.PrimeCert.small 3137)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6e1bafcdf808d76f49b1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6e1bafcdf808d76f49b1

/-- Frozen certificate for 70952225104225201650747253874424856999315765468238574758893161455456192334251. -/
theorem Hex.PrimalityCorpus.h6e51b9fcfe581596d3f2 : _root_.Nat.Prime 70952225104225201650747253874424856999315765468238574758893161455456192334251 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  70952225104225201650747253874424856999315765468238574758893161455456192334251
  333243944067302126064625681
  1037833182705069071288578
  333243944067302126064625680
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 169143599 [(2, 0, Hex.Nat.PrimeCert.small 57571)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      546535873023876563
      224379
      1402835
      224353
      3
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 73), (2, 0, Hex.Nat.PrimeCert.small 3023)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6e51b9fcfe581596d3f2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6e51b9fcfe581596d3f2

/-- Frozen certificate for 71181554711905819393052468545226026592697264958555872184657835873496848586967. -/
theorem Hex.PrimalityCorpus.h422742005a8893c546fc : _root_.Nat.Prime 71181554711905819393052468545226026592697264958555872184657835873496848586967 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  71181554711905819393052468545226026592697264958555872184657835873496848586967
  147138598151608983167620606977
  4975081214192743989
  147138598151608983167620606976
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      42290094332509384712990884951
      1413122979
      8174128572
      1413122955
      4
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 19219),
       (2, 0, Hex.Nat.PrimeCert.small 41843)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h422742005a8893c546fc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h422742005a8893c546fc

/-- Frozen certificate for 71329189958208321099003361017936839355147885294339260358111875179176830840171. -/
theorem Hex.PrimalityCorpus.h201bda0e2258b0c280b2 : _root_.Nat.Prime 71329189958208321099003361017936839355147885294339260358111875179176830840171 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  71329189958208321099003361017936839355147885294339260358111875179176830840171
  54706290374342677329576741021
  2248930772489687306
  54706290374342677329576741020
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      979387352731
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          10882081697
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              340065053
              [(2, 0, Hex.Nat.PrimeCert.small 4649), (2, 0, Hex.Nat.PrimeCert.small 18287)])])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      64290398473332131
      [(3, 0, Hex.Nat.PrimeCert.small 11),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 96394643 [(2, 0, Hex.Nat.PrimeCert.small 227), (2, 0, Hex.Nat.PrimeCert.small 3169)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h201bda0e2258b0c280b2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h201bda0e2258b0c280b2

/-- Frozen certificate for 71329189958208321099003361017936839355147885294339260358111875179176830840171. -/
theorem Hex.PrimalityCorpus.h7d2fdf3adbca25a3dd2c : _root_.Nat.Prime 71329189958208321099003361017936839355147885294339260358111875179176830840171 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  71329189958208321099003361017936839355147885294339260358111875179176830840171
  6234705436750379606962395119
  655927449329285441526
  6234705436750379606962395118
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      3686894832541696832194738099
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          38197455839515310832709
          [(2, 0, Hex.Nat.PrimeCert.small 4481),
           (2, 0, Hex.Nat.PrimeCert.pock 541020721 [(2, 0, Hex.Nat.PrimeCert.small 98011)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h7d2fdf3adbca25a3dd2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h7d2fdf3adbca25a3dd2c

/-- Frozen certificate for 71528735466493266431869650911610836048895317036457802727868199341350931524071. -/
theorem Hex.PrimalityCorpus.h6584cf0b3899fe9fe3f0 : _root_.Nat.Prime 71528735466493266431869650911610836048895317036457802727868199341350931524071 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  71528735466493266431869650911610836048895317036457802727868199341350931524071
  38871477265607578032391271
  59515223236873802286279424
  38871477265607578032391264
  2
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 103),
   (2, 0, Hex.Nat.PrimeCert.pock 123803 [(3, 0, Hex.Nat.PrimeCert.small 37), (2, 0, Hex.Nat.PrimeCert.small 239)]),
   (2, 0, Hex.Nat.PrimeCert.pock 33873223 [(2, 0, Hex.Nat.PrimeCert.small 229), (2, 0, Hex.Nat.PrimeCert.small 277)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      28376336927
      16981
      183
      16980
      [(5, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 4391)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6584cf0b3899fe9fe3f0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6584cf0b3899fe9fe3f0

/-- Frozen certificate for 72003682236312057416325177435996250525692343067283327246722718438567848148709. -/
theorem Hex.PrimalityCorpus.h968189fcf8e8859b6dfb : _root_.Nat.Prime 72003682236312057416325177435996250525692343067283327246722718438567848148709 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  72003682236312057416325177435996250525692343067283327246722718438567848148709
  392561352586840221326917597
  626747872378521160319080
  392561352586840221326917596
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 331),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      18491573
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          420263
          [(2, 0, Hex.Nat.PrimeCert.pock 210131 [(2, 0, Hex.Nat.PrimeCert.small 21013)])])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      9789355042534667
      126461
      18891
      126460
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 139), (2, 0, Hex.Nat.PrimeCert.small 1831)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h968189fcf8e8859b6dfb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h968189fcf8e8859b6dfb

/-- Frozen certificate for 72445734282604743404271974616243853274886109920868316363387600382837707242943. -/
theorem Hex.PrimalityCorpus.h7d4414900967db0b5c3b : _root_.Nat.Prime 72445734282604743404271974616243853274886109920868316363387600382837707242943 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  72445734282604743404271974616243853274886109920868316363387600382837707242943
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      78501005608101881098096521608216067044990109333172069496029
      3410603849697965378899
      10558025468874092
      3410603849697965378898
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 57773),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          8343463076966209
          38171
          958162
          38070
          12
          [(7, 5, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 1031)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h7d4414900967db0b5c3b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h7d4414900967db0b5c3b

/-- Frozen certificate for 72466029392195184607047166005148600953607797700745231411184175720208391246931. -/
theorem Hex.PrimalityCorpus.he35b9fed2f9e032b0f8b : _root_.Nat.Prime 72466029392195184607047166005148600953607797700745231411184175720208391246931 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  72466029392195184607047166005148600953607797700745231411184175720208391246931
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      16562345743938543806443902435650660499407867812212917747747519
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          764671716042380517256966749121421570923530497357
          563084048621724049
          3695057982496
          563084048621724048
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              80417745826190243
              13743
              2621210
              12957
              21
              [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 61927)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he35b9fed2f9e032b0f8b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he35b9fed2f9e032b0f8b

/-- Frozen certificate for 73211236337672999294217784036036588515727291308708719008111531994890635668789. -/
theorem Hex.PrimalityCorpus.h3f0754d59da39ecf3c23 : _root_.Nat.Prime 73211236337672999294217784036036588515727291308708719008111531994890635668789 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  73211236337672999294217784036036588515727291308708719008111531994890635668789
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      57759799781921266192449165012554649714218939503605151821504985130831
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          54383852489766245385687240152763604723139322127
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              17016469101171745709008089651091224943519
              114670573826445093
              77379
              114670573826445092
              [(3, 0, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  165797390008040071
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      789511380990667
                      [(2,
                        0,
                        Hex.Nat.PrimeCert.pock3Sieve
                          312553990891
                          6781
                          12948
                          6773
                          2
                          [(2, 0, Hex.Nat.PrimeCert.small 2),
                           (2, 1, Hex.Nat.PrimeCert.small 3),
                           (2, 0, Hex.Nat.PrimeCert.small 193)])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h3f0754d59da39ecf3c23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h3f0754d59da39ecf3c23

/-- Frozen certificate for 73426358477531165433226794445980425592122755663001117046889171872335449728929. -/
theorem Hex.PrimalityCorpus.h589dc2e983f767c68e79 : _root_.Nat.Prime 73426358477531165433226794445980425592122755663001117046889171872335449728929 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  73426358477531165433226794445980425592122755663001117046889171872335449728929
  966356092229365093882358701
  51782757863887313399176
  966356092229365093882358700
  [(3, 4, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      26312882761709981561272273
      2575147623
      151560
      2575147622
      [(5, 3, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 227),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          2565257
          [(2,
            0,
            Hex.Nat.PrimeCert.pock 320657 [(2, 1, Hex.Nat.PrimeCert.small 7), (2, 0, Hex.Nat.PrimeCert.small 409)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h589dc2e983f767c68e79' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h589dc2e983f767c68e79

/-- Frozen certificate for 73608444004474270135748796379437144645757509249127242850534471424744372717299. -/
theorem Hex.PrimalityCorpus.ha01b8ab920a306583a81 : _root_.Nat.Prime 73608444004474270135748796379437144645757509249127242850534471424744372717299 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  73608444004474270135748796379437144645757509249127242850534471424744372717299
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      5946082951074839411570286435477614414665258785993416423348971361
      939761556218630212371
      6675741039700331863637
      939761556218630212342
      6
      [(3, 4, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 18239401 [(2, 0, Hex.Nat.PrimeCert.small 10133)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          1143378952273
          11237
          332
          11236
          [(5, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 2593)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha01b8ab920a306583a81' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha01b8ab920a306583a81

/-- Frozen certificate for 73650494187575423086581469229541931013586567490075636749532047494662836213149. -/
theorem Hex.PrimalityCorpus.hd9356d3818b0c8e1e6c8 : _root_.Nat.Prime 73650494187575423086581469229541931013586567490075636749532047494662836213149 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  73650494187575423086581469229541931013586567490075636749532047494662836213149
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      8307419867783243678460394371334092859928994030662648686537721579865841
      46237410674624166642973
      1401955299672190143494798
      46237410674624166642851
      19
      [(7, 3, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 5),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          48810607
          61
          4011
          0
          48
          [(3, 0, Hex.Nat.PrimeCert.small 2), (7, 0, Hex.Nat.PrimeCert.small 3), (2, 0, Hex.Nat.PrimeCert.small 13)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          13939487403313
          1628441
          8
          1628440
          [(5, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 55243)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd9356d3818b0c8e1e6c8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd9356d3818b0c8e1e6c8

/-- Frozen certificate for 74195783994782574842020011613305523516458372065068728147812408164712213868103. -/
theorem Hex.PrimalityCorpus.hbb1500dba2d6d4dbdfdb : _root_.Nat.Prime 74195783994782574842020011613305523516458372065068728147812408164712213868103 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  74195783994782574842020011613305523516458372065068728147812408164712213868103
  2224408912927314629763437
  279799306400088905348309962
  2224408912927314629762933
  23
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 1, Hex.Nat.PrimeCert.small 3),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      251316058321
      3795
      9870
      3784
      2
      [(7, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 223)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 2545414740703 [(2, 0, Hex.Nat.PrimeCert.small 6653), (2, 0, Hex.Nat.PrimeCert.small 14489)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hbb1500dba2d6d4dbdfdb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hbb1500dba2d6d4dbdfdb

/-- Frozen certificate for 75622428668850429995494284478275766537969860582314443365067794817279314380201. -/
theorem Hex.PrimalityCorpus.hb57f216bfaf46243876d : _root_.Nat.Prime 75622428668850429995494284478275766537969860582314443365067794817279314380201 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  75622428668850429995494284478275766537969860582314443365067794817279314380201
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      1102367764852047084482423971986527209008307005573096842056381848648386507
      615137322399858042230689
      2694999536770272583570923
      615137322399858042230671
      4
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 109),
       (2, 0, Hex.Nat.PrimeCert.small 1187),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          1747679108540892223
          394819
          6195914
          394756
          11
          [(3, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 3),
           (2, 0, Hex.Nat.PrimeCert.small 62591)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb57f216bfaf46243876d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb57f216bfaf46243876d

/-- Frozen certificate for 76429134078097397398429149186958466173996858996114974362933505155902672006957. -/
theorem Hex.PrimalityCorpus.hf5b5d875caa0fd3eef16 : _root_.Nat.Prime 76429134078097397398429149186958466173996858996114974362933505155902672006957 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  76429134078097397398429149186958466173996858996114974362933505155902672006957
  3651068970220915155115881395993
  264975185362
  3651068970220915155115881395992
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1255596160633
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          4756046063
          4427
          7
          4426
          [(5, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 9137)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      75613945348665571787
      1718932529
      43
      1718932528
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 11369),
       (2, 0, Hex.Nat.PrimeCert.small 40801)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hf5b5d875caa0fd3eef16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hf5b5d875caa0fd3eef16

/-- Frozen certificate for 77280203319790051489578810847431902727968846965168527630427130182246331470547. -/
theorem Hex.PrimalityCorpus.haf36dce2f37bdaa10eee : _root_.Nat.Prime 77280203319790051489578810847431902727968846965168527630427130182246331470547 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  77280203319790051489578810847431902727968846965168527630427130182246331470547
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      1220470523558194989600006528581961967126792082098740396390673
      65153873561833784683
      359630040055346850737
      65153873561833784660
      5
      [(5, 3, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 3),
       (2, 0, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.small 233),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          334834982480059
          [(2, 0, Hex.Nat.PrimeCert.small 5783), (2, 0, Hex.Nat.PrimeCert.small 81559)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.haf36dce2f37bdaa10eee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.haf36dce2f37bdaa10eee

/-- Frozen certificate for 78157755231025158873195812319513615805659585054981938700919678833625169616239. -/
theorem Hex.PrimalityCorpus.h6a230257980211a0c6bc : _root_.Nat.Prime 78157755231025158873195812319513615805659585054981938700919678833625169616239 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  78157755231025158873195812319513615805659585054981938700919678833625169616239
  26334922702299667236148055
  48253699367399527711006416
  26334922702299667236148047
  2
  [(7, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 13),
   (2, 0, Hex.Nat.PrimeCert.small 227),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      4821770423621691080279
      1848325323
      2204
      1848325322
      [(7, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 467),
       (2, 0, Hex.Nat.PrimeCert.small 971),
       (2, 0, Hex.Nat.PrimeCert.small 1153)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6a230257980211a0c6bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6a230257980211a0c6bc

/-- Frozen certificate for 78219422815159183329688090451936052509731366427118962901662059865976404704471. -/
theorem Hex.PrimalityCorpus.h827bfa8deb3ba7947888 : _root_.Nat.Prime 78219422815159183329688090451936052509731366427118962901662059865976404704471 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  78219422815159183329688090451936052509731366427118962901662059865976404704471
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      21346846634822550830409673918587616818810071854760473926530263
      8035026276398957871193
      150332320783253656
      8035026276398957871192
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 760871 [(2, 0, Hex.Nat.PrimeCert.small 6917)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          5537129221002949
          243303
          129123
          243300
          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 36607)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h827bfa8deb3ba7947888' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h827bfa8deb3ba7947888

/-- Frozen certificate for 79161549004363777961169843106208572866672055011251970369963337971202261634359. -/
theorem Hex.PrimalityCorpus.h4bfc816c19290ac77ca5 : _root_.Nat.Prime 79161549004363777961169843106208572866672055011251970369963337971202261634359 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  79161549004363777961169843106208572866672055011251970369963337971202261634359
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      399232850749383032043297773440271417974008504353099103023
      [(2, 0, Hex.Nat.PrimeCert.small 7),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          5702874889477241432878766699
          11177454151
          63831636
          11177454150
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2, 1, Hex.Nat.PrimeCert.small 7),
           (2, 0, Hex.Nat.PrimeCert.small 29),
           (2, 0, Hex.Nat.PrimeCert.pock 2351743 [(2, 0, Hex.Nat.PrimeCert.small 2861)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h4bfc816c19290ac77ca5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h4bfc816c19290ac77ca5

/-- Frozen certificate for 79627436205971106126293140613721932164696973749152626741461857658339836088897. -/
theorem Hex.PrimalityCorpus.h49b75df88a042f006c43 : _root_.Nat.Prime 79627436205971106126293140613721932164696973749152626741461857658339836088897 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  79627436205971106126293140613721932164696973749152626741461857658339836088897
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      9358174746472749608677861182611677911962980457691253114571094056543839
      38277018021331633056949
      81761529608326076553106
      38277018021331633056940
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (3, 0, Hex.Nat.PrimeCert.small 43),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          2781682910205863357249
          1210347
          139420220
          1209886
          38
          [(3, 5, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 17),
           (2, 0, Hex.Nat.PrimeCert.small 2903)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h49b75df88a042f006c43' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h49b75df88a042f006c43
