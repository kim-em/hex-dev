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

/-- Frozen certificate for 98725064373667121382174855406017825356905878104171613528130501276369518782989. -/
theorem Hex.PrimalityCorpus.h1cf86a4e2c84566b7d80 : _root_.Nat.Prime 98725064373667121382174855406017825356905878104171613528130501276369518782989 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  98725064373667121382174855406017825356905878104171613528130501276369518782989
  89620750759261414287254315
  20445084181722855024596429
  89620750759261414287254314
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 2, Hex.Nat.PrimeCert.small 3),
   (2, 0, Hex.Nat.PrimeCert.small 7),
   (2, 0, Hex.Nat.PrimeCert.small 419),
   (2, 0, Hex.Nat.PrimeCert.small 631),
   (2, 0, Hex.Nat.PrimeCert.small 2281),
   (2, 0, Hex.Nat.PrimeCert.pock 521981 [(2, 0, Hex.Nat.PrimeCert.small 26099)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      206471021
      33
      5267
      0
      39
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 5), (2, 0, Hex.Nat.PrimeCert.small 7)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h1cf86a4e2c84566b7d80' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h1cf86a4e2c84566b7d80

/-- Frozen certificate for 99964527595058093851417832181915895165218787275542031785245829336049359150449. -/
theorem Hex.PrimalityCorpus.hacd7e69de492ae9c8193 : _root_.Nat.Prime 99964527595058093851417832181915895165218787275542031785245829336049359150449 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  99964527595058093851417832181915895165218787275542031785245829336049359150449
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      1209971412210625782178139331531432645424070050002406661460561431035157
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          460319314013145577778354944072329151084199356451701342893704597
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              7394153406912362049853941971897043585592976019630827
              51651676526732950487
              2346185915349
              51651676526732950486
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.pock 152417 [(2, 0, Hex.Nat.PrimeCert.small 433)]),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3
                  130222075812071
                  55883
                  11782
                  55882
                  [(11, 0, Hex.Nat.PrimeCert.small 2),
                   (2, 0, Hex.Nat.PrimeCert.small 11),
                   (2, 0, Hex.Nat.PrimeCert.small 31),
                   (2, 0, Hex.Nat.PrimeCert.small 109)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hacd7e69de492ae9c8193' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hacd7e69de492ae9c8193

/-- Frozen certificate for 100733573085627462022153891116041346001859391688609113059823706270307760376069. -/
theorem Hex.PrimalityCorpus.h8633028a3ddc38d9d9ac : _root_.Nat.Prime 100733573085627462022153891116041346001859391688609113059823706270307760376069 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  100733573085627462022153891116041346001859391688609113059823706270307760376069
  113656300408581787220016179
  3318121983692380314613225
  113656300408581787220016178
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 3, Hex.Nat.PrimeCert.small 3),
   (2, 0, Hex.Nat.PrimeCert.small 191),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 14756519149 [(2, 0, Hex.Nat.PrimeCert.small 2939), (2, 0, Hex.Nat.PrimeCert.small 8539)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 134916058337 [(2, 0, Hex.Nat.PrimeCert.small 197), (2, 0, Hex.Nat.PrimeCert.small 3919)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8633028a3ddc38d9d9ac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8633028a3ddc38d9d9ac

/-- Frozen certificate for 101751568186725357085641185670810520904109082415637838868979836038542674111021. -/
theorem Hex.PrimalityCorpus.h94817238196f392992fb : _root_.Nat.Prime 101751568186725357085641185670810520904109082415637838868979836038542674111021 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  101751568186725357085641185670810520904109082415637838868979836038542674111021
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      5087578409336267854282059283540526045205454120781891943448991801927133705551
      42172640080689511549239975372284637
      2984171
      42172640080689511549239975372284636
      [(7, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          6315639528727
          6269
          73965
          6221
          8
          [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 2, Hex.Nat.PrimeCert.small 3), (2, 1, Hex.Nat.PrimeCert.small 11)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          2311433081620602161441
          3212673
          62058944
          3212595
          11
          [(3, 4, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.pock 134857 [(2, 0, Hex.Nat.PrimeCert.small 1873)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h94817238196f392992fb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h94817238196f392992fb

/-- Frozen certificate for 101916020242825245186419432989228344137461794529039751777293455906014010959047. -/
theorem Hex.PrimalityCorpus.h0d3a8a91a4ddf34123e1 : _root_.Nat.Prime 101916020242825245186419432989228344137461794529039751777293455906014010959047 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  101916020242825245186419432989228344137461794529039751777293455906014010959047
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      22657213
      53
      971
      0
      8
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 2, Hex.Nat.PrimeCert.small 3)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      1082994758006051214163133215833403458617116472686240667
      1044762159246204125
      860688289376423388
      1044762159246204121
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 7),
       (2, 0, Hex.Nat.PrimeCert.small 919),
       (2, 0, Hex.Nat.PrimeCert.small 2381),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          25892398949
          1563
          9050
          1539
          5
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 13),
           (2, 0, Hex.Nat.PrimeCert.small 23)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h0d3a8a91a4ddf34123e1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h0d3a8a91a4ddf34123e1

/-- Frozen certificate for 101916020242825245186419432989228344137461794529039751777293455906014010959047. -/
theorem Hex.PrimalityCorpus.h428d4ae5751df99a0bde : _root_.Nat.Prime 101916020242825245186419432989228344137461794529039751777293455906014010959047 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  101916020242825245186419432989228344137461794529039751777293455906014010959047
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      1082994758006051214163133215833403458617116472686240667
      1044762159246204125
      860688289376423388
      1044762159246204121
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 7),
       (2, 0, Hex.Nat.PrimeCert.small 919),
       (2, 0, Hex.Nat.PrimeCert.small 2381),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          25892398949
          1563
          9050
          1539
          5
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 13),
           (2, 0, Hex.Nat.PrimeCert.small 23)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h428d4ae5751df99a0bde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h428d4ae5751df99a0bde

/-- Frozen certificate for 102225077273946280054858042234293257391367821233506580585955370344116482090343. -/
theorem Hex.PrimalityCorpus.h731229412b44e4e3bca4 : _root_.Nat.Prime 102225077273946280054858042234293257391367821233506580585955370344116482090343 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  102225077273946280054858042234293257391367821233506580585955370344116482090343
  15954673027522768257280635
  784087983410680260103228871
  15954673027522768257280438
  49
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 797),
   (2, 0, Hex.Nat.PrimeCert.small 12041),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      420659259915665009
      425073
      162110
      425071
      [(3, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 71191)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h731229412b44e4e3bca4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h731229412b44e4e3bca4

/-- Frozen certificate for 102278724833297910604330989964806398545621314664301058009329121249095732546171. -/
theorem Hex.PrimalityCorpus.hb329f82b230d292753a8 : _root_.Nat.Prime 102278724833297910604330989964806398545621314664301058009329121249095732546171 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  102278724833297910604330989964806398545621314664301058009329121249095732546171
  64144727392379408499873037
  6312259894996521871990722
  64144727392379408499873036
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 160738542901 [(2, 0, Hex.Nat.PrimeCert.small 79), (2, 0, Hex.Nat.PrimeCert.small 7561)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      279985277822021
      [(2, 0, Hex.Nat.PrimeCert.small 5),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          11211331
          329
          176
          326
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 89)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb329f82b230d292753a8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb329f82b230d292753a8

/-- Frozen certificate for 102749727869766029083403126040868629803393974572290743767015396797852368020041. -/
theorem Hex.PrimalityCorpus.ha73d628037036fdaeddf : _root_.Nat.Prime 102749727869766029083403126040868629803393974572290743767015396797852368020041 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  102749727869766029083403126040868629803393974572290743767015396797852368020041
  427752092909373125442898215
  596239103115127904101190
  427752092909373125442898214
  [(3, 2, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      36692316237154681388680303
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          146792823786451
          36971
          29417
          36967
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2, 2, Hex.Nat.PrimeCert.small 3),
           (2, 1, Hex.Nat.PrimeCert.small 5),
           (2, 0, Hex.Nat.PrimeCert.small 37)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha73d628037036fdaeddf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha73d628037036fdaeddf

/-- Frozen certificate for 104614593217436974791578750722049835142507646253455213183305528885707989245811. -/
theorem Hex.PrimalityCorpus.ha36a52b663f2cebf6df9 : _root_.Nat.Prime 104614593217436974791578750722049835142507646253455213183305528885707989245811 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  104614593217436974791578750722049835142507646253455213183305528885707989245811
  25078650871930587684777606375
  326985836265821364170
  25078650871930587684777606374
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 1094618269993 [(2, 0, Hex.Nat.PrimeCert.small 491), (2, 0, Hex.Nat.PrimeCert.small 56263)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      5777287479632623
      665269
      7514
      665268
      [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 151), (2, 0, Hex.Nat.PrimeCert.small 2053)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha36a52b663f2cebf6df9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha36a52b663f2cebf6df9

/-- Frozen certificate for 104761271846337030430636558907960127824024352081322470611107345764316156373447. -/
theorem Hex.PrimalityCorpus.h1024783415840c38c741 : _root_.Nat.Prime 104761271846337030430636558907960127824024352081322470611107345764316156373447 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  104761271846337030430636558907960127824024352081322470611107345764316156373447
  368634364092200364185363905
  759134073371988253350357
  368634364092200364185363904
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      131339737868085798956110799
      230092915
      837841681
      230092900
      3
      [(13, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 2887),
       (2, 0, Hex.Nat.PrimeCert.small 48487)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h1024783415840c38c741' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h1024783415840c38c741

/-- Frozen certificate for 104761271846337030430636558907960127824024352081322470611107345764316156373447. -/
theorem Hex.PrimalityCorpus.h6bcc4d4108ce0a6863c6 : _root_.Nat.Prime 104761271846337030430636558907960127824024352081322470611107345764316156373447 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  104761271846337030430636558907960127824024352081322470611107345764316156373447
  43421732208326022504629205
  89355042682402492877325683
  43421732208326022504629196
  2
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 257),
   (2, 0, Hex.Nat.PrimeCert.small 36919),
   (2, 0, Hex.Nat.PrimeCert.pock 4614997 [(2, 1, Hex.Nat.PrimeCert.small 23), (2, 0, Hex.Nat.PrimeCert.small 727)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      276465777097
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          11519407379
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              122546887
              413
              1337
              399
              4
              [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 107)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6bcc4d4108ce0a6863c6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6bcc4d4108ce0a6863c6

/-- Frozen certificate for 104801585829586898441781469896636205412138763920393278256545944647830752866131. -/
theorem Hex.PrimalityCorpus.haceaeeb1beb9fc79a7ec : _root_.Nat.Prime 104801585829586898441781469896636205412138763920393278256545944647830752866131 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  104801585829586898441781469896636205412138763920393278256545944647830752866131
  1350815967826673841977847
  431825297846868845203066671
  1350815967826673841976568
  37
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 17123),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      321665909516728984489
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          3865805085048661
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              1652053455149
              73449
              236
              73448
              [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 14771)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.haceaeeb1beb9fc79a7ec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.haceaeeb1beb9fc79a7ec

/-- Frozen certificate for 105039327026386772558657474867151596340993244709107183708095107448311298209557. -/
theorem Hex.PrimalityCorpus.h10394c7493e3073714f4 : _root_.Nat.Prime 105039327026386772558657474867151596340993244709107183708095107448311298209557 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  105039327026386772558657474867151596340993244709107183708095107448311298209557
  44507966929949166306179929
  21305396749998478334677450
  44507966929949166306179927
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 23),
   (2, 0, Hex.Nat.PrimeCert.pock 1307311 [(2, 0, Hex.Nat.PrimeCert.small 43577)]),
   (2, 0, Hex.Nat.PrimeCert.pock 8693551 [(2, 0, Hex.Nat.PrimeCert.small 19319)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      47484536747
      61
      231
      43
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 37), (2, 0, Hex.Nat.PrimeCert.small 137)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h10394c7493e3073714f4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h10394c7493e3073714f4

/-- Frozen certificate for 105039327026386772558657474867151596340993244709107183708095107448311298209557. -/
theorem Hex.PrimalityCorpus.had25b6939c832625297b : _root_.Nat.Prime 105039327026386772558657474867151596340993244709107183708095107448311298209557 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  105039327026386772558657474867151596340993244709107183708095107448311298209557
  3736131640661305092245347
  542679677113474122421077394
  3736131640661305092244765
  47
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 23),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      47484536747
      61
      231
      43
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 37), (2, 0, Hex.Nat.PrimeCert.small 137)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      2251900284211
      3077
      42784
      3020
      7
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (3, 2, Hex.Nat.PrimeCert.small 3),
       (2, 0, Hex.Nat.PrimeCert.small 5),
       (2, 0, Hex.Nat.PrimeCert.small 19)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.had25b6939c832625297b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.had25b6939c832625297b

/-- Frozen certificate for 105321625529729239420699997521394234748783492818863771001358863951153830125299. -/
theorem Hex.PrimalityCorpus.he10f5fd43b614643cb15 : _root_.Nat.Prime 105321625529729239420699997521394234748783492818863771001358863951153830125299 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  105321625529729239420699997521394234748783492818863771001358863951153830125299
  185236716954948967619820705
  483122671524516089379854
  185236716954948967619820704
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 109),
   (2, 0, Hex.Nat.PrimeCert.small 4273),
   (2, 0, Hex.Nat.PrimeCert.pock 875773 [(3, 4, Hex.Nat.PrimeCert.small 3), (2, 0, Hex.Nat.PrimeCert.small 53)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 2166547 [(2, 0, Hex.Nat.PrimeCert.pock 361091 [(2, 0, Hex.Nat.PrimeCert.small 36109)])]),
   (2, 0, Hex.Nat.PrimeCert.pock 186795331 [(2, 0, Hex.Nat.PrimeCert.small 199), (2, 0, Hex.Nat.PrimeCert.small 467)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he10f5fd43b614643cb15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he10f5fd43b614643cb15

/-- Frozen certificate for 106770378147401690308816315609815045291847961459074076953293326602989236680033. -/
theorem Hex.PrimalityCorpus.hd60b74212e190d8bf6e3 : _root_.Nat.Prime 106770378147401690308816315609815045291847961459074076953293326602989236680033 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  106770378147401690308816315609815045291847961459074076953293326602989236680033
  173815066280575374125718085
  6072872633143388754414709
  173815066280575374125718084
  [(5, 4, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 13),
   (2, 0, Hex.Nat.PrimeCert.small 1009),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      223372039406632382363
      2972033
      46765422
      2971970
      16
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 71), (2, 0, Hex.Nat.PrimeCert.small 10883)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd60b74212e190d8bf6e3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd60b74212e190d8bf6e3

/-- Frozen certificate for 106909176538015120514508289845463240744708672823907250278308803774544403712909. -/
theorem Hex.PrimalityCorpus.h2df81564dbba2c5f2e66 : _root_.Nat.Prime 106909176538015120514508289845463240744708672823907250278308803774544403712909 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  106909176538015120514508289845463240744708672823907250278308803774544403712909
  1435958740497398470793215
  293706561046182907314735124
  1435958740497398470792396
  21
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      15695046673
      41
      9435
      0
      11
      [(5, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 3), (2, 0, Hex.Nat.PrimeCert.small 19)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      214888447087597
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          5969123530211
          [(2, 0, Hex.Nat.PrimeCert.pock 3108449 [(2, 0, Hex.Nat.PrimeCert.small 13877)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h2df81564dbba2c5f2e66' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h2df81564dbba2c5f2e66

/-- Frozen certificate for 106944557080331330783586833010686313248488375397493422290143238524879091414921. -/
theorem Hex.PrimalityCorpus.h08b8d8e3f248a6ac4d43 : _root_.Nat.Prime 106944557080331330783586833010686313248488375397493422290143238524879091414921 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  106944557080331330783586833010686313248488375397493422290143238524879091414921
  2705306845544198654973637
  123896084484493634699364341
  2705306845544198654973453
  6
  [(7, 2, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 29),
   (2, 0, Hex.Nat.PrimeCert.small 137),
   (2, 0, Hex.Nat.PrimeCert.small 3301),
   (2, 0, Hex.Nat.PrimeCert.pock 116189 [(2, 0, Hex.Nat.PrimeCert.small 937)]),
   (2, 0, Hex.Nat.PrimeCert.pock 156589 [(2, 0, Hex.Nat.PrimeCert.small 13049)]),
   (2, 0, Hex.Nat.PrimeCert.pock 2176633 [(2, 0, Hex.Nat.PrimeCert.small 3359)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h08b8d8e3f248a6ac4d43' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h08b8d8e3f248a6ac4d43

/-- Frozen certificate for 107265678545310402583624752737392354466276597804215977783944348712594375122207. -/
theorem Hex.PrimalityCorpus.hce8647bd5152c56c8c49 : _root_.Nat.Prime 107265678545310402583624752737392354466276597804215977783944348712594375122207 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  107265678545310402583624752737392354466276597804215977783944348712594375122207
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      973622895738858500727848267273871847845346057866114313589107
      116233757114510596223
      109934852283844645699
      116233757114510596219
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.small 31),
       (2, 0, Hex.Nat.PrimeCert.small 37),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          2637099970914587
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              4082198097391
              [(2, 0, Hex.Nat.PrimeCert.small 691), (2, 0, Hex.Nat.PrimeCert.small 83477)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hce8647bd5152c56c8c49' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hce8647bd5152c56c8c49

/-- Frozen certificate for 107335849514235290402042722152977653195484467299465939385501167858230334032627. -/
theorem Hex.PrimalityCorpus.h9d9870e60763e1ef3440 : _root_.Nat.Prime 107335849514235290402042722152977653195484467299465939385501167858230334032627 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  107335849514235290402042722152977653195484467299465939385501167858230334032627
  4837329024433264402407686941
  7557195335002029898071
  4837329024433264402407686940
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 4919),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      3626658733
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          302221561
          [(2, 0, Hex.Nat.PrimeCert.small 163), (2, 0, Hex.Nat.PrimeCert.small 15451)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      74690190719107
      178675
      4468
      178674
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 45707)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h9d9870e60763e1ef3440' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h9d9870e60763e1ef3440

/-- Frozen certificate for 108791656105230340848900347951061271065068479802234343811913018009053930031891. -/
theorem Hex.PrimalityCorpus.h6dfcf770115acd6ee9ec : _root_.Nat.Prime 108791656105230340848900347951061271065068479802234343811913018009053930031891 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  108791656105230340848900347951061271065068479802234343811913018009053930031891
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      28932521470516997664163604568296120123010905879
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          3206885554258146493478564017767248960652949
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              267240462854845541123213668147270746721079
              4050597623013638907
              24998
              4050597623013638906
              [(11, 0, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  1155968162038498841
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock3Sieve
                      119913709755031
                      22003
                      305465
                      21947
                      13
                      [(3, 0, Hex.Nat.PrimeCert.small 2),
                       (2, 0, Hex.Nat.PrimeCert.small 3),
                       (2, 0, Hex.Nat.PrimeCert.small 5),
                       (2, 0, Hex.Nat.PrimeCert.small 467)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6dfcf770115acd6ee9ec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6dfcf770115acd6ee9ec

/-- Frozen certificate for 108949689068317562998875225051259340359183364262329585874269125417144652216737. -/
theorem Hex.PrimalityCorpus.hd2a30516fd4ab61ae34b : _root_.Nat.Prime 108949689068317562998875225051259340359183364262329585874269125417144652216737 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  108949689068317562998875225051259340359183364262329585874269125417144652216737
  1507682302657544475126070500025175
  70217745268
  1507682302657544475126070500025174
  [(5, 4, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      129848216804491
      6465
      203400
      6337
      10
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 8933)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      211976926821841873
      [(2, 0, Hex.Nat.PrimeCert.small 16417), (2, 0, Hex.Nat.PrimeCert.small 50131)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd2a30516fd4ab61ae34b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd2a30516fd4ab61ae34b

/-- Frozen certificate for 109399562254340585084600118916547624079854289716703676659366040258580691530713. -/
theorem Hex.PrimalityCorpus.hfd97509905b118fdb8ad : _root_.Nat.Prime 109399562254340585084600118916547624079854289716703676659366040258580691530713 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  109399562254340585084600118916547624079854289716703676659366040258580691530713
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      410229673067707068255270092262132022258979447329485737
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          61345823583954053859719414917701051839
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              16643007719318646234520778819
              174571758419
              32317
              174571758418
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 3109),
               (2, 0, Hex.Nat.PrimeCert.small 7907),
               (2, 0, Hex.Nat.PrimeCert.small 10321)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hfd97509905b118fdb8ad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hfd97509905b118fdb8ad

/-- Frozen certificate for 109441662012562789639896596629053827110104267792577437645706841979667509371299. -/
theorem Hex.PrimalityCorpus.h58dea65787eaed28af7f : _root_.Nat.Prime 109441662012562789639896596629053827110104267792577437645706841979667509371299 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  109441662012562789639896596629053827110104267792577437645706841979667509371299
  16767205794439524398135867
  465872877190209392164213510
  16767205794439524398135755
  25
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (3, 1, Hex.Nat.PrimeCert.small 3),
   (2, 0, Hex.Nat.PrimeCert.small 11),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      54736552223976446312233
      73749789
      16275759
      73749788
      [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 173), (2, 0, Hex.Nat.PrimeCert.small 29629)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h58dea65787eaed28af7f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h58dea65787eaed28af7f

/-- Frozen certificate for 109969778722913172357976384148984458637076820903606339029770653125227967735407. -/
theorem Hex.PrimalityCorpus.h822a1976890456d50263 : _root_.Nat.Prime 109969778722913172357976384148984458637076820903606339029770653125227967735407 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  109969778722913172357976384148984458637076820903606339029770653125227967735407
  39639652623886669395441787117523
  1932138883002
  39639652623886669395441787117522
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 382777907 [(2, 0, Hex.Nat.PrimeCert.small 47059)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      220356389761159757105111
      38430253
      57413148
      38430247
      [(11, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.small 73),
       (2, 0, Hex.Nat.PrimeCert.small 27277)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h822a1976890456d50263' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h822a1976890456d50263

/-- Frozen certificate for 109969778722913172357976384148984458637076820903606339029770653125227967735407. -/
theorem Hex.PrimalityCorpus.h869f86ca7052c20a919d : _root_.Nat.Prime 109969778722913172357976384148984458637076820903606339029770653125227967735407 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  109969778722913172357976384148984458637076820903606339029770653125227967735407
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      35132639881388453
      179923
      1954792
      179879
      11
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 13), (2, 0, Hex.Nat.PrimeCert.small 1823)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      220356389761159757105111
      38430253
      57413148
      38430247
      [(11, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.small 73),
       (2, 0, Hex.Nat.PrimeCert.small 27277)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h869f86ca7052c20a919d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h869f86ca7052c20a919d

/-- Frozen certificate for 110238676677212071519811163236873839493915645345988446446372553193628049911561. -/
theorem Hex.PrimalityCorpus.h16b6cd69f91ad3dd0447 : _root_.Nat.Prime 110238676677212071519811163236873839493915645345988446446372553193628049911561 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  110238676677212071519811163236873839493915645345988446446372553193628049911561
  7890917964288089630958757
  196009240469212569392680711
  7890917964288089630958657
  10
  [(7, 2, Hex.Nat.PrimeCert.small 2),
   (2, 1, Hex.Nat.PrimeCert.small 3),
   (2, 0, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 2081),
   (2, 0, Hex.Nat.PrimeCert.pock 504547 [(2, 0, Hex.Nat.PrimeCert.small 41), (2, 0, Hex.Nat.PrimeCert.small 293)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      44364696585659
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          22182348292829
          2607
          563
          2606
          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 35089)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h16b6cd69f91ad3dd0447' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h16b6cd69f91ad3dd0447

/-- Frozen certificate for 110238676677212071519811163236873839493915645345988446446372553193628049911561. -/
theorem Hex.PrimalityCorpus.hedac8a4adee0d90f623d : _root_.Nat.Prime 110238676677212071519811163236873839493915645345988446446372553193628049911561 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  110238676677212071519811163236873839493915645345988446446372553193628049911561
  28603251849744411647934733159
  229168479540064572448
  28603251849744411647934733158
  [(7, 2, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 2081),
   (2, 0, Hex.Nat.PrimeCert.pock 504547 [(2, 0, Hex.Nat.PrimeCert.small 41), (2, 0, Hex.Nat.PrimeCert.small 293)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1846336522925139901
      [(2, 0, Hex.Nat.PrimeCert.small 797),
       (2, 0, Hex.Nat.PrimeCert.small 2017),
       (2, 0, Hex.Nat.PrimeCert.small 4447)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hedac8a4adee0d90f623d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hedac8a4adee0d90f623d

/-- Frozen certificate for 110563179035163486352209484708408778505376952372118350536524234111346330039309. -/
theorem Hex.PrimalityCorpus.h6cf1486065e3b08f4aa2 : _root_.Nat.Prime 110563179035163486352209484708408778505376952372118350536524234111346330039309 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  110563179035163486352209484708408778505376952372118350536524234111346330039309
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      722134065102340967928064600490869435131218405052100594547173
      6431840073415189725503
      387132027554692
      6431840073415189725502
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 2446369 [(2, 0, Hex.Nat.PrimeCert.small 17), (2, 0, Hex.Nat.PrimeCert.small 1499)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          3120918381944711
          9489
          1646012
          8767
          47
          [(17, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 5),
           (2, 0, Hex.Nat.PrimeCert.small 3079)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6cf1486065e3b08f4aa2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6cf1486065e3b08f4aa2

/-- Frozen certificate for 110791116136583533937564380397109763311102032558533131010201405510228909261463. -/
theorem Hex.PrimalityCorpus.h0557338764d2c48edcd6 : _root_.Nat.Prime 110791116136583533937564380397109763311102032558533131010201405510228909261463 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  110791116136583533937564380397109763311102032558533131010201405510228909261463
  728906783799389749626992411
  281258809402740766346218
  728906783799389749626992410
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      710402440207
      641669
      1
      641668
      [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 353), (2, 0, Hex.Nat.PrimeCert.small 647)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      312356079881687
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          156178039940843
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              1904610243181
              11955
              11280
              11951
              [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 2297)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h0557338764d2c48edcd6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h0557338764d2c48edcd6

/-- Frozen certificate for 110791116136583533937564380397109763311102032558533131010201405510228909261463. -/
theorem Hex.PrimalityCorpus.ha8ed81fc893a7b511f1a : _root_.Nat.Prime 110791116136583533937564380397109763311102032558533131010201405510228909261463 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  110791116136583533937564380397109763311102032558533131010201405510228909261463
  4456237848498602881763066082069
  8395602913107863
  4456237848498602881763066082068
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      710402440207
      641669
      1
      641668
      [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 353), (2, 0, Hex.Nat.PrimeCert.small 647)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      1807911161406014653
      2743277
      336481
      2743276
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 593), (2, 0, Hex.Nat.PrimeCert.small 691)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha8ed81fc893a7b511f1a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha8ed81fc893a7b511f1a

/-- Frozen certificate for 111421616528645009090760720151991154587959547260781450919672858488668597984739. -/
theorem Hex.PrimalityCorpus.ha46e85257269d9fdfda6 : _root_.Nat.Prime 111421616528645009090760720151991154587959547260781450919672858488668597984739 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  111421616528645009090760720151991154587959547260781450919672858488668597984739
  21129678132243196266140492465
  398654000294637967764
  21129678132243196266140492464
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      979484857339
      22607
      2158
      22606
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 17), (2, 0, Hex.Nat.PrimeCert.small 443)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      6034536862338307
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          143679449103293
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              588850201243
              [(2, 0, Hex.Nat.PrimeCert.small 643), (2, 0, Hex.Nat.PrimeCert.small 34919)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha46e85257269d9fdfda6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha46e85257269d9fdfda6

/-- Frozen certificate for 112021200495291428401882717260580082705178898190458992005156839793852765743121. -/
theorem Hex.PrimalityCorpus.h0ea64d23610bef76aa9d : _root_.Nat.Prime 112021200495291428401882717260580082705178898190458992005156839793852765743121 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  112021200495291428401882717260580082705178898190458992005156839793852765743121
  34590245511720733627049589
  144149749174862851994293436
  34590245511720733627049572
  4
  [(3, 3, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 5303),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      232319978137337583371
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          23231997813733758337
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              109403244677393
              240351
              518
              240350
              [(3, 3, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 79),
               (2, 0, Hex.Nat.PrimeCert.small 257)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h0ea64d23610bef76aa9d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h0ea64d23610bef76aa9d

/-- Frozen certificate for 112964127394513751832284836079133916073103457206988838680219499353528386383539. -/
theorem Hex.PrimalityCorpus.h38d7a1240d1317645f00 : _root_.Nat.Prime 112964127394513751832284836079133916073103457206988838680219499353528386383539 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  112964127394513751832284836079133916073103457206988838680219499353528386383539
  11189877139698405877840919
  244733307652743026659324822
  11189877139698405877840831
  12
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 3),
   (3, 0, Hex.Nat.PrimeCert.small 13),
   (2, 0, Hex.Nat.PrimeCert.small 139),
   (3, 0, Hex.Nat.PrimeCert.small 241),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      5814097262116056659
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          2907048631058028329
          3387025
          442254
          3387024
          [(3, 2, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 19),
           (2, 0, Hex.Nat.PrimeCert.small 11927)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h38d7a1240d1317645f00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h38d7a1240d1317645f00

/-- Frozen certificate for 112964127394513751832284836079133916073103457206988838680219499353528386383539. -/
theorem Hex.PrimalityCorpus.h3ae14be48b2489fcd6c1 : _root_.Nat.Prime 112964127394513751832284836079133916073103457206988838680219499353528386383539 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  112964127394513751832284836079133916073103457206988838680219499353528386383539
  6301775321267417425080303
  39637185386325146325073530
  6301775321267417425080277
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 139),
   (3, 0, Hex.Nat.PrimeCert.small 241),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 1163753501 [(2, 0, Hex.Nat.PrimeCert.small 13), (2, 0, Hex.Nat.PrimeCert.small 25577)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      484151225137
      1391
      109331
      1029
      51
      [(5, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 3), (2, 0, Hex.Nat.PrimeCert.small 31)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h3ae14be48b2489fcd6c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h3ae14be48b2489fcd6c1

/-- Frozen certificate for 113011186749285101721031480705015796590759267578871603296179561051295243917669. -/
theorem Hex.PrimalityCorpus.h0d01216da78781ca8c0a : _root_.Nat.Prime 113011186749285101721031480705015796590759267578871603296179561051295243917669 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  113011186749285101721031480705015796590759267578871603296179561051295243917669
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      3725807290956254177800062003989707127481183818372398895429894535516788999
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          12459143835836618862233605995110075265284420978900618961316117921619
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              2786466378243094716003245135785847639433405134629707508570453
              16178857185592678662715637
              5235650291
              16178857185592678662715636
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  4078181958951314244772393
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock3
                      4130715872137
                      838235
                      8
                      838234
                      [(5, 2, Hex.Nat.PrimeCert.small 2),
                       (2, 0, Hex.Nat.PrimeCert.small 179),
                       (2, 0, Hex.Nat.PrimeCert.small 337)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h0d01216da78781ca8c0a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h0d01216da78781ca8c0a

/-- Frozen certificate for 113446148181243185580215179530906994222475749487322306597772255342782942684307. -/
theorem Hex.PrimalityCorpus.h61d412c977a1c11ffec2 : _root_.Nat.Prime 113446148181243185580215179530906994222475749487322306597772255342782942684307 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  113446148181243185580215179530906994222475749487322306597772255342782942684307
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      58451304641993789048014681359456730999412011553536789
      9387266504454021049
      37086773206670
      9387266504454021048
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          7017987513142724093
          3092857
          390180
          3092856
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 521),
           (2, 0, Hex.Nat.PrimeCert.small 1439)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h61d412c977a1c11ffec2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h61d412c977a1c11ffec2

/-- Frozen certificate for 113502733945595687904638658477297522971062497397830372947167999963995988288739. -/
theorem Hex.PrimalityCorpus.h05a95f7ad17739940cb8 : _root_.Nat.Prime 113502733945595687904638658477297522971062497397830372947167999963995988288739 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  113502733945595687904638658477297522971062497397830372947167999963995988288739
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      1295663728517564529401596521509754605728893146250432329709002077167142169
      191277248885139090409207913
      6654074026641267355
      191277248885139090409207912
      [(3, 2, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          4937936127847
          10829
          75513
          10801
          7
          [(3, 0, Hex.Nat.PrimeCert.small 2), (3, 0, Hex.Nat.PrimeCert.small 3), (2, 0, Hex.Nat.PrimeCert.small 953)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          7898632059341
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              35902872997
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  2991906083
                  [(2, 0, Hex.Nat.PrimeCert.pock 135995731 [(2, 0, Hex.Nat.PrimeCert.small 18353)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h05a95f7ad17739940cb8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h05a95f7ad17739940cb8

/-- Frozen certificate for 113502733945595687904638658477297522971062497397830372947167999963995988288739. -/
theorem Hex.PrimalityCorpus.h4852b42bb92345a5ef84 : _root_.Nat.Prime 113502733945595687904638658477297522971062497397830372947167999963995988288739 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  113502733945595687904638658477297522971062497397830372947167999963995988288739
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      1295663728517564529401596521509754605728893146250432329709002077167142169
      [(3, 2, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          995587219278805882180994412987127589
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              1648323210726499804935421213554847
              5987515986060143
              59
              5987515986060142
              [(3, 0, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3Sieve
                  1856103259820333
                  136879
                  174093
                  136873
                  2
                  [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 18253)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h4852b42bb92345a5ef84' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h4852b42bb92345a5ef84

/-- Frozen certificate for 113865990661783854534550984523895582356510133881835727442007928353482359746619. -/
theorem Hex.PrimalityCorpus.h79d6f5abecd19f0790d4 : _root_.Nat.Prime 113865990661783854534550984523895582356510133881835727442007928353482359746619 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  113865990661783854534550984523895582356510133881835727442007928353482359746619
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      358069153024477529982864731207218812441855766924011721515748202369441382851
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          12230161096966021063335720755569329142699978889080941592303597888807
          116812301381174533904399004435
          471689547
          116812301381174533904399004434
          [(3, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.pock 151438139 [(2, 0, Hex.Nat.PrimeCert.small 17027)]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3
              375930623541957970279
              8426523
              7381845
              8426519
              [(3, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 13),
               (2, 0, Hex.Nat.PrimeCert.small 421),
               (2, 0, Hex.Nat.PrimeCert.small 461)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h79d6f5abecd19f0790d4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h79d6f5abecd19f0790d4

/-- Frozen certificate for 114297596149234585536706465019756632248491740498743850274352447945381278028269. -/
theorem Hex.PrimalityCorpus.h0e78a6704e9e2c67f13f : _root_.Nat.Prime 114297596149234585536706465019756632248491740498743850274352447945381278028269 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  114297596149234585536706465019756632248491740498743850274352447945381278028269
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      892365547484363339357011061532751746951957195847144949
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          20281035170099166803568433216653448794362663541980567
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              7138357689951186421336829132418753191
              [(2,
                0,
                Hex.Nat.PrimeCert.pock3Sieve
                  58660183169949761043116354116351
                  17787140311
                  213771482878
                  17787140262
                  11
                  [(3, 0, Hex.Nat.PrimeCert.small 2),
                   (2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      5856684497
                      [(2,
                        0,
                        Hex.Nat.PrimeCert.pock
                          28157137
                          [(2, 0, Hex.Nat.PrimeCert.small 47), (2, 0, Hex.Nat.PrimeCert.small 1783)])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h0e78a6704e9e2c67f13f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h0e78a6704e9e2c67f13f

/-- Frozen certificate for 114297596149234585536706465019756632248491740498743850274352447945381278028269. -/
theorem Hex.PrimalityCorpus.h688a943053cb686a13e6 : _root_.Nat.Prime 114297596149234585536706465019756632248491740498743850274352447945381278028269 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  114297596149234585536706465019756632248491740498743850274352447945381278028269
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      892365547484363339357011061532751746951957195847144949
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          20281035170099166803568433216653448794362663541980567
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              7138357689951186421336829132418753191
              [(2, 0, Hex.Nat.PrimeCert.small 5),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3Sieve
                  58660183169949761043116354116351
                  17787140311
                  213771482878
                  17787140262
                  11
                  [(3, 0, Hex.Nat.PrimeCert.small 2),
                   (2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      5856684497
                      [(2,
                        0,
                        Hex.Nat.PrimeCert.pock
                          28157137
                          [(2, 0, Hex.Nat.PrimeCert.small 47), (2, 0, Hex.Nat.PrimeCert.small 1783)])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h688a943053cb686a13e6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h688a943053cb686a13e6

/-- Frozen certificate for 114525991912537369361333435480013669243304567704698875322349039524072620854443. -/
theorem Hex.PrimalityCorpus.h8d09b20844c3397e9931 : _root_.Nat.Prime 114525991912537369361333435480013669243304567704698875322349039524072620854443 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  114525991912537369361333435480013669243304567704698875322349039524072620854443
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      119988485377747881131817851036058332047919403721286350687
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          50270854245556280816322734054209
          3541011631
          19617588637
          3541011608
          [(11, 5, Hex.Nat.PrimeCert.small 2),
           (2, 1, Hex.Nat.PrimeCert.small 23),
           (2, 0, Hex.Nat.PrimeCert.small 41),
           (2, 0, Hex.Nat.PrimeCert.small 107),
           (2, 0, Hex.Nat.PrimeCert.small 241)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8d09b20844c3397e9931' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8d09b20844c3397e9931

/-- Frozen certificate for 114815055570146135448086104272446432487325347399055490531903142327789645386089. -/
theorem Hex.PrimalityCorpus.h7618e07864a886243551 : _root_.Nat.Prime 114815055570146135448086104272446432487325347399055490531903142327789645386089 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  114815055570146135448086104272446432487325347399055490531903142327789645386089
  7235100305118309581692553
  168810387277832892576944905
  7235100305118309581692459
  8
  [(7, 2, Hex.Nat.PrimeCert.small 2),
   (3, 0, Hex.Nat.PrimeCert.small 3),
   (2, 0, Hex.Nat.PrimeCert.small 8713),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      88187266967461791023
      38230553
      30927
      38230552
      [(5, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 941), (2, 0, Hex.Nat.PrimeCert.small 20063)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h7618e07864a886243551' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h7618e07864a886243551

/-- Frozen certificate for 115608898780222669886383713727758743794620726579292515642158503226788969215779. -/
theorem Hex.PrimalityCorpus.h9e09acaa473c0ad2d857 : _root_.Nat.Prime 115608898780222669886383713727758743794620726579292515642158503226788969215779 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  115608898780222669886383713727758743794620726579292515642158503226788969215779
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      2048696835936138622094094318367351210768899644924129865989
      1527279755465680880947
      817178044702905
      1527279755465680880946
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          279901685876330530531
          6755473
          2069807
          6755471
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (3, 0, Hex.Nat.PrimeCert.small 7),
           (2, 1, Hex.Nat.PrimeCert.small 19),
           (2, 0, Hex.Nat.PrimeCert.small 1627)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h9e09acaa473c0ad2d857' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h9e09acaa473c0ad2d857

/-- Frozen certificate for 115792089210356248762697446949407573530086143415290314195533631308867097853951. -/
theorem Hex.PrimalityCorpus.h41cbaf47006f7843845c : _root_.Nat.Prime 115792089210356248762697446949407573530086143415290314195533631308867097853951 :=
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

/-- info: 'Hex.PrimalityCorpus.h41cbaf47006f7843845c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h41cbaf47006f7843845c

/-- Frozen certificate for 115792089237316195423570985008687907853269984665640564039457584007908834671663. -/
theorem Hex.PrimalityCorpus.h9435f792c5671caf2d8c : _root_.Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 :=
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

/-- info: 'Hex.PrimalityCorpus.h9435f792c5671caf2d8c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h9435f792c5671caf2d8c
