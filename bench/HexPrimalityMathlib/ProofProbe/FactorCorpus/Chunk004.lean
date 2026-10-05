/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimalityMathlib.Prime

public section

/-! Exact frozen checker equations for factor-policy corpus outputs. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Frozen certificate for 80482677204704043204108631242322921528091640152758109356403156689668620452651. -/
theorem Hex.PrimalityCorpus.h5689933fda6a9820b0c7 : _root_.Nat.Prime 80482677204704043204108631242322921528091640152758109356403156689668620452651 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  80482677204704043204108631242322921528091640152758109356403156689668620452651
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      122714852607491872514226179587125709130938689598635466837868861996611
      18567783189141737831305
      524569731035590264772240
      18567783189141737831191
      27
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (3, 1, Hex.Nat.PrimeCert.small 3),
       (2, 0, Hex.Nat.PrimeCert.small 19),
       (2, 0, Hex.Nat.PrimeCert.small 29),
       (2, 0, Hex.Nat.PrimeCert.small 59),
       (2, 0, Hex.Nat.PrimeCert.small 463),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          39918558220363
          8683
          74372
          8648
          4
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 8191)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h5689933fda6a9820b0c7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h5689933fda6a9820b0c7

/-- Frozen certificate for 80843449576315257651351959171993442842778519838263308394803339986638598072819. -/
theorem Hex.PrimalityCorpus.h960963acb11399edc79f : _root_.Nat.Prime 80843449576315257651351959171993442842778519838263308394803339986638598072819 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  80843449576315257651351959171993442842778519838263308394803339986638598072819
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      17543780538955220185781973012475231346732066998855249
      4956535453821835413
      375114929629710
      4956535453821835412
      [(17, 3, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 1723),
       (2, 0, Hex.Nat.PrimeCert.pock 669937 [(2, 0, Hex.Nat.PrimeCert.small 821)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 261833491 [(2, 0, Hex.Nat.PrimeCert.small 19), (2, 0, Hex.Nat.PrimeCert.small 9007)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h960963acb11399edc79f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h960963acb11399edc79f

/-- Frozen certificate for 80961003145719586361928596187111104047381787971033729872072251569024088564803. -/
theorem Hex.PrimalityCorpus.h699d616554193faf9e26 : _root_.Nat.Prime 80961003145719586361928596187111104047381787971033729872072251569024088564803 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  80961003145719586361928596187111104047381787971033729872072251569024088564803
  40125278416991298547284455
  192496083565097815973264
  40125278416991298547284454
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 701),
   (2, 0, Hex.Nat.PrimeCert.pock 540391 [(2, 0, Hex.Nat.PrimeCert.small 18013)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      605279370760827589
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          6206465800837
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              3518404649
              [(2, 0, Hex.Nat.PrimeCert.small 547), (2, 0, Hex.Nat.PrimeCert.small 3847)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h699d616554193faf9e26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h699d616554193faf9e26

/-- Frozen certificate for 80961003145719586361928596187111104047381787971033729872072251569024088564803. -/
theorem Hex.PrimalityCorpus.he1187cc7ad8dd18c3155 : _root_.Nat.Prime 80961003145719586361928596187111104047381787971033729872072251569024088564803 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  80961003145719586361928596187111104047381787971033729872072251569024088564803
  11832687172620098195479411
  128409178268012339307631138
  11832687172620098195479367
  6
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 701),
   (2, 0, Hex.Nat.PrimeCert.pock 540391 [(2, 0, Hex.Nat.PrimeCert.small 18013)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      23435206682787433
      155651
      67754
      155649
      [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 227), (2, 0, Hex.Nat.PrimeCert.small 229)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he1187cc7ad8dd18c3155' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he1187cc7ad8dd18c3155

/-- Frozen certificate for 81587476923784168387360704970658656065955045116878288504705483251137045879709. -/
theorem Hex.PrimalityCorpus.he7252c6ff541f1c01677 : _root_.Nat.Prime 81587476923784168387360704970658656065955045116878288504705483251137045879709 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  81587476923784168387360704970658656065955045116878288504705483251137045879709
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      9116093397052813189340858882802572793751296026076700171
      434043659685840751623
      29344609700451
      434043659685840751622
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 28837),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          6833530597043539
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              2418092921813
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.pock 829613 [(2, 0, Hex.Nat.PrimeCert.small 29629)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he7252c6ff541f1c01677' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he7252c6ff541f1c01677

/-- Frozen certificate for 81925801005277707330098700777287820558064453374603031788913383271304342292869. -/
theorem Hex.PrimalityCorpus.h50e32f5d78aee74b754a : _root_.Nat.Prime 81925801005277707330098700777287820558064453374603031788913383271304342292869 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  81925801005277707330098700777287820558064453374603031788913383271304342292869
  2249923148231044948011326405
  5477611310165199850164
  2249923148231044948011326404
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 8111),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      84287922916874107537219
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          2006855307544621608029
          44220247
          360508
          44220246
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              13189409
              [(2, 0, Hex.Nat.PrimeCert.small 349), (2, 0, Hex.Nat.PrimeCert.small 1181)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h50e32f5d78aee74b754a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h50e32f5d78aee74b754a

/-- Frozen certificate for 81989474532707580340325483150308108436237147435162162812067359192422527556013. -/
theorem Hex.PrimalityCorpus.hb3c5e5d388ccd7828c8d : _root_.Nat.Prime 81989474532707580340325483150308108436237147435162162812067359192422527556013 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  81989474532707580340325483150308108436237147435162162812067359192422527556013
  363046264355532450659741
  3261819765451100752415060
  363046264355532450659705
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      565976085683
      43965
      104
      43964
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 26029)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      49519471511261
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          25525500779
          2747
          915
          2745
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 1867)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb3c5e5d388ccd7828c8d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb3c5e5d388ccd7828c8d

/-- Frozen certificate for 83184392761400018546867080810405065076687353804054715669034631926871234842017. -/
theorem Hex.PrimalityCorpus.hc8acef85abdb663380e1 : _root_.Nat.Prime 83184392761400018546867080810405065076687353804054715669034631926871234842017 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  83184392761400018546867080810405065076687353804054715669034631926871234842017
  4484637653800950769522239
  65186529299837970727554015
  4484637653800950769522180
  3
  [(5, 4, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 43),
   (2, 0, Hex.Nat.PrimeCert.small 80833),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      227101428989698553
      [(2,
        0,
        Hex.Nat.PrimeCert.pock 746781877 [(2, 0, Hex.Nat.PrimeCert.small 227), (2, 0, Hex.Nat.PrimeCert.small 367)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc8acef85abdb663380e1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc8acef85abdb663380e1

/-- Frozen certificate for 83786281510833410911898311104995401992668392726483564388263618488870466202293. -/
theorem Hex.PrimalityCorpus.h87d0d81560b8718d1401 : _root_.Nat.Prime 83786281510833410911898311104995401992668392726483564388263618488870466202293 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  83786281510833410911898311104995401992668392726483564388263618488870466202293
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      1430385325385528945436722303744656444359495087557051265380903
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          98444356888452454697706004801515485133569
          8018383234078603
          1878701848
          8018383234078602
          [(3, 7, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 5081),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              3935159353
              [(2, 0, Hex.Nat.PrimeCert.small 1249), (2, 0, Hex.Nat.PrimeCert.small 43759)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h87d0d81560b8718d1401' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h87d0d81560b8718d1401

/-- Frozen certificate for 84474499937929686772487031016206111415346806429312420512939506343233531841083. -/
theorem Hex.PrimalityCorpus.h7d5ac9469c0af41bcef2 : _root_.Nat.Prime 84474499937929686772487031016206111415346806429312420512939506343233531841083 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  84474499937929686772487031016206111415346806429312420512939506343233531841083
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      1308766040522060181465042461794756165332958265339065276111
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          1079262216574449233015284734944285364408991
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              101022441963031424221642433
              58871135709
              37640
              58871135708
              [(3, 5, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 5881),
               (2, 0, Hex.Nat.PrimeCert.small 97327)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h7d5ac9469c0af41bcef2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h7d5ac9469c0af41bcef2

/-- Frozen certificate for 84794998026051322066463251094461828259192124468621601690971365091162902519093. -/
theorem Hex.PrimalityCorpus.h2c32eae0a04ee29b2806 : _root_.Nat.Prime 84794998026051322066463251094461828259192124468621601690971365091162902519093 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  84794998026051322066463251094461828259192124468621601690971365091162902519093
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      3742787779803190229161428857080360992836204906617303756046034286451161
      28956196811450187139485555
      8579306759339539365
      28956196811450187139485554
      [(7, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 13933),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          1456365983
          1307
          207
          1306
          [(5, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 937)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          90981135923
          3427
          4092
          3422
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 1667)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h2c32eae0a04ee29b2806' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h2c32eae0a04ee29b2806

/-- Frozen certificate for 85899103234319305557138570768433652272007288874948466938883442674462644488009. -/
theorem Hex.PrimalityCorpus.h8c70f0bf20431e9e2232 : _root_.Nat.Prime 85899103234319305557138570768433652272007288874948466938883442674462644488009 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  85899103234319305557138570768433652272007288874948466938883442674462644488009
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      87703275239282681180750578349064056303990267382661007095397
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          269364216417818062798836575227539156363043
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              293976518499645372691297373971151939
              231266241195
              3875888871761
              231266241127
              13
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 677),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  143825867
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      71912933
                      [(2, 0, Hex.Nat.PrimeCert.small 31), (2, 0, Hex.Nat.PrimeCert.small 6373)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8c70f0bf20431e9e2232' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8c70f0bf20431e9e2232

/-- Frozen certificate for 86301243619780895624700131705272144637929012071040188499860416456059868385293. -/
theorem Hex.PrimalityCorpus.he13279283c56561a0f95 : _root_.Nat.Prime 86301243619780895624700131705272144637929012071040188499860416456059868385293 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  86301243619780895624700131705272144637929012071040188499860416456059868385293
  125333436239944556411684942691
  8979603699261371279
  125333436239944556411684942690
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 12451),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      942213402059
      8705
      15054
      8698
      2
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 2797)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      1477241304569
      91803
      35
      91802
      [(3, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 18077)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he13279283c56561a0f95' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he13279283c56561a0f95

/-- Frozen certificate for 86622917615659894600738539008939784117541826635978832181667600928016952157377. -/
theorem Hex.PrimalityCorpus.hd614d0e190b7b35ec3c3 : _root_.Nat.Prime 86622917615659894600738539008939784117541826635978832181667600928016952157377 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  86622917615659894600738539008939784117541826635978832181667600928016952157377
  20503235035161478925348941113
  363845969894875579719
  20503235035161478925348941112
  [(5, 5, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 2591),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 35688710881 [(2, 0, Hex.Nat.PrimeCert.small 1693), (2, 0, Hex.Nat.PrimeCert.small 14639)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      1843590126229
      323327
      4
      323326
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 115067 [(2, 0, Hex.Nat.PrimeCert.small 8219)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd614d0e190b7b35ec3c3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd614d0e190b7b35ec3c3

/-- Frozen certificate for 86926538394070668125386184502283006425466516212731784653976196792929912630959. -/
theorem Hex.PrimalityCorpus.hf4340972d3c086c279e8 : _root_.Nat.Prime 86926538394070668125386184502283006425466516212731784653976196792929912630959 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  86926538394070668125386184502283006425466516212731784653976196792929912630959
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      15153008844297055448203196901830288332723769191768725275621457918164203
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          9509375583686857395345746525406983665678661320013
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              463608886578992990724896231312357656141
              [(2,
                0,
                Hex.Nat.PrimeCert.pock3
                  526143313725517139858491
                  67011433
                  629083
                  67011432
                  [(2, 0, Hex.Nat.PrimeCert.small 2),
                   (2, 0, Hex.Nat.PrimeCert.small 97),
                   (2, 0, Hex.Nat.PrimeCert.small 983),
                   (2, 0, Hex.Nat.PrimeCert.small 3391)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hf4340972d3c086c279e8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hf4340972d3c086c279e8

/-- Frozen certificate for 86969621308297449247257935325388126206731377556124621529891044037043137440311. -/
theorem Hex.PrimalityCorpus.h264fd8fa3087f6210b4e : _root_.Nat.Prime 86969621308297449247257935325388126206731377556124621529891044037043137440311 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  86969621308297449247257935325388126206731377556124621529891044037043137440311
  542049138601358994007771
  341334666715058366741438547
  542049138601358994005252
  30
  [(7, 0, Hex.Nat.PrimeCert.small 2),
   (3, 0, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 29),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      702840161
      7185
      5
      7184
      [(3, 4, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 251)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      55376311509709
      136485
      489
      136484
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 59471)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h264fd8fa3087f6210b4e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h264fd8fa3087f6210b4e

/-- Frozen certificate for 86969621308297449247257935325388126206731377556124621529891044037043137440311. -/
theorem Hex.PrimalityCorpus.hd1d62332d3eae4258586 : _root_.Nat.Prime 86969621308297449247257935325388126206731377556124621529891044037043137440311 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  86969621308297449247257935325388126206731377556124621529891044037043137440311
  1881586953576625586374148621031145
  25843335840
  1881586953576625586374148621031144
  [(7, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      648581430609465599515742791841507
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          39414138548496216031
          1571353
          2885185
          1571345
          [(3, 0, Hex.Nat.PrimeCert.small 2),
           (2, 1, Hex.Nat.PrimeCert.small 3),
           (2, 0, Hex.Nat.PrimeCert.small 5),
           (2, 0, Hex.Nat.PrimeCert.small 71),
           (2, 0, Hex.Nat.PrimeCert.small 409)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd1d62332d3eae4258586' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd1d62332d3eae4258586

/-- Frozen certificate for 87019311416820045173781745449934743448990938192606957145189107221012577291959. -/
theorem Hex.PrimalityCorpus.h2030bc97f19035947901 : _root_.Nat.Prime 87019311416820045173781745449934743448990938192606957145189107221012577291959 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  87019311416820045173781745449934743448990938192606957145189107221012577291959
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      2118026125094980603601079084527389247337812733774361007
      157288983149544507233
      11209734187380
      157288983149544507232
      [(5, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          153682000662043803751
          [(2, 3, Hex.Nat.PrimeCert.small 5),
           (2, 0, Hex.Nat.PrimeCert.small 3251),
           (2, 0, Hex.Nat.PrimeCert.small 11317)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h2030bc97f19035947901' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h2030bc97f19035947901

/-- Frozen certificate for 87019311416820045173781745449934743448990938192606957145189107221012577291959. -/
theorem Hex.PrimalityCorpus.h9bac2d850765256de2a3 : _root_.Nat.Prime 87019311416820045173781745449934743448990938192606957145189107221012577291959 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  87019311416820045173781745449934743448990938192606957145189107221012577291959
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      2118026125094980603601079084527389247337812733774361007
      14384294273482544689
      5943952374116073
      14384294273482544688
      [(5, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 389),
       (2, 0, Hex.Nat.PrimeCert.small 659),
       (2, 0, Hex.Nat.PrimeCert.small 971),
       (2, 0, Hex.Nat.PrimeCert.small 7691),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 3486149 [(2, 0, Hex.Nat.PrimeCert.small 41), (2, 0, Hex.Nat.PrimeCert.small 733)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h9bac2d850765256de2a3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h9bac2d850765256de2a3

/-- Frozen certificate for 87383914982556015748280158083251544316551232064253227583053492950795294646909. -/
theorem Hex.PrimalityCorpus.h2007a08e0a7c9d0dc7ce : _root_.Nat.Prime 87383914982556015748280158083251544316551232064253227583053492950795294646909 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  87383914982556015748280158083251544316551232064253227583053492950795294646909
  1274321437996419376216633331
  63947154548370413883397
  1274321437996419376216633330
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 661),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      54754103333
      78829
      15
      78828
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 10357)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      5709683261957
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          1427420815489
          [(2, 0, Hex.Nat.PrimeCert.small 181), (2, 0, Hex.Nat.PrimeCert.small 96419)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h2007a08e0a7c9d0dc7ce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h2007a08e0a7c9d0dc7ce

/-- Frozen certificate for 87689926499306650811258439800389455890894050066866057858369890520837467505341. -/
theorem Hex.PrimalityCorpus.hba9d2699c8d5ceda2fcf : _root_.Nat.Prime 87689926499306650811258439800389455890894050066866057858369890520837467505341 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  87689926499306650811258439800389455890894050066866057858369890520837467505341
  36070599299339039550433897853059413
  47542319
  36070599299339039550433897853059412
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      68625383053539049
      5016101
      3827
      5016100
      [(7, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 263), (2, 0, Hex.Nat.PrimeCert.small 1423)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      110630505975523939
      [(2, 1, Hex.Nat.PrimeCert.small 19),
       (2, 0, Hex.Nat.PrimeCert.pock 115699631 [(2, 0, Hex.Nat.PrimeCert.small 50969)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hba9d2699c8d5ceda2fcf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hba9d2699c8d5ceda2fcf

/-- Frozen certificate for 87826951236840884608861417209733106106599707795233227499494507673950567713789. -/
theorem Hex.PrimalityCorpus.hb0c8171ce8c6c20d78b7 : _root_.Nat.Prime 87826951236840884608861417209733106106599707795233227499494507673950567713789 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  87826951236840884608861417209733106106599707795233227499494507673950567713789
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      148808816665769139838563054967175936301743840139832817893501
      77926680487672937931343
      42612489490322
      77926680487672937931342
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 32869),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          317822322876439853
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              176961204274187
              76917
              8930
              76916
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 157),
               (2, 0, Hex.Nat.PrimeCert.small 317)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb0c8171ce8c6c20d78b7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb0c8171ce8c6c20d78b7

/-- Frozen certificate for 87888589122415588729821248021948598226624561248020544301558504430844100062631. -/
theorem Hex.PrimalityCorpus.ha3ed33647e000d859e45 : _root_.Nat.Prime 87888589122415588729821248021948598226624561248020544301558504430844100062631 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  87888589122415588729821248021948598226624561248020544301558504430844100062631
  252778548575040770806104252347
  1239612036895324237
  252778548575040770806104252346
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 40387),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      9082798169
      547
      8958
      477
      10
      [(3, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 89)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      256635719194247
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          18331122799589
          203727
          653
          203726
          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 29599)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha3ed33647e000d859e45' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha3ed33647e000d859e45

/-- Frozen certificate for 88858350928396434919244528656835376624799401512286186231417506165107172543003. -/
theorem Hex.PrimalityCorpus.hdbda159a60cc707ce598 : _root_.Nat.Prime 88858350928396434919244528656835376624799401512286186231417506165107172543003 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  88858350928396434919244528656835376624799401512286186231417506165107172543003
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      1070440024619737551516656245232958711287156868873128351
      2546816946250840149
      167947025974999337
      2546816946250840148
      [(7, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 15349),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          58152706377763
          [(2, 0, Hex.Nat.PrimeCert.small 17),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              2794879
              [(2, 0, Hex.Nat.PrimeCert.small 73), (2, 0, Hex.Nat.PrimeCert.small 709)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hdbda159a60cc707ce598' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hdbda159a60cc707ce598

/-- Frozen certificate for 89064403956642397898854115727891558672937411444484005520070810340651673404409. -/
theorem Hex.PrimalityCorpus.h79a5689ff34362245770 : _root_.Nat.Prime 89064403956642397898854115727891558672937411444484005520070810340651673404409 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  89064403956642397898854115727891558672937411444484005520070810340651673404409
  2870892560832116893722282694207
  238008967884373
  2870892560832116893722282694206
  [(3, 2, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      150427144119683
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          1274806306099
          7397
          7475
          7392
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 4, Hex.Nat.PrimeCert.small 3), (2, 0, Hex.Nat.PrimeCert.small 19)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      11366433806565083
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          4250723188693
          142511
          158
          142510
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 43),
           (2, 0, Hex.Nat.PrimeCert.small 673)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h79a5689ff34362245770' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h79a5689ff34362245770

/-- Frozen certificate for 89064403956642397898854115727891558672937411444484005520070810340651673404409. -/
theorem Hex.PrimalityCorpus.hf6bbc3a1f95e1cd9ab2d : _root_.Nat.Prime 89064403956642397898854115727891558672937411444484005520070810340651673404409 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  89064403956642397898854115727891558672937411444484005520070810340651673404409
  34897906140795239696889859354935519
  55877642
  34897906140795239696889859354935518
  [(3, 2, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      11366433806565083
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          4250723188693
          142511
          158
          142510
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 43),
           (2, 0, Hex.Nat.PrimeCert.small 673)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      310458698936059987
      [(2, 0, Hex.Nat.PrimeCert.small 157),
       (2, 0, Hex.Nat.PrimeCert.small 199),
       (2, 0, Hex.Nat.PrimeCert.small 31859)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hf6bbc3a1f95e1cd9ab2d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hf6bbc3a1f95e1cd9ab2d

/-- Frozen certificate for 89176217324807231002097476798935842404708374457614395943094244220992859754799. -/
theorem Hex.PrimalityCorpus.he058612a9279a439a18b : _root_.Nat.Prime 89176217324807231002097476798935842404708374457614395943094244220992859754799 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  89176217324807231002097476798935842404708374457614395943094244220992859754799
  1904882597816368519779046141
  22884426834449683569147
  1904882597816368519779046140
  [(13, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      697926212929440093057059207
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          20099828169467186299
          [(2, 0, Hex.Nat.PrimeCert.small 41),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3
              657213463
              291
              438
              284
              [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 433)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he058612a9279a439a18b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he058612a9279a439a18b

/-- Frozen certificate for 89950742662998192670298739771337392707051811711133837146337028515268566548107. -/
theorem Hex.PrimalityCorpus.h2ded37e361451fd6ac31 : _root_.Nat.Prime 89950742662998192670298739771337392707051811711133837146337028515268566548107 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  89950742662998192670298739771337392707051811711133837146337028515268566548107
  46904494303904467988988319
  1696440794850555659985918
  46904494303904467988988318
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock3 876929 195 26 194 [(3, 6, Hex.Nat.PrimeCert.small 2)]),
   (2, 0, Hex.Nat.PrimeCert.pock 1910729 [(2, 0, Hex.Nat.PrimeCert.pock 238841 [(2, 0, Hex.Nat.PrimeCert.small 853)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      48587494208699
      38497
      34893
      38493
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 79), (2, 0, Hex.Nat.PrimeCert.small 167)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h2ded37e361451fd6ac31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h2ded37e361451fd6ac31

/-- Frozen certificate for 90007147899313114943224964605046492498337758394941686691128909278288943334279. -/
theorem Hex.PrimalityCorpus.h9e4d53bc122346fc7eef : _root_.Nat.Prime 90007147899313114943224964605046492498337758394941686691128909278288943334279 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  90007147899313114943224964605046492498337758394941686691128909278288943334279
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      62215218849539921286469445124546112925091021388017284287021
      86030424996325949629
      9736339756536816914
      86030424996325949628
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          14131083647476899863
          1602365
          5266254
          1602351
          3
          [(5, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 131),
           (2, 0, Hex.Nat.PrimeCert.small 4421)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h9e4d53bc122346fc7eef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h9e4d53bc122346fc7eef

/-- Frozen certificate for 90691595592787852810140289775731730665175303316941370673811022831408291455113. -/
theorem Hex.PrimalityCorpus.hd4ace4d0dc39e64d8dd3 : _root_.Nat.Prime 90691595592787852810140289775731730665175303316941370673811022831408291455113 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  90691595592787852810140289775731730665175303316941370673811022831408291455113
  17161056360243219727597561
  161643995672010779026724423
  17161056360243219727597523
  7
  [(5, 2, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 101),
   (2, 0, Hex.Nat.PrimeCert.small 191),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      108528551570835128587
      701611
      1805756
      701600
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 7),
       (2, 0, Hex.Nat.PrimeCert.small 17),
       (2, 0, Hex.Nat.PrimeCert.small 31),
       (2, 0, Hex.Nat.PrimeCert.small 743)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd4ace4d0dc39e64d8dd3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd4ace4d0dc39e64d8dd3

/-- Frozen certificate for 90950516911090086589593000756036933106440314083431459504283779315570811913357. -/
theorem Hex.PrimalityCorpus.hc51da25830b7b9ff3a25 : _root_.Nat.Prime 90950516911090086589593000756036933106440314083431459504283779315570811913357 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  90950516911090086589593000756036933106440314083431459504283779315570811913357
  41884550149267753871761233
  92471804790716632208627357
  41884550149267753871761224
  3
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 37),
   (2, 0, Hex.Nat.PrimeCert.small 3511),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      42676655407240577033
      [(2, 0, Hex.Nat.PrimeCert.small 1607),
       (2, 0, Hex.Nat.PrimeCert.small 6043),
       (2, 0, Hex.Nat.PrimeCert.small 9677)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc51da25830b7b9ff3a25' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc51da25830b7b9ff3a25

/-- Frozen certificate for 91987682788781540599290852057129746353469485030059681676942299999617386556543. -/
theorem Hex.PrimalityCorpus.hda2b3e9adda0a57493c0 : _root_.Nat.Prime 91987682788781540599290852057129746353469485030059681676942299999617386556543 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  91987682788781540599290852057129746353469485030059681676942299999617386556543
  96903930695633695467716719
  1611132568177090447925530
  96903930695633695467716718
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      84480058821805719274149529
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          2049615313651823
          [(2, 0, Hex.Nat.PrimeCert.small 41),
           (2, 0, Hex.Nat.PrimeCert.small 419),
           (2, 0, Hex.Nat.PrimeCert.small 4523)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hda2b3e9adda0a57493c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hda2b3e9adda0a57493c0

/-- Frozen certificate for 92647743055652287049611300650097786233113688366843917335995107141292863066249. -/
theorem Hex.PrimalityCorpus.hf23ee6f18de2c3ad043e : _root_.Nat.Prime 92647743055652287049611300650097786233113688366843917335995107141292863066249 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  92647743055652287049611300650097786233113688366843917335995107141292863066249
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      26387615273166357134156293451124048622443396733948199
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          356132170003014199555585344727876108444385533
          106316222913167353
          33672038207
          106316222913167352
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.pock 69034571 [(2, 0, Hex.Nat.PrimeCert.small 15307)]),
           (2, 0, Hex.Nat.PrimeCert.pock 263347549 [(2, 0, Hex.Nat.PrimeCert.small 17431)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hf23ee6f18de2c3ad043e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hf23ee6f18de2c3ad043e

/-- Frozen certificate for 92992595365191951391095037603354344648737012165018776834793998479632250225163. -/
theorem Hex.PrimalityCorpus.hcba5d6933cb512f1ecec : _root_.Nat.Prime 92992595365191951391095037603354344648737012165018776834793998479632250225163 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  92992595365191951391095037603354344648737012165018776834793998479632250225163
  22672639348935541440530653
  22815342444445499936500972
  22672639348935541440530648
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      22571774094433329470147033
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          995612046543383
          57257
          28512
          57255
          [(5, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 66067)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hcba5d6933cb512f1ecec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hcba5d6933cb512f1ecec

/-- Frozen certificate for 93194143571292597530547048770795003285127074325668230694132683676800224969713. -/
theorem Hex.PrimalityCorpus.h373b520bbfb6f2a5c814 : _root_.Nat.Prime 93194143571292597530547048770795003285127074325668230694132683676800224969713 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  93194143571292597530547048770795003285127074325668230694132683676800224969713
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      1300374333741573764654014155092547953988229395099584453341423653077
      20309936285125607782481
      2101773516369231555483
      20309936285125607782480
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 2801),
       (2, 0, Hex.Nat.PrimeCert.small 12203),
       (2, 0, Hex.Nat.PrimeCert.pock 2634991 [(2, 0, Hex.Nat.PrimeCert.small 87833)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 48821081 [(2, 2, Hex.Nat.PrimeCert.small 11), (2, 0, Hex.Nat.PrimeCert.small 131)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h373b520bbfb6f2a5c814' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h373b520bbfb6f2a5c814

/-- Frozen certificate for 93253399202574478794729196614654727049121621393849256673012637673042321322983. -/
theorem Hex.PrimalityCorpus.h58cf119d88ca4787fb29 : _root_.Nat.Prime 93253399202574478794729196614654727049121621393849256673012637673042321322983 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  93253399202574478794729196614654727049121621393849256673012637673042321322983
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      162962612064515951046119266135165310673393974873827422633611605089215189
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          157605902645403961212431156004871730303827486270466797132666534901
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              784204393654140818385532921322413980018881099
              [(2, 0, Hex.Nat.PrimeCert.small 89),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3
                  1276556727399668831419
                  179433267
                  6768
                  179433266
                  [(2, 0, Hex.Nat.PrimeCert.small 2),
                   (2, 0, Hex.Nat.PrimeCert.small 2131),
                   (2, 0, Hex.Nat.PrimeCert.small 72053)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h58cf119d88ca4787fb29' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h58cf119d88ca4787fb29

/-- Frozen certificate for 93272587303324044806576925703255461796450007921361762392047201056986558703757. -/
theorem Hex.PrimalityCorpus.h21459bcada3846b7dcd0 : _root_.Nat.Prime 93272587303324044806576925703255461796450007921361762392047201056986558703757 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  93272587303324044806576925703255461796450007921361762392047201056986558703757
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      558042243056884031465856005162727706251287790051702540403
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          80158910395882250891885026439578269173148754169
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              750607820771989015018775062172993006715379
              75988248535917
              8894701395768
              75988248535916
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 15581),
               (2, 0, Hex.Nat.PrimeCert.pock3Sieve 6591747073 389 3143 355 3 [(5, 9, Hex.Nat.PrimeCert.small 2)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h21459bcada3846b7dcd0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h21459bcada3846b7dcd0

/-- Frozen certificate for 93279644753710447518935214326539202885022790171543666069887108194825580715313. -/
theorem Hex.PrimalityCorpus.hdd921ba846a5e7a7ca96 : _root_.Nat.Prime 93279644753710447518935214326539202885022790171543666069887108194825580715313 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  93279644753710447518935214326539202885022790171543666069887108194825580715313
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      2724955766599359995344425764846741966139236478623148831045107
      3840627782794055706757
      299378049492091554
      3840627782794055706756
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          1066656926050788818621
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              7618978043219920133
              3476231
              269119
              3476230
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 53),
               (2, 0, Hex.Nat.PrimeCert.small 17747)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hdd921ba846a5e7a7ca96' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hdd921ba846a5e7a7ca96

/-- Frozen certificate for 94342660240778615479006404881295798177544947600574498087817747819513042075663. -/
theorem Hex.PrimalityCorpus.hbc2224c601449827eb66 : _root_.Nat.Prime 94342660240778615479006404881295798177544947600574498087817747819513042075663 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  94342660240778615479006404881295798177544947600574498087817747819513042075663
  3704287905479240930449911
  57107247115732047719943899
  3704287905479240930449849
  2
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 151),
   (2, 0, Hex.Nat.PrimeCert.small 8941),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      10643890811608934647
      [(2, 0, Hex.Nat.PrimeCert.small 13),
       (2, 0, Hex.Nat.PrimeCert.pock3Sieve 607634177 451 4635 407 10 [(3, 7, Hex.Nat.PrimeCert.small 2)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hbc2224c601449827eb66' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hbc2224c601449827eb66

/-- Frozen certificate for 95467528800959142223828529514053384696852149628690073420113032106226377345071. -/
theorem Hex.PrimalityCorpus.h9951fd4765b8a9e82f45 : _root_.Nat.Prime 95467528800959142223828529514053384696852149628690073420113032106226377345071 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  95467528800959142223828529514053384696852149628690073420113032106226377345071
  9430887279349903671746492007939
  713978947783452
  9430887279349903671746492007938
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      4088275400678100221213043441677
      6019805053
      136292016234
      6019804962
      20
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 29179),
       (2, 0, Hex.Nat.PrimeCert.small 33181)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h9951fd4765b8a9e82f45' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h9951fd4765b8a9e82f45

/-- Frozen certificate for 96116808558096091363812243184129511093100431636498585659974288419803642649957. -/
theorem Hex.PrimalityCorpus.h03c8ed71bbbafcb1acbb : _root_.Nat.Prime 96116808558096091363812243184129511093100431636498585659974288419803642649957 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  96116808558096091363812243184129511093100431636498585659974288419803642649957
  704624290775444611829122019
  327865223880881676950793
  704624290775444611829122018
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 71),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 785408249 [(2, 0, Hex.Nat.PrimeCert.small 107), (2, 0, Hex.Nat.PrimeCert.small 12923)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1716418543430933
      [(2, 0, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.pock 22597717 [(2, 0, Hex.Nat.PrimeCert.small 35531)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h03c8ed71bbbafcb1acbb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h03c8ed71bbbafcb1acbb

/-- Frozen certificate for 96116808558096091363812243184129511093100431636498585659974288419803642649957. -/
theorem Hex.PrimalityCorpus.he390ace20288137f30b2 : _root_.Nat.Prime 96116808558096091363812243184129511093100431636498585659974288419803642649957 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  96116808558096091363812243184129511093100431636498585659974288419803642649957
  109006700711713787974114775
  12767697875411784390230893
  109006700711713787974114774
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      15337987632542621026969591
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          173083326512009
          479881
          252
          479880
          [(3, 2, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 53),
           (2, 0, Hex.Nat.PrimeCert.small 1381)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he390ace20288137f30b2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he390ace20288137f30b2

/-- Frozen certificate for 96232483504155280409789386540717702968984693251455546083077388720210972348941. -/
theorem Hex.PrimalityCorpus.h2bffdeca28c742159b63 : _root_.Nat.Prime 96232483504155280409789386540717702968984693251455546083077388720210972348941 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  96232483504155280409789386540717702968984693251455546083077388720210972348941
  383275195911628451282877
  255294525633796361294531960
  383275195911628451280212
  19
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 43),
   (2, 0, Hex.Nat.PrimeCert.small 7349),
   (2, 0, Hex.Nat.PrimeCert.small 52807),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      41134564507139
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          80028335617
          16165
          422
          16164
          [(5, 8, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 19)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h2bffdeca28c742159b63' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h2bffdeca28c742159b63

/-- Frozen certificate for 96232483504155280409789386540717702968984693251455546083077388720210972348941. -/
theorem Hex.PrimalityCorpus.hd694de1deb644c5619bc : _root_.Nat.Prime 96232483504155280409789386540717702968984693251455546083077388720210972348941 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  96232483504155280409789386540717702968984693251455546083077388720210972348941
  4877425784203572869768596961
  3360337681329886624518
  4877425784203572869768596960
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      946007102016780472311537971
      645228257
      1866902938
      645228245
      3
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 19),
       (2, 0, Hex.Nat.PrimeCert.small 23),
       (2, 0, Hex.Nat.PrimeCert.small 173),
       (2, 0, Hex.Nat.PrimeCert.small 3329)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd694de1deb644c5619bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd694de1deb644c5619bc

/-- Frozen certificate for 97007223172022731947686451073011847533803552296898264597975022489118653051293. -/
theorem Hex.PrimalityCorpus.h886bcab3b61df56ce8fa : _root_.Nat.Prime 97007223172022731947686451073011847533803552296898264597975022489118653051293 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  97007223172022731947686451073011847533803552296898264597975022489118653051293
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      1121850686963529105690755429838875004166770003743906718075848557746499
      2780531739539772644681917
      222093982982672834429
      2780531739539772644681916
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 1557740677 [(2, 0, Hex.Nat.PrimeCert.small 61493)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          510104293021117
          9727
          607854
          9473
          24
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 1, Hex.Nat.PrimeCert.small 3),
           (2, 0, Hex.Nat.PrimeCert.small 569)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h886bcab3b61df56ce8fa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h886bcab3b61df56ce8fa

/-- Frozen certificate for 97451106647179920232409441801460156403746554218978821421241782503855236206483. -/
theorem Hex.PrimalityCorpus.hab3b20629c969a1f3bf5 : _root_.Nat.Prime 97451106647179920232409441801460156403746554218978821421241782503855236206483 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  97451106647179920232409441801460156403746554218978821421241782503855236206483
  159777711402604257425971081
  950919129747393730846328
  159777711402604257425971080
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 89),
   (2, 0, Hex.Nat.PrimeCert.small 863),
   (2, 0, Hex.Nat.PrimeCert.small 16691),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      88286325660407117
      431329
      300346
      431326
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 11), (2, 0, Hex.Nat.PrimeCert.small 8713)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hab3b20629c969a1f3bf5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hab3b20629c969a1f3bf5

/-- Frozen certificate for 97626265422364998117480351306826736582888202597360525202330147834107645431669. -/
theorem Hex.PrimalityCorpus.heb9769db92edfe402a4b : _root_.Nat.Prime 97626265422364998117480351306826736582888202597360525202330147834107645431669 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  97626265422364998117480351306826736582888202597360525202330147834107645431669
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      250610890744465877621469790723678313091273474029235519705161855222687
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          818521712947584689337007285841865894563145229096746014909
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              131220296007071292683334549819687201699629
              5609436536079
              636358806783872
              5609436535625
              50
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3Sieve
                  2538484336517
                  7039
                  18495
                  7028
                  2
                  [(2, 1, Hex.Nat.PrimeCert.small 2),
                   (2, 0, Hex.Nat.PrimeCert.small 19),
                   (2, 0, Hex.Nat.PrimeCert.small 109)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.heb9769db92edfe402a4b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.heb9769db92edfe402a4b

/-- Frozen certificate for 97792237598948721043797176559640854474896630974949825147196820666795464071747. -/
theorem Hex.PrimalityCorpus.ha7acdfa5e466c81a8c7c : _root_.Nat.Prime 97792237598948721043797176559640854474896630974949825147196820666795464071747 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  97792237598948721043797176559640854474896630974949825147196820666795464071747
  47326030061914861616803667
  39315924658466770228490964
  47326030061914861616803663
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      17632867786430143245198667
      91964519
      1474492936
      91964454
      12
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 2713), (2, 0, Hex.Nat.PrimeCert.small 14251)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha7acdfa5e466c81a8c7c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha7acdfa5e466c81a8c7c

/-- Frozen certificate for 97986517261700952869180856508993695497592897528926726495238648865243215429899. -/
theorem Hex.PrimalityCorpus.he79bb4538bdcf1ead034 : _root_.Nat.Prime 97986517261700952869180856508993695497592897528926726495238648865243215429899 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  97986517261700952869180856508993695497592897528926726495238648865243215429899
  193464072765235781940404379
  951803865495341661143387
  193464072765235781940404378
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 4523),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      25080595708248302843633
      [(2, 1, Hex.Nat.PrimeCert.small 11),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          71607808619
          663
          11480
          589
          6
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 883)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he79bb4538bdcf1ead034' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he79bb4538bdcf1ead034

/-- Frozen certificate for 98423300762798232456208262562185833212649263989899937264064917781586512244343. -/
theorem Hex.PrimalityCorpus.hc17e7cbf21459855064c : _root_.Nat.Prime 98423300762798232456208262562185833212649263989899937264064917781586512244343 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  98423300762798232456208262562185833212649263989899937264064917781586512244343
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      2590714839215889997851865283930326061761110493648942764181185613
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          279897517234231651817908583187913570007
          2051242249703
          13499302673224
          2051242249676
          4
          [(5, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 2467),
           (2, 0, Hex.Nat.PrimeCert.small 7103),
           (2, 0, Hex.Nat.PrimeCert.small 91873)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc17e7cbf21459855064c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc17e7cbf21459855064c

/-- Frozen certificate for 98526207931144383944170320196036284039935116430533247089966384720207488376867. -/
theorem Hex.PrimalityCorpus.h703767ae58e5645ed931 : _root_.Nat.Prime 98526207931144383944170320196036284039935116430533247089966384720207488376867 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  98526207931144383944170320196036284039935116430533247089966384720207488376867
  9738831449521865948572779
  271136014534833399167633325
  9738831449521865948572667
  15
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 424519 [(2, 0, Hex.Nat.PrimeCert.small 70753)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      15875965774379958833
      [(2, 0, Hex.Nat.PrimeCert.small 283),
       (2, 0, Hex.Nat.PrimeCert.small 7639),
       (2, 0, Hex.Nat.PrimeCert.small 20747)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h703767ae58e5645ed931' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h703767ae58e5645ed931
