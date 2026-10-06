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

/-- Frozen certificate for 19853911353100032846252747859264339251960730424013895139980672999987203865985349418183023266855109542693189923882549. -/
theorem Hex.PrimalityCorpus.h955b220ed5e4be0ecb46 : _root_.Nat.Prime 19853911353100032846252747859264339251960730424013895139980672999987203865985349418183023266855109542693189923882549 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  19853911353100032846252747859264339251960730424013895139980672999987203865985349418183023266855109542693189923882549
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      30754483250636479609695673029552872351161304532521522390685142361325590330939854411540880243769877511
      19308396971423420930148506070325848273
      32922636960783645471193013
      19308396971423420930148506070325848272
      [(13, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          1356156330238421
          5186549
          39
          5186548
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 239),
           (2, 0, Hex.Nat.PrimeCert.small 4327)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          7968052035680954711171
          245550185
          216475
          245550184
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              67830701
              [(2, 0, Hex.Nat.PrimeCert.small 109), (2, 0, Hex.Nat.PrimeCert.small 127)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h955b220ed5e4be0ecb46' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h955b220ed5e4be0ecb46

/-- Frozen certificate for 20219326970734471886145502627628838977378137876409052129607950040093175399065389888786242903594474759684348571651731. -/
theorem Hex.PrimalityCorpus.h2c6f2059c5f26eeb193c : _root_.Nat.Prime 20219326970734471886145502627628838977378137876409052129607950040093175399065389888786242903594474759684348571651731 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  20219326970734471886145502627628838977378137876409052129607950040093175399065389888786242903594474759684348571651731
  105318430550250111905709937389334591981
  709897130999510537034567266049274139569
  105318430550250111905709937389334591954
  5
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 11),
   (2, 0, Hex.Nat.PrimeCert.small 43),
   (2, 0, Hex.Nat.PrimeCert.small 5647),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      345088299161
      [(2, 0, Hex.Nat.PrimeCert.pock 784291589 [(2, 0, Hex.Nat.PrimeCert.small 54907)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      64733856568440738919
      4927585
      1004819
      4927584
      [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 353), (2, 0, Hex.Nat.PrimeCert.small 8039)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h2c6f2059c5f26eeb193c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h2c6f2059c5f26eeb193c

/-- Frozen certificate for 20317673917732167336911233292416131151326465057002670936959359475960410979620778209446316512812891908123089642228451. -/
theorem Hex.PrimalityCorpus.hc11cde2742da44350c27 : _root_.Nat.Prime 20317673917732167336911233292416131151326465057002670936959359475960410979620778209446316512812891908123089642228451 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  20317673917732167336911233292416131151326465057002670936959359475960410979620778209446316512812891908123089642228451
  309210367452054817320954783479512018955835
  137787234289668496416043991589660
  309210367452054817320954783479512018955834
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 11779),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      9236925289869293
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          375423723373
          3761
          98
          3760
          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 10939)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1247819175580850124533
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          266856111116520557
          151283
          9522460
          151031
          50
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 101),
           (2, 0, Hex.Nat.PrimeCert.small 293)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc11cde2742da44350c27' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc11cde2742da44350c27

/-- Frozen certificate for 20424376462841195254704014924457181701823943493435998333143304909444365240286226377337625909406380455081894862688551. -/
theorem Hex.PrimalityCorpus.h5bbe19bdf4ad4110830a : _root_.Nat.Prime 20424376462841195254704014924457181701823943493435998333143304909444365240286226377337625909406380455081894862688551 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  20424376462841195254704014924457181701823943493435998333143304909444365240286226377337625909406380455081894862688551
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      278352687395165779591917775499658365484160781107297124936166770069974626022632691
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          121305812482340964894688553516809804658302028079869860859237
          242747399893605861905
          2078238615515832588
          242747399893605861904
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 13487),
           (2,
            0,
            Hex.Nat.PrimeCert.pock 337901 [(2, 0, Hex.Nat.PrimeCert.small 31), (2, 0, Hex.Nat.PrimeCert.small 109)]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              9371589923
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  4685794961
                  [(2, 0, Hex.Nat.PrimeCert.small 173), (2, 0, Hex.Nat.PrimeCert.small 4397)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h5bbe19bdf4ad4110830a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h5bbe19bdf4ad4110830a

/-- Frozen certificate for 20435220525474711789016147186368793610673008889769983972727462013878251021900102031122352488004382430769150830337247. -/
theorem Hex.PrimalityCorpus.h4ea70761e3d572bd9299 : _root_.Nat.Prime 20435220525474711789016147186368793610673008889769983972727462013878251021900102031122352488004382430769150830337247 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  20435220525474711789016147186368793610673008889769983972727462013878251021900102031122352488004382430769150830337247
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      374487149869481489409436012671391147910357133285949100879394696704676408018843759526604140106971
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          3303438612722366664712198986840670331804147208445211723096492004519262689709173275990059
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              387418111740445423958347593782399034611957087331199559226601345063
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  6714119298125635575168063390911910065716215856143626897275681
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock3
                      2268398129476177920937232847822452370831353
                      404492268222755
                      8469953271081
                      404492268222754
                      [(3, 2, Hex.Nat.PrimeCert.small 2),
                       (2, 0, Hex.Nat.PrimeCert.small 1217),
                       (2, 0, Hex.Nat.PrimeCert.small 2003),
                       (2, 0, Hex.Nat.PrimeCert.small 2999),
                       (2, 0, Hex.Nat.PrimeCert.small 6257)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h4ea70761e3d572bd9299' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h4ea70761e3d572bd9299

/-- Frozen certificate for 20435220525474711789016147186368793610673008889769983972727462013878251021900102031122352488004382430769150830337247. -/
theorem Hex.PrimalityCorpus.hfd85a8846190b9257749 : _root_.Nat.Prime 20435220525474711789016147186368793610673008889769983972727462013878251021900102031122352488004382430769150830337247 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  20435220525474711789016147186368793610673008889769983972727462013878251021900102031122352488004382430769150830337247
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      374487149869481489409436012671391147910357133285949100879394696704676408018843759526604140106971
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          3303438612722366664712198986840670331804147208445211723096492004519262689709173275990059
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              387418111740445423958347593782399034611957087331199559226601345063
              [(3, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 59),
               (2, 0, Hex.Nat.PrimeCert.small 163),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  6714119298125635575168063390911910065716215856143626897275681
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock3
                      2268398129476177920937232847822452370831353
                      404492268222755
                      8469953271081
                      404492268222754
                      [(3, 2, Hex.Nat.PrimeCert.small 2),
                       (2, 0, Hex.Nat.PrimeCert.small 1217),
                       (2, 0, Hex.Nat.PrimeCert.small 2003),
                       (2, 0, Hex.Nat.PrimeCert.small 2999),
                       (2, 0, Hex.Nat.PrimeCert.small 6257)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hfd85a8846190b9257749' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hfd85a8846190b9257749

/-- Frozen certificate for 20550072593656997211392408420284044439387839864047440775054482948439646267217829847751206188244058164308313459570767. -/
theorem Hex.PrimalityCorpus.h8db363afc26da1fc8118 : _root_.Nat.Prime 20550072593656997211392408420284044439387839864047440775054482948439646267217829847751206188244058164308313459570767 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  20550072593656997211392408420284044439387839864047440775054482948439646267217829847751206188244058164308313459570767
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      61579351205073487693955577072199690806216280899006724725189247894583568350076551856942952183721
      2125895178457145860693916825061
      96272758528268653130530732737683
      2125895178457145860693916824879
      6
      [(3, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 1607),
       (2, 0, Hex.Nat.PrimeCert.small 27017),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          10027017101
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              100270171
              [(2, 1, Hex.Nat.PrimeCert.small 7),
               (2, 0, Hex.Nat.PrimeCert.small 13),
               (2, 0, Hex.Nat.PrimeCert.small 53)])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          5134948667867
          73817
          687
          73816
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 30553)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8db363afc26da1fc8118' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8db363afc26da1fc8118

/-- Frozen certificate for 20872840861387862388838484267663060491481066331437461289872002141639226486496881987574633786585554658818138863851461. -/
theorem Hex.PrimalityCorpus.h6228ff7df5165577f449 : _root_.Nat.Prime 20872840861387862388838484267663060491481066331437461289872002141639226486496881987574633786585554658818138863851461 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  20872840861387862388838484267663060491481066331437461289872002141639226486496881987574633786585554658818138863851461
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      5459058355733939400697147835164774971545481823168578347384780729403279852702503
      317056386159266284241490431
      62588783676524401480364628
      317056386159266284241490430
      [(5, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 4889),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          21357262313831803707077
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              5339315578457950926769
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  340170462439981583
                  [(2, 0, Hex.Nat.PrimeCert.small 317),
                   (2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      76217311
                      [(3, 1, Hex.Nat.PrimeCert.small 13), (2, 0, Hex.Nat.PrimeCert.small 5011)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6228ff7df5165577f449' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6228ff7df5165577f449

/-- Frozen certificate for 20874203191564839632985323551932533251800728006025680155040338374616009818715822701365432308666967940321258936340177. -/
theorem Hex.PrimalityCorpus.hd83e05eceb7a09daf519 : _root_.Nat.Prime 20874203191564839632985323551932533251800728006025680155040338374616009818715822701365432308666967940321258936340177 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  20874203191564839632985323551932533251800728006025680155040338374616009818715822701365432308666967940321258936340177
  602559291040700963292983452676739969131
  107336448793005450018462278113964856146
  602559291040700963292983452676739969130
  [(5, 3, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 61),
   (2, 0, Hex.Nat.PrimeCert.small 829),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 17977579 [(2, 0, Hex.Nat.PrimeCert.pock 2996263 [(2, 0, Hex.Nat.PrimeCert.small 8761)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      21437828389835670667012909
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          8078053199156116153
          [(2, 0, Hex.Nat.PrimeCert.small 211),
           (2, 0, Hex.Nat.PrimeCert.pock 228639991 [(2, 0, Hex.Nat.PrimeCert.small 28123)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd83e05eceb7a09daf519' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd83e05eceb7a09daf519

/-- Frozen certificate for 21013964757801490193749849300480596540789273132496189079023132996929652494052531126254435107305961399902612093543829. -/
theorem Hex.PrimalityCorpus.h53cbdbcff59ba98ae1e5 : _root_.Nat.Prime 21013964757801490193749849300480596540789273132496189079023132996929652494052531126254435107305961399902612093543829 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  21013964757801490193749849300480596540789273132496189079023132996929652494052531126254435107305961399902612093543829
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      98799977233753456612142672505221618776396259062382172714644335456574071869428709712892046279624816165641453809
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          95461677569393059006636094952583711642649078450615331308578541281537237989263
          279176982261575758681070747
          51851233356440278149907
          279176982261575758681070746
          [(5, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 373),
           (2, 0, Hex.Nat.PrimeCert.small 601),
           (2, 0, Hex.Nat.PrimeCert.small 6829),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3
              257731277
              643
              184
              641
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 11),
               (2, 0, Hex.Nat.PrimeCert.small 19)]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              1215856861
              513
              1362
              502
              2
              [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 167)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h53cbdbcff59ba98ae1e5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h53cbdbcff59ba98ae1e5

/-- Frozen certificate for 21211649573585875036056256142539130576001951935158695175756641314227426306488509322402912222351345163347077714398373. -/
theorem Hex.PrimalityCorpus.h1708445af152b26a9f64 : _root_.Nat.Prime 21211649573585875036056256142539130576001951935158695175756641314227426306488509322402912222351345163347077714398373 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  21211649573585875036056256142539130576001951935158695175756641314227426306488509322402912222351345163347077714398373
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      5302912393396468759014064035634782644000487983789673793939160328556856576622127330600728055587836290836769428599593
      52422494027964571128430000792628765601
      343032436995041427483498972959823524559
      52422494027964571128430000792628765574
      4
      [(5, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 9778973 [(2, 0, Hex.Nat.PrimeCert.small 4919)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          1275476009
          [(2, 0, Hex.Nat.PrimeCert.pock 159434501 [(2, 0, Hex.Nat.PrimeCert.small 18757)])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          881087633680727327089
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              108615339457683349
              [(2, 0, Hex.Nat.PrimeCert.pock 920106893 [(2, 0, Hex.Nat.PrimeCert.small 44381)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h1708445af152b26a9f64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h1708445af152b26a9f64

/-- Frozen certificate for 21274226905202545767292926096498003515984521238873537878585958506000028994713667723721904227306102233959619640317721. -/
theorem Hex.PrimalityCorpus.h11bce2b03f1ac33f1db4 : _root_.Nat.Prime 21274226905202545767292926096498003515984521238873537878585958506000028994713667723721904227306102233959619640317721 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  21274226905202545767292926096498003515984521238873537878585958506000028994713667723721904227306102233959619640317721
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      245207075019528998444929030476701161952302990715874120073404508441201700297920964511017
      410205545714892062364665728683
      1881094684166820075929619284
      410205545714892062364665728682
      [(3, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 151),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 544600993 [(2, 0, Hex.Nat.PrimeCert.small 23), (2, 0, Hex.Nat.PrimeCert.small 18973)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          388061724544895369
          170205
          4461101
          170100
          16
          [(3, 2, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 131),
           (2, 0, Hex.Nat.PrimeCert.small 199)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h11bce2b03f1ac33f1db4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h11bce2b03f1ac33f1db4

/-- Frozen certificate for 21317503099200513867867325766314059908104226963593845551238911082181107267578615748598260029195979233893552369470161. -/
theorem Hex.PrimalityCorpus.hcb8317c3dabf0eb3f775 : _root_.Nat.Prime 21317503099200513867867325766314059908104226963593845551238911082181107267578615748598260029195979233893552369470161 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  21317503099200513867867325766314059908104226963593845551238911082181107267578615748598260029195979233893552369470161
  410450136080740707806444606690240086137
  208973181807525065259212054630426732588
  410450136080740707806444606690240086134
  [(3, 3, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 139),
   (2, 0, Hex.Nat.PrimeCert.small 8171),
   (2, 0, Hex.Nat.PrimeCert.small 25541),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 1036031203 [(2, 0, Hex.Nat.PrimeCert.small 127), (2, 0, Hex.Nat.PrimeCert.small 7951)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      469663884578790899
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          234831942289395449
          609301
          551686
          609297
          [(3, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 57667)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hcb8317c3dabf0eb3f775' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hcb8317c3dabf0eb3f775

/-- Frozen certificate for 21437462266481709865585629751936802398186906485313766383277347754947033867699778395032428161464874584341384350696781. -/
theorem Hex.PrimalityCorpus.hb0a22090f85472db8461 : _root_.Nat.Prime 21437462266481709865585629751936802398186906485313766383277347754947033867699778395032428161464874584341384350696781 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  21437462266481709865585629751936802398186906485313766383277347754947033867699778395032428161464874584341384350696781
  107759451046247688543202172282171708039
  1100596962938399850619131365338298907688
  107759451046247688543202172282171707998
  8
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 13),
   (2, 0, Hex.Nat.PrimeCert.small 37),
   (2, 0, Hex.Nat.PrimeCert.small 2647),
   (2, 0, Hex.Nat.PrimeCert.small 12763),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      303651723891795902406364181
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          95667867213122759909
          2276267
          782680
          2276265
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.pock 1954411 [(2, 0, Hex.Nat.PrimeCert.small 65147)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb0a22090f85472db8461' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb0a22090f85472db8461

/-- Frozen certificate for 21566380355392508964174996920674106311572451472217565170511831180511788181654156244863050845432153641108130935217253. -/
theorem Hex.PrimalityCorpus.hb3569338337eb35d1497 : _root_.Nat.Prime 21566380355392508964174996920674106311572451472217565170511831180511788181654156244863050845432153641108130935217253 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  21566380355392508964174996920674106311572451472217565170511831180511788181654156244863050845432153641108130935217253
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      594635048173114115789865003195937590868401913381513856637335022165342944300264204555034488589217
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          50358659228752889209846290921065175378421571255209506829042600115628636881797442797682460077
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              159362845660610408891918642155269542336777124225346540598236076315280496461384312650893861
              419946704235472516735459634771
              964790930915211802726546290344
              419946704235472516735459634761
              2
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 5),
               (2, 0, Hex.Nat.PrimeCert.small 7),
               (2, 0, Hex.Nat.PrimeCert.small 79),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  645465563
                  [(2, 0, Hex.Nat.PrimeCert.small 127), (2, 0, Hex.Nat.PrimeCert.small 4973)]),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  40256288364784237
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      145856117263711
                      [(2,
                        0,
                        Hex.Nat.PrimeCert.pock
                          694552939351
                          [(2,
                            0,
                            Hex.Nat.PrimeCert.pock
                              4630352929
                              [(2,
                                0,
                                Hex.Nat.PrimeCert.pock
                                  48232843
                                  [(2, 0, Hex.Nat.PrimeCert.small 43),
                                   (2, 0, Hex.Nat.PrimeCert.small 1571)])])])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb3569338337eb35d1497' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb3569338337eb35d1497

/-- Frozen certificate for 21626443997501887375694237481003076277083619716092502114988109406025370617343340166586609273778421207794243266775151. -/
theorem Hex.PrimalityCorpus.hdfbdd17dc753b3aec16c : _root_.Nat.Prime 21626443997501887375694237481003076277083619716092502114988109406025370617343340166586609273778421207794243266775151 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  21626443997501887375694237481003076277083619716092502114988109406025370617343340166586609273778421207794243266775151
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      548828714672467268374157395435911340195637120206053419516167157568055253876314496211224169070176196673857
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          2410974345636131181571015231132141852473575557101558041773026912617508998773
          3782652926607312325690061
          24562282525988825759297063
          3782652926607312325690035
          3
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 11),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              88568912879
              [(13, 0, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  153001
                  [(2, 2, Hex.Nat.PrimeCert.small 5), (2, 0, Hex.Nat.PrimeCert.small 17)])]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              1797682310821
              3209
              159754
              3003
              41
              [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 593)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hdfbdd17dc753b3aec16c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hdfbdd17dc753b3aec16c

/-- Frozen certificate for 21659605301602180705833415007202139902998570169771791505032136126998269598991993879835544858197365534121616420602361. -/
theorem Hex.PrimalityCorpus.h17beca8d0e5b912b6dcd : _root_.Nat.Prime 21659605301602180705833415007202139902998570169771791505032136126998269598991993879835544858197365534121616420602361 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  21659605301602180705833415007202139902998570169771791505032136126998269598991993879835544858197365534121616420602361
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      1468004678276961616435205717341821654880466444015413353736826590890965019205873
      5814634484317578474503939034679977
      44074932846
      5814634484317578474503939034679976
      [(5, 3, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          13952598596070451
          66507
          3218373
          66313
          41
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 23279)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          18280068109533677
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              1261390291853
              74621
              424
              74620
              [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 9631)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h17beca8d0e5b912b6dcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h17beca8d0e5b912b6dcd

/-- Frozen certificate for 21659605301602180705833415007202139902998570169771791505032136126998269598991993879835544858197365534121616420602361. -/
theorem Hex.PrimalityCorpus.hb421189c987b559c5911 : _root_.Nat.Prime 21659605301602180705833415007202139902998570169771791505032136126998269598991993879835544858197365534121616420602361 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  21659605301602180705833415007202139902998570169771791505032136126998269598991993879835544858197365534121616420602361
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      1468004678276961616435205717341821654880466444015413353736826590890965019205873
      37185165626586864131177716942165689
      1125
      37185165626586864131177716942165688
      [(5, 3, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          18280068109533677
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              1261390291853
              74621
              424
              74620
              [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 9631)])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          87332225614240763939
          [(2, 0, Hex.Nat.PrimeCert.small 593),
           (2, 0, Hex.Nat.PrimeCert.pock 111333071 [(2, 0, Hex.Nat.PrimeCert.small 22861)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb421189c987b559c5911' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb421189c987b559c5911

/-- Frozen certificate for 22378980978906376012373275012429031524212592036075074699373210942425424545658355868722840799905276444815102470952979. -/
theorem Hex.PrimalityCorpus.h5f10e0042c5b072aee81 : _root_.Nat.Prime 22378980978906376012373275012429031524212592036075074699373210942425424545658355868722840799905276444815102470952979 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  22378980978906376012373275012429031524212592036075074699373210942425424545658355868722840799905276444815102470952979
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      430395448535781538561484853804763104233594658701913635083133988558778405742901787
      [(2, 0, Hex.Nat.PrimeCert.small 17191),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          5978187860872767916409816247094960014071
          352387958477953655
          39925
          352387958477953654
          [(7, 0, Hex.Nat.PrimeCert.small 2),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              136808733034403537
              131187
              708290
              131165
              2
              [(3, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 19423)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h5f10e0042c5b072aee81' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h5f10e0042c5b072aee81

/-- Frozen certificate for 22719613819394320975557048052901760194974965061116468133099404059724767918465475220768887802917303826807223043190213. -/
theorem Hex.PrimalityCorpus.h2a162cc1f18842b9c766 : _root_.Nat.Prime 22719613819394320975557048052901760194974965061116468133099404059724767918465475220768887802917303826807223043190213 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  22719613819394320975557048052901760194974965061116468133099404059724767918465475220768887802917303826807223043190213
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      763170465375439036611431581983311336324886912681979181643092845655168233548953
      8954008461507821603995567
      138600235594284674763747097
      8954008461507821603995505
      3
      [(3, 2, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          5373509327
          495
          923
          487
          [(5, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 853)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          1220578740469763
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              69516957539
              [(2, 0, Hex.Nat.PrimeCert.small 149), (2, 0, Hex.Nat.PrimeCert.small 3583)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h2a162cc1f18842b9c766' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h2a162cc1f18842b9c766

/-- Frozen certificate for 23091078377273781865977230296351586422456906773368913045449302584907679252044144160574346442639545202947581457412791. -/
theorem Hex.PrimalityCorpus.h77eab66a539da3965265 : _root_.Nat.Prime 23091078377273781865977230296351586422456906773368913045449302584907679252044144160574346442639545202947581457412791 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  23091078377273781865977230296351586422456906773368913045449302584907679252044144160574346442639545202947581457412791
  482832071421767711855189134052518285151
  95947772915160378406745210916685403183
  482832071421767711855189134052518285150
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 379528843 [(2, 1, Hex.Nat.PrimeCert.small 11), (2, 0, Hex.Nat.PrimeCert.small 191)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      511976225759419
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          451478153227
          2423
          6587
          2412
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 2927)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      892616856490361
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          22315421412259
          [(2, 1, Hex.Nat.PrimeCert.small 13),
           (2, 0, Hex.Nat.PrimeCert.small 101),
           (2, 0, Hex.Nat.PrimeCert.small 509)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h77eab66a539da3965265' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h77eab66a539da3965265

/-- Frozen certificate for 23862579784369885371155987887410970997692039342870740255377598160644199894068728809506198332510525965739716290431683. -/
theorem Hex.PrimalityCorpus.h7610dc3de6d304277fbc : _root_.Nat.Prime 23862579784369885371155987887410970997692039342870740255377598160644199894068728809506198332510525965739716290431683 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  23862579784369885371155987887410970997692039342870740255377598160644199894068728809506198332510525965739716290431683
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      38762335948974152759210725458550990477131971551214616498603165456162499002268426900397110705837
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          424652551755784550828080232496847260046959549239980431303248416363077132429481
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              68893217594119506190059504838163799125692832050254304441
              2694133130542415937859
              12206702655622
              2694133130542415937858
              [(7, 2, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  603348943
                  [(2, 0, Hex.Nat.PrimeCert.small 307), (2, 0, Hex.Nat.PrimeCert.small 641)]),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  348029061491
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock3Sieve
                      3163900559
                      441
                      6482
                      377
                      10
                      [(7, 0, Hex.Nat.PrimeCert.small 2),
                       (2, 0, Hex.Nat.PrimeCert.small 13),
                       (2, 0, Hex.Nat.PrimeCert.small 19)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h7610dc3de6d304277fbc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h7610dc3de6d304277fbc

/-- Frozen certificate for 23911666676129196047555008689688514451100533708902228789153805054706192411365078437052847877316390136825667720259323. -/
theorem Hex.PrimalityCorpus.hd6515007b0d65f38a5c9 : _root_.Nat.Prime 23911666676129196047555008689688514451100533708902228789153805054706192411365078437052847877316390136825667720259323 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  23911666676129196047555008689688514451100533708902228789153805054706192411365078437052847877316390136825667720259323
  1686526530966288870232351168898512356238409
  3158364405846193926754118971338
  1686526530966288870232351168898512356238408
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 24971941 [(2, 0, Hex.Nat.PrimeCert.small 19819)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      616282700574193
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          675748575191
          7849
          9699
          7844
          [(7, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 13),
           (2, 0, Hex.Nat.PrimeCert.small 227)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      63211563879633135289
      4238891
      2105711
      4238889
      [(13, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 271), (2, 0, Hex.Nat.PrimeCert.small 1787)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd6515007b0d65f38a5c9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd6515007b0d65f38a5c9

/-- Frozen certificate for 24128711784271643079763797861136769544774892545451342398274709663128299789850599952752185970922565075915289634020469. -/
theorem Hex.PrimalityCorpus.h1c471d0e98ee389ef8a2 : _root_.Nat.Prime 24128711784271643079763797861136769544774892545451342398274709663128299789850599952752185970922565075915289634020469 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  24128711784271643079763797861136769544774892545451342398274709663128299789850599952752185970922565075915289634020469
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      6286602212231105138394983083567559307318666152278822019538251201591503788093288278685190229599
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          326667020507501353484172769846205331830364630876701196696125071660272701
          202303870579085594789800387
          6287666747511984529
          202303870579085594789800386
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 14759),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              974770637
              219
              1175
              196
              2
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 7),
               (2, 0, Hex.Nat.PrimeCert.small 23)]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              2800744730423
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  1400372365211
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock3Sieve
                      1538870731
                      1097
                      2506
                      1087
                      3
                      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 277)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h1c471d0e98ee389ef8a2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h1c471d0e98ee389ef8a2

/-- Frozen certificate for 24128711784271643079763797861136769544774892545451342398274709663128299789850599952752185970922565075915289634020469. -/
theorem Hex.PrimalityCorpus.hda0eddb4bd94bcbd726c : _root_.Nat.Prime 24128711784271643079763797861136769544774892545451342398274709663128299789850599952752185970922565075915289634020469 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  24128711784271643079763797861136769544774892545451342398274709663128299789850599952752185970922565075915289634020469
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      6286602212231105138394983083567559307318666152278822019538251201591503788093288278685190229599
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          326667020507501353484172769846205331830364630876701196696125071660272701
          11088573547801681314542625
          292526116943023491725
          11088573547801681314542624
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 14759),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3
              400256506676166557281
              332516261
              1384
              332516260
              [(11, 4, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 2113),
               (2, 0, Hex.Nat.PrimeCert.small 5623)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hda0eddb4bd94bcbd726c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hda0eddb4bd94bcbd726c

/-- Frozen certificate for 24231958192514654320802083948010486515282856058626578461503852934602233885105290476609960342919880112347646760396467. -/
theorem Hex.PrimalityCorpus.h298ab595c622c23e82f0 : _root_.Nat.Prime 24231958192514654320802083948010486515282856058626578461503852934602233885105290476609960342919880112347646760396467 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  24231958192514654320802083948010486515282856058626578461503852934602233885105290476609960342919880112347646760396467
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      52487449312326981535174366681067754066404667845910016324957936647803349761358214604238543012744329
      729076858126154724131412954540391
      127690190523117518216397128182660
      729076858126154724131412954540390
      [(3, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 389),
       (2, 0, Hex.Nat.PrimeCert.small 22189),
       (2, 0, Hex.Nat.PrimeCert.pock 408497 [(2, 1, Hex.Nat.PrimeCert.small 11), (2, 0, Hex.Nat.PrimeCert.small 211)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          16071920625958286743
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              116397403105189
              [(2,
                0,
                Hex.Nat.PrimeCert.pock3
                  9699783592099
                  544811
                  31
                  544810
                  [(2, 0, Hex.Nat.PrimeCert.small 2),
                   (2, 0, Hex.Nat.PrimeCert.small 131),
                   (2, 0, Hex.Nat.PrimeCert.small 1493)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h298ab595c622c23e82f0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h298ab595c622c23e82f0

/-- Frozen certificate for 24667361512537599586222186745449578135793071121713649560824634929799576999140929457805173651429107526690220214302391. -/
theorem Hex.PrimalityCorpus.hc8b94987592b218a61a2 : _root_.Nat.Prime 24667361512537599586222186745449578135793071121713649560824634929799576999140929457805173651429107526690220214302391 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  24667361512537599586222186745449578135793071121713649560824634929799576999140929457805173651429107526690220214302391
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      447468352482257086553095192559488638972102418696046966484294118577584815075220694520976378497841
      80063563440294198320830959257251
      102002988120994725764693007767434
      80063563440294198320830959257245
      2
      [(7, 3, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.small 223),
       (2, 0, Hex.Nat.PrimeCert.small 797),
       (2, 0, Hex.Nat.PrimeCert.small 2347),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 79843193 [(2, 0, Hex.Nat.PrimeCert.small 71), (2, 0, Hex.Nat.PrimeCert.small 983)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          7989744273803
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              3994872136901
              15255
              830
              15254
              [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 12263)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc8b94987592b218a61a2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc8b94987592b218a61a2

/-- Frozen certificate for 24861271949501155038098851397582471748353308045473779587871460192011746627324314757688931426673049463601196745062591. -/
theorem Hex.PrimalityCorpus.h2657cfbb03d1b0824d43 : _root_.Nat.Prime 24861271949501155038098851397582471748353308045473779587871460192011746627324314757688931426673049463601196745062591 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  24861271949501155038098851397582471748353308045473779587871460192011746627324314757688931426673049463601196745062591
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      243755077003778000066173760052506430927458181845496719687302494645900692066153747884831
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          7922477394875340609702251768566906109675972663495321619636012601102367067761
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              211874294033471525638464095739490183998026496015048937563528401
              [(2,
                0,
                Hex.Nat.PrimeCert.pock3
                  51681699198329477421812883144572686115237217293162488429
                  4928772308834636029906781
                  1643036
                  4928772308834636029906780
                  [(2, 1, Hex.Nat.PrimeCert.small 2),
                   (2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      991447634934130671520759
                      [(2, 0, Hex.Nat.PrimeCert.small 28433),
                       (2,
                        0,
                        Hex.Nat.PrimeCert.pock
                          192320331647
                          [(2, 0, Hex.Nat.PrimeCert.small 3299), (2, 0, Hex.Nat.PrimeCert.small 32423)])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h2657cfbb03d1b0824d43' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h2657cfbb03d1b0824d43

/-- Frozen certificate for 24991765315764590222885428910692178235030846306576439588120388899635471449503491529770320297940892920756845713220567. -/
theorem Hex.PrimalityCorpus.hbbe766583f9077b58e60 : _root_.Nat.Prime 24991765315764590222885428910692178235030846306576439588120388899635471449503491529770320297940892920756845713220567 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  24991765315764590222885428910692178235030846306576439588120388899635471449503491529770320297940892920756845713220567
  1705530706718275400754752614655195646631344323
  4100904887060987704094589
  1705530706718275400754752614655195646631344322
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      18995907401910508657397
      2617769859
      3185
      2617769858
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 431666791 [(2, 0, Hex.Nat.PrimeCert.small 157), (2, 0, Hex.Nat.PrimeCert.small 2477)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      45946621335019730538569
      [(2, 0, Hex.Nat.PrimeCert.small 373),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          11682166117
          977
          6724
          949
          5
          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 233)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hbbe766583f9077b58e60' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hbbe766583f9077b58e60

/-- Frozen certificate for 25176979668039615543200987383617902940058202405475526365394493430601116745039345123459124480813576813572280965474207. -/
theorem Hex.PrimalityCorpus.hab81081fa071fdaf8f3c : _root_.Nat.Prime 25176979668039615543200987383617902940058202405475526365394493430601116745039345123459124480813576813572280965474207 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  25176979668039615543200987383617902940058202405475526365394493430601116745039345123459124480813576813572280965474207
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      26396978612951994625692821525842099394384384735806633909605379358565655366031819477
      167591369046070221844120232959
      531407132353371680836
      167591369046070221844120232958
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 477574121 [(2, 0, Hex.Nat.PrimeCert.small 33073)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          2608841212886952232243
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              14720752575227411
              1550269
              1354
              1550268
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 223),
               (2, 0, Hex.Nat.PrimeCert.small 5227)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hab81081fa071fdaf8f3c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hab81081fa071fdaf8f3c

/-- Frozen certificate for 25399013307622669896904623369478464302110671711137304964074017026735930611717052232144154094895263661801069850384157. -/
theorem Hex.PrimalityCorpus.h71b894e2deb65ebeb97f : _root_.Nat.Prime 25399013307622669896904623369478464302110671711137304964074017026735930611717052232144154094895263661801069850384157 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  25399013307622669896904623369478464302110671711137304964074017026735930611717052232144154094895263661801069850384157
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      2405562227078616249513150542283893917603704758153686256666603875903014060367661114730090556351940953257264403
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          15089975089019921495160155064117733742047735258724262507173409476023737796980281026502739341
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              1593555651376055146828923004345259780064387110933242566026160293
              160697747319808111041
              14424213338516234278523
              160697747319808110681
              46
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 1193),
               (2, 0, Hex.Nat.PrimeCert.small 43399),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3Sieve
                  1134860273231
                  5609
                  12754
                  5599
                  2
                  [(11, 0, Hex.Nat.PrimeCert.small 2),
                   (2, 0, Hex.Nat.PrimeCert.small 5),
                   (2, 0, Hex.Nat.PrimeCert.small 23),
                   (2, 0, Hex.Nat.PrimeCert.small 29)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h71b894e2deb65ebeb97f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h71b894e2deb65ebeb97f

/-- Frozen certificate for 26030551197010678992134958438970088688533706283268825629775742145630802468995465817310736909120989547802931888279101. -/
theorem Hex.PrimalityCorpus.h0e2d23af6b76f5278bc0 : _root_.Nat.Prime 26030551197010678992134958438970088688533706283268825629775742145630802468995465817310736909120989547802931888279101 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  26030551197010678992134958438970088688533706283268825629775742145630802468995465817310736909120989547802931888279101
  39602646151778393751422122852043749589
  3870722409950759259552381763017329452027
  39602646151778393751422122852043749198
  50
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 1, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 2903),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      161629820163389
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          40407455040847
          12213
          147540
          12164
          9
          [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 5851)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1235839708656758857
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          11922510116701
          [(2, 0, Hex.Nat.PrimeCert.small 2029), (2, 0, Hex.Nat.PrimeCert.small 91957)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h0e2d23af6b76f5278bc0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h0e2d23af6b76f5278bc0

/-- Frozen certificate for 26620698427083243253142548623801234036779982023429265707209652921149479896047977176951461817678565245003911506100427. -/
theorem Hex.PrimalityCorpus.h04a35fbb83544ab8e9d5 : _root_.Nat.Prime 26620698427083243253142548623801234036779982023429265707209652921149479896047977176951461817678565245003911506100427 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  26620698427083243253142548623801234036779982023429265707209652921149479896047977176951461817678565245003911506100427
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      542948116021344355777237741240317055225872784827468661357973336262507365304310457433577
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          489958160993567990471738300558332300285405598534739513494514593902738401685247563
          182233570121236672020998843
          1159241775785881781996090337
          182233570121236672020998817
          3
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (3, 2, Hex.Nat.PrimeCert.small 3),
           (2, 0, Hex.Nat.PrimeCert.small 13),
           (2, 0, Hex.Nat.PrimeCert.pock 5027941 [(2, 0, Hex.Nat.PrimeCert.small 9311)]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3
              130241744119214953
              566081
              563090
              566077
              [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 42509)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h04a35fbb83544ab8e9d5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h04a35fbb83544ab8e9d5

/-- Frozen certificate for 26764630365948291954552935821147649601138750993886408071982447369215055140709180768191557622805120369731232377866543. -/
theorem Hex.PrimalityCorpus.h8375be9ce41dd7b1057e : _root_.Nat.Prime 26764630365948291954552935821147649601138750993886408071982447369215055140709180768191557622805120369731232377866543 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  26764630365948291954552935821147649601138750993886408071982447369215055140709180768191557622805120369731232377866543
  9133946960632897758779197966197297689977
  385961147821688465077331140566916036
  9133946960632897758779197966197297689976
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 449),
   (2, 0, Hex.Nat.PrimeCert.small 691),
   (2, 0, Hex.Nat.PrimeCert.small 58171),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      100289036536699
      5367
      311583
      5129
      21
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 6343)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1626595099786061
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          81329754989303
          [(2, 0, Hex.Nat.PrimeCert.small 27851), (2, 0, Hex.Nat.PrimeCert.small 76649)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8375be9ce41dd7b1057e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8375be9ce41dd7b1057e

/-- Frozen certificate for 27048438825649370928726440953731705957464381392831555700788543953861755510795810976741597427256791611788419947306917. -/
theorem Hex.PrimalityCorpus.hfe549f708f8ee377918c : _root_.Nat.Prime 27048438825649370928726440953731705957464381392831555700788543953861755510795810976741597427256791611788419947306917 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  27048438825649370928726440953731705957464381392831555700788543953861755510795810976741597427256791611788419947306917
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      6762109706412342732181610238432926489366095348207888925197135988465438877698952744185399356814197902947104986826729
      86403167722712059252800999565833138927
      719267465918577858409938657313889393763
      86403167722712059252800999565833138893
      7
      [(11, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 68059),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          2127042319
          593
          5543
          554
          8
          [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 3), (2, 0, Hex.Nat.PrimeCert.small 73)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          59201024001923975557879
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              1741839080800457
              29055
              967172
              28921
              22
              [(3, 2, Hex.Nat.PrimeCert.small 2),
               (2, 1, Hex.Nat.PrimeCert.small 11),
               (2, 0, Hex.Nat.PrimeCert.small 31)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hfe549f708f8ee377918c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hfe549f708f8ee377918c

/-- Frozen certificate for 27126767733819568317652494260301651482398471512000953694335249008016397415238538384793639490582694786521645778976421. -/
theorem Hex.PrimalityCorpus.h1296e53431fc865c2f96 : _root_.Nat.Prime 27126767733819568317652494260301651482398471512000953694335249008016397415238538384793639490582694786521645778976421 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  27126767733819568317652494260301651482398471512000953694335249008016397415238538384793639490582694786521645778976421
  246127727888929235259134123374520837197
  509578951577597479367186767025793367926
  246127727888929235259134123374520837188
  2
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (11, 0, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 37),
   (2, 0, Hex.Nat.PrimeCert.small 4243),
   (2, 0, Hex.Nat.PrimeCert.pock 307919 [(2, 0, Hex.Nat.PrimeCert.small 911)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      7022232351269
      11923
      6009
      11920
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 6043)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      24030447128213
      12345
      178169
      12287
      13
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 2053)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h1296e53431fc865c2f96' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h1296e53431fc865c2f96

/-- Frozen certificate for 27347577534468967108198378750693233312362940678974381134592983547008025590495855679634155618518799288229354254205871. -/
theorem Hex.PrimalityCorpus.h68063c83fa9749019223 : _root_.Nat.Prime 27347577534468967108198378750693233312362940678974381134592983547008025590495855679634155618518799288229354254205871 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  27347577534468967108198378750693233312362940678974381134592983547008025590495855679634155618518799288229354254205871
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      714413237130773298330199286227661545054229879180663550436466570714951043870869710621867
      251649572930985996979593537433899
      1488444848665630574808
      251649572930985996979593537433898
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          1481217943
          3045
          156
          3044
          [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 1087)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          165365312124397621719673
          68741797
          66831220
          68741793
          [(5, 2, Hex.Nat.PrimeCert.small 2),
           (2, 2, Hex.Nat.PrimeCert.small 3),
           (3, 0, Hex.Nat.PrimeCert.small 7),
           (2, 0, Hex.Nat.PrimeCert.small 43),
           (2, 0, Hex.Nat.PrimeCert.small 541)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h68063c83fa9749019223' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h68063c83fa9749019223

/-- Frozen certificate for 27499630246961702949569697836976175603154016207515351136023368326891118791731883404355789147984911838570242308416943. -/
theorem Hex.PrimalityCorpus.hc56f9344cdfdf85d434e : _root_.Nat.Prime 27499630246961702949569697836976175603154016207515351136023368326891118791731883404355789147984911838570242308416943 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  27499630246961702949569697836976175603154016207515351136023368326891118791731883404355789147984911838570242308416943
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      14905567957965054864409226391685457317418005159479287217165660732431293758549866124155327
      624458394246150865093584393142415823
      10002803187756962
      624458394246150865093584393142415822
      [(5, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          11735833972067
          19575
          34817
          19567
          2
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 6491)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          36775149945351821199731
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              3677514994535182119973
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  920299047681477007
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      1893619439673821
                      [(2,
                        0,
                        Hex.Nat.PrimeCert.pock
                          94680971983691
                          [(2, 0, Hex.Nat.PrimeCert.pock 30887693 [(2, 0, Hex.Nat.PrimeCert.small 36947)])])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc56f9344cdfdf85d434e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc56f9344cdfdf85d434e
