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

/-- Frozen certificate for 288620160655650420641576358199358182823. -/
theorem Hex.PrimalityCorpus.hf958c54617a95dd73ddd : _root_.Nat.Prime 288620160655650420641576358199358182823 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  288620160655650420641576358199358182823
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      3951844406732519544330215527
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          183618827559358774478683
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              30603137926559795746447
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  24404416209377827549
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      1568004125506157
                      [(2,
                        0,
                        Hex.Nat.PrimeCert.pock
                          30153925490503
                          [(2, 0, Hex.Nat.PrimeCert.small 11),
                           (2, 0, Hex.Nat.PrimeCert.pock 868891 [(2, 0, Hex.Nat.PrimeCert.small 2633)])])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hf958c54617a95dd73ddd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hf958c54617a95dd73ddd

/-- Frozen certificate for 290755429786894847960257695542746457557. -/
theorem Hex.PrimalityCorpus.h18b41d92f3ed9757f6e0 : _root_.Nat.Prime 290755429786894847960257695542746457557 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  290755429786894847960257695542746457557
  53180532307789
  51135938495
  53180532307788
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      13329866878961
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          7244492869
          1969
          1662
          1965
          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 1, Hex.Nat.PrimeCert.small 3), (2, 0, Hex.Nat.PrimeCert.small 41)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h18b41d92f3ed9757f6e0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h18b41d92f3ed9757f6e0

/-- Frozen certificate for 292903071461687349518847670501205356573. -/
theorem Hex.PrimalityCorpus.h8cb9c748f07cc0c55751 : _root_.Nat.Prime 292903071461687349518847670501205356573 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  292903071461687349518847670501205356573
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      3707821553770916875776592112274107
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          966400473363782028093840259
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              260058974307827983369
              64506257
              7378
              64506256
              [(17, 2, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3Sieve
                  16594129
                  37
                  400
                  0
                  3
                  [(7, 3, Hex.Nat.PrimeCert.small 2), (2, 1, Hex.Nat.PrimeCert.small 3)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8cb9c748f07cc0c55751' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8cb9c748f07cc0c55751

/-- Frozen certificate for 293961660912959831961958908015258136517. -/
theorem Hex.PrimalityCorpus.hc5955ae5941b4612035c : _root_.Nat.Prime 293961660912959831961958908015258136517 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  293961660912959831961958908015258136517
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      147868038688611585493943112683731457
      103304578309
      4162696699701
      103304578147
      23
      [(3, 8, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          260294393
          [(2, 0, Hex.Nat.PrimeCert.pock 32536799 [(2, 0, Hex.Nat.PrimeCert.small 26113)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc5955ae5941b4612035c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc5955ae5941b4612035c

/-- Frozen certificate for 294808343265139261612007680311895941629. -/
theorem Hex.PrimalityCorpus.hb18c5cb5e26edf1c6264 : _root_.Nat.Prime 294808343265139261612007680311895941629 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  294808343265139261612007680311895941629
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      2153900417669220048120948559
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          401503360085911
          33877
          113642
          33863
          2
          [(3, 0, Hex.Nat.PrimeCert.small 2),
           (2, 1, Hex.Nat.PrimeCert.small 3),
           (5, 0, Hex.Nat.PrimeCert.small 5),
           (2, 0, Hex.Nat.PrimeCert.small 467)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb18c5cb5e26edf1c6264' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb18c5cb5e26edf1c6264

/-- Frozen certificate for 296773857123945696882764840335296027049. -/
theorem Hex.PrimalityCorpus.h1e50924ef2212ccea6a2 : _root_.Nat.Prime 296773857123945696882764840335296027049 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  296773857123945696882764840335296027049
  4583868098969
  25644671464321
  4583868098946
  6
  [(7, 2, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 17),
   (2, 0, Hex.Nat.PrimeCert.small 23),
   (2, 0, Hex.Nat.PrimeCert.small 37),
   (2, 0, Hex.Nat.PrimeCert.small 1171),
   (2, 0, Hex.Nat.PrimeCert.small 17749)]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h1e50924ef2212ccea6a2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h1e50924ef2212ccea6a2

/-- Frozen certificate for 296802690131721461449689701458510966991. -/
theorem Hex.PrimalityCorpus.h999160b3991312288d9b : _root_.Nat.Prime 296802690131721461449689701458510966991 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  296802690131721461449689701458510966991
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      58410270563371549562805488719
      34250824425
      59411304
      34250824424
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 61469),
       (2, 0, Hex.Nat.PrimeCert.pock 180347 [(2, 0, Hex.Nat.PrimeCert.small 90173)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h999160b3991312288d9b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h999160b3991312288d9b

/-- Frozen certificate for 297917967708716413941345490704533923757. -/
theorem Hex.PrimalityCorpus.h33df64c49ee7b53223b4 : _root_.Nat.Prime 297917967708716413941345490704533923757 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  297917967708716413941345490704533923757
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      24071289852599101818530506963
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          4020009423916081
          70171
          477031
          70143
          5
          [(11, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 4057)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h33df64c49ee7b53223b4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h33df64c49ee7b53223b4

/-- Frozen certificate for 297965033157886857777343400459408597099. -/
theorem Hex.PrimalityCorpus.h02081518137f5e7e335c : _root_.Nat.Prime 297965033157886857777343400459408597099 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  297965033157886857777343400459408597099
  7203610235979
  9879851187155
  7203610235973
  2
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 1941612037051 [(2, 0, Hex.Nat.PrimeCert.small 257), (2, 0, Hex.Nat.PrimeCert.small 6547)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h02081518137f5e7e335c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h02081518137f5e7e335c

/-- Frozen certificate for 298353949157768786961948646154068896343. -/
theorem Hex.PrimalityCorpus.he38d312af8f9e15652ef : _root_.Nat.Prime 298353949157768786961948646154068896343 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  298353949157768786961948646154068896343
  3321097833
  68763596828601
  3321015011
  47
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 273193 [(2, 0, Hex.Nat.PrimeCert.small 11383)]),
   (2, 0, Hex.Nat.PrimeCert.pock 2695703 [(2, 0, Hex.Nat.PrimeCert.small 10613)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he38d312af8f9e15652ef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he38d312af8f9e15652ef

/-- Frozen certificate for 298809726736941943364984253815628807227. -/
theorem Hex.PrimalityCorpus.ha9031eca6fcada6c4521 : _root_.Nat.Prime 298809726736941943364984253815628807227 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  298809726736941943364984253815628807227
  [(2, 0, Hex.Nat.PrimeCert.small 2411),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      189740360753055317
      60477
      688382
      60431
      2
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 92809)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha9031eca6fcada6c4521' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha9031eca6fcada6c4521

/-- Frozen certificate for 299726210193971518939965618362353987103. -/
theorem Hex.PrimalityCorpus.h39dc36041d3fdae57f78 : _root_.Nat.Prime 299726210193971518939965618362353987103 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  299726210193971518939965618362353987103
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      79885278618249862855598495069069
      28634775497259
      20600
      28634775497258
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          11008327726313
          24415
          1059
          24414
          [(3, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 9011)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h39dc36041d3fdae57f78' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h39dc36041d3fdae57f78

/-- Frozen certificate for 300054727485831611900052366893844397753. -/
theorem Hex.PrimalityCorpus.h06e9c10f5d0baac22c5a : _root_.Nat.Prime 300054727485831611900052366893844397753 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  300054727485831611900052366893844397753
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      8822300606523837266263514789
      189228599
      10700392872
      189228372
      15
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 71),
       (2, 0, Hex.Nat.PrimeCert.small 149),
       (2, 0, Hex.Nat.PrimeCert.small 15173)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h06e9c10f5d0baac22c5a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h06e9c10f5d0baac22c5a

/-- Frozen certificate for 304419254533937312273651459981811718787. -/
theorem Hex.PrimalityCorpus.h1f979579dda84662fcbe : _root_.Nat.Prime 304419254533937312273651459981811718787 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  304419254533937312273651459981811718787
  196650070056550591
  9811
  196650070056550590
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      62275461667548907
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          7451000438807
          [(2, 1, Hex.Nat.PrimeCert.small 29),
           (2, 0, Hex.Nat.PrimeCert.small 37),
           (2, 0, Hex.Nat.PrimeCert.small 89)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h1f979579dda84662fcbe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h1f979579dda84662fcbe

/-- Frozen certificate for 304574867067517007672846937101346983747. -/
theorem Hex.PrimalityCorpus.hbb58035f8758b20cc0ad : _root_.Nat.Prime 304574867067517007672846937101346983747 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  304574867067517007672846937101346983747
  [(2, 0, Hex.Nat.PrimeCert.small 20611),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      5934273094506397061
      2977639
      108409
      2977638
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 1, Hex.Nat.PrimeCert.small 19), (2, 0, Hex.Nat.PrimeCert.small 3623)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hbb58035f8758b20cc0ad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hbb58035f8758b20cc0ad

/-- Frozen certificate for 304846524189496738661883166997523670811. -/
theorem Hex.PrimalityCorpus.h576270e4eef66d20eb14 : _root_.Nat.Prime 304846524189496738661883166997523670811 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  304846524189496738661883166997523670811
  8623447612799
  5596689962812
  8623447612796
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 37),
   (2, 0, Hex.Nat.PrimeCert.small 827),
   (2, 0, Hex.Nat.PrimeCert.pock3Sieve 17055041 117 2081 0 19 [(3, 5, Hex.Nat.PrimeCert.small 2)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h576270e4eef66d20eb14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h576270e4eef66d20eb14

/-- Frozen certificate for 305663149610859998375960174902498698251. -/
theorem Hex.PrimalityCorpus.hb88b3a0d8c19e5bac1ee : _root_.Nat.Prime 305663149610859998375960174902498698251 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  305663149610859998375960174902498698251
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      918188507301964474501783387
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          26882773232457431
          905339
          45913
          905338
          [(7, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 97),
           (2, 0, Hex.Nat.PrimeCert.small 2789)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb88b3a0d8c19e5bac1ee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb88b3a0d8c19e5bac1ee

/-- Frozen certificate for 306689611144552403882756340300580873417. -/
theorem Hex.PrimalityCorpus.he4a19400ea9cb68fce8c : _root_.Nat.Prime 306689611144552403882756340300580873417 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  306689611144552403882756340300580873417
  [(2, 0, Hex.Nat.PrimeCert.small 41),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      4655629460567715181
      214569
      1809480
      214535
      2
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 5), (2, 0, Hex.Nat.PrimeCert.small 56711)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he4a19400ea9cb68fce8c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he4a19400ea9cb68fce8c

/-- Frozen certificate for 307035969720702947500358274362002552481. -/
theorem Hex.PrimalityCorpus.h15333fd2b9c77118dbf3 : _root_.Nat.Prime 307035969720702947500358274362002552481 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  307035969720702947500358274362002552481
  [(2, 1, Hex.Nat.PrimeCert.small 13),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      4353719453548038467
      745715
      10925673
      745656
      14
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 53), (2, 0, Hex.Nat.PrimeCert.small 4211)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h15333fd2b9c77118dbf3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h15333fd2b9c77118dbf3

/-- Frozen certificate for 307087401839216939071741926871210718677. -/
theorem Hex.PrimalityCorpus.h6dd19640c742652ab2cf : _root_.Nat.Prime 307087401839216939071741926871210718677 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  307087401839216939071741926871210718677
  325891873389
  21239124794196
  325891873128
  8
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      672183275273
      3041
      8880
      3029
      2
      [(3, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 769)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6dd19640c742652ab2cf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6dd19640c742652ab2cf

/-- Frozen certificate for 307913375851605812234977945686925698427. -/
theorem Hex.PrimalityCorpus.he674cbfbba1e489f824f : _root_.Nat.Prime 307913375851605812234977945686925698427 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  307913375851605812234977945686925698427
  4746119909729
  13847255419298
  4746119909717
  3
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 3),
   (2, 0, Hex.Nat.PrimeCert.small 7),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      79390427009
      12055
      454
      12054
      [(3, 6, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 73)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he674cbfbba1e489f824f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he674cbfbba1e489f824f

/-- Frozen certificate for 309253505669046954925946901214061325697. -/
theorem Hex.PrimalityCorpus.hd6a9336a95674fb99b40 : _root_.Nat.Prime 309253505669046954925946901214061325697 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  309253505669046954925946901214061325697
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      79682167904733661005869205030667
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          13280361317455610167644867505111
          4370305373
          47230321639
          4370305329
          4
          [(3, 0, Hex.Nat.PrimeCert.small 2),
           (2, 1, Hex.Nat.PrimeCert.small 3),
           (2, 0, Hex.Nat.PrimeCert.small 5),
           (2, 1, Hex.Nat.PrimeCert.small 23),
           (2, 0, Hex.Nat.PrimeCert.small 37),
           (2, 0, Hex.Nat.PrimeCert.small 53),
           (2, 0, Hex.Nat.PrimeCert.small 127)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd6a9336a95674fb99b40' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd6a9336a95674fb99b40

/-- Frozen certificate for 310235404253313441763163429262671940047. -/
theorem Hex.PrimalityCorpus.h8a59c458120c6c232cfa : _root_.Nat.Prime 310235404253313441763163429262671940047 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  310235404253313441763163429262671940047
  4162308632466525
  2030078
  4162308632466524
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 206279 [(2, 0, Hex.Nat.PrimeCert.small 6067)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 21187966637 [(2, 0, Hex.Nat.PrimeCert.small 1163), (2, 0, Hex.Nat.PrimeCert.small 67979)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8a59c458120c6c232cfa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8a59c458120c6c232cfa

/-- Frozen certificate for 310843247047678437235677462831007791913. -/
theorem Hex.PrimalityCorpus.h3fcda2c399765bf72307 : _root_.Nat.Prime 310843247047678437235677462831007791913 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  310843247047678437235677462831007791913
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      4656902953468269940388201017
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          150067767255358015609313
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              814311117681878449
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  6990035002763
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock3Sieve
                      7032228373
                      521
                      16053
                      378
                      23
                      [(2, 1, Hex.Nat.PrimeCert.small 2),
                       (3, 1, Hex.Nat.PrimeCert.small 3),
                       (2, 0, Hex.Nat.PrimeCert.small 13)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h3fcda2c399765bf72307' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h3fcda2c399765bf72307

/-- Frozen certificate for 313150337055890180889411181094800256731. -/
theorem Hex.PrimalityCorpus.h06dc36f8fa8daf3e7be9 : _root_.Nat.Prime 313150337055890180889411181094800256731 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  313150337055890180889411181094800256731
  14600461203491
  1941613566352
  14600461203490
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 4490038339183 [(2, 0, Hex.Nat.PrimeCert.small 1097), (2, 0, Hex.Nat.PrimeCert.small 18181)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h06dc36f8fa8daf3e7be9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h06dc36f8fa8daf3e7be9

/-- Frozen certificate for 313810473278236862961265710307404235517. -/
theorem Hex.PrimalityCorpus.h8a78362c585e3be76dad : _root_.Nat.Prime 313810473278236862961265710307404235517 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  313810473278236862961265710307404235517
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      6886100724459810867768134969
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          325089515127054552101
          1280367
          95254853
          1280069
          49
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 1, Hex.Nat.PrimeCert.small 5),
           (2, 0, Hex.Nat.PrimeCert.small 13063)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8a78362c585e3be76dad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8a78362c585e3be76dad

/-- Frozen certificate for 315026635997759466035200862982192740423. -/
theorem Hex.PrimalityCorpus.h3a797f89e4f7258f8561 : _root_.Nat.Prime 315026635997759466035200862982192740423 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  315026635997759466035200862982192740423
  376398590066188971
  380
  376398590066188970
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      321787971075866521
      1366013
      122132
      1366012
      [(11, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 53), (2, 0, Hex.Nat.PrimeCert.small 2707)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h3a797f89e4f7258f8561' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h3a797f89e4f7258f8561

/-- Frozen certificate for 315096417703678961363146583470948853087. -/
theorem Hex.PrimalityCorpus.h79c89b53aa841030b0c7 : _root_.Nat.Prime 315096417703678961363146583470948853087 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  315096417703678961363146583470948853087
  1420732022554609
  197826715
  1420732022554608
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 3, Hex.Nat.PrimeCert.small 7),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      185841246067
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          232883767
          [(2, 0, Hex.Nat.PrimeCert.pock 12937987 [(2, 0, Hex.Nat.PrimeCert.small 42281)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h79c89b53aa841030b0c7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h79c89b53aa841030b0c7

/-- Frozen certificate for 315844155192386703083817762877382634757. -/
theorem Hex.PrimalityCorpus.h28eed19352593727ddd2 : _root_.Nat.Prime 315844155192386703083817762877382634757 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  315844155192386703083817762877382634757
  453182838517051
  1013120113
  453182838517050
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      98703138961243
      73267
      34807
      73265
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 67), (2, 0, Hex.Nat.PrimeCert.small 281)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h28eed19352593727ddd2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h28eed19352593727ddd2

/-- Frozen certificate for 319053365356384419565168645703194043171. -/
theorem Hex.PrimalityCorpus.hbeafa2beb8624d027d83 : _root_.Nat.Prime 319053365356384419565168645703194043171 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  319053365356384419565168645703194043171
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      54257088988531900637849
      5575459
      72111282
      5575407
      4
      [(3, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 269), (2, 0, Hex.Nat.PrimeCert.small 9013)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hbeafa2beb8624d027d83' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hbeafa2beb8624d027d83

/-- Frozen certificate for 319315375106950085224176598118787813083. -/
theorem Hex.PrimalityCorpus.h538e17bab1b5c146e7f4 : _root_.Nat.Prime 319315375106950085224176598118787813083 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  319315375106950085224176598118787813083
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      22808241079067863230298328437056272363
      969752146431
      15559454720
      969752146430
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          13536416770571
          3531
          24782
          3502
          2
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 8263)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h538e17bab1b5c146e7f4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h538e17bab1b5c146e7f4

/-- Frozen certificate for 320901304584665771756326094831917745639. -/
theorem Hex.PrimalityCorpus.hb69895b7a324f2047343 : _root_.Nat.Prime 320901304584665771756326094831917745639 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  320901304584665771756326094831917745639
  [(2, 0, Hex.Nat.PrimeCert.small 4219),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      142247160631895129
      [(2, 0, Hex.Nat.PrimeCert.small 241), (2, 0, Hex.Nat.PrimeCert.small 547), (2, 0, Hex.Nat.PrimeCert.small 2999)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb69895b7a324f2047343' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb69895b7a324f2047343

/-- Frozen certificate for 323879760545210191071174406759498661641. -/
theorem Hex.PrimalityCorpus.h068758e3c9793689e7a1 : _root_.Nat.Prime 323879760545210191071174406759498661641 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  323879760545210191071174406759498661641
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      588474925768890161815968391
      237414989
      679423979
      237414977
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 19),
       (2, 0, Hex.Nat.PrimeCert.small 757),
       (2, 0, Hex.Nat.PrimeCert.small 22877)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h068758e3c9793689e7a1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h068758e3c9793689e7a1

/-- Frozen certificate for 324286123708088817124708054663267139467. -/
theorem Hex.PrimalityCorpus.h46016610030ba6e020c0 : _root_.Nat.Prime 324286123708088817124708054663267139467 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  324286123708088817124708054663267139467
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      6009178924434600168283
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          14779019592708841
          251755
          8750
          251754
          [(11, 2, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 313),
           (2, 0, Hex.Nat.PrimeCert.small 367)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h46016610030ba6e020c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h46016610030ba6e020c0

/-- Frozen certificate for 325119218482890075532766115700375715687. -/
theorem Hex.PrimalityCorpus.h73448f66d2edefbe1abb : _root_.Nat.Prime 325119218482890075532766115700375715687 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  325119218482890075532766115700375715687
  203795623697659
  3994089276
  203795623697658
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 58109),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1735897357
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          48219371
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              4821937
              [(2, 0, Hex.Nat.PrimeCert.small 113), (2, 0, Hex.Nat.PrimeCert.small 127)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h73448f66d2edefbe1abb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h73448f66d2edefbe1abb

/-- Frozen certificate for 327213163616266751863121713522233707213. -/
theorem Hex.PrimalityCorpus.heb5149843497fef43568 : _root_.Nat.Prime 327213163616266751863121713522233707213 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  327213163616266751863121713522233707213
  5918274689831287
  10367961
  5918274689831286
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      993101644817773
      35749
      1329748
      35599
      36
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 4831)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.heb5149843497fef43568' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.heb5149843497fef43568

/-- Frozen certificate for 329804500762788125115628309732792231523. -/
theorem Hex.PrimalityCorpus.hc87deb3995e7eb298da3 : _root_.Nat.Prime 329804500762788125115628309732792231523 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  329804500762788125115628309732792231523
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      237244004399468256915381184669
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          3199402545522051000283
          7411103
          3097912
          7411101
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 1103),
           (2, 0, Hex.Nat.PrimeCert.small 10301)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc87deb3995e7eb298da3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc87deb3995e7eb298da3

/-- Frozen certificate for 329839203489149340652763118540116700701. -/
theorem Hex.PrimalityCorpus.h98abec0ea8de3fc2e6c0 : _root_.Nat.Prime 329839203489149340652763118540116700701 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  329839203489149340652763118540116700701
  240874755231
  39007054694819
  240874754583
  18
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      514049058097
      3421
      1780
      3418
      [(5, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 751)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h98abec0ea8de3fc2e6c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h98abec0ea8de3fc2e6c0

/-- Frozen certificate for 330955914842979462334838615160556008529. -/
theorem Hex.PrimalityCorpus.h707947918a10cf73a7cd : _root_.Nat.Prime 330955914842979462334838615160556008529 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  330955914842979462334838615160556008529
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      405583228974239537175047322500681383
      76294677413413
      90583880
      76294677413412
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 9749),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          2426663003
          [(2, 0, Hex.Nat.PrimeCert.small 27701), (2, 0, Hex.Nat.PrimeCert.small 43801)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h707947918a10cf73a7cd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h707947918a10cf73a7cd

/-- Frozen certificate for 331141689854343830823298622721389238163. -/
theorem Hex.PrimalityCorpus.h48a839cac80bbaacc563 : _root_.Nat.Prime 331141689854343830823298622721389238163 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  331141689854343830823298622721389238163
  53269299795787
  108242143736
  53269299795786
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 97),
   (2, 0, Hex.Nat.PrimeCert.small 379),
   (2, 0, Hex.Nat.PrimeCert.pock 531927937 [(2, 0, Hex.Nat.PrimeCert.small 389), (2, 0, Hex.Nat.PrimeCert.small 1187)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h48a839cac80bbaacc563' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h48a839cac80bbaacc563

/-- Frozen certificate for 331389535622552344877684594048310297709. -/
theorem Hex.PrimalityCorpus.h5640b19b1fb30d96114e : _root_.Nat.Prime 331389535622552344877684594048310297709 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  331389535622552344877684594048310297709
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      4184498517127417291894991606347
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          697416419521236215315831934391
          5384115111843
          10344
          5384115111842
          [(3, 0, Hex.Nat.PrimeCert.small 2),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              2903000436617
              527
              21009
              331
              3
              [(3, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 1039)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h5640b19b1fb30d96114e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h5640b19b1fb30d96114e

/-- Frozen certificate for 332177205138333501499661030773749904141. -/
theorem Hex.PrimalityCorpus.h63acabce841cc851e2f6 : _root_.Nat.Prime 332177205138333501499661030773749904141 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  332177205138333501499661030773749904141
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      218644080103690942629741473331589
      [(2, 0, Hex.Nat.PrimeCert.small 2273),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          1990228921346569
          145433
          57410
          145431
          [(11, 2, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 7),
           (2, 0, Hex.Nat.PrimeCert.small 2351)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h63acabce841cc851e2f6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h63acabce841cc851e2f6

/-- Frozen certificate for 333147626386545075065602620451367864759. -/
theorem Hex.PrimalityCorpus.h4d832e2eca25224fdef5 : _root_.Nat.Prime 333147626386545075065602620451367864759 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  333147626386545075065602620451367864759
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      2101452034520032098672646897
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          43780250719167335389013477
          [(2, 0, Hex.Nat.PrimeCert.small 29443),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              5210762377817
              9665
              91503
              9627
              10
              [(3, 2, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 23),
               (2, 0, Hex.Nat.PrimeCert.small 29)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h4d832e2eca25224fdef5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h4d832e2eca25224fdef5

/-- Frozen certificate for 338916320817998667668332038084489273743. -/
theorem Hex.PrimalityCorpus.h6904530049a1f86bc7e4 : _root_.Nat.Prime 338916320817998667668332038084489273743 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  338916320817998667668332038084489273743
  24787976839542745
  711609
  24787976839542744
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 30323),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      254453319577
      15627
      1290
      15626
      [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 17), (2, 0, Hex.Nat.PrimeCert.small 73)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6904530049a1f86bc7e4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6904530049a1f86bc7e4

/-- Frozen certificate for 338916320817998667668332038084489273743. -/
theorem Hex.PrimalityCorpus.hde612b3beee90d07819f : _root_.Nat.Prime 338916320817998667668332038084489273743 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  338916320817998667668332038084489273743
  15299359873753
  1086881218737
  15299359873752
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 30323),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 205891321 [(2, 0, Hex.Nat.PrimeCert.pock 1715761 [(2, 0, Hex.Nat.PrimeCert.small 2383)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hde612b3beee90d07819f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hde612b3beee90d07819f

/-- Frozen certificate for 339321961936533108018569310546491699399. -/
theorem Hex.PrimalityCorpus.h40915b2a181d9247ce52 : _root_.Nat.Prime 339321961936533108018569310546491699399 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  339321961936533108018569310546491699399
  2048879714959
  48399506017122
  2048879714864
  17
  [(11, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 20347),
   (2, 0, Hex.Nat.PrimeCert.pock 46008719 [(2, 0, Hex.Nat.PrimeCert.small 10567)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h40915b2a181d9247ce52' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h40915b2a181d9247ce52

/-- Frozen certificate for 339321961936533108018569310546491699399. -/
theorem Hex.PrimalityCorpus.hc4e1c1f42d552b01a880 : _root_.Nat.Prime 339321961936533108018569310546491699399 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  339321961936533108018569310546491699399
  5479491594905
  1004963484699
  5479491594904
  [(11, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 20347),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      319290109
      389
      2222
      365
      5
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 67)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc4e1c1f42d552b01a880' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc4e1c1f42d552b01a880

/-- Frozen certificate for 339498083478407318739034480503721151573. -/
theorem Hex.PrimalityCorpus.h9eadaddfc3deb2172def : _root_.Nat.Prime 339498083478407318739034480503721151573 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  339498083478407318739034480503721151573
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      308218806154612612383869834245183
      4109501599
      869101262529
      4109500753
      57
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 3),
       (2, 1, Hex.Nat.PrimeCert.small 13),
       (2, 0, Hex.Nat.PrimeCert.small 151),
       (2, 0, Hex.Nat.PrimeCert.small 86969)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h9eadaddfc3deb2172def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h9eadaddfc3deb2172def

/-- Frozen certificate for 339524808297908403352114178915754310651. -/
theorem Hex.PrimalityCorpus.hbb29d82bf65ae1a36b64 : _root_.Nat.Prime 339524808297908403352114178915754310651 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  339524808297908403352114178915754310651
  12377940584293
  653006072488
  12377940584292
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      8061802470041
      4439
      57675
      4386
      6
      [(3, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 5),
       (2, 0, Hex.Nat.PrimeCert.small 11),
       (3, 0, Hex.Nat.PrimeCert.small 19)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hbb29d82bf65ae1a36b64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hbb29d82bf65ae1a36b64

/-- Frozen certificate for 57896044618658097711785492504343953926634992332820282019728792003956564819949. -/
theorem Hex.PrimalityCorpus.h739c795dac137a70f1b1 : _root_.Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 :=
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

/-- info: 'Hex.PrimalityCorpus.h739c795dac137a70f1b1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h739c795dac137a70f1b1

/-- Frozen certificate for 57965305192312155919369229466438223992904354679076180339330854185187943510811. -/
theorem Hex.PrimalityCorpus.h916f59d749250a2bffce : _root_.Nat.Prime 57965305192312155919369229466438223992904354679076180339330854185187943510811 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  57965305192312155919369229466438223992904354679076180339330854185187943510811
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      74911357542724190520433811030098147196032253940531801405735812203
      37809383955357111027977
      37605789721300330181
      37809383955357111027976
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 1, Hex.Nat.PrimeCert.small 13),
       (2, 0, Hex.Nat.PrimeCert.small 1783),
       (2, 0, Hex.Nat.PrimeCert.small 2297),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          22798298761039
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              422190717797
              [(2,
                0,
                Hex.Nat.PrimeCert.pock3
                  105547679449
                  14117
                  763
                  14116
                  [(17, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 1039)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h916f59d749250a2bffce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h916f59d749250a2bffce

/-- Frozen certificate for 57965305192312155919369229466438223992904354679076180339330854185187943510811. -/
theorem Hex.PrimalityCorpus.hded0ee0c264f7a834916 : _root_.Nat.Prime 57965305192312155919369229466438223992904354679076180339330854185187943510811 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  57965305192312155919369229466438223992904354679076180339330854185187943510811
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      74911357542724190520433811030098147196032253940531801405735812203
      761280618429388886777
      29914299365039600415931
      761280618429388886619
      20
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          559486256102378617681
          3732065
          4868810
          3732059
          [(13, 3, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 227),
           (2, 0, Hex.Nat.PrimeCert.small 2087)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hded0ee0c264f7a834916' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hded0ee0c264f7a834916

/-- Frozen certificate for 58155927171746404856652310417527841235378089361966399939646264838133067545261. -/
theorem Hex.PrimalityCorpus.h58282b043ef439341614 : _root_.Nat.Prime 58155927171746404856652310417527841235378089361966399939646264838133067545261 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  58155927171746404856652310417527841235378089361966399939646264838133067545261
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      16519532003327416143105787119798745242810194598657343663
      [(2, 0, Hex.Nat.PrimeCert.small 2633),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          42695650753280249458840423
          2937902647
          7046012
          2937902646
          [(3, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.pock 870312277 [(2, 0, Hex.Nat.PrimeCert.small 99487)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h58282b043ef439341614' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h58282b043ef439341614

/-- Frozen certificate for 58406655015028475135524921672845911842758636198409572701972165552674893727603. -/
theorem Hex.PrimalityCorpus.h4b59d7d73dfceeb74e22 : _root_.Nat.Prime 58406655015028475135524921672845911842758636198409572701972165552674893727603 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  58406655015028475135524921672845911842758636198409572701972165552674893727603
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      7060584951854969551096193697447432469532740314436249606272135535441
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          65521389679426220778546712114397109034268191485117386843653819
          6141586486153431256379
          1011438013346084611
          6141586486153431256378
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 1471),
           (2, 0, Hex.Nat.PrimeCert.small 2957),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              654203590450481
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  1168220697233
                  [(2, 0, Hex.Nat.PrimeCert.small 4139), (2, 0, Hex.Nat.PrimeCert.small 5233)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h4b59d7d73dfceeb74e22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h4b59d7d73dfceeb74e22

/-- Frozen certificate for 58988068871129626299522615539489014879024228812218716814496185707579940866133. -/
theorem Hex.PrimalityCorpus.h9ae49c2f9bdb52da445f : _root_.Nat.Prime 58988068871129626299522615539489014879024228812218716814496185707579940866133 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  58988068871129626299522615539489014879024228812218716814496185707579940866133
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      1518070579291645688407705143600713234465730010134169457
      358126368154114289
      6581667718718241310
      358126368154114215
      13
      [(3, 3, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 61),
       (2, 0, Hex.Nat.PrimeCert.small 97),
       (2, 0, Hex.Nat.PrimeCert.small 439),
       (2, 0, Hex.Nat.PrimeCert.small 643),
       (2, 0, Hex.Nat.PrimeCert.small 751),
       (2, 0, Hex.Nat.PrimeCert.small 16921)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h9ae49c2f9bdb52da445f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h9ae49c2f9bdb52da445f

/-- Frozen certificate for 59053639098910021439417129069699888351209331320396441448694773779176149874589. -/
theorem Hex.PrimalityCorpus.ha79cdc5b014f15c0b537 : _root_.Nat.Prime 59053639098910021439417129069699888351209331320396441448694773779176149874589 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  59053639098910021439417129069699888351209331320396441448694773779176149874589
  24496785965245421214320182447
  91120403473731989968
  24496785965245421214320182446
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 222148821029 [(2, 0, Hex.Nat.PrimeCert.small 35999), (2, 0, Hex.Nat.PrimeCert.small 81197)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      20257997530179797
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          297911728384997
          15643
          98154
          15617
          3
          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 9739)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha79cdc5b014f15c0b537' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha79cdc5b014f15c0b537

/-- Frozen certificate for 59635472134680750126332383212123220624375629674842127571589138541995188975317. -/
theorem Hex.PrimalityCorpus.h30b2e77954ba151a8ab9 : _root_.Nat.Prime 59635472134680750126332383212123220624375629674842127571589138541995188975317 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  59635472134680750126332383212123220624375629674842127571589138541995188975317
  44677712953456847270525855
  1930557475737601968837882
  44677712953456847270525854
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 97),
   (2, 0, Hex.Nat.PrimeCert.small 131),
   (2, 0, Hex.Nat.PrimeCert.small 1129),
   (2, 0, Hex.Nat.PrimeCert.small 6679),
   (2, 0, Hex.Nat.PrimeCert.pock 990371 [(2, 0, Hex.Nat.PrimeCert.small 1021)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 327408269 [(2, 0, Hex.Nat.PrimeCert.pock 7441097 [(2, 0, Hex.Nat.PrimeCert.small 71549)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h30b2e77954ba151a8ab9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h30b2e77954ba151a8ab9

/-- Frozen certificate for 59783610270248042175634862587885201727596460096960054561164058625739981307083. -/
theorem Hex.PrimalityCorpus.he90b06aece28e7722e29 : _root_.Nat.Prime 59783610270248042175634862587885201727596460096960054561164058625739981307083 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  59783610270248042175634862587885201727596460096960054561164058625739981307083
  19470906983120643736628939
  61229525477807562317476408
  19470906983120643736628926
  2
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 181),
   (2, 0, Hex.Nat.PrimeCert.pock 344759 [(2, 0, Hex.Nat.PrimeCert.small 773)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 9807143 [(2, 0, Hex.Nat.PrimeCert.pock 4903571 [(2, 0, Hex.Nat.PrimeCert.small 70051)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      18052150003
      2587
      4565
      2579
      2
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 19), (2, 0, Hex.Nat.PrimeCert.small 37)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.he90b06aece28e7722e29' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.he90b06aece28e7722e29

/-- Frozen certificate for 59844776178632531294330607122730566758230002515124497965675254832175515702799. -/
theorem Hex.PrimalityCorpus.h26f8c78f0cbce6861366 : _root_.Nat.Prime 59844776178632531294330607122730566758230002515124497965675254832175515702799 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  59844776178632531294330607122730566758230002515124497965675254832175515702799
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      2516092927075838651146338281974500303564498303188885295811
      4881142781574936337
      60272126648753349529
      4881142781574936287
      9
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 3),
       (2, 0, Hex.Nat.PrimeCert.small 5),
       (2, 0, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.small 67),
       (2, 0, Hex.Nat.PrimeCert.small 79),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          2615617588237
          [(2, 0, Hex.Nat.PrimeCert.small 14149), (2, 0, Hex.Nat.PrimeCert.small 16763)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h26f8c78f0cbce6861366' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h26f8c78f0cbce6861366

/-- Frozen certificate for 59964021128713967647876921031552123898529736477448372743135451276976912379387. -/
theorem Hex.PrimalityCorpus.h7e0e3059618e1396903c : _root_.Nat.Prime 59964021128713967647876921031552123898529736477448372743135451276976912379387 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  59964021128713967647876921031552123898529736477448372743135451276976912379387
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      251700642672953397476627628578709105632590086673635160537
      [(2, 0, Hex.Nat.PrimeCert.small 283),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          23168124475445837220664415933490432092261
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              165486603396041694433317256667788800659
              34016431896149
              67372092427
              34016431896148
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 3533),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3
                  4959669901
                  5031
                  294
                  5030
                  [(2, 1, Hex.Nat.PrimeCert.small 2),
                   (3, 1, Hex.Nat.PrimeCert.small 5),
                   (2, 0, Hex.Nat.PrimeCert.small 29)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h7e0e3059618e1396903c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h7e0e3059618e1396903c

/-- Frozen certificate for 59964021128713967647876921031552123898529736477448372743135451276976912379387. -/
theorem Hex.PrimalityCorpus.hce7de9af7b81ea99085d : _root_.Nat.Prime 59964021128713967647876921031552123898529736477448372743135451276976912379387 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  59964021128713967647876921031552123898529736477448372743135451276976912379387
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      251700642672953397476627628578709105632590086673635160537
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          23168124475445837220664415933490432092261
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              165486603396041694433317256667788800659
              34016431896149
              67372092427
              34016431896148
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 3533),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3
                  4959669901
                  5031
                  294
                  5030
                  [(2, 1, Hex.Nat.PrimeCert.small 2),
                   (3, 1, Hex.Nat.PrimeCert.small 5),
                   (2, 0, Hex.Nat.PrimeCert.small 29)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hce7de9af7b81ea99085d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hce7de9af7b81ea99085d
