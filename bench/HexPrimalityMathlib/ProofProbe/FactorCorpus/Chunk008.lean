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

/-- Frozen certificate for 38263153534549020075577499487925562752666468595869529540948441374417978266391745412596275461280463099871108717719333. -/
theorem Hex.PrimalityCorpus.hdf9d35acda44669255e3 : _root_.Nat.Prime 38263153534549020075577499487925562752666468595869529540948441374417978266391745412596275461280463099871108717719333 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  38263153534549020075577499487925562752666468595869529540948441374417978266391745412596275461280463099871108717719333
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      23686560707672368858686244681809072663451939725901163723089398208873813768138380417222638272595838406450057
      49506226423578623063875048971693361
      2197289239593383379289640604201432351
      49506226423578623063875048971693183
      23
      [(5, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 3),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          991275198405251
          200425
          17925
          200424
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 71),
           (2, 0, Hex.Nat.PrimeCert.small 1171)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          3085935954794131337
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              351633540883561
              531889
              157
              531888
              [(7, 2, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  132173
                  [(2, 0, Hex.Nat.PrimeCert.small 173), (2, 0, Hex.Nat.PrimeCert.small 191)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hdf9d35acda44669255e3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hdf9d35acda44669255e3

/-- Frozen certificate for 38465422011343652472203446314607451952968560290041116995353291824545410585731877795425499388389614719761558259005009. -/
theorem Hex.PrimalityCorpus.h8c4a4185b8c1c7507f3c : _root_.Nat.Prime 38465422011343652472203446314607451952968560290041116995353291824545410585731877795425499388389614719761558259005009 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  38465422011343652472203446314607451952968560290041116995353291824545410585731877795425499388389614719761558259005009
  9076615757101952018525595108776788151743
  168932896869055541644036531736906298
  9076615757101952018525595108776788151742
  [(3, 3, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      13986478090508089
      148583
      942209
      148557
      6
      [(7, 2, Hex.Nat.PrimeCert.small 2), (2, 1, Hex.Nat.PrimeCert.small 11), (2, 0, Hex.Nat.PrimeCert.small 89)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      47679839652848580925171
      188715359
      811922
      188715358
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 41),
       (2, 0, Hex.Nat.PrimeCert.small 967),
       (2, 0, Hex.Nat.PrimeCert.small 2161)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8c4a4185b8c1c7507f3c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8c4a4185b8c1c7507f3c

/-- Frozen certificate for 38788441225733943802425445772615571512523936425459840784564285060612329862922317091054361760588949590637092491522237. -/
theorem Hex.PrimalityCorpus.h37be38655b01248d95c0 : _root_.Nat.Prime 38788441225733943802425445772615571512523936425459840784564285060612329862922317091054361760588949590637092491522237 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  38788441225733943802425445772615571512523936425459840784564285060612329862922317091054361760588949590637092491522237
  6136415806363055595611320159065773758923
  394531465272786415236682320836120864
  6136415806363055595611320159065773758922
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      368947102216573603
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          6832353744751363
          [(2, 0, Hex.Nat.PrimeCert.small 569),
           (2, 0, Hex.Nat.PrimeCert.small 1559),
           (2, 0, Hex.Nat.PrimeCert.small 8039)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      4750849228859080630639
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          57473194803647149
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              532159211144881
              23
              809677
              0
              45
              [(7, 3, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 11),
               (2, 0, Hex.Nat.PrimeCert.small 103)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h37be38655b01248d95c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h37be38655b01248d95c0

/-- Frozen certificate for 38788441225733943802425445772615571512523936425459840784564285060612329862922317091054361760588949590637092491522237. -/
theorem Hex.PrimalityCorpus.h593f37dffa2a57b31865 : _root_.Nat.Prime 38788441225733943802425445772615571512523936425459840784564285060612329862922317091054361760588949590637092491522237 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  38788441225733943802425445772615571512523936425459840784564285060612329862922317091054361760588949590637092491522237
  1568783049987447797450134434086482252045845636608657355
  19404332
  1568783049987447797450134434086482252045845636608657354
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      249934850313956819258220721264608154937884134873770893
      9997196521185349903
      2287515931386950
      9997196521185349902
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 26879),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          68745337511779
          160975
          3169
          160974
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 52067)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h593f37dffa2a57b31865' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h593f37dffa2a57b31865

/-- Frozen certificate for 38928991131374055859740224319372010011732589576351224110936400141819050841949478139481224289802065041234891670212941. -/
theorem Hex.PrimalityCorpus.hf7493b89d81477f25a17 : _root_.Nat.Prime 38928991131374055859740224319372010011732589576351224110936400141819050841949478139481224289802065041234891670212941 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  38928991131374055859740224319372010011732589576351224110936400141819050841949478139481224289802065041234891670212941
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      4839695520471890541690092012977958027618371695550955188714363052639238277001650760718981976393
      62772941673623572338527942217035
      1056358518469775343901920549104
      62772941673623572338527942217034
      [(5, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 31),
       (2, 0, Hex.Nat.PrimeCert.small 4111),
       (2, 0, Hex.Nat.PrimeCert.pock 1646221 [(2, 0, Hex.Nat.PrimeCert.small 27437)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          28516817585765045591
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              46748881288139419
              694573
              75709
              694572
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 1, Hex.Nat.PrimeCert.small 3),
               (2, 0, Hex.Nat.PrimeCert.small 30869)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hf7493b89d81477f25a17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hf7493b89d81477f25a17

/-- Frozen certificate for 38974594251204624085855238773686039048319100907127804618371165464180174835720397017559908772302917069155529585296027. -/
theorem Hex.PrimalityCorpus.hbbbf9c1f82123de3ea41 : _root_.Nat.Prime 38974594251204624085855238773686039048319100907127804618371165464180174835720397017559908772302917069155529585296027 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  38974594251204624085855238773686039048319100907127804618371165464180174835720397017559908772302917069155529585296027
  1173278336845704547615148227637194836023
  46129056313370587849534911428740505512
  1173278336845704547615148227637194836022
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 13),
   (3, 0, Hex.Nat.PrimeCert.small 41),
   (2, 0, Hex.Nat.PrimeCert.small 109),
   (2, 0, Hex.Nat.PrimeCert.pock 1754561 [(2, 0, Hex.Nat.PrimeCert.small 5483)]),
   (2, 0, Hex.Nat.PrimeCert.pock 29118053 [(2, 1, Hex.Nat.PrimeCert.small 43), (2, 0, Hex.Nat.PrimeCert.small 127)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      109489888089969167567
      [(2, 0, Hex.Nat.PrimeCert.small 97),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          1631646733
          [(2, 0, Hex.Nat.PrimeCert.small 281), (2, 0, Hex.Nat.PrimeCert.small 2797)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hbbbf9c1f82123de3ea41' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hbbbf9c1f82123de3ea41

/-- Frozen certificate for 39113455128659980860479509291208529756328098304243338347459203847492004209853949553962069239270607720082915642079523. -/
theorem Hex.PrimalityCorpus.h8eb10f7aa6a6daff79ae : _root_.Nat.Prime 39113455128659980860479509291208529756328098304243338347459203847492004209853949553962069239270607720082915642079523 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  39113455128659980860479509291208529756328098304243338347459203847492004209853949553962069239270607720082915642079523
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      12323079750680523270472435189416676041691272307575090846710524211560177759878370999988049539782800163857251305003
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          25070372922051868272144187880842704899596604428246518666934903060562802248677924727722324864279751069
          1218541862331294092441514054394807
          530270121166999943011882169711670
          1218541862331294092441514054394805
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 21139),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              20942479580713
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  872603315863
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock3
                      145433885977
                      11743
                      814
                      11742
                      [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 1181)])])]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3
              2745644405220643
              52625
              9049
              52624
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.pock 194749 [(2, 0, Hex.Nat.PrimeCert.small 16229)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8eb10f7aa6a6daff79ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8eb10f7aa6a6daff79ae

/-- Frozen certificate for 39132875132198844600252876265576177977680335425105386946776391102316827061380289463549716393300264469913216837301889. -/
theorem Hex.PrimalityCorpus.hf98b1636e9322b8ecdfe : _root_.Nat.Prime 39132875132198844600252876265576177977680335425105386946776391102316827061380289463549716393300264469913216837301889 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  39132875132198844600252876265576177977680335425105386946776391102316827061380289463549716393300264469913216837301889
  146442203398230150567069149856682408237
  376298073377001751494790403067021449068
  146442203398230150567069149856682408226
  2
  [(3, 6, Hex.Nat.PrimeCert.small 2),
   (2, 1, Hex.Nat.PrimeCert.small 11),
   (2, 0, Hex.Nat.PrimeCert.small 103),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      2193761610636587
      35699
      983373
      35588
      20
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 16699)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      65158021153672877
      2383073
      18370
      2383072
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 67), (2, 0, Hex.Nat.PrimeCert.small 4969)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hf98b1636e9322b8ecdfe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hf98b1636e9322b8ecdfe

/-- Frozen certificate for 39282187476716505336850721004780027393893614195777338302452245346939777046158314189153143181776521664156766652223911. -/
theorem Hex.PrimalityCorpus.h6c117f216b79dd5d130a : _root_.Nat.Prime 39282187476716505336850721004780027393893614195777338302452245346939777046158314189153143181776521664156766652223911 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  39282187476716505336850721004780027393893614195777338302452245346939777046158314189153143181776521664156766652223911
  136338406804900968728801163983449833295
  3230188638487136563202997453656422194475
  136338406804900968728801163983449833200
  23
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 113),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      6425754172867
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          50998048991
          6327
          713
          6326
          [(7, 0, Hex.Nat.PrimeCert.small 2), (2, 1, Hex.Nat.PrimeCert.small 7), (2, 0, Hex.Nat.PrimeCert.small 61)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      53695308939851560212499
      348042047
      90530
      348042046
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 2089),
       (2, 0, Hex.Nat.PrimeCert.pock 130343 [(2, 0, Hex.Nat.PrimeCert.small 65171)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h6c117f216b79dd5d130a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h6c117f216b79dd5d130a

/-- Frozen certificate for 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319. -/
theorem Hex.PrimalityCorpus.h353230e6524ae7c69f84 : _root_.Nat.Prime 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 :=
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

/-- info: 'Hex.PrimalityCorpus.h353230e6524ae7c69f84' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h353230e6524ae7c69f84

/-- Frozen certificate for 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439. -/
theorem Hex.PrimalityCorpus.h5c54522e9b432fbfc907 : _root_.Nat.Prime 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439 :=
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

/-- info: 'Hex.PrimalityCorpus.h5c54522e9b432fbfc907' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h5c54522e9b432fbfc907

/-- Frozen certificate for 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439. -/
theorem Hex.PrimalityCorpus.heeab2fb1b28340d543a5 : _root_.Nat.Prime 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439 :=
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

/-- info: 'Hex.PrimalityCorpus.heeab2fb1b28340d543a5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.heeab2fb1b28340d543a5

/-- Frozen certificate for 6740565740260157005294296552000378713458967589728908113103172095488889011284834500460017980438377700546713551779481139455569782132169350234663462748017441. -/
theorem Hex.PrimalityCorpus.hce4d6e567e86df6d1381 : _root_.Nat.Prime 6740565740260157005294296552000378713458967589728908113103172095488889011284834500460017980438377700546713551779481139455569782132169350234663462748017441 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  6740565740260157005294296552000378713458967589728908113103172095488889011284834500460017980438377700546713551779481139455569782132169350234663462748017441
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      19142774713069802728830015099308510108240485788214292242465203189049949093492085589528492024086638753839680689237
      12879188277426291871447556245769833859
      42077021745991283916761719048621879351
      12879188277426291871447556245769833845
      2
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 13),
       (2, 0, Hex.Nat.PrimeCert.small 197),
       (2, 0, Hex.Nat.PrimeCert.pock 29938999 [(2, 0, Hex.Nat.PrimeCert.small 5651)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          2197337922751
          116081
          181
          116080
          [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 2, Hex.Nat.PrimeCert.small 5), (2, 0, Hex.Nat.PrimeCert.small 311)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          22380060358247
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              31461037
              [(2, 0, Hex.Nat.PrimeCert.small 43), (2, 0, Hex.Nat.PrimeCert.small 3209)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hce4d6e567e86df6d1381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hce4d6e567e86df6d1381

/-- Frozen certificate for 7091468326161682575538845180377201793099992074941075493341359813985390421588465653499270635776940082463506783778005346995436029925509918350271389955855231. -/
theorem Hex.PrimalityCorpus.hbdcf6c7ed1c94de16803 : _root_.Nat.Prime 7091468326161682575538845180377201793099992074941075493341359813985390421588465653499270635776940082463506783778005346995436029925509918350271389955855231 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  7091468326161682575538845180377201793099992074941075493341359813985390421588465653499270635776940082463506783778005346995436029925509918350271389955855231
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      1218840815808028392934626268929083602433365731843228518364064465903912186720613149945987510390525409787932438070343
      72743699121924966870724892497859396625
      198314599495876220462658248960542942536
      72743699121924966870724892497859396614
      3
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 1, Hex.Nat.PrimeCert.small 11),
       (2, 0, Hex.Nat.PrimeCert.small 89123),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          18411637998211
          39579
          10869
          39577
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 14551)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          139599403562421619
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              6437840291
              [(2, 0, Hex.Nat.PrimeCert.small 7309), (2, 0, Hex.Nat.PrimeCert.small 12583)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hbdcf6c7ed1c94de16803' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hbdcf6c7ed1c94de16803

/-- Frozen certificate for 7329455408318349479478083581181287929773390775871978415275891608700170038095846579717414861032774269599340170707633109673791935756471909830634953858116813. -/
theorem Hex.PrimalityCorpus.hbb824f9ea8e873a894a3 : _root_.Nat.Prime 7329455408318349479478083581181287929773390775871978415275891608700170038095846579717414861032774269599340170707633109673791935756471909830634953858116813 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  7329455408318349479478083581181287929773390775871978415275891608700170038095846579717414861032774269599340170707633109673791935756471909830634953858116813
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      59232064449232374910317168364847365265584280163650160931378755121954620487697660099949668515761146856215815359340916250041148971094849353
      2264604988874103331440012801827570468758125449
      6414780052811671195149681261841408175489836935
      2264604988874103331440012801827570468758125437
      2
      [(3, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 13),
       (2, 0, Hex.Nat.PrimeCert.small 1409),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          109911251606928287
          1094731
          113266
          1094730
          [(5, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 59),
           (2, 0, Hex.Nat.PrimeCert.small 5903)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          133409287932499278678379
          [(2, 0, Hex.Nat.PrimeCert.small 7649),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              1524293011
              [(2, 0, Hex.Nat.PrimeCert.small 101), (2, 0, Hex.Nat.PrimeCert.small 2749)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hbb824f9ea8e873a894a3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hbb824f9ea8e873a894a3

/-- Frozen certificate for 7769068362092178164622653439836630683980168213894134017771943657385414463526248501772153084817168121527238746007129562164546819979672131117483568764141837. -/
theorem Hex.PrimalityCorpus.hd63f2595b4440f9c8223 : _root_.Nat.Prime 7769068362092178164622653439836630683980168213894134017771943657385414463526248501772153084817168121527238746007129562164546819979672131117483568764141837 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  7769068362092178164622653439836630683980168213894134017771943657385414463526248501772153084817168121527238746007129562164546819979672131117483568764141837
  7837225292231729083205054872226456056296014560720425
  14091933709219770474100732843333626874982789493672
  7837225292231729083205054872226456056296014560720424
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 191),
   (2, 0, Hex.Nat.PrimeCert.small 853),
   (3, 0, Hex.Nat.PrimeCert.small 3701),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      5406616722526289423
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          399802526479
          21805
          19
          21804
          [(3, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 199),
           (2, 0, Hex.Nat.PrimeCert.small 257)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1273201435781952430504243
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          48370239183266941361
          4113461
          80103
          4113460
          [(3, 3, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 137),
           (2, 0, Hex.Nat.PrimeCert.small 7927)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd63f2595b4440f9c8223' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd63f2595b4440f9c8223

/-- Frozen certificate for 8081949555828043025927653170626481807901260451231556083734069617048243554436140607044031194803126607228969513833171121479465595151170241932135708519160137. -/
theorem Hex.PrimalityCorpus.h16559913697c9d41e364 : _root_.Nat.Prime 8081949555828043025927653170626481807901260451231556083734069617048243554436140607044031194803126607228969513833171121479465595151170241932135708519160137 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  8081949555828043025927653170626481807901260451231556083734069617048243554436140607044031194803126607228969513833171121479465595151170241932135708519160137
  1918825823052976746810695421557919010006343579768241567
  1643810005170348714681370340582753784199125747
  1918825823052976746810695421557919010006343579768241566
  [(5, 2, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      279247081433
      80657
      45
      80656
      [(3, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 6907)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      21434014970088695419
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          288300849677033
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              973989357017
              [(2, 0, Hex.Nat.PrimeCert.small 2917), (2, 0, Hex.Nat.PrimeCert.small 78307)])])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      32744254013674659962381
      6925347
      331724336
      6925155
      32
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 7),
       (2, 0, Hex.Nat.PrimeCert.small 17),
       (2, 0, Hex.Nat.PrimeCert.small 14759)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h16559913697c9d41e364' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h16559913697c9d41e364

/-- Frozen certificate for 8095732221855367088470689038568063625338535409090280480559010269940202911400929358069438125961637012288429972711098840020250212436797201218756681538059811. -/
theorem Hex.PrimalityCorpus.h5f8bfff3abb8b523024e : _root_.Nat.Prime 8095732221855367088470689038568063625338535409090280480559010269940202911400929358069438125961637012288429972711098840020250212436797201218756681538059811 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  8095732221855367088470689038568063625338535409090280480559010269940202911400929358069438125961637012288429972711098840020250212436797201218756681538059811
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      463993473593302884620898007389205891504725716822479334362877924356895923415659043320815726577234392436205610474361383664354798066175286857921
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          55537434816182479470375447187560067730168389798776681026465985513065023205569759147889111079034372306932395107261
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              1520460234443111395509677609575507112282725407129574799296132329490601498206498303
              [(2,
                0,
                Hex.Nat.PrimeCert.pock3
                  420248821017996516171829079484661998972560919604636484050893402291487423495439
                  1569415046389559493655986245
                  109746684478421899197141
                  1569415046389559493655986244
                  [(13, 0, Hex.Nat.PrimeCert.small 2),
                   (2, 0, Hex.Nat.PrimeCert.pock 107927 [(2, 0, Hex.Nat.PrimeCert.small 593)]),
                   (2, 0, Hex.Nat.PrimeCert.pock 333049 [(2, 0, Hex.Nat.PrimeCert.small 13877)]),
                   (2, 0, Hex.Nat.PrimeCert.pock 11088923 [(2, 0, Hex.Nat.PrimeCert.small 6007)]),
                   (2,
                    0,
                    Hex.Nat.PrimeCert.pock3
                      1735741099
                      1523
                      323
                      1522
                      [(2, 0, Hex.Nat.PrimeCert.small 2),
                       (2, 1, Hex.Nat.PrimeCert.small 3),
                       (2, 0, Hex.Nat.PrimeCert.small 7),
                       (2, 0, Hex.Nat.PrimeCert.small 13)])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h5f8bfff3abb8b523024e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h5f8bfff3abb8b523024e

/-- Frozen certificate for 8108676961281079787991974099820077367358386512499408615121421578253622702700471292440815660983243280840512595191713368356377953534259769343135363356886143. -/
theorem Hex.PrimalityCorpus.hbe1cdf30fe2d7b55cd14 : _root_.Nat.Prime 8108676961281079787991974099820077367358386512499408615121421578253622702700471292440815660983243280840512595191713368356377953534259769343135363356886143 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  8108676961281079787991974099820077367358386512499408615121421578253622702700471292440815660983243280840512595191713368356377953534259769343135363356886143
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      297621683145827857168187121931880800681695026569125769854281995015915036811301758174923063456422220806209519929245217
      140229054715970422206473498005496741709
      200541390661451845040142493274359566621
      140229054715970422206473498005496741703
      [(5, 4, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 1171),
       (2, 0, Hex.Nat.PrimeCert.small 9733),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 962867 [(2, 0, Hex.Nat.PrimeCert.pock 481433 [(2, 0, Hex.Nat.PrimeCert.small 8597)])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          2452987730620224163930793
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              16138077175133053710071
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  1613807717513305371007
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      7641786314711033
                      [(2,
                        0,
                        Hex.Nat.PrimeCert.pock3
                          86838480848989
                          137663
                          713
                          137662
                          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 61681)])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hbe1cdf30fe2d7b55cd14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hbe1cdf30fe2d7b55cd14

/-- Frozen certificate for 8260158602607665759574305241821466585195378373324789045828236845420042177041608528430613438210205449159474438685394283494568683363853107333036526956987603. -/
theorem Hex.PrimalityCorpus.hd97fadb11a2d00444808 : _root_.Nat.Prime 8260158602607665759574305241821466585195378373324789045828236845420042177041608528430613438210205449159474438685394283494568683363853107333036526956987603 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  8260158602607665759574305241821466585195378373324789045828236845420042177041608528430613438210205449159474438685394283494568683363853107333036526956987603
  7440026424760025679277813527470846457634193901652525629
  2047427878376702484601642664714575350356973
  7440026424760025679277813527470846457634193901652525628
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.pock 1984843909 [(2, 0, Hex.Nat.PrimeCert.small 71), (2, 0, Hex.Nat.PrimeCert.small 2687)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 47189219317 [(2, 0, Hex.Nat.PrimeCert.small 1307), (2, 0, Hex.Nat.PrimeCert.small 6701)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      68751114566941
      1543
      21723
      1485
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 1, Hex.Nat.PrimeCert.small 3),
       (3, 0, Hex.Nat.PrimeCert.small 5),
       (3, 0, Hex.Nat.PrimeCert.small 13),
       (2, 0, Hex.Nat.PrimeCert.small 17)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      3487353711422248565957
      64719565
      184882
      64719564
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 1949), (2, 0, Hex.Nat.PrimeCert.small 12457)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd97fadb11a2d00444808' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd97fadb11a2d00444808

/-- Frozen certificate for 8369282364814061273453451793453705800361942767811708907092338470261571449756321377673456362598367922240474705494854074054762465251551160193550804518199017. -/
theorem Hex.PrimalityCorpus.hc26b83707a54e8c4c009 : _root_.Nat.Prime 8369282364814061273453451793453705800361942767811708907092338470261571449756321377673456362598367922240474705494854074054762465251551160193550804518199017 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  8369282364814061273453451793453705800361942767811708907092338470261571449756321377673456362598367922240474705494854074054762465251551160193550804518199017
  141305301796944446284459474676861156212742996814984211
  87735235242965723371336640569526551936294451920
  141305301796944446284459474676861156212742996814984210
  [(5, 2, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 2141),
   (2, 0, Hex.Nat.PrimeCert.small 5281),
   (2, 0, Hex.Nat.PrimeCert.small 10253),
   (2, 0, Hex.Nat.PrimeCert.pock 89762147 [(2, 0, Hex.Nat.PrimeCert.small 1307), (2, 0, Hex.Nat.PrimeCert.small 1493)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      3732519365699
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 919), (2, 0, Hex.Nat.PrimeCert.small 1429)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      702866766718897214543
      20632031
      3072093
      20632030
      [(5, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          5347789
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              445649
              [(2, 0, Hex.Nat.PrimeCert.small 23), (2, 0, Hex.Nat.PrimeCert.small 173)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc26b83707a54e8c4c009' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc26b83707a54e8c4c009

/-- Frozen certificate for 8402079676891770358081919740175322987009862152285195508007390665983755037102308968264385553990041331884215788569301284688599060734526954906058298607258587. -/
theorem Hex.PrimalityCorpus.h1db23d50069a4188f25d : _root_.Nat.Prime 8402079676891770358081919740175322987009862152285195508007390665983755037102308968264385553990041331884215788569301284688599060734526954906058298607258587 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  8402079676891770358081919740175322987009862152285195508007390665983755037102308968264385553990041331884215788569301284688599060734526954906058298607258587
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      6580300784323984741718307896887663997289447852965464705094778887948645897514926393051764914808846009951210546038577489
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          4970330351518645608234901130010942698136742148678233531805750756612826770539255929689575681
          848962241445338591032976417295
          4620815057384184983329483938315
          848962241445338591032976417273
          4
          [(7, 7, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 23),
           (2, 0, Hex.Nat.PrimeCert.small 2269),
           (2, 0, Hex.Nat.PrimeCert.small 22807),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              2406843635194356667
              [(2, 0, Hex.Nat.PrimeCert.small 31),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  367076081
                  [(2, 0, Hex.Nat.PrimeCert.small 739), (2, 0, Hex.Nat.PrimeCert.small 887)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h1db23d50069a4188f25d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h1db23d50069a4188f25d

/-- Frozen certificate for 8415712166559782785009936268516112112797478297238434800925165774928262229121436613752777257969149780915400997171006833089375404704915193810391962933641021. -/
theorem Hex.PrimalityCorpus.h714b594862cd7336ce80 : _root_.Nat.Prime 8415712166559782785009936268516112112797478297238434800925165774928262229121436613752777257969149780915400997171006833089375404704915193810391962933641021 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  8415712166559782785009936268516112112797478297238434800925165774928262229121436613752777257969149780915400997171006833089375404704915193810391962933641021
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      44579469046296126628932812101473207505018954853471950423377295131519558370173941168305844146462282979740443887970160149853667786338145957253903818909
      1176096236360009075494904059666575076061322562367753
      62825006803975989989246590404043578026937494700
      1176096236360009075494904059666575076061322562367752
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 127144001 [(2, 0, Hex.Nat.PrimeCert.small 23), (2, 0, Hex.Nat.PrimeCert.small 691)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          52338963581
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              2616948179
              [(2, 0, Hex.Nat.PrimeCert.small 211), (2, 0, Hex.Nat.PrimeCert.small 4723)])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          209167078817443
          7823
          61261
          7791
          2
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 73), (2, 0, Hex.Nat.PrimeCert.small 283)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          106982282889232073
          1179799
          140649
          1179798
          [(3, 2, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 157),
           (2, 0, Hex.Nat.PrimeCert.small 491)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h714b594862cd7336ce80' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h714b594862cd7336ce80

/-- Frozen certificate for 8415712166559782785009936268516112112797478297238434800925165774928262229121436613752777257969149780915400997171006833089375404704915193810391962933641021. -/
theorem Hex.PrimalityCorpus.hfc076b5f656ce7cffcda : _root_.Nat.Prime 8415712166559782785009936268516112112797478297238434800925165774928262229121436613752777257969149780915400997171006833089375404704915193810391962933641021 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  8415712166559782785009936268516112112797478297238434800925165774928262229121436613752777257969149780915400997171006833089375404704915193810391962933641021
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      44579469046296126628932812101473207505018954853471950423377295131519558370173941168305844146462282979740443887970160149853667786338145957253903818909
      62513487977770018888367688216051744100971104522457
      17725382456226180327739630775929337137764537690884
      62513487977770018888367688216051744100971104522455
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          209167078817443
          7823
          61261
          7791
          2
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 73), (2, 0, Hex.Nat.PrimeCert.small 283)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          106982282889232073
          1179799
          140649
          1179798
          [(3, 2, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 157),
           (2, 0, Hex.Nat.PrimeCert.small 491)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          396177180690164333
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              38480645771
              9235
              805
              9234
              [(2, 0, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 7),
               (2, 0, Hex.Nat.PrimeCert.small 349)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hfc076b5f656ce7cffcda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hfc076b5f656ce7cffcda

/-- Frozen certificate for 8826903346870273214484765959616693794541506684136501637756022555100155698924960264191697963086636800204315868822299347135474583432968463295353626572646051. -/
theorem Hex.PrimalityCorpus.hc2d1ef6a31de51ff51dc : _root_.Nat.Prime 8826903346870273214484765959616693794541506684136501637756022555100155698924960264191697963086636800204315868822299347135474583432968463295353626572646051 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  8826903346870273214484765959616693794541506684136501637756022555100155698924960264191697963086636800204315868822299347135474583432968463295353626572646051
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      162978067877330916239635141660701672275173318425470120159487311481284340976721356485054587147152864329011394353
      905763200262273197246470165205020806093
      82457652325566495347314855498382
      905763200262273197246470165205020806092
      [(3, 3, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 637883 [(2, 0, Hex.Nat.PrimeCert.small 23), (2, 0, Hex.Nat.PrimeCert.small 283)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          158368361
          [(2, 0, Hex.Nat.PrimeCert.pock 3959209 [(2, 0, Hex.Nat.PrimeCert.small 4999)])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          603644113
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              4191973
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  349331
                  [(2, 0, Hex.Nat.PrimeCert.small 181), (2, 0, Hex.Nat.PrimeCert.small 193)])])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          1018881553027573
          97655
          120919
          97650
          2
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (5, 2, Hex.Nat.PrimeCert.small 3),
           (2, 0, Hex.Nat.PrimeCert.small 601)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc2d1ef6a31de51ff51dc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc2d1ef6a31de51ff51dc

/-- Frozen certificate for 9145724578212729510637561582304292642543985087400701703788070676882074582300129320788125921305009099616295926780748504958314812675387426543697035578992521. -/
theorem Hex.PrimalityCorpus.h8d9fe62f5e2ee77469ef : _root_.Nat.Prime 9145724578212729510637561582304292642543985087400701703788070676882074582300129320788125921305009099616295926780748504958314812675387426543697035578992521 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  9145724578212729510637561582304292642543985087400701703788070676882074582300129320788125921305009099616295926780748504958314812675387426543697035578992521
  894935646000877648485218444763357426746991040368835
  1645895067533338930846535030461447773749320801774155
  894935646000877648485218444763357426746991040368827
  [(3, 2, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 32993),
   (2, 0, Hex.Nat.PrimeCert.small 34297),
   (2, 0, Hex.Nat.PrimeCert.pock 189380071 [(2, 0, Hex.Nat.PrimeCert.small 233), (2, 0, Hex.Nat.PrimeCert.small 821)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      14091100957006649
      108229
      1982922
      108155
      18
      [(3, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 7451)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      68999486805285389
      97395705
      11
      97395704
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 13458307 [(2, 0, Hex.Nat.PrimeCert.small 60623)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8d9fe62f5e2ee77469ef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8d9fe62f5e2ee77469ef

/-- Frozen certificate for 9235125673264905925184926628583001815881495091206119539391298310816982656457897439422390956653379367814108221616492936170961818950917891772907620178181869. -/
theorem Hex.PrimalityCorpus.ha9d83e20f9a9b6dd0ce8 : _root_.Nat.Prime 9235125673264905925184926628583001815881495091206119539391298310816982656457897439422390956653379367814108221616492936170961818950917891772907620178181869 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  9235125673264905925184926628583001815881495091206119539391298310816982656457897439422390956653379367814108221616492936170961818950917891772907620178181869
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      8889501483786889817302894523777058127346511454537093342300482573360579271906122630627461922757852029370454138976623
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          105506781093231777230754970814488217096120494581538341691946582201128034850881154824816305511670618618104281
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              4617704817896309930439605256155769586854653053241567914554299944154210317262383
              [(2,
                0,
                Hex.Nat.PrimeCert.pock3Sieve
                  36648450935684999447933375048855314181386135343187046940907142413922304105257
                  422674369262239104626837
                  322803910804510078120624097
                  422674369262239104623782
                  42
                  [(5, 2, Hex.Nat.PrimeCert.small 2),
                   (2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      16513799
                      [(2, 1, Hex.Nat.PrimeCert.small 61), (2, 0, Hex.Nat.PrimeCert.small 317)]),
                   (2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      57030402726468343
                      [(2,
                        0,
                        Hex.Nat.PrimeCert.pock
                          15306066217517
                          [(2,
                            0,
                            Hex.Nat.PrimeCert.pock
                              7233490651
                              [(2, 0, Hex.Nat.PrimeCert.small 71), (2, 0, Hex.Nat.PrimeCert.small 39953)])])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.ha9d83e20f9a9b6dd0ce8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.ha9d83e20f9a9b6dd0ce8

/-- Frozen certificate for 9493342787348848248814100589378034086621661102152365095219325456748724175586191180347701741555935385086135434379808223297558276923864974803820665176866743. -/
theorem Hex.PrimalityCorpus.h8dcba55085c912921686 : _root_.Nat.Prime 9493342787348848248814100589378034086621661102152365095219325456748724175586191180347701741555935385086135434379808223297558276923864974803820665176866743 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  9493342787348848248814100589378034086621661102152365095219325456748724175586191180347701741555935385086135434379808223297558276923864974803820665176866743
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      5667852968532269991912483487129729251988794904274862201936795124608282842546310105426375928348513612162316294754982259023826057012019019
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          149588222947877851146433758464664215788596009904922741051474975631693777967248919971150158570451893
          68210894571922875788802563782893607055
          61556530183024065698296
          68210894571922875788802563782893607054
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              1992883
              [(2, 0, Hex.Nat.PrimeCert.pock 332147 [(2, 0, Hex.Nat.PrimeCert.small 9769)])]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              105224429881
              [(2, 0, Hex.Nat.PrimeCert.small 6143), (2, 0, Hex.Nat.PrimeCert.small 47581)]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              41556432990964329337
              [(2, 0, Hex.Nat.PrimeCert.small 881),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  2812122323
                  [(2, 0, Hex.Nat.PrimeCert.small 223), (2, 0, Hex.Nat.PrimeCert.small 8969)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h8dcba55085c912921686' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h8dcba55085c912921686

/-- Frozen certificate for 9606824415276783753504458889690064022064334681361972041257092383741148218073771687604578048614449378954783570277651674764139753794801194661926536049206401. -/
theorem Hex.PrimalityCorpus.hd569a3291d9beae2b315 : _root_.Nat.Prime 9606824415276783753504458889690064022064334681361972041257092383741148218073771687604578048614449378954783570277651674764139753794801194661926536049206401 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  9606824415276783753504458889690064022064334681361972041257092383741148218073771687604578048614449378954783570277651674764139753794801194661926536049206401
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      4711767891593318073025406200086784907686847354518975209235839011703534155955595432365534623521613355438866836282667938682518867
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          102737493280485767670600336539459185815288579486571063753262280218888193712443927944290015367109487
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              133030949192965473785728240647666582250107440509409987390454742627643480991689
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  551081257722898901433033886392705919277503735316946307
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock3
                      373353402123098144374790033598985160807
                      205248403144331
                      9061711075
                      205248403144330
                      [(5, 0, Hex.Nat.PrimeCert.small 2),
                       (2,
                        0,
                        Hex.Nat.PrimeCert.pock3
                          71764548615413
                          21383
                          1822
                          21382
                          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 35083)])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd569a3291d9beae2b315' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd569a3291d9beae2b315

/-- Frozen certificate for 9716686159105215918133309965282703854591427666210402552069818638115683917869024508113703183853195745722971931275144642877646218104961984113510988379251287. -/
theorem Hex.PrimalityCorpus.h823586e2e450be5299ab : _root_.Nat.Prime 9716686159105215918133309965282703854591427666210402552069818638115683917869024508113703183853195745722971931275144642877646218104961984113510988379251287 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  9716686159105215918133309965282703854591427666210402552069818638115683917869024508113703183853195745722971931275144642877646218104961984113510988379251287
  37129067976458319265066006056926350593733841442490021
  192350827745438565339195234998961642908061221696
  37129067976458319265066006056926350593733841442490020
  [(3, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      15436221700849
      32447
      5918
      32446
      [(7, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 37), (2, 0, Hex.Nat.PrimeCert.small 61)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      262499406466523969
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          5688700729597
          17505
          30888
          17497
          2
          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 2399)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      19610909310422424296639
      5610013
      24586245
      5609995
      2
      [(7, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 199), (2, 0, Hex.Nat.PrimeCert.small 50177)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h823586e2e450be5299ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h823586e2e450be5299ab

/-- Frozen certificate for 9954863366424261644357326429984918190614433900947707648764120324121306520490745888468397394805242124586347959960310579248986211092877959844774656822535549. -/
theorem Hex.PrimalityCorpus.hd04c4e359b0f7d9af3c8 : _root_.Nat.Prime 9954863366424261644357326429984918190614433900947707648764120324121306520490745888468397394805242124586347959960310579248986211092877959844774656822535549 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  9954863366424261644357326429984918190614433900947707648764120324121306520490745888468397394805242124586347959960310579248986211092877959844774656822535549
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      1363164365541745261180825732848514014100303206053076469008518826371766298725962214812421090972452184806385516247203075046338670727
      36472854339366393781568494873847745693510417909
      1999149345687125771930241053076254966
      36472854339366393781568494873847745693510417908
      [(5, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 753937 [(2, 0, Hex.Nat.PrimeCert.small 113), (2, 0, Hex.Nat.PrimeCert.small 139)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          69812659997
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              286117459
              [(2, 0, Hex.Nat.PrimeCert.small 839), (2, 0, Hex.Nat.PrimeCert.small 5167)])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          3330565398007
          3119
          140561
          2933
          29
          [(3, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 1721)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          52664660708958877
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              22053878018827
              [(2, 0, Hex.Nat.PrimeCert.small 3637), (2, 0, Hex.Nat.PrimeCert.small 30941)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd04c4e359b0f7d9af3c8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd04c4e359b0f7d9af3c8

/-- Frozen certificate for 10010306706404997773015893455817820376647491999253846070172787476469380200663988992449133250475576167667351014492076422069272095415707732267013941288094167. -/
theorem Hex.PrimalityCorpus.h1cadb2a629ddb5bf6fca : _root_.Nat.Prime 10010306706404997773015893455817820376647491999253846070172787476469380200663988992449133250475576167667351014492076422069272095415707732267013941288094167 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  10010306706404997773015893455817820376647491999253846070172787476469380200663988992449133250475576167667351014492076422069272095415707732267013941288094167
  2546117696514552131761961139060058646146966749803361
  1096867567612954820039133101892399560482356409232870
  2546117696514552131761961139060058646146966749803359
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 131),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      556190281711
      12169
      6031
      12167
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 5),
       (2, 0, Hex.Nat.PrimeCert.small 7),
       (2, 0, Hex.Nat.PrimeCert.small 97)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      483532612587368249
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          1655437019
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              7735687
              [(2, 0, Hex.Nat.PrimeCert.small 67), (2, 0, Hex.Nat.PrimeCert.small 2749)])])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      30316644975794876087
      21643499
      22698
      21643498
      [(5, 0, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 12921049 [(2, 0, Hex.Nat.PrimeCert.small 31), (2, 0, Hex.Nat.PrimeCert.small 827)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h1cadb2a629ddb5bf6fca' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h1cadb2a629ddb5bf6fca

/-- Frozen certificate for 10085956325382758296537844116857748906648679250641300839209930866168332673484446382629860905879317648250015023001074281865320119669455472630137866475884471. -/
theorem Hex.PrimalityCorpus.h83592b3893ad26090d67 : _root_.Nat.Prime 10085956325382758296537844116857748906648679250641300839209930866168332673484446382629860905879317648250015023001074281865320119669455472630137866475884471 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  10085956325382758296537844116857748906648679250641300839209930866168332673484446382629860905879317648250015023001074281865320119669455472630137866475884471
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      124400851666659446129245415470065439253609061950246491888160008962158431708868021598110226918265830099689
      187889600619653190571895090187720701
      3315789930342096128576148476224047
      187889600619653190571895090187720700
      [(3, 2, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 83),
       (2, 0, Hex.Nat.PrimeCert.small 1093),
       (2, 0, Hex.Nat.PrimeCert.small 69473),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          274248217723
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              862415779
              [(2, 0, Hex.Nat.PrimeCert.small 811), (2, 0, Hex.Nat.PrimeCert.small 3617)])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          9905013380029
          53021
          2545
          53020
          [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 11027)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h83592b3893ad26090d67' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h83592b3893ad26090d67

/-- Frozen certificate for 10133471647181947579896384650266844060713849090766027760095687469597152104840850612898432794360461807067553923683341850211950624196278029816845868121453607. -/
theorem Hex.PrimalityCorpus.haa1e7727492f9b40c020 : _root_.Nat.Prime 10133471647181947579896384650266844060713849090766027760095687469597152104840850612898432794360461807067553923683341850211950624196278029816845868121453607 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  10133471647181947579896384650266844060713849090766027760095687469597152104840850612898432794360461807067553923683341850211950624196278029816845868121453607
  16059049624798146041337717045143151895520877299554513
  36304844930463693486113342554881605619084703813770
  16059049624798146041337717045143151895520877299554512
  [(5, 0, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      3629127755347981
      1013635
      170
      1013634
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 816401 [(2, 0, Hex.Nat.PrimeCert.small 13), (2, 0, Hex.Nat.PrimeCert.small 157)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      1073581394361096667
      227007
      2880294
      226956
      6
      [(2, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 215851 [(2, 0, Hex.Nat.PrimeCert.small 1439)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      1516053783519900773
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          136384831191067
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              22730805198511
              [(5, 0, Hex.Nat.PrimeCert.small 5),
               (2, 0, Hex.Nat.PrimeCert.small 1051),
               (2, 0, Hex.Nat.PrimeCert.small 1733)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.haa1e7727492f9b40c020' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.haa1e7727492f9b40c020

/-- Frozen certificate for 10412653304508950294979616189482973981530100639222633503329849552063535584575804536682779499168432292062676093008868715654010422373584966273978479669211023. -/
theorem Hex.PrimalityCorpus.h06e82fec068ae9d4409a : _root_.Nat.Prime 10412653304508950294979616189482973981530100639222633503329849552063535584575804536682779499168432292062676093008868715654010422373584966273978479669211023 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  10412653304508950294979616189482973981530100639222633503329849552063535584575804536682779499168432292062676093008868715654010422373584966273978479669211023
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      2295112212685548451339668690938532073551725615307997656296672728776532324252168072533005046574114731445108066795405419323620269533
      988012827256238302421052166012433166296662971
      867467923473972034463844155844127838030
      988012827256238302421052166012433166296662970
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.pock 776753 [(2, 0, Hex.Nat.PrimeCert.small 1129)]),
       (2, 0, Hex.Nat.PrimeCert.pock3Sieve 3168449 99 386 81 4 [(3, 5, Hex.Nat.PrimeCert.small 2)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          123720534529
          2455
          26219
          2411
          10
          [(13, 8, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 3)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          944340927771571341301
          770877
          48601881
          770624
          14
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (3, 1, Hex.Nat.PrimeCert.small 5),
           (2, 0, Hex.Nat.PrimeCert.small 71),
           (2, 0, Hex.Nat.PrimeCert.small 439)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h06e82fec068ae9d4409a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h06e82fec068ae9d4409a
