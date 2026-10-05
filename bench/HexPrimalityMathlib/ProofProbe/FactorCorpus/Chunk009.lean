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

/-- Frozen certificate for 10461581242931373748355390987053124159721177491242137159954721062240255713886717680425545221966560041817890478123108522520409672575492392488889017529720187. -/
theorem Hex.PrimalityCorpus.h430b50a1f36f3195a6c6 : _root_.Nat.Prime 10461581242931373748355390987053124159721177491242137159954721062240255713886717680425545221966560041817890478123108522520409672575492392488889017529720187 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  10461581242931373748355390987053124159721177491242137159954721062240255713886717680425545221966560041817890478123108522520409672575492392488889017529720187
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      50735987328246530044852563877524213923714994350293388833080693866437189737181934323679382264611789666555791142981852580807224740907063
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          49779173514861130250031130826102624238380906919320002667032703476915890620839564374329354601696624460709
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              1676859794902305571785302504397645448785702517025999978579956825056702280673
              424871070215069438141178143
              5764435858011964586370
              424871070215069438141178142
              [(3, 4, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  4200556691
                  [(2, 0, Hex.Nat.PrimeCert.small 1117), (2, 0, Hex.Nat.PrimeCert.small 2011)]),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3Sieve
                  2837253523184027
                  40639
                  314163
                  40608
                  4
                  [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 33599)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h430b50a1f36f3195a6c6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h430b50a1f36f3195a6c6

/-- Frozen certificate for 11103000223932292503382845183539526033558230908746737868768856615387717392815565362891988725236554022267095605240768187803267055225766429820710912898660009. -/
theorem Hex.PrimalityCorpus.h0bd62294e84aa54a57a4 : _root_.Nat.Prime 11103000223932292503382845183539526033558230908746737868768856615387717392815565362891988725236554022267095605240768187803267055225766429820710912898660009 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  11103000223932292503382845183539526033558230908746737868768856615387717392815565362891988725236554022267095605240768187803267055225766429820710912898660009
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      8605341722676205878360921794658302570719065941379408476364092542918345023265071036448798947887472541746608590863667
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          160158813942946096263833306142072203254927565800126930174428377179735669380985965917
          6384723652595370953525626285
          5037291944172781482510262402
          6384723652595370953525626281
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 7),
           (2, 0, Hex.Nat.PrimeCert.small 127),
           (2, 0, Hex.Nat.PrimeCert.small 1459),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3
              768501676152509226233
              216751739
              22584
              216751738
              [(3, 2, Hex.Nat.PrimeCert.small 2),
               (2, 0, Hex.Nat.PrimeCert.small 739),
               (2, 0, Hex.Nat.PrimeCert.small 22063)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h0bd62294e84aa54a57a4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h0bd62294e84aa54a57a4

/-- Frozen certificate for 11139301085590814129221478576765121965448329254503730582771848562254170482538518355491863976372021516063104047042173204803874862890184139212032910577973459. -/
theorem Hex.PrimalityCorpus.hed536213501d777e05e0 : _root_.Nat.Prime 11139301085590814129221478576765121965448329254503730582771848562254170482538518355491863976372021516063104047042173204803874862890184139212032910577973459 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  11139301085590814129221478576765121965448329254503730582771848562254170482538518355491863976372021516063104047042173204803874862890184139212032910577973459
  940795650832579202430265617495017550107702940850327
  7516926699129728016307503450555941797339031908569350
  940795650832579202430265617495017550107702940850295
  6
  [(2, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 3),
   (2, 0, Hex.Nat.PrimeCert.small 1061),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 12951896299 [(2, 0, Hex.Nat.PrimeCert.small 103), (2, 0, Hex.Nat.PrimeCert.small 82837)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      648290993209
      1073031
      0
      1073031
      [(7, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 75521)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      16103631912438447011356259
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          2923313265237637
          156307
          133459
          156303
          [(2, 1, Hex.Nat.PrimeCert.small 2),
           (2, 3, Hex.Nat.PrimeCert.small 3),
           (2, 0, Hex.Nat.PrimeCert.small 17),
           (2, 0, Hex.Nat.PrimeCert.small 19)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hed536213501d777e05e0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hed536213501d777e05e0

/-- Frozen certificate for 11256126957126506099951912787334809009879091320240956484141529292023191237370195310972640467521048274463390468361042167823412425342512017057470647585997199. -/
theorem Hex.PrimalityCorpus.hddb41900e59a5ddbb3cf : _root_.Nat.Prime 11256126957126506099951912787334809009879091320240956484141529292023191237370195310972640467521048274463390468361042167823412425342512017057470647585997199 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  11256126957126506099951912787334809009879091320240956484141529292023191237370195310972640467521048274463390468361042167823412425342512017057470647585997199
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      1453627394482371190423748011326954754804180809559867558287269831001612222660283826185373662669852825122296187325298862961076807
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          36067063127279979293579372604011428495996737586314306162454446678276975984442155840224167199637025752331
          742360329529366812309266233944495
          60795482154360328011344027717372100
          742360329529366812309266233944167
          4
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 547),
           (2, 0, Hex.Nat.PrimeCert.small 1559),
           (2, 0, Hex.Nat.PrimeCert.pock 231481 [(2, 0, Hex.Nat.PrimeCert.small 643)]),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              43624046898506785052599
              [(2, 0, Hex.Nat.PrimeCert.small 16141),
               (2,
                0,
                Hex.Nat.PrimeCert.pock3
                  7470974389
                  14863
                  25
                  14862
                  [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 3019)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hddb41900e59a5ddbb3cf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hddb41900e59a5ddbb3cf

/-- Frozen certificate for 11468625035903882423573187058985058028489909939278236344622423157377413774963417653448352314131103618848758800808252890485424889434200861923555186642307401. -/
theorem Hex.PrimalityCorpus.hc0b3a59165806cf98580 : _root_.Nat.Prime 11468625035903882423573187058985058028489909939278236344622423157377413774963417653448352314131103618848758800808252890485424889434200861923555186642307401 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  11468625035903882423573187058985058028489909939278236344622423157377413774963417653448352314131103618848758800808252890485424889434200861923555186642307401
  1387079964590250055689274123550544679417163404650903
  1518104671748585725931406702527779537110054822301895
  1387079964590250055689274123550544679417163404650898
  [(3, 2, Hex.Nat.PrimeCert.small 2),
   (2, 1, Hex.Nat.PrimeCert.small 5),
   (2, 0, Hex.Nat.PrimeCert.small 7),
   (2, 0, Hex.Nat.PrimeCert.pock 736091 [(2, 0, Hex.Nat.PrimeCert.small 73609)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      347607893
      847
      172
      846
      [(2, 1, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 251)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 649271321 [(2, 0, Hex.Nat.PrimeCert.small 1009), (2, 0, Hex.Nat.PrimeCert.small 16087)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      8356307787830807847083039
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3Sieve
          808599921709123
          41843
          352097
          41809
          7
          [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 16943)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hc0b3a59165806cf98580' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hc0b3a59165806cf98580

/-- Frozen certificate for 11743726560448344919944734091785007213176558041815058461956581357563775245944011046485692619380180663898807840901860162169814315896871251483540050901941799. -/
theorem Hex.PrimalityCorpus.h7ce3d5bf5113ec55134b : _root_.Nat.Prime 11743726560448344919944734091785007213176558041815058461956581357563775245944011046485692619380180663898807840901860162169814315896871251483540050901941799 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  11743726560448344919944734091785007213176558041815058461956581357563775245944011046485692619380180663898807840901860162169814315896871251483540050901941799
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      72001573025897714303750910917503569412625987310816835751244253024864142658278182822637055288872916558734724962568319261223
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          277981756262480246464015769519981665853700993768537400100246729768063586328596023439855707490052916449963612452481
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              14947570992034178664563230113802041671311736919750454809779916301169784173265625029840135743
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  776174628312087374834522282365876086369910526521469249651049761198971034025632206347499
                  [(2,
                    0,
                    Hex.Nat.PrimeCert.pock
                      64626467225106512963132893056357214144892110390043922722230761619
                      [(2,
                        0,
                        Hex.Nat.PrimeCert.pock3
                          73630811852651363280600417738941945341690224667
                          51032838659907267
                          43605608823804
                          51032838659907266
                          [(2, 0, Hex.Nat.PrimeCert.small 2),
                           (2, 0, Hex.Nat.PrimeCert.small 773),
                           (2,
                            0,
                            Hex.Nat.PrimeCert.pock3Sieve
                              18794645122387
                              11915
                              76463
                              11889
                              5
                              [(2, 0, Hex.Nat.PrimeCert.small 2),
                               (2, 0, Hex.Nat.PrimeCert.small 23),
                               (2, 0, Hex.Nat.PrimeCert.small 241)])])])])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h7ce3d5bf5113ec55134b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h7ce3d5bf5113ec55134b

/-- Frozen certificate for 11867460853364119819728781287178898494655976801551777045688174446092621531651963592115210931540235829866232126989959264721074206903793649532242053706061571. -/
theorem Hex.PrimalityCorpus.haf4674e6c98551c85d7e : _root_.Nat.Prime 11867460853364119819728781287178898494655976801551777045688174446092621531651963592115210931540235829866232126989959264721074206903793649532242053706061571 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  11867460853364119819728781287178898494655976801551777045688174446092621531651963592115210931540235829866232126989959264721074206903793649532242053706061571
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      1831502442520937513065900587325402237860402070177555993961601646306177594742177067067001275745456625626200223274377515789
      330990422214869371315392176415776627864735
      99100902788583289160892468506997386
      330990422214869371315392176415776627864734
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          9272307977949491
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3
              8665708390607
              458763
              14
              458762
              [(5, 0, Hex.Nat.PrimeCert.small 2),
               (2,
                0,
                Hex.Nat.PrimeCert.pock
                  274093
                  [(2, 0, Hex.Nat.PrimeCert.small 13), (2, 0, Hex.Nat.PrimeCert.small 251)])])]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          81960029927339537026498847
          [(2,
            0,
            Hex.Nat.PrimeCert.pock
              21418510626760254677
              [(2,
                0,
                Hex.Nat.PrimeCert.pock3
                  57314014481
                  62767
                  6
                  62766
                  [(3, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 4159)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.haf4674e6c98551c85d7e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.haf4674e6c98551c85d7e

/-- Frozen certificate for 12249467942532342482208878016834640862225041326345391320127211057009236128979336259879257647192147915933242185212593808730153105444501748192712330182011871. -/
theorem Hex.PrimalityCorpus.hfe34abef8eee6452dc79 : _root_.Nat.Prime 12249467942532342482208878016834640862225041326345391320127211057009236128979336259879257647192147915933242185212593808730153105444501748192712330182011871 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3Sieve
  12249467942532342482208878016834640862225041326345391320127211057009236128979336259879257647192147915933242185212593808730153105444501748192712330182011871
  594183883381480338896442581029211974410986701854579
  24914885944866027429987177901181075549159166491040332
  594183883381480338896442581029211974410986701854411
  32
  [(7, 0, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 11),
   (2, 0, Hex.Nat.PrimeCert.small 4451),
   (2, 0, Hex.Nat.PrimeCert.small 18229),
   (2, 0, Hex.Nat.PrimeCert.small 32321),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      966385787857681
      971041
      1106
      971040
      [(17, 3, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 61), (2, 0, Hex.Nat.PrimeCert.small 677)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      8892742552749176251393
      [(5, 9, Hex.Nat.PrimeCert.small 2),
       (2,
        0,
        Hex.Nat.PrimeCert.pock 287050441 [(2, 0, Hex.Nat.PrimeCert.small 37), (2, 0, Hex.Nat.PrimeCert.small 3803)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hfe34abef8eee6452dc79' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hfe34abef8eee6452dc79

/-- Frozen certificate for 12382617197963185584839454954756574678134636869124423656213601374064173361145147703798536060972996832114457529196338191991145928249553075896225397464552091. -/
theorem Hex.PrimalityCorpus.h3fd83900622655e6c9bd : _root_.Nat.Prime 12382617197963185584839454954756574678134636869124423656213601374064173361145147703798536060972996832114457529196338191991145928249553075896225397464552091 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  12382617197963185584839454954756574678134636869124423656213601374064173361145147703798536060972996832114457529196338191991145928249553075896225397464552091
  [(2,
    0,
    Hex.Nat.PrimeCert.pock3
      25967928078345133104455880126083032029858728193882682313028548499911371951445263164028524334519021654151863890707982495928575542760322530455011879
      382896879485322896438875449051842998367736348957
      1534500805263693037218975055771310371755686838348
      382896879485322896438875449051842998367736348940
      [(3, 0, Hex.Nat.PrimeCert.small 2),
       (2, 0, Hex.Nat.PrimeCert.small 19),
       (2, 0, Hex.Nat.PrimeCert.small 23),
       (2, 0, Hex.Nat.PrimeCert.small 61),
       (2, 0, Hex.Nat.PrimeCert.small 409),
       (2, 0, Hex.Nat.PrimeCert.small 15137),
       (2,
        0,
        Hex.Nat.PrimeCert.pock
          27076738985547863
          [(2, 0, Hex.Nat.PrimeCert.small 16141), (2, 0, Hex.Nat.PrimeCert.small 72973)]),
       (2,
        0,
        Hex.Nat.PrimeCert.pock3
          325476282235618211521
          82873037
          38683
          82873036
          [(7, 5, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 487),
           (2, 0, Hex.Nat.PrimeCert.small 2081)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.h3fd83900622655e6c9bd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h3fd83900622655e6c9bd

/-- Frozen certificate for 12861575418016517354273005224520481840836590366327288535079156425602458059088281363126007490838940253680710085238304627054216195434860593801690281863447521. -/
theorem Hex.PrimalityCorpus.hd04f2d23e3bf82565be1 : _root_.Nat.Prime 12861575418016517354273005224520481840836590366327288535079156425602458059088281363126007490838940253680710085238304627054216195434860593801690281863447521 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  12861575418016517354273005224520481840836590366327288535079156425602458059088281363126007490838940253680710085238304627054216195434860593801690281863447521
  5391832553979630273142382475378473887093278073100803
  71388254884778167070189178902797047459770453395481
  5391832553979630273142382475378473887093278073100802
  [(7, 4, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3Sieve
      66743873409931
      2601
      279345
      2128
      23
      [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 5), (2, 0, Hex.Nat.PrimeCert.small 1093)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      291318536146722257
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          18207408509170141
          [(2, 0, Hex.Nat.PrimeCert.small 3271), (2, 0, Hex.Nat.PrimeCert.small 86399)])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      15254191688214857039
      7518459
      405311
      7518458
      [(7, 0, Hex.Nat.PrimeCert.small 2),
       (2, 1, Hex.Nat.PrimeCert.small 31),
       (2, 0, Hex.Nat.PrimeCert.small 37),
       (2, 0, Hex.Nat.PrimeCert.small 61)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hd04f2d23e3bf82565be1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hd04f2d23e3bf82565be1

/-- Frozen certificate for 12872851557632665890972727532639777936560710431364558137632598948916662787706259423521668262948380452258502319578620448332383399984117507551658910332177621. -/
theorem Hex.PrimalityCorpus.hb252d00380520595c5aa : _root_.Nat.Prime 12872851557632665890972727532639777936560710431364558137632598948916662787706259423521668262948380452258502319578620448332383399984117507551658910332177621 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  12872851557632665890972727532639777936560710431364558137632598948916662787706259423521668262948380452258502319578620448332383399984117507551658910332177621
  4799370066807511141633715433318258244359429182384133
  102320545340649777757362114920460984773070729937029
  4799370066807511141633715433318258244359429182384132
  [(2, 1, Hex.Nat.PrimeCert.small 2),
   (2, 0, Hex.Nat.PrimeCert.small 31),
   (2,
    0,
    Hex.Nat.PrimeCert.pock 13748859332479 [(2, 0, Hex.Nat.PrimeCert.small 5503), (2, 0, Hex.Nat.PrimeCert.small 9601)]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      7439041088899513
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          309960045370813
          [(2,
            0,
            Hex.Nat.PrimeCert.pock3Sieve
              25830003780901
              26371
              40307
              26364
              2
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (2, 1, Hex.Nat.PrimeCert.small 5),
               (2, 0, Hex.Nat.PrimeCert.small 179)])])]),
   (2,
    0,
    Hex.Nat.PrimeCert.pock
      625367990987634647633
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          3553227221520651407
          627275
          1077838
          627268
          [(5, 0, Hex.Nat.PrimeCert.small 2),
           (2, 0, Hex.Nat.PrimeCert.small 373),
           (2, 0, Hex.Nat.PrimeCert.small 1721)])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityCorpus.hb252d00380520595c5aa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.hb252d00380520595c5aa

/-- Frozen certificate for 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151. -/
theorem Hex.PrimalityCorpus.h854c10fc9a7c6cf1f5a3 : _root_.Nat.Prime 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 :=
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

/-- info: 'Hex.PrimalityCorpus.h854c10fc9a7c6cf1f5a3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h854c10fc9a7c6cf1f5a3

/-- Frozen certificate for 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151. -/
theorem Hex.PrimalityCorpus.h89aaabdc4405832e079f : _root_.Nat.Prime 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 :=
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

/-- info: 'Hex.PrimalityCorpus.h89aaabdc4405832e079f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityCorpus.h89aaabdc4405832e079f
