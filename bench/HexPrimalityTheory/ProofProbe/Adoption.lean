/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimalityTheory.Prime

public section

/-! Frozen certificates from the adopted factor-search comparison. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Frozen certificate for 69720056183201689673043526946867998580043318488979852658170286968852334279321. -/
theorem Hex.PrimalityAdoption.h13664edef8a245ef5b5f : _root_.Nat.Prime 69720056183201689673043526946867998580043318488979852658170286968852334279321 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock3
  69720056183201689673043526946867998580043318488979852658170286968852334279321
  8155740637493983986425013211175
  179327126798440
  8155740637493983986425013211174
  [(7, 2, Hex.Nat.PrimeCert.small 2),
   (2,
    0,
    Hex.Nat.PrimeCert.pock3
      1742813375229269179225295318389
      466369261
      797985852
      466369254
      [(2, 1, Hex.Nat.PrimeCert.small 2),
       (2, 2, Hex.Nat.PrimeCert.small 3),
       (2, 0, Hex.Nat.PrimeCert.small 41),
       (2, 0, Hex.Nat.PrimeCert.small 113),
       (2, 0, Hex.Nat.PrimeCert.small 211),
       (2, 0, Hex.Nat.PrimeCert.small 313)])]) (by decide +kernel)

/-- info: 'Hex.PrimalityAdoption.h13664edef8a245ef5b5f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityAdoption.h13664edef8a245ef5b5f

/-- Frozen certificate for 115219968303613180170318760115437973610941062152781770424416328511434156923419. -/
theorem Hex.PrimalityAdoption.h1727418a767668f8bdd3 : _root_.Nat.Prime 115219968303613180170318760115437973610941062152781770424416328511434156923419 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  115219968303613180170318760115437973610941062152781770424416328511434156923419
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      45862237193743742748804221806010957525504490853138766903
      [(2,
        0,
        Hex.Nat.PrimeCert.pock3
          24346916115929274623004442222697564856736319119699
          207033914835407159
          458172508331345
          207033914835407158
          [(2, 0, Hex.Nat.PrimeCert.small 2),
           (2,
            0,
            Hex.Nat.PrimeCert.pock
              81500912810811491
              [(2,
                0,
                Hex.Nat.PrimeCert.pock
                  1308410865481
                  [(2, 0, Hex.Nat.PrimeCert.small 2557), (2, 0, Hex.Nat.PrimeCert.small 4999)])])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityAdoption.h1727418a767668f8bdd3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityAdoption.h1727418a767668f8bdd3

/-- Frozen certificate for 96590133568377947488922651108406533027621815589740576200326951544495709460191. -/
theorem Hex.PrimalityAdoption.h191be6736f1737947bdd : _root_.Nat.Prime 96590133568377947488922651108406533027621815589740576200326951544495709460191 :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.pock
  96590133568377947488922651108406533027621815589740576200326951544495709460191
  [(2,
    0,
    Hex.Nat.PrimeCert.pock
      13596502756513155034176285505009231528806356541260779742862268109
      [(2,
        0,
        Hex.Nat.PrimeCert.pock
          11671899846949893238322767694352121508952208909719338567749
          [(2, 0, Hex.Nat.PrimeCert.small 17327),
           (2,
            0,
            Hex.Nat.PrimeCert.pock3
              54816603279049951812177013
              949352873
              36667897
              949352872
              [(2, 1, Hex.Nat.PrimeCert.small 2),
               (5, 4, Hex.Nat.PrimeCert.small 3),
               (2, 1, Hex.Nat.PrimeCert.small 11),
               (2, 0, Hex.Nat.PrimeCert.small 7351)])])])]) (by decide +kernel)

/-- info: 'Hex.PrimalityAdoption.h191be6736f1737947bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityAdoption.h191be6736f1737947bdd

/-- Frozen certificate for 8303243761314623153536298383293640890258824928930362945199766069795505229347391151296947598482864968712933522433529495861410413812952831043952026306423823. -/
theorem Hex.PrimalityAdoption.h3d2c3dbb7bfc1177a75c : _root_.Nat.Prime 8303243761314623153536298383293640890258824928930362945199766069795505229347391151296947598482864968712933522433529495861410413812952831043952026306423823 :=
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

/-- info: 'Hex.PrimalityAdoption.h3d2c3dbb7bfc1177a75c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityAdoption.h3d2c3dbb7bfc1177a75c

/-- Frozen certificate for 7983226596738841058766325436315975273752711604126516516644200892341180092058466758226580125510711294302178552878759289723290167401444678034498033356114163. -/
theorem Hex.PrimalityAdoption.h0fd47bae858921b84b04 : _root_.Nat.Prime 7983226596738841058766325436315975273752711604126516516644200892341180092058466758226580125510711294302178552878759289723290167401444678034498033356114163 :=
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

/-- info: 'Hex.PrimalityAdoption.h0fd47bae858921b84b04' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.PrimalityAdoption.h0fd47bae858921b84b04
