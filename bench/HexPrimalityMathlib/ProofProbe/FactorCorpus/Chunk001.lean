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
