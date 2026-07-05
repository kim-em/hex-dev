/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekamp.RabinSoundness
import HexGFqRing.Basic
import HexConway.Table

/-!
Rabin irreducibility certificates for the committed Conway table entries
and the resulting `luebeckConwayPolynomial_p_n_irreducible` proofs.
-/
namespace Hex

namespace Conway
/-- Rabin irreducibility certificate for the committed `C(2, 2)` entry. -/
private def cert_2_2 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 2), 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs (#[] : Array (ZMod64 2)), right := FpPoly.ofCoeffs #[(1 : ZMod64 2)] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_2_2_incremental_check` confirms the incremental Rabin certificate `cert_2_2` validates for the committed `C(2, 2)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_2_2_irreducible`. -/
private theorem cert_2_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_2_2 luebeckConwayPolynomial_2_2_monic cert_2_2 = true := by
  decide

/-- The committed `C(2, 2)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_2_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_2
    luebeckConwayPolynomial_2_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_2_2 luebeckConwayPolynomial_2_2_monic cert_2_2 cert_2_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(2, 3)` entry. -/
private def cert_2_3 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 2), 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 2)], right := FpPoly.ofCoeffs #[(1 : ZMod64 2), 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_2_3_incremental_check` confirms the incremental Rabin certificate `cert_2_3` validates for the committed `C(2, 3)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_2_3_irreducible`. -/
private theorem cert_2_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_2_3 luebeckConwayPolynomial_2_3_monic cert_2_3 = true := by
  decide

/-- The committed `C(2, 3)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_2_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_3
    luebeckConwayPolynomial_2_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_2_3 luebeckConwayPolynomial_2_3_monic cert_2_3 cert_2_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(2, 4)` entry. -/
private def cert_2_4 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 2), 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs (#[] : Array (ZMod64 2)), right := FpPoly.ofCoeffs #[(1 : ZMod64 2)] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_2_4_incremental_check` confirms the incremental Rabin certificate `cert_2_4` validates for the committed `C(2, 4)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_2_4_irreducible`. -/
private theorem cert_2_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_2_4 luebeckConwayPolynomial_2_4_monic cert_2_4 = true := by
  decide

/-- The committed `C(2, 4)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_2_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_4
    luebeckConwayPolynomial_2_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_2_4 luebeckConwayPolynomial_2_4_monic cert_2_4 cert_2_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(2, 5)` entry. -/
private def cert_2_5 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 2), 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 0, 0, 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 0, 1, 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 1, 0, 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 2)], right := FpPoly.ofCoeffs #[(0 : ZMod64 2), 1, 1, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_2_5_incremental_check` confirms the incremental Rabin certificate `cert_2_5` validates for the committed `C(2, 5)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_2_5_irreducible`. -/
private theorem cert_2_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_2_5 luebeckConwayPolynomial_2_5_monic cert_2_5 = true := by
  decide

/-- The committed `C(2, 5)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_2_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_5
    luebeckConwayPolynomial_2_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_2_5 luebeckConwayPolynomial_2_5_monic cert_2_5 cert_2_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(2, 6)` entry. -/
private def cert_2_6 : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 2), 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 0, 0, 0, 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 1, 1, 0, 1, 1], FpPoly.ofCoeffs #[(1 : ZMod64 2), 1, 0, 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1, 0, 0, 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 2), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 2)], right := FpPoly.ofCoeffs #[(1 : ZMod64 2), 0, 1] }, { left := FpPoly.ofCoeffs #[(1 : ZMod64 2), 0, 1, 1], right := FpPoly.ofCoeffs #[(0 : ZMod64 2), 1, 1, 0, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_2_6_incremental_check` confirms the incremental Rabin certificate `cert_2_6` validates for the committed `C(2, 6)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_2_6_irreducible`. -/
private theorem cert_2_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_2_6 luebeckConwayPolynomial_2_6_monic cert_2_6 = true := by
  decide

/-- The committed `C(2, 6)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_2_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_2_6
    luebeckConwayPolynomial_2_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_2_6 luebeckConwayPolynomial_2_6_monic cert_2_6 cert_2_6_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 1)` entry. -/
private def cert_3_1 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(2 : ZMod64 3)], FpPoly.ofCoeffs #[(2 : ZMod64 3)]]
  bezout := #[]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_3_1_incremental_check` confirms the incremental Rabin certificate `cert_3_1` validates for the committed `C(3, 1)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_3_1_irreducible`. -/
private theorem cert_3_1_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_1 luebeckConwayPolynomial_3_1_monic cert_3_1 = true := by
  decide

/-- The committed `C(3, 1)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_3_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_1
    luebeckConwayPolynomial_3_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_1 luebeckConwayPolynomial_3_1_monic cert_3_1 cert_3_1_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 2)` entry. -/
private def cert_3_2 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 3), 1], FpPoly.ofCoeffs #[(1 : ZMod64 3), 2], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 3)], right := FpPoly.ofCoeffs #[(2 : ZMod64 3), 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_3_2_incremental_check` confirms the incremental Rabin certificate `cert_3_2` validates for the committed `C(3, 2)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_3_2_irreducible`. -/
private theorem cert_3_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_2 luebeckConwayPolynomial_3_2_monic cert_3_2 = true := by
  decide

/-- The committed `C(3, 2)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_3_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_2
    luebeckConwayPolynomial_3_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_2 luebeckConwayPolynomial_3_2_monic cert_3_2 cert_3_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 3)` entry. -/
private def cert_3_3 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 3), 1], FpPoly.ofCoeffs #[(2 : ZMod64 3), 1], FpPoly.ofCoeffs #[(1 : ZMod64 3), 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs (#[] : Array (ZMod64 3)), right := FpPoly.ofCoeffs #[(2 : ZMod64 3)] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_3_3_incremental_check` confirms the incremental Rabin certificate `cert_3_3` validates for the committed `C(3, 3)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_3_3_irreducible`. -/
private theorem cert_3_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_3 luebeckConwayPolynomial_3_3_monic cert_3_3 = true := by
  decide

/-- The committed `C(3, 3)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_3_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_3
    luebeckConwayPolynomial_3_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_3 luebeckConwayPolynomial_3_3_monic cert_3_3 cert_3_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 4)` entry. -/
private def cert_3_4 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 3), 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 0, 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 2, 1, 1], FpPoly.ofCoeffs #[(1 : ZMod64 3), 0, 2, 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(2 : ZMod64 3), 1, 2], right := FpPoly.ofCoeffs #[(1 : ZMod64 3), 1, 0, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_3_4_incremental_check` confirms the incremental Rabin certificate `cert_3_4` validates for the committed `C(3, 4)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_3_4_irreducible`. -/
private theorem cert_3_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_4 luebeckConwayPolynomial_3_4_monic cert_3_4 = true := by
  decide

/-- The committed `C(3, 4)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_3_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_4
    luebeckConwayPolynomial_3_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_4 luebeckConwayPolynomial_3_4_monic cert_3_4 cert_3_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 5)` entry. -/
private def cert_3_5 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 3), 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 0, 0, 1], FpPoly.ofCoeffs #[(2 : ZMod64 3), 1, 0, 0, 2], FpPoly.ofCoeffs #[(2 : ZMod64 3), 0, 2, 0, 2], FpPoly.ofCoeffs #[(2 : ZMod64 3), 1, 1, 2, 2], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 3)], right := FpPoly.ofCoeffs #[(2 : ZMod64 3), 0, 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_3_5_incremental_check` confirms the incremental Rabin certificate `cert_3_5` validates for the committed `C(3, 5)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_3_5_irreducible`. -/
private theorem cert_3_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_5 luebeckConwayPolynomial_3_5_monic cert_3_5 = true := by
  decide

/-- The committed `C(3, 5)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_3_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_5
    luebeckConwayPolynomial_3_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_5 luebeckConwayPolynomial_3_5_monic cert_3_5 cert_3_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(3, 6)` entry. -/
private def cert_3_6 : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 3), 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 0, 0, 1], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1, 1, 0, 1], FpPoly.ofCoeffs #[(1 : ZMod64 3), 2, 0, 0, 2, 2], FpPoly.ofCoeffs #[(0 : ZMod64 3), 0, 0, 2, 2, 2], FpPoly.ofCoeffs #[(2 : ZMod64 3), 2, 2, 0, 1, 2], FpPoly.ofCoeffs #[(0 : ZMod64 3), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(2 : ZMod64 3), 1, 1, 2], right := FpPoly.ofCoeffs #[(0 : ZMod64 3), 2, 0, 0, 2, 1] }, { left := FpPoly.ofCoeffs #[(1 : ZMod64 3), 2, 1, 0, 1], right := FpPoly.ofCoeffs #[(2 : ZMod64 3), 1, 1, 1, 2, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_3_6_incremental_check` confirms the incremental Rabin certificate `cert_3_6` validates for the committed `C(3, 6)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_3_6_irreducible`. -/
private theorem cert_3_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_3_6 luebeckConwayPolynomial_3_6_monic cert_3_6 = true := by
  decide

/-- The committed `C(3, 6)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_3_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_3_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_3_6
    luebeckConwayPolynomial_3_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_3_6 luebeckConwayPolynomial_3_6_monic cert_3_6 cert_3_6_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 1)` entry. -/
private def cert_5_1 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(2 : ZMod64 5)], FpPoly.ofCoeffs #[(2 : ZMod64 5)]]
  bezout := #[]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_5_1_incremental_check` confirms the incremental Rabin certificate `cert_5_1` validates for the committed `C(5, 1)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_5_1_irreducible`. -/
private theorem cert_5_1_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_1 luebeckConwayPolynomial_5_1_monic cert_5_1 = true := by
  decide

/-- The committed `C(5, 1)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_5_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_1
    luebeckConwayPolynomial_5_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_1 luebeckConwayPolynomial_5_1_monic cert_5_1 cert_5_1_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 2)` entry. -/
private def cert_5_2 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 5), 1], FpPoly.ofCoeffs #[(1 : ZMod64 5), 4], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(2 : ZMod64 5)], right := FpPoly.ofCoeffs #[(2 : ZMod64 5), 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_5_2_incremental_check` confirms the incremental Rabin certificate `cert_5_2` validates for the committed `C(5, 2)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_5_2_irreducible`. -/
private theorem cert_5_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_2 luebeckConwayPolynomial_5_2_monic cert_5_2 = true := by
  decide

/-- The committed `C(5, 2)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_5_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_2
    luebeckConwayPolynomial_5_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_2 luebeckConwayPolynomial_5_2_monic cert_5_2 cert_5_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 3)` entry. -/
private def cert_5_3 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 5), 1], FpPoly.ofCoeffs #[(4 : ZMod64 5), 4, 2], FpPoly.ofCoeffs #[(1 : ZMod64 5), 0, 3], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(3 : ZMod64 5), 3], right := FpPoly.ofCoeffs #[(3 : ZMod64 5), 2, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_5_3_incremental_check` confirms the incremental Rabin certificate `cert_5_3` validates for the committed `C(5, 3)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_5_3_irreducible`. -/
private theorem cert_5_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_3 luebeckConwayPolynomial_5_3_monic cert_5_3 = true := by
  decide

/-- The committed `C(5, 3)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_5_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_3
    luebeckConwayPolynomial_5_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_3 luebeckConwayPolynomial_5_3_monic cert_5_3 cert_5_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 4)` entry. -/
private def cert_5_4 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 5), 1], FpPoly.ofCoeffs #[(0 : ZMod64 5), 3, 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 5), 0, 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1, 3, 3], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(3 : ZMod64 5), 3, 1], right := FpPoly.ofCoeffs #[(3 : ZMod64 5), 4, 3, 4] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_5_4_incremental_check` confirms the incremental Rabin certificate `cert_5_4` validates for the committed `C(5, 4)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_5_4_irreducible`. -/
private theorem cert_5_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_4 luebeckConwayPolynomial_5_4_monic cert_5_4 = true := by
  decide

/-- The committed `C(5, 4)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_5_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_4
    luebeckConwayPolynomial_5_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_4 luebeckConwayPolynomial_5_4_monic cert_5_4 cert_5_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 5)` entry. -/
private def cert_5_5 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 5), 1], FpPoly.ofCoeffs #[(2 : ZMod64 5), 1], FpPoly.ofCoeffs #[(4 : ZMod64 5), 1], FpPoly.ofCoeffs #[(1 : ZMod64 5), 1], FpPoly.ofCoeffs #[(3 : ZMod64 5), 1], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs (#[] : Array (ZMod64 5)), right := FpPoly.ofCoeffs #[(3 : ZMod64 5)] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_5_5_incremental_check` confirms the incremental Rabin certificate `cert_5_5` validates for the committed `C(5, 5)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_5_5_irreducible`. -/
private theorem cert_5_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_5 luebeckConwayPolynomial_5_5_monic cert_5_5 = true := by
  decide

/-- The committed `C(5, 5)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_5_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_5
    luebeckConwayPolynomial_5_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_5 luebeckConwayPolynomial_5_5_monic cert_5_5 cert_5_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(5, 6)` entry. -/
private def cert_5_6 : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 5), 1], FpPoly.ofCoeffs #[(0 : ZMod64 5), 0, 0, 0, 0, 1], FpPoly.ofCoeffs #[(4 : ZMod64 5), 4, 0, 3, 4, 2], FpPoly.ofCoeffs #[(3 : ZMod64 5), 0, 3, 2, 4, 1], FpPoly.ofCoeffs #[(1 : ZMod64 5), 0, 0, 2, 1, 3], FpPoly.ofCoeffs #[(2 : ZMod64 5), 0, 2, 3, 1, 3], FpPoly.ofCoeffs #[(0 : ZMod64 5), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(0 : ZMod64 5), 4, 0, 1, 1], right := FpPoly.ofCoeffs #[(4 : ZMod64 5), 0, 0, 3, 3, 2] }, { left := FpPoly.ofCoeffs #[(4 : ZMod64 5), 2, 1, 4, 3], right := FpPoly.ofCoeffs #[(1 : ZMod64 5), 4, 0, 0, 3, 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_5_6_incremental_check` confirms the incremental Rabin certificate `cert_5_6` validates for the committed `C(5, 6)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_5_6_irreducible`. -/
private theorem cert_5_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_5_6 luebeckConwayPolynomial_5_6_monic cert_5_6 = true := by
  decide

/-- The committed `C(5, 6)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_5_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_5_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_5_6
    luebeckConwayPolynomial_5_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_5_6 luebeckConwayPolynomial_5_6_monic cert_5_6 cert_5_6_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 1)` entry. -/
private def cert_7_1 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(3 : ZMod64 7)], FpPoly.ofCoeffs #[(3 : ZMod64 7)]]
  bezout := #[]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_7_1_incremental_check` confirms the incremental Rabin certificate `cert_7_1` validates for the committed `C(7, 1)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_7_1_irreducible`. -/
private theorem cert_7_1_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_1 luebeckConwayPolynomial_7_1_monic cert_7_1 = true := by
  decide

/-- The committed `C(7, 1)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_7_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_1
    luebeckConwayPolynomial_7_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_1 luebeckConwayPolynomial_7_1_monic cert_7_1 cert_7_1_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 2)` entry. -/
private def cert_7_2 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 7), 1], FpPoly.ofCoeffs #[(1 : ZMod64 7), 6], FpPoly.ofCoeffs #[(0 : ZMod64 7), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(1 : ZMod64 7)], right := FpPoly.ofCoeffs #[(5 : ZMod64 7), 4] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_7_2_incremental_check` confirms the incremental Rabin certificate `cert_7_2` validates for the committed `C(7, 2)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_7_2_irreducible`. -/
private theorem cert_7_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_2 luebeckConwayPolynomial_7_2_monic cert_7_2 = true := by
  decide

/-- The committed `C(7, 2)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_7_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_2
    luebeckConwayPolynomial_7_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_2 luebeckConwayPolynomial_7_2_monic cert_7_2 cert_7_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 3)` entry. -/
private def cert_7_3 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 7), 1], FpPoly.ofCoeffs #[(0 : ZMod64 7), 5, 3], FpPoly.ofCoeffs #[(1 : ZMod64 7), 1, 4], FpPoly.ofCoeffs #[(0 : ZMod64 7), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(2 : ZMod64 7)], right := FpPoly.ofCoeffs #[(0 : ZMod64 7), 4] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_7_3_incremental_check` confirms the incremental Rabin certificate `cert_7_3` validates for the committed `C(7, 3)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_7_3_irreducible`. -/
private theorem cert_7_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_3 luebeckConwayPolynomial_7_3_monic cert_7_3 = true := by
  decide

/-- The committed `C(7, 3)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_7_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_3
    luebeckConwayPolynomial_7_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_3 luebeckConwayPolynomial_7_3_monic cert_7_3 cert_7_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 4)` entry. -/
private def cert_7_4 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 7), 1], FpPoly.ofCoeffs #[(5 : ZMod64 7), 3, 5, 1], FpPoly.ofCoeffs #[(0 : ZMod64 7), 0, 3, 1], FpPoly.ofCoeffs #[(2 : ZMod64 7), 3, 6, 5], FpPoly.ofCoeffs #[(0 : ZMod64 7), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(5 : ZMod64 7), 3, 5], right := FpPoly.ofCoeffs #[(1 : ZMod64 7), 6, 5, 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_7_4_incremental_check` confirms the incremental Rabin certificate `cert_7_4` validates for the committed `C(7, 4)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_7_4_irreducible`. -/
private theorem cert_7_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_4 luebeckConwayPolynomial_7_4_monic cert_7_4 = true := by
  decide

/-- The committed `C(7, 4)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_7_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_4
    luebeckConwayPolynomial_7_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_4 luebeckConwayPolynomial_7_4_monic cert_7_4 cert_7_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 5)` entry. -/
private def cert_7_5 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 7), 1], FpPoly.ofCoeffs #[(0 : ZMod64 7), 0, 3, 6], FpPoly.ofCoeffs #[(6 : ZMod64 7), 3, 0, 2, 4], FpPoly.ofCoeffs #[(4 : ZMod64 7), 2, 4, 4, 5], FpPoly.ofCoeffs #[(4 : ZMod64 7), 1, 0, 2, 5], FpPoly.ofCoeffs #[(0 : ZMod64 7), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(2 : ZMod64 7)], right := FpPoly.ofCoeffs #[(2 : ZMod64 7), 6, 2] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_7_5_incremental_check` confirms the incremental Rabin certificate `cert_7_5` validates for the committed `C(7, 5)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_7_5_irreducible`. -/
private theorem cert_7_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_5 luebeckConwayPolynomial_7_5_monic cert_7_5 = true := by
  decide

/-- The committed `C(7, 5)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_7_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_5
    luebeckConwayPolynomial_7_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_5 luebeckConwayPolynomial_7_5_monic cert_7_5 cert_7_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(7, 6)` entry. -/
private def cert_7_6 : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 7), 1], FpPoly.ofCoeffs #[(0 : ZMod64 7), 4, 1, 3, 2, 6], FpPoly.ofCoeffs #[(1 : ZMod64 7), 3, 4, 5, 5], FpPoly.ofCoeffs #[(6 : ZMod64 7), 4, 5, 6, 0, 4], FpPoly.ofCoeffs #[(3 : ZMod64 7), 2, 5, 0, 5, 3], FpPoly.ofCoeffs #[(4 : ZMod64 7), 0, 6, 0, 2, 1], FpPoly.ofCoeffs #[(0 : ZMod64 7), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(6 : ZMod64 7), 0, 2, 2], right := FpPoly.ofCoeffs #[(4 : ZMod64 7), 5, 0, 3, 0, 1] }, { left := FpPoly.ofCoeffs #[(1 : ZMod64 7), 1, 0, 2, 3], right := FpPoly.ofCoeffs #[(2 : ZMod64 7), 1, 2, 3, 3, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_7_6_incremental_check` confirms the incremental Rabin certificate `cert_7_6` validates for the committed `C(7, 6)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_7_6_irreducible`. -/
private theorem cert_7_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_7_6 luebeckConwayPolynomial_7_6_monic cert_7_6 = true := by
  decide

/-- The committed `C(7, 6)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_7_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_7_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_7_6
    luebeckConwayPolynomial_7_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_7_6 luebeckConwayPolynomial_7_6_monic cert_7_6 cert_7_6_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 1)` entry. -/
private def cert_11_1 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(2 : ZMod64 11)], FpPoly.ofCoeffs #[(2 : ZMod64 11)]]
  bezout := #[]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_11_1_incremental_check` confirms the incremental Rabin certificate `cert_11_1` validates for the committed `C(11, 1)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_11_1_irreducible`. -/
private theorem cert_11_1_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_1 luebeckConwayPolynomial_11_1_monic cert_11_1 = true := by
  decide

/-- The committed `C(11, 1)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_11_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_1
    luebeckConwayPolynomial_11_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_1 luebeckConwayPolynomial_11_1_monic cert_11_1 cert_11_1_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 2)` entry. -/
private def cert_11_2 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 11), 1], FpPoly.ofCoeffs #[(4 : ZMod64 11), 10], FpPoly.ofCoeffs #[(0 : ZMod64 11), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(5 : ZMod64 11)], right := FpPoly.ofCoeffs #[(6 : ZMod64 11), 8] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_11_2_incremental_check` confirms the incremental Rabin certificate `cert_11_2` validates for the committed `C(11, 2)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_11_2_irreducible`. -/
private theorem cert_11_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_2 luebeckConwayPolynomial_11_2_monic cert_11_2 = true := by
  decide

/-- The committed `C(11, 2)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_11_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_2
    luebeckConwayPolynomial_11_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_2 luebeckConwayPolynomial_11_2_monic cert_11_2 cert_11_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 3)` entry. -/
private def cert_11_3 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 11), 1], FpPoly.ofCoeffs #[(6 : ZMod64 11), 9, 10], FpPoly.ofCoeffs #[(5 : ZMod64 11), 1, 1], FpPoly.ofCoeffs #[(0 : ZMod64 11), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(10 : ZMod64 11), 1], right := FpPoly.ofCoeffs #[(9 : ZMod64 11), 7, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_11_3_incremental_check` confirms the incremental Rabin certificate `cert_11_3` validates for the committed `C(11, 3)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_11_3_irreducible`. -/
private theorem cert_11_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_3 luebeckConwayPolynomial_11_3_monic cert_11_3 = true := by
  decide

/-- The committed `C(11, 3)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_11_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_3
    luebeckConwayPolynomial_11_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_3 luebeckConwayPolynomial_11_3_monic cert_11_3 cert_11_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 4)` entry. -/
private def cert_11_4 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 11), 1], FpPoly.ofCoeffs #[(9 : ZMod64 11), 2, 7, 7], FpPoly.ofCoeffs #[(2 : ZMod64 11), 6, 10, 3], FpPoly.ofCoeffs #[(0 : ZMod64 11), 2, 5, 1], FpPoly.ofCoeffs #[(0 : ZMod64 11), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(5 : ZMod64 11), 5, 3], right := FpPoly.ofCoeffs #[(1 : ZMod64 11), 6, 9, 10] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_11_4_incremental_check` confirms the incremental Rabin certificate `cert_11_4` validates for the committed `C(11, 4)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_11_4_irreducible`. -/
private theorem cert_11_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_4 luebeckConwayPolynomial_11_4_monic cert_11_4 = true := by
  decide

/-- The committed `C(11, 4)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_11_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_4
    luebeckConwayPolynomial_11_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_4 luebeckConwayPolynomial_11_4_monic cert_11_4 cert_11_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 5)` entry. -/
private def cert_11_5 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 11), 1], FpPoly.ofCoeffs #[(2 : ZMod64 11), 4, 1, 4], FpPoly.ofCoeffs #[(9 : ZMod64 11), 2, 7, 7, 2], FpPoly.ofCoeffs #[(1 : ZMod64 11), 9, 1, 2, 6], FpPoly.ofCoeffs #[(10 : ZMod64 11), 6, 2, 9, 3], FpPoly.ofCoeffs #[(0 : ZMod64 11), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(6 : ZMod64 11), 10, 8], right := FpPoly.ofCoeffs #[(1 : ZMod64 11), 3, 6, 9, 9] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
/-- `cert_11_5_incremental_check` confirms the incremental Rabin certificate `cert_11_5` validates for the committed `C(11, 5)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_11_5_irreducible`. -/
private theorem cert_11_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_5 luebeckConwayPolynomial_11_5_monic cert_11_5 = true := by
  decide

/-- The committed `C(11, 5)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_11_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_5
    luebeckConwayPolynomial_11_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_5 luebeckConwayPolynomial_11_5_monic cert_11_5 cert_11_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(11, 6)` entry. -/
private def cert_11_6 : Berlekamp.IrreducibilityCertificate where
  p := 11
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 11), 1], FpPoly.ofCoeffs #[(10 : ZMod64 11), 7, 6, 3, 4, 1], FpPoly.ofCoeffs #[(5 : ZMod64 11), 10, 3, 2, 8, 9], FpPoly.ofCoeffs #[(9 : ZMod64 11), 2, 9, 6, 6, 3], FpPoly.ofCoeffs #[(10 : ZMod64 11), 3, 10, 10, 9, 3], FpPoly.ofCoeffs #[(10 : ZMod64 11), 10, 5, 1, 6, 6], FpPoly.ofCoeffs #[(0 : ZMod64 11), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(9 : ZMod64 11), 6, 7, 8, 2], right := FpPoly.ofCoeffs #[(1 : ZMod64 11), 3, 5, 1, 8, 1] }, { left := FpPoly.ofCoeffs #[(5 : ZMod64 11), 9, 6, 8], right := FpPoly.ofCoeffs #[(10 : ZMod64 11), 4, 6, 7, 1] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
/-- `cert_11_6_incremental_check` confirms the incremental Rabin certificate `cert_11_6` validates for the committed `C(11, 6)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_11_6_irreducible`. -/
private theorem cert_11_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_11_6 luebeckConwayPolynomial_11_6_monic cert_11_6 = true := by
  decide

/-- The committed `C(11, 6)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_11_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_11_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_11_6
    luebeckConwayPolynomial_11_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_11_6 luebeckConwayPolynomial_11_6_monic cert_11_6 cert_11_6_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 1)` entry. -/
private def cert_13_1 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 1
  powChain := #[FpPoly.ofCoeffs #[(2 : ZMod64 13)], FpPoly.ofCoeffs #[(2 : ZMod64 13)]]
  bezout := #[]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_13_1_incremental_check` confirms the incremental Rabin certificate `cert_13_1` validates for the committed `C(13, 1)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_13_1_irreducible`. -/
private theorem cert_13_1_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_1 luebeckConwayPolynomial_13_1_monic cert_13_1 = true := by
  decide

/-- The committed `C(13, 1)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_13_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_1 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_1
    luebeckConwayPolynomial_13_1_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_1 luebeckConwayPolynomial_13_1_monic cert_13_1 cert_13_1_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 2)` entry. -/
private def cert_13_2 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 13), 1], FpPoly.ofCoeffs #[(1 : ZMod64 13), 12], FpPoly.ofCoeffs #[(0 : ZMod64 13), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(8 : ZMod64 13)], right := FpPoly.ofCoeffs #[(11 : ZMod64 13), 4] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_13_2_incremental_check` confirms the incremental Rabin certificate `cert_13_2` validates for the committed `C(13, 2)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_13_2_irreducible`. -/
private theorem cert_13_2_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_2 luebeckConwayPolynomial_13_2_monic cert_13_2 = true := by
  decide

/-- The committed `C(13, 2)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_13_2_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_2 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_2
    luebeckConwayPolynomial_13_2_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_2 luebeckConwayPolynomial_13_2_monic cert_13_2 cert_13_2_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 3)` entry. -/
private def cert_13_3 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 3
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 13), 1], FpPoly.ofCoeffs #[(11 : ZMod64 13), 7, 5], FpPoly.ofCoeffs #[(2 : ZMod64 13), 5, 8], FpPoly.ofCoeffs #[(0 : ZMod64 13), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(6 : ZMod64 13), 10], right := FpPoly.ofCoeffs #[(0 : ZMod64 13), 9, 11] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_13_3_incremental_check` confirms the incremental Rabin certificate `cert_13_3` validates for the committed `C(13, 3)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_13_3_irreducible`. -/
private theorem cert_13_3_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_3 luebeckConwayPolynomial_13_3_monic cert_13_3 = true := by
  decide

/-- The committed `C(13, 3)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_13_3_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_3 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_3
    luebeckConwayPolynomial_13_3_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_3 luebeckConwayPolynomial_13_3_monic cert_13_3 cert_13_3_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 4)` entry. -/
private def cert_13_4 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 4
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 13), 1], FpPoly.ofCoeffs #[(12 : ZMod64 13), 2, 7, 11], FpPoly.ofCoeffs #[(5 : ZMod64 13), 9, 1, 4], FpPoly.ofCoeffs #[(9 : ZMod64 13), 1, 5, 11], FpPoly.ofCoeffs #[(0 : ZMod64 13), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(10 : ZMod64 13), 1, 4], right := FpPoly.ofCoeffs #[(4 : ZMod64 13), 3, 0, 12] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- `cert_13_4_incremental_check` confirms the incremental Rabin certificate `cert_13_4` validates for the committed `C(13, 4)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_13_4_irreducible`. -/
private theorem cert_13_4_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_4 luebeckConwayPolynomial_13_4_monic cert_13_4 = true := by
  decide

/-- The committed `C(13, 4)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_13_4_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_4 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_4
    luebeckConwayPolynomial_13_4_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_4 luebeckConwayPolynomial_13_4_monic cert_13_4 cert_13_4_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 5)` entry. -/
private def cert_13_5 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 5
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 13), 1], FpPoly.ofCoeffs #[(6 : ZMod64 13), 1, 0, 4, 10], FpPoly.ofCoeffs #[(2 : ZMod64 13), 8, 3, 0, 12], FpPoly.ofCoeffs #[(1 : ZMod64 13), 11, 6, 6, 6], FpPoly.ofCoeffs #[(4 : ZMod64 13), 5, 4, 3, 11], FpPoly.ofCoeffs #[(0 : ZMod64 13), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(9 : ZMod64 13), 5, 0, 7], right := FpPoly.ofCoeffs #[(1 : ZMod64 13), 0, 1, 6, 11] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
/-- `cert_13_5_incremental_check` confirms the incremental Rabin certificate `cert_13_5` validates for the committed `C(13, 5)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_13_5_irreducible`. -/
private theorem cert_13_5_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_5 luebeckConwayPolynomial_13_5_monic cert_13_5 = true := by
  decide

/-- The committed `C(13, 5)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_13_5_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_5 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_5
    luebeckConwayPolynomial_13_5_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_5 luebeckConwayPolynomial_13_5_monic cert_13_5 cert_13_5_incremental_check)

/-- Rabin irreducibility certificate for the committed `C(13, 6)` entry. -/
private def cert_13_6 : Berlekamp.IrreducibilityCertificate where
  p := 13
  n := 6
  powChain := #[FpPoly.ofCoeffs #[(0 : ZMod64 13), 1], FpPoly.ofCoeffs #[(2 : ZMod64 13), 10, 8, 11, 10, 3], FpPoly.ofCoeffs #[(1 : ZMod64 13), 5, 10, 9, 9, 1], FpPoly.ofCoeffs #[(9 : ZMod64 13), 2, 7, 4, 6, 7], FpPoly.ofCoeffs #[(1 : ZMod64 13), 4, 3, 12, 5, 8], FpPoly.ofCoeffs #[(0 : ZMod64 13), 4, 11, 3, 9, 7], FpPoly.ofCoeffs #[(0 : ZMod64 13), 1]]
  bezout := #[{ left := FpPoly.ofCoeffs #[(10 : ZMod64 13), 1, 9, 7, 1], right := FpPoly.ofCoeffs #[(7 : ZMod64 13), 3, 0, 8, 2, 12] }, { left := FpPoly.ofCoeffs #[(11 : ZMod64 13), 10, 11, 12, 4], right := FpPoly.ofCoeffs #[(2 : ZMod64 13), 0, 5, 10, 7, 5] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 20000000 in
/-- `cert_13_6_incremental_check` confirms the incremental Rabin certificate `cert_13_6` validates for the committed `C(13, 6)` entry: `checkIrreducibilityCertificateLinearIncremental` evaluates to `true`, supplying the irreducibility witness for `luebeckConwayPolynomial_13_6_irreducible`. -/
private theorem cert_13_6_incremental_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        luebeckConwayPolynomial_13_6 luebeckConwayPolynomial_13_6_monic cert_13_6 = true := by
  decide

/-- The committed `C(13, 6)` entry is irreducible. -/
@[grind .] theorem luebeckConwayPolynomial_13_6_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_13_6 :=
  Berlekamp.rabinTest_imp_irreducible
    luebeckConwayPolynomial_13_6
    luebeckConwayPolynomial_13_6_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      luebeckConwayPolynomial_13_6 luebeckConwayPolynomial_13_6_monic cert_13_6 cert_13_6_incremental_check)


end Conway

end Hex
