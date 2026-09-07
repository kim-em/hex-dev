/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexConway.CompatibilityCore

public import HexConway.CompatibilityProofs.S0_0
public import HexConway.CompatibilityProofs.S0_1
public import HexConway.CompatibilityProofs.S0_2
public import HexConway.CompatibilityProofs.S0_3
public import HexConway.CompatibilityProofs.S0_4
public import HexConway.CompatibilityProofs.S0_5
public import HexConway.CompatibilityProofs.S1_0
public import HexConway.CompatibilityProofs.S1_1
public import HexConway.CompatibilityProofs.S1_2
public import HexConway.CompatibilityProofs.S1_3
public import HexConway.CompatibilityProofs.S1_4
public import HexConway.CompatibilityProofs.S1_5
public import HexConway.CompatibilityProofs.S2_0
public import HexConway.CompatibilityProofs.S2_1
public import HexConway.CompatibilityProofs.S2_2
public import HexConway.CompatibilityProofs.S2_3
public import HexConway.CompatibilityProofs.S2_4
public import HexConway.CompatibilityProofs.S2_5
public import HexConway.CompatibilityProofs.S3_0
public import HexConway.CompatibilityProofs.S3_1
public import HexConway.CompatibilityProofs.S3_2
public import HexConway.CompatibilityProofs.S3_3
public import HexConway.CompatibilityProofs.S3_4
public import HexConway.CompatibilityProofs.S3_5

public section

namespace Hex
namespace Conway

set_option maxRecDepth 1000000
set_option maxHeartbeats 80000000

-- BEGIN GENERATED
-- END GENERATED

/-- Re-export a supplied compatibility witness through the uniform API.
The generated `compat_p_m_n` theorems supply the witnesses for supported
proper-divisor pairs. -/
theorem conwayPoly_compat (p m n : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (_hdvd : m ∣ n) (hm : SupportedEntry p m) (hn : SupportedEntry p n)
    (hcompat : Compatible p m n hm hn) :
    Compatible p m n hm hn :=
  hcompat

/-- Compatibility is not vacuous: it fails when the degrees are not in the
subfield lattice. Here `4 ∤ 6`, and the check says so rather than returning
`true` for everything put in front of it. -/
theorem not_compatible_11_4_6 :
    ¬ Compatible 11 4 6 supportedEntry_11_4 supportedEntry_11_6 := by
  decide

end Conway

end Hex
