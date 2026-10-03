/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public section

namespace Hex.RCF.CarrierModes
open Hex RealCoefficients

set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option rcf.algebraic.monicCore true

def product : DensePoly Rat := DensePoly.ofList [-6, 0, 3]
def normalized : RadicalCert Rat Nat :=
  ⟨7, DensePoly.ofList [-2, 0, 1], 3,
    DensePoly.ofList [-2 / 3, 0, 1 / 3], 0⟩

-- The normalized certificate retains the original scalar in its quotient.
#guard normalized.check 7 product
#guard !(normalized.check 8 product)
#guard !({normalized with quotient := 1}).check 7 product
#guard (RadicalCert.buildMonic 7 product).isSome
#guard (RadicalCert.buildMonic 7 (0 : DensePoly Rat)).isNone
#guard (RadicalCert.buildMonic 7 (3 : DensePoly Rat)).isSome

-- Check the exact producer output, including the scalar retained in its
-- quotient. This fixture distinguishes normalization from the raw producer.
#guard (RadicalCert.buildMonic 7 product).map
    (fun c => (c.context, c.core, c.quotient, c.cofactor, c.exponent)) ==
    some (7, normalized.core, normalized.quotient, normalized.cofactor,
      normalized.exponent)

#guard (RadicalCert.build 7 product).map (·.core) != some normalized.core

theorem negative_leading : ∀ x : ℝ, -(x ^ 2 + Real.sqrt 2) < 0 := by rcf

theorem repeated : ∀ x : ℝ, (x - Real.sqrt 2) ^ 4 ≥ 0 := by rcf

theorem common_root : ∃ x : ℝ,
    (x - Real.sqrt 2) ^ 2 = 0 ∧ (x - Real.sqrt 2) * (x - Real.sqrt 3) = 0 := by rcf

theorem leading_cancellation : ∀ x : ℝ,
    (Real.sqrt 2 - Real.sqrt 2) * x ^ 4 + x ^ 2 + Real.sqrt 2 > 0 := by rcf

/-- info: 'Hex.RCF.CarrierModes.negative_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negative_leading
/-- info: 'Hex.RCF.CarrierModes.repeated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms repeated
/-- info: 'Hex.RCF.CarrierModes.common_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms common_root
/-- info: 'Hex.RCF.CarrierModes.leading_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leading_cancellation

end Hex.RCF.CarrierModes
