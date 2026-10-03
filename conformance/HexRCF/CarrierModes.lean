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
#guard !({normalized with cofactor := 1}).check 7 product
#guard !({normalized with core := DensePoly.ofList [-3, 0, 1]}).check 7 product
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

/-- Every nonzero rational polynomial has an actual checked monic proposal. -/
theorem rational_progress (input : DensePoly Rat) (nonzero : input ≠ 0) :
    ∃ cert, RadicalCert.buildMonic 7 input = some cert := by
  exact RadicalCert.buildMonic_success_real (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by norm_num)
    (fun a b => Rat.cast_add a b) (fun a b => Rat.cast_sub a b)
    (fun a b => Rat.cast_mul a b) (fun a b => Rat.cast_div a b)
    (fun a => Rat.cast_inv a) (fun n => by norm_num) 7 input nonzero

/-- info: 'Hex.RCF.CarrierModes.rational_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational_progress

/-- info: 'Hex.RCF.RealCoefficients.RadicalCert.buildMonic_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RadicalCert.buildMonic_success

/-- info: 'Hex.RCF.RealCoefficients.RadicalCert.buildMonic_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RadicalCert.buildMonic_squarefree

theorem negative_leading : ∀ x : ℝ, -(x ^ 2 + Real.sqrt 2) < 0 := by rcf

theorem repeated : ∀ x : ℝ, (x - Real.sqrt 2) ^ 4 ≥ 0 := by rcf

theorem common_root : ∃ x : ℝ,
    (x - Real.sqrt 2) ^ 2 = 0 ∧ (x - Real.sqrt 2) * (x - Real.sqrt 3) = 0 := by rcf

theorem leading_cancellation : ∀ x : ℝ,
    (Real.sqrt 2 - Real.sqrt 2) * x ^ 4 + x ^ 2 + Real.sqrt 2 > 0 := by rcf

set_option rcf.algebraic.monicCore false in
theorem raw_negative_leading : ∀ x : ℝ, -(x ^ 2 + Real.sqrt 2) < 0 := by rcf

set_option rcf.algebraic.monicCore false in
theorem raw_common_root : ∃ x : ℝ,
    (x - Real.sqrt 2) ^ 2 = 0 ∧ (x - Real.sqrt 2) * (x - Real.sqrt 3) = 0 := by rcf

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
/-- info: 'Hex.RCF.CarrierModes.raw_negative_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_negative_leading
/-- info: 'Hex.RCF.CarrierModes.raw_common_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_common_root

end Hex.RCF.CarrierModes
