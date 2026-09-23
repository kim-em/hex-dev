/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.RootAliases
public meta import HexRCF.RealCoefficients.RootAliases
public meta import HexRealAlgebraicMathlib.Order
public meta import HexRealAlgebraic.Order

public section

/-! Exact algebraic coefficient aliases. These check coefficient conversion,
not discharge of quantified goals by the optional tactic handler.
Computational conformance owner: `HexRCF`. -/
namespace Hex.RCF.RootAliasTests

open RealCoefficients.Coefficients

@[expose] def two : RealAlgebraicNumber := 2
theorem two_nonneg : 0 ≤ two := by norm_num [two]
theorem two_toReal : two.toReal = 2 := by
  change RealAlgebraicNumber.toRealHom (2 : RealAlgebraicNumber) = 2
  exact map_ofNat _ _

@[expose] def cubeRoot : RealAlgebraicNumber := root two 3 two_nonneg
@[expose] def squareRoot : RealAlgebraicNumber := root two 2 two_nonneg

#guard cubeRoot ^ 3 = 2
#guard 1 < cubeRoot && cubeRoot < 3 / 2
#guard squareRoot ^ 2 = 2
#guard root (0 : RealAlgebraicNumber) 3 (le_refl _) = 0
#guard root two 0 two_nonneg = 1

/-- The cubic coefficient uses Mathlib's real-root notation with its exact branch. -/
theorem cubic_alias : cubeRoot.toReal = (2 : ℝ) ^ (1 / 3 : ℝ) := by
  simpa only [cubeRoot, two_toReal, Nat.cast_ofNat] using root_toReal two 3 two_nonneg

/-- The same construction authenticates the familiar square-root notation. -/
theorem square_alias : squareRoot.toReal = Real.sqrt 2 := by
  simpa only [squareRoot, two_toReal] using root_two two two_nonneg

/-- Kernel proofs identify the selected nonnegative cubic root. -/
theorem cubic_power : cubeRoot ^ 3 = 2 := root_pow two 3 two_nonneg (by decide)

theorem cubic_nonneg : 0 ≤ cubeRoot := root_nonneg two 3 two_nonneg

/-- info: 'Hex.RCF.RootAliasTests.cubic_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_power

/-- info: 'Hex.RCF.RootAliasTests.cubic_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_nonneg

/-- info: 'Hex.RCF.RootAliasTests.cubic_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_alias

/-- info: 'Hex.RCF.RootAliasTests.square_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square_alias

end Hex.RCF.RootAliasTests
