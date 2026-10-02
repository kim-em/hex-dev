/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.PseudoInterpret
public import HexPoly.InterpretTests
public meta import HexPoly.InterpretTests
public meta import HexPoly.PseudoGcd
public meta import HexPoly.PseudoDiv

public section

/-! Integer and noncanonical-coefficient regressions for shared pseudo-division. -/
namespace HexPoly.PseudoTests

open Hex DensePoly

@[expose] def p : DensePoly Int := ofCoeffs #[1, 0, 1]
@[expose] def q : DensePoly Int := ofCoeffs #[1, 2]

example : (pseudoDiv p q).multiplier = 4 := by
  simp only [pseudoDiv, pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel
example : (pseudoDiv p q).quotient.toArray.toList = [-1, 2] := by
  simp only [pseudoDiv, pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel
example : (pseudoDiv p q).remainder.toArray.toList = [5] := by
  simp only [pseudoDiv, pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel
example : (pseudoDiv p 0).multiplier = 1 := by
  simp only [pseudoDiv, pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel
example : (pseudoDiv p 0).remainder = p := by
  simp only [pseudoDiv, pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel
example : (pseudoDiv (0 : DensePoly Int) q).multiplier = 1 := by
  simp only [pseudoDiv, pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel

@[expose] def negative : DensePoly Int := ofCoeffs #[3, -2]
@[expose] def linear : DensePoly Int := ofCoeffs #[1, 1]
example : (pseudoDiv linear negative).multiplier = -2 := by
  simp only [pseudoDiv, pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel
example : (positivePseudoDiv Int.sign linear negative).multiplier = 2 := by
  simp only [positivePseudoDiv, pseudoDiv, pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel
example : (positivePseudoDiv Int.sign linear negative).quotient.toArray.toList = [-1] := by
  simp only [positivePseudoDiv, pseudoDiv, pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel
example : (positivePseudoDiv Int.sign linear negative).remainder.toArray.toList = [5] := by
  simp only [positivePseudoDiv, pseudoDiv, pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel

example : (pseudoGcd (C (2 : Int)) (ofCoeffs #[0, 1])).toArray.toList = [2] := by
  have hfirst : pseudoDivMod (C (2 : Int)) (ofCoeffs #[0, 1]) = (0, C 2) :=
    pseudoDivMod_of_size_lt _ _ (by decide +kernel)
  have hlast : (pseudoDivMod (ofCoeffs #[0, 1]) (C (2 : Int))).2 = 0 := by
    simp only [pseudoDivMod, ← Array.foldl_toList, Array.toList_range]
    decide +kernel
  rw [pseudoGcd_step _ _ (by decide +kernel), hfirst,
    pseudoGcd_step _ _ (by decide +kernel), hlast, pseudoGcd_zero_right]
  decide +kernel
example : (pseudoGcd (ofCoeffs #[0, 4]) (C (4 : Int))).toArray.toList = [4] := by
  have hlast : (pseudoDivMod (ofCoeffs #[0, 4]) (C (4 : Int))).2 = 0 := by
    simp only [pseudoDivMod, ← Array.foldl_toList, Array.toList_range]
    decide +kernel
  rw [pseudoGcd_step _ _ (by decide +kernel), hlast, pseudoGcd_zero_right]
  decide +kernel
example : pseudoGcd (0 : DensePoly Int) 0 = 0 := pseudoGcd_zero_right _

#guard (pseudoDiv p q).quotient.toArray.toList == [-1, 2]
#guard (pseudoDiv p q).remainder.toArray.toList == [5]
#guard (positivePseudoDiv Int.sign linear negative).remainder.toArray.toList == [5]
#guard (pseudoGcd (C (2 : Int)) (ofCoeffs #[0, 1])).toArray.toList == [2]

open HexPoly.InterpretTests in
theorem noninjective_division (p q : Poly) :
    (mapped (pseudoDivMod p q).1, mapped (pseudoDivMod p q).2) =
      pseudoDivMod (mapped p) (mapped q) :=
  Interpret.map_pseudoDivMod value value_eq_zero value_one value_add value_sub value_mul p q

open HexPoly.InterpretTests in
theorem noninjective_gcd (p q : Poly) :
    mapped (pseudoGcd p q) = pseudoGcd (mapped p) (mapped q) :=
  Interpret.map_pseudoGcd value value_eq_zero value_one value_add value_sub value_mul p q

open HexPoly.InterpretTests in
example : mapped (pseudoDivMod product noncanonicalDivisor).1 =
    (ofCoeffs #[-5, 2] : DensePoly Rat) := by
  simp only [pseudoDivMod, ← Array.foldl_toList, Array.toList_range]
  decide +kernel
open HexPoly.InterpretTests in
example : mapped (pseudoDivMod product noncanonicalDivisor).2 = C (9 : Rat) := by
  simp only [pseudoDivMod, ← Array.foldl_toList, Array.toList_range]
  decide +kernel
open HexPoly.InterpretTests in
example : pseudoGcd product a = a := by
  have hr : (pseudoDivMod product a).2 = 0 := by
    simp only [pseudoDivMod, ← Array.foldl_toList, Array.toList_range]
    decide +kernel
  rw [pseudoGcd_step _ _ (by decide +kernel), hr, pseudoGcd_zero_right]

open HexPoly.InterpretTests in
#guard (mapped (pseudoDivMod product noncanonicalDivisor).1).toArray.toList == [-5, 2]
open HexPoly.InterpretTests in
#guard (mapped (pseudoDivMod product noncanonicalDivisor).2).toArray.toList == [9]

/-- info: 'HexPoly.PseudoTests.noninjective_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noninjective_division
/-- info: 'HexPoly.PseudoTests.noninjective_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noninjective_gcd

end HexPoly.PseudoTests
