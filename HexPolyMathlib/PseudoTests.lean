/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyMathlib.Pseudo
public import HexPoly.PseudoTests

public section

/-! Ordinary proof probes for integer and noninjective pseudo-division correspondence. -/
namespace HexPolyMathlib.PseudoTests

open Hex DensePoly HexPolyMathlib.Interpret

theorem cast_zero (z : Int) : (z : Rat) = 0 ↔ z = 0 := Int.cast_eq_zero

noncomputable abbrev denoteInt := interpret (fun z : Int => (z : Rat)) cast_zero

theorem integer_division (p q : DensePoly Int) :
    (denoteInt (pseudoDiv p q).quotient, denoteInt (pseudoDiv p q).remainder) =
      (Polynomial.C ((pseudoDiv p q).multiplier : Rat) * (denoteInt p / denoteInt q),
       Polynomial.C ((pseudoDiv p q).multiplier : Rat) * (denoteInt p % denoteInt q)) :=
  pseudo_divMod (fun z : Int => (z : Rat)) cast_zero (by decide +kernel)
    (fun a b => Int.cast_add a b) (fun a b => Int.cast_sub a b) (fun a b => Int.cast_mul a b) p q

theorem integer_gcd (p q : DensePoly Int) :
    Associated (denoteInt (pseudoGcd p q)) (EuclideanDomain.gcd (denoteInt p) (denoteInt q)) :=
  interpret_pseudoGcd (fun z : Int => (z : Rat)) cast_zero (by decide +kernel)
    (fun a b => Int.cast_add a b) (fun a b => Int.cast_sub a b) (fun a b => Int.cast_mul a b) p q

open HexPoly.InterpretTests
noncomputable abbrev denoteRep := interpret value value_eq_zero

theorem noninjective_division (p q : Poly) :
    (denoteRep (pseudoDiv p q).quotient, denoteRep (pseudoDiv p q).remainder) =
      (Polynomial.C (value (pseudoDiv p q).multiplier) * (denoteRep p / denoteRep q),
       Polynomial.C (value (pseudoDiv p q).multiplier) * (denoteRep p % denoteRep q)) :=
  pseudo_divMod value value_eq_zero value_one value_add value_sub value_mul p q

theorem noninjective_gcd (p q : Poly) :
    Associated (denoteRep (pseudoGcd p q)) (EuclideanDomain.gcd (denoteRep p) (denoteRep q)) :=
  interpret_pseudoGcd value value_eq_zero value_one value_add value_sub value_mul p q

/-- info: 'HexPolyMathlib.PseudoTests.integer_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integer_division
/-- info: 'HexPolyMathlib.PseudoTests.noninjective_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noninjective_gcd

end HexPolyMathlib.PseudoTests
