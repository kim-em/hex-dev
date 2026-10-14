/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausTheory
public import HexBerlekampZassenhausTheory.LatticeTotality

public section

/-!
# Integer polynomial irreducibility API tests

These checks ensure that importing the package exposes the advertised
correspondence between executable and Mathlib irreducibility at the root
`Hex.ZPoly` namespace.
-/

#check Hex.ZPoly.Irreducible_iff_polynomialIrreducible
#check Hex.ZPoly.polynomialIrreducible_iff_irreducible
#check Hex.ZPoly.isIrreducible_iff

example (f : Hex.ZPoly) : Decidable (Hex.ZPoly.Irreducible f) :=
  inferInstance

/-!
The release-critical factorization statements must remain within Lean and
Mathlib's documented foundations.  Keeping these commands in a compiled test
module makes any new nonstandard axiom visible in both the monorepo and the
standalone package build.
-/

/--
info: 'Hex.factorize_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.factorize_product

/--
info: 'HexBerlekampZassenhausTheory.factorize_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HexBerlekampZassenhausTheory.factorize_unique

/--
info: 'HexBerlekampZassenhausTheory.factorize_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HexBerlekampZassenhausTheory.factorize_normalized

/--
info: 'HexBerlekampZassenhausTheory.factorize_irreducible_of_nonUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HexBerlekampZassenhausTheory.factorize_irreducible_of_nonUnit

/--
info: 'HexBerlekampZassenhausTheory.factorLattice_ne_none_of_directPrimePlan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HexBerlekampZassenhausTheory.factorLattice_ne_none_of_directPrimePlan
