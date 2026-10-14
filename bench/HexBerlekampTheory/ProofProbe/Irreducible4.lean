/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampTheory.FactorTactic
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampTheory.FactorTactic

public section

open Polynomial

namespace HexBerlekampTheory.ProofProbe

/-! `irreducibility` on an irreducible quartic over `F_5`. -/

set_option maxHeartbeats 1000000 in
theorem irreducible4 : Irreducible (X ^ 4 + 2 : Polynomial (ZMod 5)) :=
  irreducibility (X ^ 4 + 2 : Polynomial (ZMod 5))

/-- info: 'HexBerlekampTheory.ProofProbe.irreducible4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms irreducible4

end HexBerlekampTheory.ProofProbe
