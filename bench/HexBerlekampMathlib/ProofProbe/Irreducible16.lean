/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampMathlib.FactorTactic
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampMathlib.FactorTactic

public section

open Polynomial

namespace HexBerlekampMathlib.ProofProbe

/-! `irreducibility` on an irreducible degree-16 binomial over `F_5`. -/

set_option maxHeartbeats 1000000 in
theorem irreducible16 : Irreducible (X ^ 16 + 2 : Polynomial (ZMod 5)) :=
  irreducibility (X ^ 16 + 2 : Polynomial (ZMod 5))

#print axioms irreducible16

end HexBerlekampMathlib.ProofProbe
