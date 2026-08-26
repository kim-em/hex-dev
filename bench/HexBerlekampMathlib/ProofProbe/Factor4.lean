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

/-! `factor_poly` on a degree-4 product of two distinct irreducible
quadratics over `F_5`. -/

set_option maxHeartbeats 1000000 in
noncomputable def factor4 :=
  factor_poly ((X ^ 2 + 2) * (X ^ 2 + 3) : Polynomial (ZMod 5))

#print axioms factor4

end HexBerlekampMathlib.ProofProbe
