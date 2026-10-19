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

/-! `factor_poly` on a degree-8 fourth power of one irreducible quadratic
over `F_5`: same degree and factor count as `Factor8`, all multiplicity. -/

set_option maxHeartbeats 1000000 in
noncomputable def repeated8 :=
  factor_poly
    ((X ^ 2 + 2) * (X ^ 2 + 2) * (X ^ 2 + 2) * (X ^ 2 + 2) :
      Polynomial (ZMod 5))

/-- info: 'HexBerlekampTheory.ProofProbe.repeated8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms repeated8

end HexBerlekampTheory.ProofProbe
