/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.ModSound
public import HexReflectMathlib.Residue

public section

namespace Hex.Kronecker

open scoped HexModArithMathlib.ZMod64

/-- The residue provider's interpretation agrees with the canonical integer lift.
This coefficient bridge requires no injectivity assumption on the target ring. -/
theorem residue_cast {p : Nat} [Hex.ZMod64.Bounds p]
    {R : Type u} [CommRing R] [CharP R p] (a : Hex.ZMod64 p) :
    HexReflectMathlib.residueHom p R a = ((a.toNat : Int) : R) := by
  have ha : (a.toNat : Hex.ZMod64 p) = a := by
    apply HexModArithMathlib.ZMod64.equiv.injective
    change HexModArithMathlib.ZMod64.toZMod (a.toNat : Hex.ZMod64 p) = _
    rw [HexModArithMathlib.ZMod64.toZMod_natCast]
    rfl
  calc
    HexReflectMathlib.residueHom p R a =
        HexReflectMathlib.residueHom p R (a.toNat : Hex.ZMod64 p) := congrArg _ ha.symm
    _ = ((a.toNat : Int) : R) := by rw [map_natCast]; simp

/-- Canonical machine residues give admissible integer literals to the Mod checks. -/
theorem residue_literal {p : Nat} [Hex.ZMod64.Bounds p] (a : Hex.ZMod64 p) :
    Expr.residues p (.int a.toNat) = true := by
  simp only [Expr.residues, Bool.and_eq_true_iff, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr a.toNat_lt⟩

end Hex.Kronecker
