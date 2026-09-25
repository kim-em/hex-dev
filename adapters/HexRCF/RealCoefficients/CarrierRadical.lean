/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Carrier
public import HexRCF.RealCoefficients.Radical

public section

/-! Transfer atom root coverage through a checked repeated-root reduction. -/

namespace Hex.RCF.RealCoefficients.Specialize

open Hex.RealFormula HexPolyMathlib.Interpret

/-- Every nonzero atom root remains a root of the reduced head. The first
alternative records atoms that vanish identically after specialization. -/
theorem atom_roots_of_radical {Ctx : Type u} [DecidableEq Ctx]
    (values : Fin n → RealAlgebraicNumber) (formula : QF (n + 1))
    (context : Ctx) (cert : RadicalCert RealAlgebraicNumber Ctx)
    (checked : cert.check context (product values formula) = true)
    (p : Hex.RealFormula.Poly (n + 1)) (hp : p ∈ formula.polys) :
    interpret RealAlgebraicNumber.toReal toReal_eq_zero (polynomial values p) = 0 ∨
      (∀ x, (interpret RealAlgebraicNumber.toReal toReal_eq_zero
          (polynomial values p)).IsRoot x →
        (interpret RealAlgebraicNumber.toReal toReal_eq_zero cert.core).IsRoot x) := by
  rcases atom_roots values formula p hp with hzero | hroots
  · exact Or.inl hzero
  · right
    intro x hx
    exact (cert.roots_algebraic context (product values formula) checked x).mpr
      (hroots x hx)

end Hex.RCF.RealCoefficients.Specialize
