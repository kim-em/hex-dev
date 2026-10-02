/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.Instances

public section

/-! Exact replay of a proposed root-preserving polynomial reduction. -/

namespace Hex.RCF.RealCoefficients

/-- A proposed core of a polynomial product. The two identities checked below
say that the core divides the product and every root of the complementary
factor is already a root of the core. They do not assert squarefreeness; the
prepared Sturm domain checks that property separately. -/
structure RadicalCert (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E] where
  context : Ctx
  core : DensePoly E
  quotient : DensePoly E
  cofactor : DensePoly E
  exponent : Nat

namespace RadicalCert

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [DecidableEq Ctx]

/-- Context identity is literal; semantic polynomial identities use zero
differences so canonical-zero coefficient representations are accepted. A
compiled verdict still needs a proof of this Boolean check for kernel replay. -/
@[expose] def check (context : Ctx) (product : DensePoly E)
    (cert : RadicalCert E Ctx) : Bool :=
  decide (cert.context = context) &&
    decide (cert.exponent ≤ product.natDegree) &&
    (product - cert.core * cert.quotient).isZero &&
    (DensePoly.natPow cert.core (cert.exponent + 1) -
      cert.quotient * cert.cofactor).isZero &&
    !cert.core.isZero

theorem check_context (context : Ctx) (product : DensePoly E)
    (cert : RadicalCert E Ctx) (h : cert.check context product = true) :
    cert.context = context := by
  simp only [check, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.1.1

/-- Replay bounds the exponent before constructing the proposed power. -/
theorem check_bound (context : Ctx) (product : DensePoly E)
    (cert : RadicalCert E Ctx) (h : cert.check context product = true) :
    cert.exponent ≤ product.natDegree := by
  simp only [check, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.1.2

theorem check_identities (context : Ctx) (product : DensePoly E)
    (cert : RadicalCert E Ctx) (h : cert.check context product = true) :
    (product - cert.core * cert.quotient).isZero = true ∧
      (DensePoly.natPow cert.core (cert.exponent + 1) -
        cert.quotient * cert.cofactor).isZero = true ∧
      cert.core.isZero = false := by
  simp only [check, Bool.and_eq_true] at h
  have hcore : cert.core.isZero = false := by
    cases hc : cert.core.isZero <;> simp_all
  exact ⟨h.1.1.2, h.1.2, hcore⟩

/-- The proposed core cannot be the zero polynomial. -/
theorem core_ne_zero (context : Ctx) (product : DensePoly E)
    (cert : RadicalCert E Ctx) (h : cert.check context product = true) :
    cert.core ≠ 0 := by
  intro hzero
  have hcore := (cert.check_identities context product h).2.2
  rw [hzero] at hcore
  have hz : (0 : DensePoly E).isZero = true := by rfl
  exact Bool.false_ne_true (hcore.symm.trans hz)

end RadicalCert
end Hex.RCF.RealCoefficients
