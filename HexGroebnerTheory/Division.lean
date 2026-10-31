/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Division
public import HexGroebnerTheory.CertificateDivision
public import HexGroebnerTheory.Certificate

public section

namespace HexGroebnerTheory
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

/-- Explicit quotients reconstruct the dividend, and the remainder is standard
and irreducible by the supplied divisors. No Gröbner-basis hypothesis is needed. -/
@[expose] def DivisionSpec (context : Hex.Groebner.Context)
    (divisors : Array Hex.Groebner.Certificate.Polynomial)
    (dividend : Hex.Groebner.Certificate.Polynomial) (value : Hex.Groebner.Certificate.Division) : Prop :=
  (∀ q ∈ value.quotients, Hex.MvPoly.Kernel.CanonicalMod context.field.modulus.toNat context.variables q) ∧
    Hex.MvPoly.Kernel.CanonicalMod context.field.modulus.toNat context.variables value.remainder ∧
    value.quotients.size = divisors.size ∧
    denote context dividend = (∑ i : Fin divisors.size,
      denote context (value.quotients[i.val]?.getD []) * denote context divisors[i]) +
        denote context value.remainder ∧
    (toMonomialOrder (context.order.cmp context.variables)).IsRemainder
      (denote context dividend) (Set.range fun i : Fin divisors.size => denote context divisors[i])
      (denote context value.remainder)

/-- A checked receipt has the full division postcondition independently of its producer. -/
theorem checkedDivision_sound (context : Hex.Groebner.Context)
    (divisors : Array Hex.Groebner.Certificate.Polynomial)
    (dividend : Hex.Groebner.Certificate.Polynomial)
    (value : Hex.Groebner.Certificate.CheckedDivision context divisors dividend) :
    DivisionSpec context divisors dividend value.value := by
  let := fieldBounds context.field
  let : Fact context.field.modulus.toNat.Prime := ⟨fieldPrime context.field⟩
  exact Certificate.checkDivision_sound context.order divisors dividend value.value value.accepted

/-- Successful bounded division is correct without any producer-provenance
hypothesis. Generation and replay exhaustion never become successful results. -/
theorem divideWith_sound (context : Hex.Groebner.Context) (budget : Hex.Groebner.Certificate.Budget)
    (divisors : Array Hex.Groebner.Certificate.Polynomial)
    (dividend : Hex.Groebner.Certificate.Polynomial)
    (value : Hex.Groebner.Certificate.CheckedDivision context divisors dividend)
    (usage : Hex.Groebner.Certificate.Usage)
    (_h : Hex.Groebner.divideWith context budget divisors dividend = .success value usage) :
    DivisionSpec context divisors dividend value.value :=
  checkedDivision_sound context divisors dividend value

end HexGroebnerTheory
