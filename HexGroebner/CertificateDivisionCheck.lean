/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateDivision

@[expose] public section

namespace Hex.Groebner.Certificate

/-- No remainder term is divisible by the actual leading monomial of a nonzero
supplied divisor. Zero divisors have no leading monomial and are skipped. -/
def irreducible (order : TermOrder) (divisors : Array Polynomial) (remainder : Polynomial) : Bool :=
  remainder.all fun term => divisors.toList.all fun divisor =>
    match leading order divisor with
    | none => true
    | some head => !divides head.1 term.1

/-- Independently check explicit quotients, reconstruction, irreducibility and
standard division degree bounds. This uses only ordinary coefficient and term
lists and makes no Gröbner-basis assumption about the supplied divisors. -/
def checkDivision (p n : Nat) (order : TermOrder) (divisors : Array Polynomial)
    (dividend : Polynomial) (result : Division) : Bool :=
  if result.quotients.size != divisors.size ||
      !divisors.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) ||
      !result.quotients.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) ||
      !Hex.MvPoly.Kernel.isCanonicalMod p n dividend ||
      !Hex.MvPoly.Kernel.isCanonicalMod p n result.remainder then false else
    let rows := products p divisors result.quotients
    rows.all (fun row => degreeLE order row dividend) &&
      degreeLE order result.remainder dividend &&
      irreducible order divisors result.remainder &&
      Hex.MvPoly.Kernel.beq
        (Hex.MvPoly.Kernel.addMod p (sum p rows) result.remainder) dividend

end Hex.Groebner.Certificate
