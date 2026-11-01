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
  let heads := divisors.toList.map (leading order)
  remainder.all fun term => heads.all fun head =>
    match head with
    | none => true
    | some head => !divides head.1 term.1

/-- Caching leading terms preserves the original exact predicate. -/
theorem irreducible_eq (order : TermOrder) (divisors : Array Polynomial) (remainder : Polynomial) :
    irreducible order divisors remainder =
      remainder.all (fun term => divisors.toList.all fun divisor =>
        match leading order divisor with
        | none => true
        | some head => !divides head.1 term.1) := by
  simp [irreducible, List.all_map]

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
    let targetHead := leading order dividend
    rows.all (fun row => degreeLELeading order (leading order row) targetHead) &&
      degreeLELeading order (leading order result.remainder) targetHead &&
      irreducible order divisors result.remainder &&
      Hex.MvPoly.Kernel.beq
        (Hex.MvPoly.Kernel.addMod p (sum p rows) result.remainder) dividend

end Hex.Groebner.Certificate
