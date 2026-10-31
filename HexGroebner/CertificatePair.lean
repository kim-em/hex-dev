/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateOrder

@[expose] public section

namespace Hex.Groebner.Certificate

/-- Pointwise truncated subtraction. Certificate callers validate equal arities. -/
def difference (a b : List Nat) : List Nat := a.zipWith Nat.sub b

/-- The exact S-polynomial in the selected global order, using the opposite
leading coefficient and pointwise exponent differences. Inputs must first pass
canonical residue checks. The result uses descending-lex certificate storage.
Zero inputs give zero. This operation alone proves no reduction obligation. -/
def sPolynomial (p : Nat) (order : TermOrder) (f g : Polynomial) : Polynomial :=
  match leading order f, leading order g with
  | some a, some b =>
    Hex.MvPoly.Kernel.subMod p
      (Hex.MvPoly.Kernel.mulMod p [(difference b.1 a.1, b.2)] f)
      (Hex.MvPoly.Kernel.mulMod p [(difference a.1 b.1, a.2)] g)
  | _, _ => []

end Hex.Groebner.Certificate
