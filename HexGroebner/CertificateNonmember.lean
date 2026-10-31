/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateDivisionCheck

@[expose] public section

namespace Hex.Groebner
namespace Certificate

/-- A complete basis certificate and an independently reconstructed nonzero
irreducible remainder prove nonmembership in the original generated ideal. -/
structure Nonmember where
  basis : Array Polynomial
  certificate : Basis
  division : Division
  deriving Repr, Inhabited

end Certificate

/-- Negative membership never trusts an unchecked producer: both ideal
containments, the full basis and exact division are replayed independently. -/
def checkNonmember (context : Context) (generators : Array Certificate.Polynomial)
    (target : Certificate.Polynomial) (witness : Certificate.Nonmember) : Bool :=
  checkBasis context generators witness.basis witness.certificate &&
    Certificate.checkDivision context.field.modulus.toNat context.variables context.order
      witness.basis target witness.division &&
    !Hex.MvPoly.Kernel.isZero witness.division.remainder

end Hex.Groebner
