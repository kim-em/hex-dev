/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateDivisionCheck
public import HexGroebner.CertificateContainment

@[expose] public section

namespace Hex.Groebner
namespace Certificate

/-- A shared forward containment and explicit zero-remainder representation.
No Gröbner-basis claim is needed for this positive membership certificate. -/
structure Combination where
  basis : Array Polynomial
  forward : Containment
  division : Division
  deriving Repr, Inhabited

/-- Positive certificates support direct shared derivations and composition of
an accepted forward containment with explicit cofactors. -/
inductive Member where
  | derivation (value : Derivation)
  | combination (value : Combination)
  deriving Repr, Inhabited

end Certificate

/-- Independent positive membership checking. Composition validates the shared
forward derivation, the exact cofactor identity and the zero remainder. -/
def checkMember (context : Context) (generators : Array Certificate.Polynomial)
    (target : Certificate.Polynomial) : Certificate.Member → Bool
  | .derivation value => checkDerivation context generators target value
  | .combination value =>
    Certificate.checkContainment context.field.modulus.toNat context.variables
      generators value.basis value.forward &&
    Certificate.checkDivision context.field.modulus.toNat context.variables context.order
      value.basis target value.division && Hex.MvPoly.Kernel.isZero value.division.remainder

end Hex.Groebner
