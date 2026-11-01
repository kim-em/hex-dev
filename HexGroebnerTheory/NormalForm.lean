/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.NormalForm
public import HexGroebnerTheory.CertificateNormalForm
public import HexGroebnerTheory.Division

public section

namespace HexGroebnerTheory

/-- A successful normal-form call is the unique irreducible representative of
its original-ideal coset, independently of the candidate producer. -/
theorem normalFormWith_sound (basis : Hex.Groebner.CheckedBasis)
    (budget : Hex.Groebner.Certificate.Budget) (target : Hex.Groebner.Certificate.Polynomial)
    (value : Hex.Groebner.Certificate.CheckedDivision basis.context basis.polynomials target)
    (usage : Hex.Groebner.Certificate.Usage)
    (_h : Hex.Groebner.normalFormWith basis budget target = .success value usage) :
    IsNormalForm basis.context basis.generators basis.polynomials target
        (denote basis.context value.value.remainder) ∧
      ∀ r, IsNormalForm basis.context basis.generators basis.polynomials target r →
        r = denote basis.context value.value.remainder :=
  normalForm_spec basis.context basis.generators basis.polynomials basis.certificate target value.value
    basis.accepted value.accepted

end HexGroebnerTheory
