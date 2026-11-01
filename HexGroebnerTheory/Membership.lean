/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Membership
public import HexGroebnerTheory.NormalForm
public import HexGroebnerTheory.Member

public section

namespace HexGroebnerTheory
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

/-- A successful zero normal form proves membership in the original input ideal.
The result includes an independently checked derivation against the original
generators as well as explicit cofactors against the accepted basis. -/
theorem memberWith_member_sound (basis : Hex.Groebner.CheckedBasis)
    (budget : Hex.Groebner.Certificate.Budget) (target : Hex.Groebner.Certificate.Polynomial)
    (value : Hex.Groebner.Certificate.CheckedDivision basis.context basis.polynomials target)
    (certificate : Hex.Groebner.CheckedMember basis target)
    (zero : Hex.MvPoly.Kernel.isZero value.value.remainder = true)
    (usage : Hex.Groebner.Certificate.Usage)
    (_h : Hex.Groebner.memberWith basis budget target = .member value certificate zero usage) :
    denote basis.context target ∈ Ideal.span
      (Set.range fun i : Fin basis.generators.size => denote basis.context basis.generators[i]) :=
  checkMember_sound basis.context basis.generators target certificate.witness certificate.accepted

/-- A negative result carries a complete independently accepted nonmembership
certificate; exhaustion and failed verification cannot inhabit this case. -/
theorem memberWith_nonmember_sound (basis : Hex.Groebner.CheckedBasis)
    (budget : Hex.Groebner.Certificate.Budget) (target : Hex.Groebner.Certificate.Polynomial)
    (value : Hex.Groebner.CheckedNonmember basis target) (usage : Hex.Groebner.Certificate.Usage)
    (_h : Hex.Groebner.memberWith basis budget target = .nonmember value usage) :
    denote basis.context target ∉ Ideal.span
      (Set.range fun i : Fin basis.generators.size => denote basis.context basis.generators[i]) :=
  checkNonmember_sound basis.context basis.generators target value.witness value.accepted

end HexGroebnerTheory
