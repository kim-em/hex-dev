/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Membership
public import HexGroebnerTheory.NormalForm

public section

namespace HexGroebnerTheory
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

/-- A successful zero normal form proves membership in the original input ideal.
The explicit cofactors are against the accepted basis; its forward certificate
supplies the original-generator containment. -/
theorem memberWith_member_sound (basis : Hex.Groebner.CheckedBasis)
    (budget : Hex.Groebner.Certificate.Budget) (target : Hex.Groebner.Certificate.Polynomial)
    (value : Hex.Groebner.Certificate.CheckedDivision basis.context basis.polynomials target)
    (zero : Hex.MvPoly.Kernel.isZero value.value.remainder = true)
    (usage : Hex.Groebner.Certificate.Usage)
    (_h : Hex.Groebner.memberWith basis budget target = .member value zero usage) :
    denote basis.context target ∈ Ideal.span
      (Set.range fun i : Fin basis.generators.size => denote basis.context basis.generators[i]) := by
  have certified := checkBasis_sound basis.context basis.generators basis.polynomials
    basis.certificate basis.accepted
  obtain ⟨_, _, _, reconstruction, _⟩ :=
    checkedDivision_sound basis.context basis.polynomials target value
  have empty : value.value.remainder = [] := by
    cases hr : value.value.remainder with
    | nil => rfl
    | cons t ts => simp [hr, Hex.MvPoly.Kernel.isZero] at zero
  rw [empty] at reconstruction
  have denoteNil : denote basis.context [] = 0 := by simp [denote]
  rw [denoteNil, add_zero] at reconstruction
  rw [reconstruction]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (certified.1.1 (Set.mem_range_self i))

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
