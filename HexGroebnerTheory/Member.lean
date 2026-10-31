/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Member
public import HexGroebnerTheory.Certificate
public import HexGroebnerTheory.CertificateContainment
public import HexGroebnerTheory.CertificateDivision

public section

namespace HexGroebnerTheory
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

/-- Both positive certificate encodings prove membership in the original
input ideal independently of the producer and without assuming a Gröbner basis. -/
theorem checkMember_sound (context : Hex.Groebner.Context)
    (generators : Array Hex.Groebner.Certificate.Polynomial)
    (target : Hex.Groebner.Certificate.Polynomial)
    (certificate : Hex.Groebner.Certificate.Member)
    (h : Hex.Groebner.checkMember context generators target certificate = true) :
    denote context target ∈ Ideal.span
      (Set.range fun i : Fin generators.size => denote context generators[i]) := by
  cases certificate with
  | derivation value => exact checkDerivation_sound context generators target value h
  | combination value =>
    let := fieldBounds context.field
    let : Fact context.field.modulus.toNat.Prime := ⟨fieldPrime context.field⟩
    simp only [Hex.Groebner.checkMember, Bool.and_eq_true] at h
    have containment := Certificate.checkContainment_sound context.field.modulus.toNat context.variables
      (cmp := context.order.cmp context.variables) generators value.basis value.forward h.1.1
    obtain ⟨_,_,_,reconstruction,_⟩ :=
      Certificate.checkDivision_sound context.order value.basis target value.division h.1.2
    have empty : value.division.remainder = [] := by
      cases hr : value.division.remainder with
      | nil => rfl
      | cons t ts => simp [hr, Hex.MvPoly.Kernel.isZero] at h
    change denote context target = (∑ i : Fin value.basis.size,
      denote context (value.division.quotients[i.val]?.getD []) * denote context value.basis[i]) +
        denote context value.division.remainder at reconstruction
    rw [empty] at reconstruction
    have nilZero : denote context [] = 0 := by simp [denote]
    rw [nilZero,add_zero] at reconstruction
    rw [reconstruction]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (containment.2.2 i)

end HexGroebnerTheory
