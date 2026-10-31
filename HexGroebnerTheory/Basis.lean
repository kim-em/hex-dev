/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Basis
public import HexGroebnerTheory.CertificateBasis

public section

namespace HexGroebnerTheory.Checked
open Hex.Groebner

/-- An accepted receipt proves the reduced basis of the exact original ideal. -/
theorem basis_sound {context : Context} {generators : Array Certificate.Polynomial}
    {expected : Option (Array Certificate.Polynomial)} (basis : Checked.Basis context generators expected) :
    IsReducedBasis context generators basis.value.polynomials := by
  have sound := checkBasis_sound basis.value.context basis.value.generators basis.value.polynomials
    basis.value.certificate basis.value.accepted
  simpa only [basis.context_eq,basis.generators_eq] using sound

/-- Checked computation needs no producer provenance or mathematical assumption
about its seed, pair criteria or elimination strategy. -/
theorem basisWith_sound (context : Context) (budget : Producer.Budget)
    (generators : Array Certificate.Polynomial) (basis : Checked.Basis context generators none)
    (usage : Certificate.Usage)
    (_h : Checked.basisWith context budget generators = .success basis usage) :
    IsReducedBasis context generators basis.value.polynomials := basis_sound basis

/-- Certification proves the supplied candidate, rather than merely some basis
for an ideal associated with producer metadata. -/
theorem certifyWith_sound (context : Context) (budget : Producer.Budget)
    (generators candidate : Array Certificate.Polynomial)
    (basis : Checked.Basis context generators (some candidate)) (usage : Certificate.Usage)
    (_h : Checked.certifyWith context budget generators candidate = .success basis usage) :
    IsReducedBasis context generators candidate := by
  rw [← basis.candidate_eq candidate rfl]
  exact basis_sound basis

/-- info: 'HexGroebnerTheory.Checked.basisWith_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms basisWith_sound
/-- info: 'HexGroebnerTheory.Checked.certifyWith_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms certifyWith_sound

end HexGroebnerTheory.Checked

namespace HexGroebnerTheory
open Hex.Groebner

/-- Every successful checked computation gives the reduced Gröbner basis of
its exact original ideal, without trusting the F4 producer. -/
theorem basisWith_sound (context : Context) (limits : BasisLimits)
    (generators : Array Certificate.Polynomial) (basis : BasisReceipt context generators none)
    (usage : Certificate.Usage)
    (_h : basisWith context limits generators = .success basis usage) :
    IsReducedBasis context generators basis.value.polynomials :=
  Checked.basis_sound basis

/-- Accepted certification proves the supplied candidate is the reduced basis
of the original input ideal, with no producer-provenance hypothesis. -/
theorem certifyWith_sound (context : Context) (limits : BasisLimits)
    (generators candidate : Array Certificate.Polynomial)
    (basis : BasisReceipt context generators (some candidate)) (usage : Certificate.Usage)
    (_h : certifyWith context limits generators candidate = .success basis usage) :
    IsReducedBasis context generators candidate :=
  by
    rw [← basis.candidate_eq candidate rfl]
    exact Checked.basis_sound basis

end HexGroebnerTheory
