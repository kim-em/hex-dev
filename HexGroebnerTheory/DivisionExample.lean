/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.CertificateNormalForm

@[expose] public section

namespace HexGroebnerTheory.DivisionExample
open Hex.Groebner

/-- Ordinary polynomial-ring metadata over F₂. -/
def context : Context :=
  ⟨⟨2, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩, 1, .grevlex⟩

def generators : Array Certificate.Polynomial := #[[([2], 1), ([1], 1)]]
def target : Certificate.Polynomial := [([2], 1)]

def basis : Certificate.Basis := {
  forward := ⟨[.generator 0], #[0]⟩
  backward := ⟨[.generator 0], #[0]⟩
  pairs := #[#[#[[]]]] }

def division : Certificate.Division := ⟨#[[([0], 1)]], [([1], 1)]⟩
def witness : Certificate.Nonmember := ⟨generators, basis, division⟩

/-- x² has nonzero normal form x modulo x²+x in the ordinary ring `F₂[x]`. -/
theorem nonmember : denote context target ∉ Ideal.span
    (Set.range fun i : Fin generators.size => denote context generators[i]) :=
  checkNonmember_sound context generators target witness (by decide +kernel)

/-- The literal remainder is the unique irreducible representative of its ideal coset. -/
theorem normal_form : IsNormalForm context generators generators target
      (denote context division.remainder) ∧
    ∀ r, IsNormalForm context generators generators target r → r = denote context division.remainder :=
  normalForm_spec context generators generators basis target division (by decide +kernel) (by decide +kernel)

theorem reject_reducible : checkNonmember context generators target { witness with
    division := ⟨#[[]], target⟩ } = false := by decide +kernel
theorem reject_zero : checkNonmember context generators generators[0]! { witness with
    division := ⟨#[[([0], 1)]], []⟩ } = false := by decide +kernel
theorem reject_arity : checkNonmember context generators target { witness with
    division := ⟨#[[([0, 0], 1)]], division.remainder⟩ } = false := by decide +kernel

/-- info: 'HexGroebnerTheory.DivisionExample.nonmember' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nonmember
/-- info: 'HexGroebnerTheory.DivisionExample.normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms normal_form
/-- info: 'HexGroebnerTheory.checkNonmember_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.checkNonmember_sound
/-- info: 'HexGroebnerTheory.Certificate.checkDivision_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.Certificate.checkDivision_sound

end HexGroebnerTheory.DivisionExample
