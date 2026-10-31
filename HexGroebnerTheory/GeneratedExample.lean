/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.CertificateBasis
public import HexGroebnerTheory.CertificateNormalForm

@[expose] public section

open Hex.Groebner
namespace HexGroebnerTheory.GeneratedExample

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

abbrev context : Context := ⟨⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩,2,.grevlex⟩
def generators : Array Certificate.Polynomial := #[[([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)]]
def polynomials : Array Certificate.Polynomial := #[[([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)], [([1, 0], 6), ([0, 2], 1)]]
def certificate : Certificate.Basis := {
  forward := {
    nodes := [
      .generator 0, .generator 1,
      .multiply [([0, 1], 1)] 0, .multiply [([1, 0], 1)] 1,
      .scale 6 3, .add 2 4, .scale 6 5,
      .multiply [([0, 1], 1)] 1, .multiply [([1, 0], 1)] 6,
      .scale 6 8, .add 7 9, .multiply [([0, 0], 1)] 0,
      .scale 6 11, .add 10 12]
    roots := #[0, 1, 6] }
  backward := {
    nodes := [
      .generator 0, .generator 1, .generator 2, .zero,
      .multiply [([0, 0], 1)] 0, .add 3 4,
      .multiply [([0, 0], 1)] 1, .add 3 6]
    roots := #[5, 7] }
  pairs := #[
    #[#[[], [], []], #[[], [], [([0, 0], 6)]],
      #[[([1, 0], 1)], [], [([0, 1], 6)]]],
    #[#[[], [], [([0, 0], 1)]], #[[], [], []], #[[([0, 0], 1)], [], []]],
    #[#[[([1, 0], 6)], [], [([0, 1], 1)]], #[[([0, 0], 6)], [], []], #[[], [], []]]] }

theorem basis : IsReducedBasis context generators polynomials :=
  checkBasis_sound context generators polynomials certificate (by decide +kernel)
/-- info: 'HexGroebnerTheory.GeneratedExample.basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms basis

def target : Certificate.Polynomial := [([1,0],1)]

def nonmember : Certificate.Nonmember := ⟨polynomials,certificate,⟨#[[],[],[]],target⟩⟩

/-- The ordinary polynomial x has nonzero normal form modulo this input ideal. -/
theorem x_not_mem : denote context target ∉ Ideal.span
    (Set.range fun i : Fin generators.size => denote context generators[i]) :=
  checkNonmember_sound context generators target nonmember (by decide +kernel)

/-- info: 'HexGroebnerTheory.GeneratedExample.x_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms x_not_mem

end HexGroebnerTheory.GeneratedExample
