/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateNonmember

@[expose] public section

namespace Hex.Groebner.PrimeExample

abbrev context : Context := ⟨⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩,2,.grevlex⟩
def generators : Array Certificate.Polynomial := #[[([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)]]
def polynomials : Array Certificate.Polynomial := #[[([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)], [([1, 0], 6), ([0, 2], 1)]]
def certificate : Certificate.Basis := {
  forward := {
    nodes := [
      .generator 0, .generator 1,
      .multiply [([0, 1], 1)] 0, .multiply [([1, 0], 1)] 1,
      .scale 6 3, .add 2 4, .scale 6 5]
    roots := #[0, 1, 6] }
  backward := {
    nodes := [
      .zero, .generator 0, .multiply [([0, 0], 1)] 1, .add 0 2,
      .generator 1, .multiply [([0, 0], 1)] 4, .add 0 5]
    roots := #[3, 6] }
  pairs := #[
    #[#[[], [], []], #[[], [], [([0, 0], 6)]],
      #[[([1, 0], 1)], [], [([0, 1], 6)]]],
    #[#[[], [], [([0, 0], 1)]], #[[], [], []], #[[([0, 0], 1)], [], []]],
    #[#[[([1, 0], 6)], [], [([0, 1], 1)]], #[[([0, 0], 6)], [], []], #[[], [], []]]] }

def target : Certificate.Polynomial := [([1, 0], 1)]

def nonmember : Certificate.Nonmember := ⟨polynomials, certificate, ⟨#[[], [], []], target⟩⟩

end Hex.Groebner.PrimeExample
