/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Producer.Compute
import HexGroebner.F4Fixtures

open Hex.Groebner

private def check : Bool := Id.run do
  let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let context : Context := ⟨field,2,.grevlex⟩
  let generators : Array RawPolynomial := #[#[⟨#[2,0],1⟩,⟨#[0,1],6⟩],#[⟨#[1,1],1⟩,⟨#[0,0],6⟩]]
  let .candidate value _ := Producer.computeWith context {} 1000000 generators | return false
  return Certificate.checkContainment 7 2 value.generators value.polynomials value.forward

#guard check

private def canonical (p : Nat) (raw : RawPolynomial) : Certificate.Polynomial :=
  raw.foldl (fun f term => if term.coefficient == 0 then f else
    Hex.MvPoly.Kernel.addMod p f [(term.exponents.toList,term.coefficient.toNat)]) []

private def corpus : Bool := Id.run do
  for field in Fixtures.fields do
    for order in [TermOrder.lex,.grlex,.grevlex] do
      for c in F4Fixtures.cases field do
        let context : Context := ⟨field,c.variables,order⟩
        let .candidate expected _ := computeWith context {} c.generators | return false
        let .candidate actual _ := Producer.computeWith context {} 1000000 c.generators | return false
        if actual.polynomials != expected.polynomials.map (canonical field.modulus.toNat) ||
            !Certificate.checkContainment field.modulus.toNat c.variables actual.generators
              actual.polynomials actual.forward then return false
  return true

#guard corpus
