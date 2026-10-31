/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Producer.Certificate
import HexGroebner.F4Fixtures

open Hex.Groebner

private def certify (context : Context) (generators : Array RawPolynomial) : Bool := Id.run do
  let .candidate candidate statistics := Producer.computeWith context {} 1000000 generators | return false
  let usage : Certificate.Usage := { maxExponentBits := candidate.maxExponentBits,allocatedTerms := candidate.allocatedTerms,work := statistics.work,allocatedBytes := statistics.allocatedBytes+candidate.monomialBytes }
  let .success basis final := Producer.certifyFrom {} candidate usage | return false
  return basis.polynomials == candidate.polynomials && final.work > statistics.work &&
    checkBasis basis.context basis.generators basis.polynomials basis.certificate

#guard certify ⟨⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩,2,.grevlex⟩
  #[#[⟨#[2,0],1⟩,⟨#[0,1],6⟩],#[⟨#[1,1],1⟩,⟨#[0,0],6⟩]]

private def corpus : Bool := Id.run do
  for field in Fixtures.fields do
    for order in [TermOrder.lex,.grlex,.grevlex] do
      for c in F4Fixtures.cases field do
        if !certify ⟨field,c.variables,order⟩ c.generators then return false
  return true

#guard corpus
