/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Basis
import HexGroebner.F4Fixtures

open Hex.Groebner

private def canonical (p : Nat) (raw : RawPolynomial) : Certificate.Polynomial :=
  raw.foldl (fun f term => if term.coefficient == 0 then f else
    Hex.MvPoly.Kernel.addMod p f [(term.exponents.toList,term.coefficient.toNat)]) []

private def corpus : Bool := Id.run do
  for field in Fixtures.fields do
    for order in [TermOrder.lex,.grlex,.grevlex] do
      for c in F4Fixtures.cases field do
        let context : Context := ⟨field,c.variables,order⟩
        let generators := c.generators.map (canonical field.modulus.toNat)
        let .success basis _ := Checked.basisWith context {} generators | return false
        if basis.value.generators != generators then return false
        let .success accepted _ := Checked.certifyWith context {} generators basis.value.polynomials | return false
        if accepted.value.polynomials != basis.value.polynomials then return false
  return true

#guard corpus

private def context : Context := ⟨⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩,2,.grevlex⟩
private def generators : Array Certificate.Polynomial := #[[([2,0],1),([0,1],6)],[([1,1],1),([0,0],6)]]

#guard match Checked.basisWith context {} #[[([0],1)]] with
  | .invalid 0 _ => true
  | _ => false
#guard match Checked.basisWith context {} #[[([0,0],7)]] with
  | .invalid 0 _ => true
  | _ => false
#guard match Checked.certifyWith context {} generators #[[([1,0],1)]] with
  | .rejected _ => true
  | _ => false

private def resumes : Bool := Id.run do
  let .success expected total := Checked.basisWith context {} generators | return false
  for work in [0,1,total.work/2,total.work-1,total.work] do
    match Checked.basisWith context { certificate.work := work } generators with
    | .success actual _ => if actual.value.polynomials != expected.value.polynomials then return false
    | .computeExhausted .work state | .certificateExhausted .work state =>
      let .success actual final := Checked.resumeWith {} state | return false
      if actual.value.polynomials != expected.value.polynomials || final.work < work then return false
    | _ => return false
  for budget in [({ certificate.nodes := 0 } : Producer.Budget),{ certificate.allocatedTerms := 0 },
      { certificate.exponentBits := 0 },{ certificate.variables := 0 },{ certificate.allocatedBytes := 0 },
      { certificate.pairs := 0 },{ certificate.steps := 0 },{ computation.matrixEntries := 0 }] do
    let state ← match Checked.basisWith context budget generators with
      | .computeExhausted _ state | .certificateExhausted _ state => pure state
      | _ => return false
    let .success actual _ := Checked.resumeWith {} state | return false
    if actual.value.polynomials != expected.value.polynomials then return false
  return true

#guard resumes

private def historyResume : Bool := Id.run do
  let .success expected total := Checked.basisWith context {} generators | return false
  let .certificateExhausted .work state := Checked.basisWith context
      { certificate.work := total.work-1 } generators | return false
  for (computation,resource) in [(({ pairs := 0 } : Limits),F4Resource.pairs),
      ({ rounds := 0 },.rounds),({ matrixEntries := 0 },.matrixEntries),
      ({ matrixRows := 0 },.matrixRows),({ monomials := 0 },.monomials),({ basis := 0 },.basis)] do
    match Checked.resumeWith { computation } state with
    | .computeExhausted actual retained =>
      if actual != resource then return false
      let .success value _ := Checked.resumeWith {} retained | return false
      if value.value.polynomials != expected.value.polynomials then return false
    | _ => return false
  return true

#guard historyResume

namespace Hex.Groebner.BasisUseTest

private def context : Context := ⟨⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩,2,.grevlex⟩
private def generators : Array Certificate.Polynomial := #[[([2,0],1),([0,1],6)],[([1,1],1),([0,0],6)]]

private def checked : Bool := Id.run do
  let .success basis _ := basisWith context {} generators | return false
  let .success normal _ := normalFormWith basis.value {} [([2,0],1)] | return false
  if normal.value.remainder != [([0,1],1)] then return false
  let target : Certificate.Polynomial := [([1,0],6),([0,2],1)]
  let .member _ positive _ _ := memberWith basis.value {} target | return false
  if !checkMember context generators target positive.witness then return false
  let .nonmember negative _ := memberWith basis.value {} [([1,0],1)] | return false
  return checkNonmember context generators [([1,0],1)] negative.witness

#guard checked

end Hex.Groebner.BasisUseTest
