/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Producer.Pipeline

open Hex.Groebner

namespace Hex.Groebner.Producer.Test
private def context : Context := ⟨⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩,2,.grevlex⟩
private def generators : Array RawPolynomial := #[#[⟨#[2,0],1⟩,⟨#[0,1],6⟩],#[⟨#[1,1],1⟩,⟨#[0,0],6⟩]]

private def complete : Bool := Id.run do
  let .success value _ _ := basisWith context {} generators | return false
  let .success accepted _ _ := certifyWith context {} generators value.polynomials | return false
  return accepted.polynomials == value.polynomials &&
    Hex.Groebner.checkBasis context value.generators value.polynomials value.certificate

#guard complete
#guard match basisWith context {} #[#[⟨#[0],1⟩]] with
  | .invalid (.arity 0 0) _ => true
  | _ => false
#guard match certifyWith context {} generators #[[([1,0],1)]] with
  | .rejected _ => true
  | _ => false
#guard match certifyWith context {} generators #[[([0,0],7)]] with
  | .rejected _ => true
  | _ => false

private def resume (operation : Bool) : Bool := Id.run do
  let .success expected total _ := basisWith context {} generators | return false
  let mut production := false
  let mut certification := false
  for work in [0,1,total.work/2,total.work-1,total.work] do
    let budget : Budget := { certificate.work := work }
    let outcome := if operation then certifyWith context budget generators expected.polynomials
      else basisWith context budget generators
    let state ← match outcome with
      | .computeExhausted .work state =>
        production := true
        pure (some state)
      | .certificateExhausted .work state =>
        certification := true
        pure (some state)
      | .success actual _ _ =>
        if actual.polynomials != expected.polynomials then return false
        pure none
      | _ => return false
    if let some state := state then
      let .success actual usage _ := resumeBasisWith {} state | return false
      if actual.polynomials != expected.polynomials || usage.work < work then return false
  return production || certification

#guard resume false
#guard resume true

private def categories : Bool := Id.run do
  for budget in [({ certificate.nodes := 0 } : Budget),{ certificate.allocatedTerms := 0 },
      { certificate.allocatedBytes := 0 },{ certificate.pairs := 0 },{ certificate.steps := 0 },
      { certificate.variables := 0 },{ certificate.exponentBits := 0 },{ computation.monomials := 0 },{ computation.matrixEntries := 0 }] do
    let state ← match basisWith context budget generators with
      | .computeExhausted _ state => pure state
      | .certificateExhausted _ state => pure state
      | _ => return false
    let .success value _ _ := resumeBasisWith {} state | return false
    if !Hex.Groebner.checkBasis context value.generators value.polynomials value.certificate then return false
  let .success expected _ _ := basisWith context {} generators | return false
  match certifyWith context { certificate.allocatedTerms := 0 } generators expected.polynomials with
  | .certificateExhausted .allocatedTerms state =>
    let .success actual _ _ := resumeBasisWith {} state | return false
    return actual.polynomials == expected.polynomials
  | _ => return false

#guard categories
end Hex.Groebner.Producer.Test

namespace Hex.Groebner.Producer.AllocationTest

#guard match (do
    Computation.allocate { packedBytes := USize.size*2 } (USize.size/2)
    Computation.allocate { packedBytes := USize.size*2 } (USize.size/2)).run
    ⟨{ arity := 0 },{}⟩ with
  | (.ok _,workspace) => workspace.statistics.allocatedBytes == USize.size
  | _ => false
#guard match (Computation.allocate { packedBytes := USize.size*2 } USize.size).run
    ⟨{ arity := 0 },{}⟩ with
  | (.error (.representation .address),workspace) => workspace.statistics.allocatedBytes == 0
  | _ => false

end Hex.Groebner.Producer.AllocationTest
