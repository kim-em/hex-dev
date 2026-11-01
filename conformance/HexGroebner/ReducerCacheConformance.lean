/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexGroebner.F4Fixtures
open Hex.Groebner
open Hex.Groebner.Computation
namespace Hex.Groebner.ReducerCacheConformance

private def field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
private def context : Context := ⟨field,2,.grevlex⟩
private def generators : Array RawPolynomial := #[#[⟨#[2,0],1⟩,⟨#[0,1],6⟩],#[⟨#[1,1],1⟩,⟨#[0,0],6⟩]]

def budgetChecks : Bool := Id.run do
  for work in [0,1,2,5,20,50,100,500,2000,10000,100000] do
    for bytes in [0,1,8,24,100,1000,10000,100000] do
      let limits : Limits := {work,packedBytes:=bytes}
      match computeWith context limits generators with
      | .candidate actual stats =>
        if stats.work > work || stats.allocatedBytes > bytes then return false
        let .candidate expected _ := computeWith context {} generators | return false
        if actual.polynomials != expected.polynomials then return false
      | .exhausted _ state =>
        let stats := state.workspace.statistics
        if stats.work > work || stats.allocatedBytes > bytes then return false
      | _ => return false
  return true
#guard budgetChecks


private def cacheChecks : Bool := Id.run do
  let limits : Limits := {work:=1000000,packedBytes:=1000000}
  let action : Computation Bool := do
    let g ← Polynomial.normalize context limits 0 #[⟨#[1,0],1⟩,⟨#[0,0],1⟩]
    let h ← Polynomial.normalize context limits 0 #[⟨#[1,0],1⟩,⟨#[0,1],1⟩]
    let target ← Polynomial.normalize context limits 0 #[⟨#[3,0],1⟩]
    let basis : Array BasisElement := #[⟨g,1⟩]
    let targets : Array BasisElement := #[⟨target,3⟩]
    let index ← ReducerIndex.build context limits basis
    let first ← SymbolicMatrix.prepareWith context limits index basis targets
    let before := (← get).statistics
    let second ← SymbolicMatrix.prepareWith context limits index basis targets first.cache
    let after := (← get).statistics
    if first.reducers.size != second.reducers.size then return false
    for (a,b) in first.reducers.zip second.reducers do
      if a.polynomial.support != b.polynomial.support || a.polynomial.coefficients != b.polynomial.coefficients then return false
    if after.allocatedBytes != before.allocatedBytes then return false
    let changed : Array BasisElement := #[⟨h,1⟩]
    let index ← ReducerIndex.build context limits changed
    let reused ← SymbolicMatrix.prepareWith context limits index changed targets second.cache
    let fresh ← SymbolicMatrix.prepareWith context limits index changed targets
    if reused.reducers.size != fresh.reducers.size then return false
    for (a,b) in reused.reducers.zip fresh.reducers do
      if a.polynomial.support != b.polynomial.support || a.polynomial.coefficients != b.polynomial.coefficients then return false
    return true
  let workspace : Workspace := {table:={arity:=context.variables}}
  match action.run workspace with
  | (.ok result,_) => return result
  | _ => return false

#guard cacheChecks

end Hex.Groebner.ReducerCacheConformance
