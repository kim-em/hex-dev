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

private def cacheChecks (seed : Nat) : Bool := Id.run do
  let limits : Limits := {work:=1000000,packedBytes:=1000000}
  let action : Computation Bool := do
    let g ← Polynomial.normalize context limits 0 #[⟨#[1,0],1⟩,⟨#[0,0],1⟩]
    let h ← Polynomial.normalize context limits 0 #[⟨#[1,0],1⟩,⟨#[0,1],1⟩]
    let k ← Polynomial.normalize context limits 0 #[⟨#[1,0],1⟩,⟨#[0,0],(2+seed%5).toUInt64⟩]
    let target ← Polynomial.normalize context limits 0 #[⟨#[3+seed%2,0],1⟩]
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
    -- Re-encoding the exponent arena must preserve cached polynomial IDs.
    let _ ← intern limits #[65536,0]
    if (← get).table.width != .u32 then return false
    let widened ← SymbolicMatrix.prepareWith context limits index basis targets second.cache
    if widened.reducers.size != first.reducers.size then return false
    for (a,b) in first.reducers.zip widened.reducers do
      if a.polynomial.support != b.polynomial.support || a.polynomial.coefficients != b.polynomial.coefficients then return false
    for polynomial in [h,k] do
      let changed : Array BasisElement := #[⟨polynomial,1⟩]
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

#guard cacheChecks 0

private def copy (bytes : ByteArray) : ByteArray := Id.run do
  let mut result := ByteArray.emptyWithCapacity bytes.size
  for i in [:bytes.size] do result := result.push bytes[i]!
  return result

private def longChecks (seed : Nat) : Bool := Id.run do
  let context : Context := ⟨field,1,.grevlex⟩
  let limits : Limits := { work := 1000000, packedBytes := 1000000 }
  let action : Computation Bool := do
    let p ← Polynomial.normalize context limits 0
      ((Array.range 4200).map fun i => RawTerm.mk #[2*i] 1)
    let multiplier ← intern limits #[1]
    let (first, cache) ← ReducerCache.empty.multiply context limits p multiplier
    let cloned : Polynomial := { support := copy p.support, coefficients := copy p.coefficients }
    let before := (← get).statistics.allocatedBytes
    let (hit, _) ← cache.multiply context limits cloned multiplier
    if (← get).statistics.allocatedBytes != before then return false
    if hit.support != first.support || hit.coefficients != first.coefficients then return false
    let replacement ← intern limits #[5399]
    let changedSupport := { cloned with
      support := Packed.set .u32 (copy cloned.support) 1500 replacement.toUInt64 }
    let (supportResult, _) ← cache.multiply context limits changedSupport multiplier
    let supportExpected ← changedSupport.multiply context limits multiplier
    if supportResult.support != supportExpected.support || supportResult.coefficients != supportExpected.coefficients then
      return false
    let changedTail := { cloned with support := Packed.set .u32 (copy cloned.support) 4199 multiplier.toUInt64 }
    let (tailResult, _) ← cache.multiply context limits changedTail multiplier
    let tailExpected ← changedTail.multiply context limits multiplier
    if tailResult.support != tailExpected.support || tailResult.coefficients != tailExpected.coefficients then return false
    for offset in [4096,4150,4199] do
      let changed := { cloned with coefficients := cloned.coefficients.set! offset (2 + seed%5).toUInt8 }
      let (actual, _) ← cache.multiply context limits changed multiplier
      let expected ← changed.multiply context limits multiplier
      if actual.support != expected.support || actual.coefficients != expected.coefficients then return false
    return true
  match action.run { table := { arity := 1 } } with
  | (.ok value, _) => return value
  | _ => return false

#guard longChecks 0

private def contextChecks (seed : Nat) : Bool := Id.run do
  let other : PrimeField := ⟨5,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let action : Computation Bool := do
    let p ← Polynomial.normalize context {} 0 #[⟨#[1,0],1⟩,⟨#[0,0],(1+seed%3).toUInt64⟩]
    let multiplier ← intern {} #[1,0]
    let (_, cache) ← ReducerCache.empty.multiply context {} p multiplier
    for changed in [{ context with order := .lex }, { context with field := other }] do
      let before := (← get).statistics.allocatedBytes
      let (actual, _) ← cache.multiply changed {} p multiplier
      if (← get).statistics.allocatedBytes == before then return false
      let expected ← p.multiply changed {} multiplier
      if actual.support != expected.support || actual.coefficients != expected.coefficients then return false
    return true
  match action.run { table := { arity := context.variables } } with
  | (.ok value, _) => return value
  | _ => return false

#guard contextChecks 0

/-- Byte-equal identifiers from independent arenas must not validate a cached
product, even when the base and multiplier retain their exponent meanings. -/
private def arenaChecks (seed : Nat) : Bool := Id.run do
  let context : Context := ⟨field,1,.grevlex⟩
  let a := 1+seed%3
  let first : Computation ReducerCache := do
    let _ ← intern {} #[0]
    let p ← Polynomial.normalize context {} 0 #[⟨#[a],1⟩,⟨#[0],1⟩]
    let multiplier ← intern {} #[a.toUInt64]
    return (← ReducerCache.empty.multiply context {} p multiplier).2
  let (.ok cache, _) := first.run { table := { arity := 1 } } | return false
  for shifted in [false,true] do
    let second : Computation Bool := do
      let _ ← intern {} #[0]
      let exponent := if shifted then 2*a else a
      let p ← Polynomial.normalize context {} 0 #[⟨#[exponent],1⟩,⟨#[0],1⟩]
      let _ ← intern {} #[(3*a).toUInt64]
      let multiplier ← intern {} #[exponent.toUInt64]
      let (actual, _) ← cache.multiply context {} p multiplier
      let expected ← p.multiply context {} multiplier
      return actual.support == expected.support && actual.coefficients == expected.coefficients
    match second.run { table := { arity := 1 } } with
    | (.ok true, _) => pure ()
    | _ => return false
  return true

#guard arenaChecks 0

private def capacityChecks (seed : Nat) : Bool := Id.run do
  let context : Context := ⟨field,1,.grevlex⟩
  let action : Computation Bool := do
    let p ← Polynomial.normalize context {} 0 #[⟨#[1],1⟩,⟨#[0],(1+seed%3).toUInt64⟩]
    let mut cache := ReducerCache.empty
    for exponent in [1:16385] do
      let multiplier ← intern {} #[exponent.toUInt64]
      cache := (← cache.multiply context {} p multiplier).2
    let changed ← Polynomial.normalize context {} 0 #[⟨#[1],1⟩,⟨#[0],(4+seed%3).toUInt64⟩]
    let first ← intern {} #[1]
    let before := (← get).statistics.allocatedBytes
    let (actual, replaced) ← cache.multiply context {} changed first
    if (← get).statistics.allocatedBytes != before + 16 then return false
    let (hit, _) ← replaced.multiply context {} changed first
    if (← get).statistics.allocatedBytes != before + 16 || actual.support != hit.support ||
        actual.coefficients != hit.coefficients then return false
    let outside ← intern {} #[16385]
    let before := (← get).statistics.allocatedBytes
    let (_, full) ← replaced.multiply context {} changed outside
    if (← get).statistics.allocatedBytes != before + 8 then return false
    let _ ← full.multiply context {} changed outside
    return (← get).statistics.allocatedBytes == before + 16
  match action.run { table := { arity := 1 } } with
  | (.ok value, _) => return value
  | _ => return false

#guard capacityChecks 0

/-- Full F4 execution, called between native-counter observations by the harness. -/
def f4Checks (seed : Nat) : Bool := Id.run do
  let field : PrimeField := ⟨65537,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let context : Context := ⟨field,5,.grevlex⟩
  let mut generators : Array RawPolynomial := #[]
  for degree in [1:5] do
    let mut polynomial := #[]
    for start in [:5] do
      let mut exponents := Array.replicate 5 0
      for step in [:degree] do
        exponents := exponents.modify ((start+step)%5) (·+1)
      polynomial := polynomial.push ⟨exponents,1⟩
    generators := generators.push polynomial
  generators := generators.push #[⟨Array.replicate 5 1,1⟩,
    ⟨Array.replicate 5 0,(65537 - (seed%65536 + 1)).toUInt64⟩]
  match computeWith context {} generators with
  | .candidate value statistics => return !value.polynomials.isEmpty && statistics.matrixCalls > 1
  | _ => return false

/-- Multi-chunk hits, coefficient-only changes, context changes and widening. -/
def runtimeChecks (seed : Nat) : Bool := cacheChecks seed && longChecks seed && contextChecks seed && arenaChecks seed && capacityChecks seed

end Hex.Groebner.ReducerCacheConformance
