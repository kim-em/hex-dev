/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexGroebner.PairRows

namespace Hex.Groebner.PairRowsConformance
open Computation

private def field : PrimeField := ⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩

/-- Check row grouping and every selected S-polynomial identity. These identities
check the matrix input span; the complete F4 oracle/certificate suite separately
checks the final Gröbner property. -/
private def groupCheck (variables : Nat) (raw : Array RawPolynomial)
    (indices : Array (Nat × Nat)) (expectedReducers : Array Nat) (targetCount : Nat) : Bool := Id.run do
  let context : Context := ⟨field, variables, .grevlex⟩
  let action : Computation Bool := do
    let mut basis := #[]
    for i in [:raw.size] do
      let p ← Polynomial.normalize context {} i raw[i]!
      basis := basis.push (BasisElement.mk p 2)
    let mut pairs := #[]
    for (a,b) in indices do
      let lcm ← combine {} .lcm (basis[a]!.polynomial.monomial 0) (basis[b]!.polynomial.monomial 0)
      pairs := pairs.push (CriticalPair.mk a b lcm 3 3)
    let rows ← PairRows.prepare context {} basis pairs .empty
    if rows.reducers.map (·.basis) != expectedReducers || rows.targets.size != targetCount then return false
    let all := rows.reducers ++ rows.targets
    for pair in pairs do
      let some left := all.find? (fun row => row.basis == pair.left && row.polynomial.monomial 0 == pair.lcm) | return false
      let some right := all.find? (fun row => row.basis == pair.right && row.polynomial.monomial 0 == pair.lcm) | return false
      let actual ← left.polynomial.subtract context {} right.polynomial
      let expected ← basis[pair.left]!.polynomial.sPolynomial context {} basis[pair.right]!.polynomial
      if actual.support != expected.support || actual.coefficients != expected.coefficients then return false
    let index ← ReducerIndex.build context {} basis
    let targets := rows.targets.map fun r => BasisElement.mk r.polynomial r.sugar
    let matrix ← SymbolicMatrix.prepareWith context {} index basis targets rows.cache rows.reducers
    for reducer in rows.reducers do
      if (matrix.reducers.filter (·.polynomial.monomial 0 == reducer.polynomial.monomial 0)).size != 1 then
        return false
    return true
  match action.run { table := { arity := variables } } with
  | (.ok value, _) => return value
  | _ => return false

#guard groupCheck 3 #[
  #[⟨#[1,1,0],1⟩,⟨#[0,0,0],1⟩],
  #[⟨#[1,0,1],1⟩,⟨#[0,1,0],1⟩,⟨#[0,0,0],1⟩],
  #[⟨#[0,1,1],1⟩,⟨#[1,0,0],1⟩]] #[(0,1),(0,2),(1,2)] #[0] 2

-- Same LCM with disconnected pair components retains both selected identities.
#guard groupCheck 4 #[
  #[⟨#[1,1,0,0],1⟩,⟨#[0,0,0,0],1⟩],
  #[⟨#[0,0,1,1],1⟩,⟨#[0,0,0,0],1⟩],
  #[⟨#[1,0,1,0],1⟩,⟨#[0,0,0,0],1⟩],
  #[⟨#[0,1,0,1],1⟩,⟨#[0,0,0,0],1⟩]] #[(0,1),(2,3)] #[0] 3

-- Three LCMs share sources with different multipliers. The xy seed also occurs
-- in the x² target's tail, and must retain exactly one known pivot.
#guard groupCheck 2 #[
  #[⟨#[1,0],1⟩,⟨#[0,0],1⟩],
  #[⟨#[0,1],1⟩,⟨#[0,0],1⟩],
  #[⟨#[2,0],1⟩,⟨#[1,1],1⟩,⟨#[0,0],1⟩]] #[(0,1),(0,2),(1,2)] #[0,0,1] 3

-- Sparsity selects a later basis element; repeated and reversed pairs dedupe.
#guard groupCheck 2 #[
  #[⟨#[1,0],1⟩,⟨#[0,1],1⟩,⟨#[0,0],1⟩],
  #[⟨#[0,1],1⟩]] #[(0,1),(0,1),(1,0)] #[1] 1

private def invalidSeeds : Bool := Id.run do
  let context : Context := ⟨field, 2, .grevlex⟩
  let action : Computation Bool := do
    let f ← Polynomial.normalize context {} 0 #[⟨#[1,0],1⟩,⟨#[0,0],1⟩]
    let g ← Polynomial.normalize context {} 1 #[⟨#[0,1],1⟩]
    let basis := #[BasisElement.mk f 1, BasisElement.mk g 1]
    let lcm ← combine {} .lcm (f.monomial 0) (g.monomial 0)
    let rows ← PairRows.prepare context {} basis #[CriticalPair.mk 0 1 lcm 2 2] .empty
    let index ← ReducerIndex.build context {} basis
    let targets := rows.targets.map fun r => BasisElement.mk r.polynomial r.sugar
    let some seed := rows.reducers[0]? | return false
    for initial in [#[seed,seed], #[{ seed with polynomial := {} }]] do
      try
        let _ ← SymbolicMatrix.prepareWith context {} index basis targets rows.cache initial
        return false
      catch
        | .matrix .dimensions => pure ()
        | _ => return false
    for bad in [CriticalPair.mk 0 2 lcm 2 2, CriticalPair.mk 2 0 lcm 2 2] do
      try
        let _ ← PairRows.prepare context {} basis #[bad] .empty
        return false
      catch
        | .matrix .dimensions => pure ()
        | _ => return false
    try
      let _ ← PairRows.prepare context {} #[basis[0]!,BasisElement.mk {} 0]
        #[CriticalPair.mk 0 1 lcm 2 2] .empty
      return false
    catch
      | .matrix .dimensions => pure ()
      | _ => return false
    return true
  match action.run { table := { arity := 2 } } with
  | (.ok value, _) => value
  | _ => false

#guard invalidSeeds

/-- Independent reduction retains the association between each target and its
remainder, even when the longer target precedes the shorter one. -/
private def orderedRemainders : Bool := Id.run do
  let context : Context := ⟨field,1,.lex⟩
  let action : Computation Bool := do
    let g ← Polynomial.normalize context {} 0 #[⟨#[2],1⟩,⟨#[0],6⟩]
    let f ← Polynomial.normalize context {} 1 #[⟨#[3],1⟩,⟨#[1],1⟩,⟨#[0],1⟩]
    let h ← Polynomial.normalize context {} 2 #[⟨#[0],1⟩]
    let matrix ← SymbolicMatrix.prepare context {} #[BasisElement.mk g 2]
      #[BasisElement.mk f 3, BasisElement.mk h 0]
    let output ← matrix.reduce context {}
    let table := (← get).table
    return output.size == 2 &&
      output[0]!.polynomial.toRaw field table == #[⟨#[1],2⟩,⟨#[0],1⟩] &&
      output[1]!.polynomial.toRaw field table == #[⟨#[0],1⟩]
  match action.run { table := { arity := 1 } } with
  | (.ok result, _) => result
  | _ => false

#guard orderedRemainders

/-- Missing symbolic columns preserve the explicit representation error even
when several joint targets require ordering before row translation. -/
private def missingColumns : Bool := Id.run do
  let context : Context := ⟨field,2,.grevlex⟩
  let trial : Computation (Array BasisElement) := do
    let p ← Polynomial.normalize context {} 0 #[⟨#[1,0],1⟩]
    let q ← Polynomial.normalize context {} 0 #[⟨#[0,1],1⟩,⟨#[0,0],1⟩]
    let matrix : SymbolicMatrix := { columns := #[],reducers := #[],targets := #[⟨p,1⟩,⟨q,1⟩] }
    matrix.eliminate context {}
  match trial.run { table := { arity := 2 }, statistics := {} } with
  | (.error (.representation .index),_) => return true
  | _ => return false

#guard missingColumns

/-- In one variable, closing x^k under x-1 has exactly degrees k down to 0.
Unrelated arena entries and newly interned lower powers cross bitmap bytes. -/
private def bitmapClosure (padding k : Nat) (seeded native : Bool) : Bool := Id.run do
  let context : Context := ⟨field,1,.lex⟩
  let limits : Limits := { nativeRows := native,nativeMonomials := native }
  let action : Computation Bool := do
    for i in [:padding] do
      let _ ← Polynomial.normalize context limits 0 #[⟨#[1000+i],1⟩]
    let g ← Polynomial.normalize context limits 0 #[⟨#[1],1⟩,⟨#[0],6⟩]
    let target ← Polynomial.normalize context limits 0 #[⟨#[k],1⟩]
    let basis := #[BasisElement.mk g 1]
    let index ← ReducerIndex.build context limits basis
    let unit ← intern limits #[0]
    let initial := if seeded then #[SymbolicReducer.mk 0 unit g 1] else #[]
    let matrix ← SymbolicMatrix.prepareWith context limits index basis #[⟨target,k⟩] .empty initial
    let table := (← get).table
    if matrix.columns.map table.degree != (Array.range (k+1)).reverse ||
        matrix.reducers.size != k then return false
    let degrees := matrix.reducers.map fun r => table.degree (r.polynomial.monomial 0)
    return degrees.qsort (· ≤ ·) == (Array.range k).map (·+1)
  match action.run { table := { arity := 1 } } with
  | (.ok value,_) => value
  | _ => false

#guard bitmapClosure 7 8 false false
#guard bitmapClosure 8 9 true false

/-- Compiled native/scalar coverage of arena padding and growth within and
across bitmap bytes, with and without preselected reducers. -/
def bitmapChecks (seed : Nat) : Bool := Id.run do
  for padding in [0,1,7,8,9,63,64,65] do
    for k in [1,7,8,9,63,64,65,129] do
      for seeded in [false,true] do
        if !bitmapClosure (padding+seed%2) k seeded false ||
            !bitmapClosure (padding+seed%2) k seeded true then return false
  return true


/-- Production symbolic preprocessing crosses both chunk limits: a 40000-ID
arena needs 5000 bitmap bytes, and each target contains 4200 distinct IDs.
Separate-tail remainders reuse the bitmap: only the first call pays its growth.
The visited queue is cleared between calls, without changing the normal form. -/
def chunkChecks (seed : Nat) (native : Bool) : Bool := Id.run do
  let context : Context := ⟨field,1,.lex⟩
  let limits : Limits := { work := 1000000000, nativeRows := native,nativeMonomials := native }
  let action : Computation Bool := do
    for i in [:40000] do
      let _ ← intern limits #[i.toUInt64]
    let mut p : Polynomial := {}
    for i in [:4200] do
      p := { support := Packed.push .u32 p.support (4199-i+seed%17).toUInt64, coefficients := p.coefficients.push 1 }
    let index ← ReducerIndex.build context limits #[]
    let before := (← get).statistics
    let first ← p.remainderWith context limits index #[]
    let middle := (← get).statistics
    let second ← p.remainderWith context limits index #[]
    let after := (← get).statistics
    if first.support != p.support || first.coefficients != p.coefficients ||
        second.support != p.support || second.coefficients != p.coefficients then return false
    if middle.allocatedBytes-before.allocatedBytes != after.allocatedBytes-middle.allocatedBytes+5000 then
      return false
    if (← get).support.bits.size != 5000 || (← get).support.queue.size != 4200 then return false
    let beforeClear := (← get).statistics.work
    resetSupport limits
    return (← get).statistics.work == beforeClear+4200 && (← get).support.queue.isEmpty
  match action.run { table := { arity := 1 } } with
  | (.ok value,_) => value
  | _ => false


/-- A failed clearing reservation preserves paid-for scratch for a later retry.
Repeated preparation under an exact byte allowance needs no additional bitmap. -/
def scratchChecks (native : Bool) : Bool := Id.run do
  let limits : Limits := { nativeMonomials := native }
  let action : Computation Bool := do
    for i in [:16] do
      let _ ← intern limits #[i.toUInt64]
    let support := Packed.push .u32 {} 15
    queueSupport limits support
    let before := (← get).statistics
    let bits := (← get).support.bits
    try
      resetSupport { limits with work := before.work }
      return false
    catch
      | .exhausted .work => pure ()
      | _ => return false
    if (← get).support.bits != bits || (← get).support.queue != #[15] then return false
    let bytes := before.allocatedBytes+(← get).table.bytes
    resetSupport { limits with packedBytes := bytes }
    queueSupport { limits with packedBytes := bytes } support
    if (← get).statistics.allocatedBytes != before.allocatedBytes then return false
    return (← get).support.bits == bits && (← get).support.queue == #[15]
  match action.run { table := { arity := 1 } } with
  | (.ok value,_) => value
  | _ => false

#guard scratchChecks false
#guard scratchChecks true


private def canonical (raw : RawPolynomial) : Certificate.Polynomial :=
  raw.foldl (fun f term => if term.coefficient == 0 then f else
    Hex.MvPoly.Kernel.addMod 7 f [(term.exponents.toList,term.coefficient.toNat)]) []

/-- Exercise the public deterministic, sampled and certificate-producing outer
loops. Every route performs multiple rounds; counters surround these calls in
IO so a direct exclusive-workspace test cannot substitute for this coverage. -/
def systemChecks (seed route : Nat) : Bool := Id.run do
  let context : Context := ⟨field,2,.grevlex⟩
  let raw : Array RawPolynomial := #[#[⟨#[2,0],1⟩,⟨#[0,1],6⟩],
    #[⟨#[1,1],1⟩,⟨#[0,0],(1+seed%6).toUInt64⟩]]
  let .candidate expected _ := computeWith context { nativeMonomials := false,nativeRows := false } raw |
    return false
  match route with
  | 0 =>
    let .candidate actual stats := computeWith context {} raw seed.toUInt64 | return false
    return stats.rounds ≥ 2 && actual.polynomials == expected.polynomials && actual.randomState == seed.toUInt64
  | 1 =>
    let .candidate actual stats _ := Sampled.computeWith context {} raw (Hex.Rand.ofSeed seed) | return false
    return stats.rounds ≥ 2 && actual.polynomials == expected.polynomials
  | 2 =>
    let .candidate actual stats := Producer.computeWith context {} 1000000 raw | return false
    return stats.rounds ≥ 2 && actual.polynomials == expected.polynomials.map canonical
  | _ => return false

#guard systemChecks 0 0
#guard systemChecks 0 1
#guard systemChecks 0 2

end Hex.Groebner.PairRowsConformance
