/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

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
      pairs := pairs.push (CriticalPair.mk a b lcm 3)
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
    let rows ← PairRows.prepare context {} basis #[CriticalPair.mk 0 1 lcm 2] .empty
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
    for bad in [CriticalPair.mk 0 2 lcm 2, CriticalPair.mk 2 0 lcm 2] do
      try
        let _ ← PairRows.prepare context {} basis #[bad] .empty
        return false
      catch
        | .matrix .dimensions => pure ()
        | _ => return false
    try
      let _ ← PairRows.prepare context {} #[basis[0]!,BasisElement.mk {} 0]
        #[CriticalPair.mk 0 1 lcm 2] .empty
      return false
    catch
      | .matrix .dimensions => pure ()
      | _ => return false
    return true
  match action.run { table := { arity := 2 } } with
  | (.ok value, _) => value
  | _ => false

#guard invalidSeeds

end Hex.Groebner.PairRowsConformance
