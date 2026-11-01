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
    (indices : Array (Nat × Nat)) (targetCount : Nat) : Bool := Id.run do
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
    if rows.reducers.size != 1 || rows.targets.size != targetCount then return false
    let some reducer := rows.reducers[0]? | return false
    if reducer.basis != 0 then return false
    let all := rows.reducers ++ rows.targets
    for pair in pairs do
      let some left := all.find? (·.basis == pair.left) | return false
      let some right := all.find? (·.basis == pair.right) | return false
      let actual ← left.polynomial.subtract context {} right.polynomial
      let expected ← basis[pair.left]!.polynomial.sPolynomial context {} basis[pair.right]!.polynomial
      if actual.support != expected.support || actual.coefficients != expected.coefficients then return false
    let index ← ReducerIndex.build context {} basis
    let targets := rows.targets.map fun r => BasisElement.mk r.polynomial r.sugar
    let matrix ← SymbolicMatrix.prepareWith context {} index basis targets rows.cache rows.reducers
    if (matrix.reducers.filter (·.polynomial.monomial 0 == reducer.polynomial.monomial 0)).size != 1 then
      return false
    return true
  match action.run { table := { arity := variables } } with
  | (.ok value, _) => return value
  | _ => return false

#guard groupCheck 3 #[
  #[⟨#[1,1,0],1⟩,⟨#[0,0,0],1⟩],
  #[⟨#[1,0,1],1⟩,⟨#[0,1,0],1⟩,⟨#[0,0,0],1⟩],
  #[⟨#[0,1,1],1⟩,⟨#[1,0,0],1⟩]] #[(0,1),(0,2),(1,2)] 2

-- Same LCM with disconnected pair components retains both selected identities.
#guard groupCheck 4 #[
  #[⟨#[1,1,0,0],1⟩,⟨#[0,0,0,0],1⟩],
  #[⟨#[0,0,1,1],1⟩,⟨#[0,0,0,0],1⟩],
  #[⟨#[1,0,1,0],1⟩,⟨#[0,0,0,0],1⟩],
  #[⟨#[0,1,0,1],1⟩,⟨#[0,0,0,0],1⟩]] #[(0,1),(2,3)] 3

end Hex.Groebner.PairRowsConformance
