/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Reducer

namespace Hex.Groebner.ReducerConformance
open Computation

private def field : PrimeField := ⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩
private def context : Context := ⟨field, 2, .grevlex⟩

/-- The three branches have explicit visit/edge costs. Test every allowance
around the root's indivisible three-edge charge and all subsequent visits. -/
def budgetChecks : Bool := Id.run do
  let prepare : Computation (ReducerIndex × Array BasisElement × Nat × Nat) := do
    let p ← Polynomial.normalize context {} 0 #[⟨#[2,0],1⟩, ⟨#[0,1],1⟩]
    let q ← Polynomial.normalize context {} 1 #[⟨#[1,1],1⟩, ⟨#[0,0],1⟩]
    let r ← Polynomial.normalize context {} 2 #[⟨#[0,3],1⟩]
    let basis := #[BasisElement.mk p 2, ⟨q,2⟩, ⟨r,3⟩]
    let index ← ReducerIndex.build context {} basis
    let all ← intern {} #[2,3]
    let tie ← intern {} #[2,2]
    return (index, basis, all, tie)
  let (.ok (index, basis, all, tie), initial) := prepare.run { table := { arity := 2 } }
    | return false
  let statistics : Statistics := { work := 17, pairs := 42, allocatedBytes := 1234 }
  let initial := { initial with statistics }
  for allowance in [:17] do
    let limits : Limits := { work := 17 + allowance }
    let (result, final) := (index.find context limits basis all).run initial
    let charged := if allowance < 4 then min allowance 1 else min allowance 11
    if final.statistics != { statistics with work := 17 + charged } then return false
    if final.table.work != initial.table.work || final.table.count != initial.table.count ||
        final.table.exponents != initial.table.exponents || final.table.metadata != initial.table.metadata then
      return false
    match result with
    | .ok selected => if allowance < 11 || selected != some 2 then return false
    | .error (.exhausted .work) => if allowance ≥ 11 then return false
    | _ => return false
  -- Equal support size and degree retain the first leaf in the traversal.
  let (result, final) := (index.find context { work := 28 } basis tie).run initial
  match result with
  | .ok (some 1) => return final.statistics.work == 28
  | _ => return false

#guard budgetChecks

private def oracleChecks : Bool := Id.run do
  let action : Computation Bool := do
    let mut basis := #[]
    for (a,b,c) in [(3,0,1),(2,1,2),(1,2,3),(0,3,1),(2,0,4),(0,2,2)] do
      let raw := #[RawTerm.mk #[a,b] 1] ++
        (Array.range c).map (fun k => RawTerm.mk #[0,k] 1)
      let p ← Polynomial.normalize context {} basis.size raw
      basis := basis.push (BasisElement.mk p (a+b))
    let index ← ReducerIndex.build context {} basis
    let original : ReducerIndex := { index with nodes := index.nodes.map fun n => { n with minSize := 0, maxDegree := 0 } }
    for a in [:6] do
      for b in [:6] do
        let monomial ← intern {} #[a.toUInt64,b.toUInt64]
        let selected ← index.find context {} basis monomial
        let expected ← original.find context {} basis monomial
        if selected != expected then return false
        let table := (← get).table
        let divisors := (Array.range basis.size).filter fun k => table.divides (basis[k]!.polynomial.monomial 0) monomial
        if divisors.isEmpty != selected.isNone then return false
        if let some selected := selected then
          if !divisors.contains selected then return false
          let p := basis[selected]!.polynomial
          for k in divisors do
            let q := basis[k]!.polynomial
            if q.size < p.size || (q.size == p.size && table.degree (q.monomial 0) > table.degree (p.monomial 0)) then
              return false
    return true
  match action.run { table := { arity := 2 } } with
  | (.ok value, _) => return value
  | _ => return false

#guard oracleChecks

end Hex.Groebner.ReducerConformance
