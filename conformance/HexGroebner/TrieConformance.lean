/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner

namespace Hex.Groebner.TrieConformance
open Computation

private def field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
private def limits : Limits := { work := 1000000000,packedBytes := 1000000000 }

private def equal (a b : Except ComputeError (Option Nat)) : Bool :=
  match a,b with
  | .ok a,.ok b => a == b
  | .error a,.error b => a == b
  | _,_ => false

/-- Compare every lookup and its exhausted prefix against the original node
traversal, and compare native calls directly with the packed portable model. -/
def runtimeChecks (seed : Nat) : Bool := Id.run do
  for n in [0,1,3,7,65,513,2047,4097] do
    for base in [1,257,65537] do
      let context : Context := ⟨field,n,.grevlex⟩
      let trial : Computation Bool := do
        let mut basis : Array BasisElement := #[]
        for k in [:4] do
          let exponents := (Array.range n).map fun i => base+(k+i)%3
          let p ← Polynomial.normalize context limits k #[⟨exponents,1⟩]
          basis := basis.push ⟨p,0⟩
        let index ← ReducerIndex.build context limits basis
        if n ≤ 513 && index.packed.isNone then return false
        if n > 513 && index.packed.isSome then return false
        for k in [:5] do
          let values := (Array.range n).map fun i => (base+(k+2*i+seed)%4).toUInt64
          let monomial ← intern limits values
          let state ← get
          for allowance in [0,1,2,5,17,1000,4096,100000,2^90] do
            let budget := { limits with work := state.statistics.work+allowance }
            let (expected,work) := ReducerIndex.findPortable context index basis state.table monomial
              state.statistics.work budget.work
            let (actual,next) := (index.find context budget basis monomial).run state
            if !equal actual expected || next.statistics.work != work then return false
            if let some view := index.packed then
              let a := Native.Trie.lookup view state.table.width.bytes.toUInt8 state.table.count.toUInt64
                monomial.toUInt64 state.table.exponents state.table.metadata (min allowance 4096).toUInt64
              let b := Native.Trie.lookupPortable view state.table.width.bytes.toUInt8 state.table.count.toUInt64
                monomial.toUInt64 state.table.exponents state.table.metadata (min allowance 4096).toUInt64
              if a.reducer != b.reducer || a.work != b.work || a.status != b.status then return false
        return true
      match trial.run ⟨{arity := n},{}⟩ with
      | (.ok true,_) => pure ()
      | _ => return false
  return true

/-- Maximum admitted tree, reaching 4095 charged visits and edge tests. -/
def boundaryChecks : Bool := Id.run do
  let context : Context := ⟨field,2047,.grevlex⟩
  let trial : Computation Bool := do
    let p ← Polynomial.normalize context limits 0 #[⟨Array.replicate 2047 65537,1⟩]
    let basis := #[BasisElement.mk p 0]
    let index ← ReducerIndex.build context limits basis
    let some view := index.packed | return false
    if index.nodes.size != 2048 then return false
    let state ← get
    let monomial := p.monomial 0
    for allowance in [0,1,2,3,4093,4094,4095,4096,2^90] do
      let a := Native.Trie.lookup view 4 state.table.count.toUInt64 monomial.toUInt64
        state.table.exponents state.table.metadata (min allowance 4096).toUInt64
      let b := Native.Trie.lookupPortable view 4 state.table.count.toUInt64 monomial.toUInt64
        state.table.exponents state.table.metadata (min allowance 4096).toUInt64
      if a.reducer != b.reducer || a.work != b.work || a.status != b.status then return false
      if allowance ≥ 4095 && (a.status != 1 || a.work != 4095 || a.reducer != some 0) then return false
    for viewData in [view.nodes.extract 0 (view.nodes.size-1),
        Native.write view.nodes 4 0 1,Native.write view.nodes 4 4 1,
        Native.write view.nodes 4 8 2,Native.write view.nodes 4 12 1] do
      if (Native.Trie.View.check view.arity viewData view.edges view.maxLeading).isSome then return false
    for links in [view.edges.extract 0 (view.edges.size-1),
        Native.write view.edges 4 4 0,Native.write view.edges 4 4 2048,
        Native.write view.edges 4 12 1] do
      if (Native.Trie.View.check view.arity view.nodes links view.maxLeading).isSome then return false
    for arena in [state.table.exponents.extract 0 (state.table.exponents.size-1),{}] do
      let a := Native.Trie.lookup view 4 state.table.count.toUInt64 monomial.toUInt64
        arena state.table.metadata 4096
      let b := Native.Trie.lookupPortable view 4 state.table.count.toUInt64 monomial.toUInt64
        arena state.table.metadata 4096
      if a.status != 3 || a.reducer != b.reducer || a.work != b.work || a.status != b.status then return false
    return true
  match trial.run ⟨{arity := 2047},{}⟩ with
  | (.ok true,_) => return true
  | _ => return false

#guard boundaryChecks

#guard runtimeChecks 0

end Hex.Groebner.TrieConformance
