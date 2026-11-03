/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexGroebnerTrieNative
import LeanBench

namespace Hex.Groebner.Bench
open Computation

private def trieField : PrimeField :=
  ⟨32003,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩

private def trieLimits : Limits := { work := 1000000000, packedBytes := 1000000000 }

structure TrieInput where
  index : ReducerIndex
  basis : Array BasisElement
  state : Workspace
  query : Nat

instance : Hashable TrieInput where
  hash input := hash (input.query,
    input.index.nodes.map (fun n => (n.edges,n.reducer,n.depth)),
    input.index.packed.map (fun v => (v.arity,v.nodes,v.edges,v.maxLeading)),
    input.basis.map (fun p => (p.polynomial.support,p.polynomial.coefficients,p.sugar)),
    input.state.table.arity,input.state.table.width.bytes,input.state.table.count,
    input.state.table.hashBits,input.state.table.work,input.state.table.exponents,
    input.state.table.metadata,input.state.table.workspace,input.state.table.index.heads,
    input.state.table.index.links,reprStr input.state.statistics)

private def trieContext : Context := ⟨trieField,2,.grevlex⟩

/-- A monomial antichain of degree n. The query admits every reducer, and the
first LIFO leaf has the least validated priority. Preparation is excluded. -/
def prepareTrie (n : Nat) : Option TrieInput :=
  let trial : Computation (ReducerIndex × Array BasisElement × Nat) := do
    let mut basis : Array BasisElement := #[]
    for i in [:n] do
      let p ← Polynomial.normalize trieContext trieLimits i #[⟨#[i,n-i],1⟩]
      basis := basis.push ⟨p,n⟩
    let index ← ReducerIndex.build trieContext trieLimits basis
    let query ← intern trieLimits #[n.toUInt64,n.toUInt64]
    return (index,basis,query)
  match trial.run { table := { arity := 2 } } with
  | (.ok (index,basis,query),state) => some ⟨index,basis,state,query⟩
  | _ => none

private def lookupTrie (native : Bool) (input : Option TrieInput) :
    Bool × Array Nat × Nat := Id.run do
  let some input := input | return (false,#[],0)
  let initial := input.state.statistics.work
  let (result,work) := if native then
    let (result,state) := (input.index.find trieContext trieLimits input.basis input.query).run input.state
    (result,state.statistics.work)
  else
    ReducerIndex.findPortable trieContext input.index input.basis input.state.table
      input.query initial trieLimits.work
  let .ok (some selected) := result | return (false,#[],work-initial)
  return (input.index.packed.isSome && selected+1 == input.basis.size &&
      work-initial == input.basis.size+4,
    input.state.table.exponentsAt (input.basis[selected]!.polynomial.monomial 0),work-initial)

/-- Read-only reducer lookup, including exact work accounting and decoding the
selected leading monomial for result hashing. -/
def trieLookup (input : Option TrieInput) := lookupTrie true input

/-- The same immutable index through the independent node traversal. -/
def trieLookupPortable (input : Option TrieInput) := lookupTrie false input

#guard (#[16,32,64,128,256,512,1024,2048].all fun n =>
  let input := prepareTrie n
  let result := trieLookup input
  result.1 && result == trieLookupPortable input)

-- The root scans n exponent edges; the first branch, edge and leaf finish the
-- lookup at the global priority bound. The query therefore takes n+4 work.
setup_benchmark trieLookup n => n
  with prep := prepareTrie
  where {
    paramFloor := 16
    paramCeiling := 2048
    paramSchedule := .custom #[16,32,64,128,256,512,1024,2048]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

setup_benchmark trieLookupPortable n => n
  with prep := prepareTrie
  where {
    paramFloor := 16
    paramCeiling := 2048
    paramSchedule := .custom #[16,32,64,128,256,512,1024,2048]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

end Hex.Groebner.Bench
