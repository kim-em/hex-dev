/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Monomial

namespace Hex.Groebner.HitConformance

private def same (a b : InternResult) : Bool :=
  (match a.result, b.result with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false) &&
    a.table.arity == b.table.arity && a.table.width == b.table.width &&
    a.table.exponents == b.table.exponents && a.table.metadata == b.table.metadata &&
    a.table.count == b.table.count && a.table.workspace == b.table.workspace &&
    a.table.index.heads == b.table.index.heads && a.table.index.links == b.table.index.links &&
    a.table.hashBits == b.table.hashBits && a.table.work == b.table.work

private def sameAttempt (a b : MonomialTable.Attempt) : Bool :=
  match a,b with
  | .accepted x,.accepted y => same x y
  | .deferred x,.deferred y => same ⟨.ok 0,x⟩ ⟨.ok 0,y⟩
  | _,_ => false

/-- Compare the fused native path with its full reference, including every
returned byte, aliases, budget prefixes, hash collisions and fallback arities. -/
def runtimeChecks (seed : Nat) : Bool := Id.run do
  for arity in [1,2,5,65,2047,2048,2049,4096] do
    for hashBits in [0,3,64] do
      for count in [13,30,32] do
        let mut table : MonomialTable := { arity, hashBits }
        for id in [:count] do
          let values := (Array.range arity).map fun i => (id + i%3 + seed%7).toUInt64
          let next := table.internOwned values 100 10000000 10000000
          if !next.result.isOk then return false
          table := next.table
        for workspace in [ByteArray.empty, table.exponents, table.metadata, table.index.heads] do
          let input := { table with workspace }
          for (a,b) in [(0,0),(0,count-1),(7,5),(count-1,count-1)] do
            for op in [MonomialTable.Operation.lcm,.product,.quotient] do
              for budget in [0,1,arity,2*arity,2*arity+1,3*arity,10000000,2^90] do
                let x := input.attempt op a b 100 10000000 budget true
                let y := input.attemptPortable op a b 100 10000000 budget true
                if !sameAttempt x y then return false
  -- Exact same-width insertion and lookup at every exponent storage width.
  for large in ([0,256,65536] : List UInt64) do
    let mut table : MonomialTable := { arity := 2, hashBits := seed%4 }
    for id in [:5] do
      let next := table.internOwned #[large+id.toUInt64, (id%2).toUInt64] 100 1000000
      if !next.result.isOk then return false
      table := next.table
    for (a,b) in [(0,1),(2,4),(3,4)] do
      for op in [MonomialTable.Operation.lcm,.product,.quotient] do
        let x := table.attempt op a b 100 1000000 1000000 true
        let y := table.attemptPortable op a b 100 1000000 1000000 true
        if !sameAttempt x y then return false
  return true

/-- Malformed geometry, machine-size boundaries and arbitrary Nat metadata
must defer the identical table, with no partially prepared workspace. -/
def malformedChecks (seed : Nat) : Bool := Id.run do
  let original : MonomialTable := { arity := 2 }
  let x := original.internOwned #[1,(seed%7).toUInt64] 100 1000000
  if !x.result.isOk then return false
  let table := x.table
  let malformed := #[table,{ table with arity := 2^90 },{ table with count := 2^90 },
    { table with hashBits := 2^90 },{ table with work := 2^90 },
    { table with exponents := table.exponents.push 0 },
    { table with metadata := table.metadata.push 0 },
    { table with index.links := table.index.links.push 0 },
    { table with index.heads := table.index.heads.push 0 },
    { table with index.heads := {} },{ table with workspace := table.exponents }]
  for input in malformed do
    for native in [false,true] do
      for (a,b) in [(0,0),(0,1),(2^90,0),(0,2^90)] do
        for limit in [0,1,1000000,USize.size/2-1,USize.size/2,2^90] do
          let x := input.attempt .lcm a b limit limit limit native
          let y := input.attemptPortable .lcm a b limit limit limit native
          if !sameAttempt x y then return false
  return true

#guard malformedChecks 0

#guard runtimeChecks 0

/-- Build independently allocated equal tables with spare index and exponent
capacity. Inputs differing by seven have equal values without sharing buffers. -/
@[noinline] private def ownedTable (seed : Nat) (alias : Bool) : Option MonomialTable := Id.run do
  let mut table : MonomialTable := { arity := 1, hashBits := 0 }
  for id in [:32] do
    let next := table.internOwned #[(id+1+seed%7).toUInt64] 100 1000000
    if !next.result.isOk then return none
    table := next.table
  let mut heads := ByteArray.emptyWithCapacity 512
  for _ in [:512] do heads := heads.push 0
  let mut index : MonomialIndex := { heads }
  for id in [:32] do index := index.insert id (table.hashAt id) table.hashAt
  let mut exponents := ByteArray.emptyWithCapacity 128
  for id in [:32] do exponents := exponents.push (id+1+seed%7).toUInt8
  let workspace := if alias then exponents else ByteArray.empty
  return some { table with index, exponents, workspace }

/-- Consume independent equal tables so native mutation is compared directly
with the reference, including workspace/exponent aliasing and insertion bounds.
The compiled harness requires an accepted unique-table aliased insertion. -/
def ownedChecks (seed : Nat) : Bool := Id.run do
  for alias in [false,true] do
    for operation in [MonomialTable.Operation.lcm,.product] do
      let some input := ownedTable (seed+7) alias | return false
      let bytes := input.bytes
      let initial := input.work
      let .accepted expected := input.attemptPortable operation 31 31 100 1000000 1000000 true
        | return false
      if !expected.result.isOk then return false
      let outputBytes := expected.table.bytes
      let totalWork := expected.table.work
      for count in [31,32,33,100,2^90] do
        for limit in [0,bytes-1,bytes,outputBytes-1,outputBytes,1000000,2^90] do
          let some reference := ownedTable (seed+7) alias | return false
          let expected := reference.attemptPortable operation 31 31 count limit 1000000 true
          let some actual := ownedTable seed alias | return false
          let actual := actual.attempt operation 31 31 count limit 1000000 true
          if !sameAttempt actual expected then return false
      for work in [0,initial-1,initial,initial+1,totalWork-1,totalWork,totalWork+1,2^90] do
        let some reference := ownedTable (seed+7) alias | return false
        let expected := reference.attemptPortable operation 31 31 100 1000000 work true
        let some actual := ownedTable seed alias | return false
        let actual := actual.attempt operation 31 31 100 1000000 work true
        if !sameAttempt actual expected then return false
  return true

#guard ownedChecks 0

end Hex.Groebner.HitConformance
