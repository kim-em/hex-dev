/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Monomial

namespace Hex.Groebner.ProductBatchConformance

private def same (a b : ProductResult) : Bool :=
  (match a.result,b.result with
    | .ok x,.ok y => x.data == y.data
    | .error x,.error y => x == y
    | _,_ => false) &&
    a.table.arity == b.table.arity && a.table.width == b.table.width &&
    a.table.exponents == b.table.exponents && a.table.metadata == b.table.metadata &&
    a.table.count == b.table.count && a.table.workspace == b.table.workspace &&
    a.table.index.heads == b.table.index.heads && a.table.index.links == b.table.index.links &&
    a.table.hashBits == b.table.hashBits && a.table.work == b.table.work

private def check (table : MonomialTable) (support : ByteArray)
    (monomial start count maxCount maxBytes maxWork : Nat) (native : Bool) : Bool :=
  let actual := table.productsAttempt support monomial start count maxCount maxBytes maxWork native
  let expected := table.productsAttemptPortable support monomial start count maxCount maxBytes maxWork native
  let admission := match actual,expected with
    | .accepted x,.accepted y => same x y
    | .deferred x,.deferred y => same ⟨.ok {},x⟩ ⟨.ok {},y⟩
    | _,_ => false
  admission && same (table.productsWith support monomial start count maxCount maxBytes maxWork native)
    (table.productsReference support monomial start count maxCount maxBytes maxWork native)

/-- Compare complete slice results and failure states, including forced collisions,
width growth, malformed indices, arbitrary Nat limits and partial slices. -/
def checks (seed : Nat) : Bool := Id.run do
  for arity in [0,1,3,65] do
    for bits in [0,3,64] do
      for large in ([0,255,65535,4294967295] : List UInt64) do
        let mut table : MonomialTable := { arity,hashBits := bits }
        for i in [:8] do
          let values := (Array.range arity).map fun j =>
            if j == 0 then large else ((i+j+seed)%7).toUInt64
          let next := table.internOwned values 1000 10000000 10000000
          let .ok _ := next.result | return false
          table := next.table
        let support := (Array.range 9).foldl (fun bytes i => Packed.push .u32 bytes i.toUInt64) {}
        for monomial in [0,table.count-1,table.count,2^90] do
          for start in [0,1,7,9,2^90] do
            for count in [0,1,4,64,2^90] do
              for limit in [0,1,100,10000000,2^90] do
                for native in [false,true] do
                  if !check table support monomial start count limit limit limit native then return false
  return true

/-- Complete successful batches straddle the 64-ID and 4096-visit bounds.
Shared workspace aliases, insertions and every relevant allowance prefix retain
all scalar bytes and counters. The larger arities run in compiled checks. -/
def boundaryChecks (seed : Nat) (full := true) : Bool := Id.run do
  for arity in (if full then [1,2,21,22,65,1365,1366,2047] else [1,21,22]) do
    for bits in [0,3,64] do
      for step in ([1,257,65537] : List Nat) do
        let mut table : MonomialTable := { arity,hashBits := bits }
        for id in [:128] do
          let next := table.internOwned (Array.replicate arity (id*step).toUInt64)
            1000 10000000 1000000000
          let .ok _ := next.result | return false
          table := next.table
        let support := (Array.range 66).foldl (fun bytes i =>
          Packed.push .u32 bytes ((i+seed%3)%66).toUInt64) {}
        for workspace in [table.workspace,table.exponents,table.metadata,
            table.index.heads,table.index.links,support] do
          let input := { table with workspace }
          let snapshots := [input.exponents,input.metadata,input.workspace,
            input.index.heads,input.index.links,support].map fun bytes => bytes.data.toList
          for (start,count,monomial) in [(0,1,0),(0,63,1),(0,64,1),(0,65,1),
              (1,64,1),(65,64,1),(66,64,1),(0,64,127),(0,64,128)] do
            for allowance in [0,1,3*arity,3*arity+1,4095,4096,4097,100000000] do
              let work := input.work+allowance
              if !check input support monomial start count 1000 10000000 work true then return false
          if snapshots != ([input.exponents,input.metadata,input.workspace,
              input.index.heads,input.index.links,support].map fun bytes => bytes.data.toList) then
            return false
  return true

/-- Malformed packed geometry, arbitrary Nat metadata and independently large
allowances must make the same admission decision and preserve failure prefixes. -/
def malformedChecks (seed : Nat) : Bool := Id.run do
  let mut table : MonomialTable := { arity := 2 }
  for value in ([0,1,2+seed%3] : List Nat) do
    let next := table.internOwned #[value.toUInt64,value.toUInt64] 100 1000000
    let .ok _ := next.result | return false
    table := next.table
  let support := Packed.push .u32 {} 0
  for input in [table,{ table with arity := 2^90 },{ table with count := 2^90 },
      { table with work := 2^90 },{ table with hashBits := 2^90 },
      { table with exponents := table.exponents.push 0 },
      { table with metadata := table.metadata.push 0 },
      { table with index.heads := {} },{ table with index.heads := table.index.heads.push 0 },
      { table with index.links := table.index.links.push 0 }] do
    for bytes in [support,support.push 0] do
      for native in [false,true] do
        for (maxCount,maxBytes,maxWork) in [(0,0,0),(100,1000000,1000000),
            (2^90,1000000,1000000),(100,2^90,1000000),(100,1000000,2^90),
            (2^90,2^90,2^90)] do
          if !check input bytes 0 0 64 maxCount maxBytes maxWork native then return false
  return true

/-- Repeating the newest collision-chain head makes every hit cost exactly
`3*arity+1`. Require positive admission at the work cap and deferral above it. -/
def capacityChecks : Bool := Id.run do
  for arity in [21,22,65,1365] do
    let mut table : MonomialTable := { arity,hashBits := 0 }
    for value in ([0,1] : List UInt64) do
      let next := table.internOwned (Array.replicate arity value) 100 1000000 1000000
      let .ok _ := next.result | return false
      table := next.table
    table := { table with work := 0 }
    let count := 4096/(3*arity+1)
    let support := (Array.range (count+1)).foldl (fun bytes _ => Packed.push .u32 bytes 1) {}
    for attempt in [table.productsAttempt support 0 0 count 100 1000000 1000000 true,
        table.productsAttemptPortable support 0 0 count 100 1000000 1000000 true] do
      let .accepted result := attempt | return false
      if !result.result.isOk || result.table.work != count*(3*arity+1) then return false
    for attempt in [table.productsAttempt support 0 0 (count+1) 100 1000000 1000000 true,
        table.productsAttemptPortable support 0 0 (count+1) 100 1000000 1000000 true] do
      let .deferred returned := attempt | return false
      if !same ⟨.ok {},returned⟩ ⟨.ok {},table⟩ then return false
    if !check table support 0 0 count 100 1000000 1000000 true then return false
  return true

/-- Exactly the final product is missing; a discarded nonempty prefix must
reach ordinary scalar insertion while preserving the complete reference state. -/
def lastMiss (seed : Nat) : Bool := Id.run do
  let mut table : MonomialTable := { arity := 3 }
  let step := 1+seed%7
  for i in [:64] do
    let next := table.internOwned (Array.replicate 3 (i*step).toUInt64) 1000 10000000 1000000000
    let .ok _ := next.result | return false
    table := next.table
  let support := (Array.range 64).foldl (fun bytes i => Packed.push .u32 bytes i.toUInt64) {}
  return check table support 1 0 64 1000 10000000 1000000000 true

#guard capacityChecks
#guard lastMiss 0

#guard checks 0
#guard malformedChecks 0
#guard boundaryChecks 0 false

/-- info: 'Hex.Groebner.MonomialTable.productsWith_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MonomialTable.productsWith_spec

end Hex.Groebner.ProductBatchConformance
