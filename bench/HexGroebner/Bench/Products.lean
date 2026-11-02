/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Monomial
import LeanBench

namespace Hex.Groebner.Bench

/-- A prepared table contains every requested product; supports use stable IDs. -/
structure ProductInput where
  table : MonomialTable
  support : ByteArray

instance : Hashable ProductInput where
  hash input := hash (input.table.arity,input.table.width.bytes,input.table.count,
    input.table.hashBits,input.table.work,input.table.exponents,input.table.metadata,
    input.table.workspace,input.table.index.heads,input.table.index.links,input.support)

/-- Interning and support generation are excluded from the product timing. -/
def prepareProducts (n : Nat) : ProductInput := Id.run do
  let mut table : MonomialTable := { arity := 3 }
  for i in [:n+2] do
    let next := table.internOwned (Array.replicate 3 i.toUInt64) (n+3) 1000000000 1000000000
    table := next.table
  let support := (Array.range n).foldl (fun bytes i => Packed.push .u32 bytes i.toUInt64) {}
  return ⟨table,support⟩

private def runProducts (input : ProductInput) (batch : Bool) := Id.run do
  let mut table := input.table
  let mut output := ByteArray.emptyWithCapacity input.support.size
  for start in [:(input.support.size/4+63)/64] do
    let result := if batch then table.productsWith input.support 1 (start*64) 64
        1000000000 1000000000 1000000000 true
      else table.productsReference input.support 1 (start*64) 64
        1000000000 1000000000 1000000000 true
    table := result.table
    let .ok ids := result.result | return (false,table.count,table.work,output,table.workspace)
    output := output ++ ids
  let mut valid := output.size == input.support.size && table.count == input.table.count
  for i in [:output.size/4] do
    if Packed.read .u32 output i != (i+1).toUInt64 then valid := false
  return (valid,table.count,table.work,output,table.workspace)

/-- Bounded batched lookup, with complete output support/workspace consumption. -/
def monomialProducts (input : ProductInput) := runProducts input true

/-- Original per-term native lookup under the same limits and output contract. -/
def monomialProductsReference (input : ProductInput) := runProducts input false

#guard (#[0,1,63,64,65,256,512,1024,2048,4096].all fun n =>
  let input := prepareProducts n
  (monomialProducts input).1 && monomialProducts input == monomialProductsReference input)

-- Expected O(n) exact hash lookups at fixed arity/load, bounded per native call.
-- Output assembly, independent ID validation and complete hashing are O(n).
setup_benchmark monomialProducts n => n
  with prep := prepareProducts
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- The same scalar lookups, support assembly and output consumption are O(n).
setup_benchmark monomialProductsReference n => n
  with prep := prepareProducts
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

end Hex.Groebner.Bench
