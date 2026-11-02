/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Monomial
import LeanBench

namespace Hex.Groebner.Bench

/-- Prepared stable IDs, with optional missing products at each slice's last term. -/
structure ProductInput where
  table : MonomialTable
  support : ByteArray
  misses : Bool

instance : Hashable ProductInput where
  hash input := hash (input.table.arity,input.table.width.bytes,input.table.count,
    input.table.hashBits,input.table.work,input.table.exponents,input.table.metadata,
    input.table.workspace,input.table.index.heads,input.table.index.links,input.support,input.misses)

private def prepareProductInput (n : Nat) (misses : Bool) (arity := 3) : ProductInput := Id.run do
  let mut table : MonomialTable := { arity }
  for i in [:n+2] do
    let exponent := if misses then i+i/64 else i
    let next := table.internOwned (Array.replicate arity exponent.toUInt64) (n+3) 1000000000 1000000000
    table := next.table
  let support := (Array.range n).foldl (fun bytes i => Packed.push .u32 bytes i.toUInt64) {}
  return ⟨table,support,misses⟩

/-- Interning and support generation are excluded; every product already exists. -/
def prepareProducts (n : Nat) : ProductInput := prepareProductInput n false

/-- Twenty-two variables require shorter slices under the native work cap. -/
def prepareProducts22 (n : Nat) : ProductInput := prepareProductInput n false 22

/-- Each complete 64-term slice lacks exactly its last product at call entry.
Earlier products exist. Missing exponents are distinct between slices. -/
def prepareProductMisses (n : Nat) : ProductInput := prepareProductInput n true

private def runProducts (input : ProductInput) (batch : Bool) := Id.run do
  let mut table := input.table
  let mut output := ByteArray.emptyWithCapacity input.support.size
  let size := max 1 (min 64 (4096/(3*input.table.arity+4)))
  for start in [:(input.support.size/4+size-1)/size] do
    let result := if batch then table.productsWith input.support 1 (start*size) size
        1000000000 1000000000 1000000000 true
      else table.productsReference input.support 1 (start*size) size
        1000000000 1000000000 1000000000 true
    table := result.table
    let .ok ids := result.result | return (false,table,output)
    output := output ++ ids
  let expectedCount := input.table.count + if input.misses then input.support.size/4/64 else 0
  let mut valid := output.size == input.support.size && table.count == expectedCount
  for i in [:output.size/4] do
    let expected := if input.misses && i%64 == 63 then input.table.count+i/64 else i+1
    if Packed.read .u32 output i != expected.toUInt64 then valid := false
  return (valid,table,output)

private def consumeProducts (input : ProductInput) (batch : Bool) :=
  let (valid,table,output) := runProducts input batch
  (valid,table.count,table.work,output,table.workspace)

private def consumeProductMisses (input : ProductInput) (batch : Bool) :=
  let (valid,table,output) := runProducts input batch
  (valid,table.count,table.work,output,table.workspace,table.exponents,table.metadata,
    table.index.heads,table.index.links)

/-- Bounded lookup with complete output support/workspace consumption. -/
def monomialProducts (input : ProductInput) := consumeProducts input true

/-- Original per-term native lookup, with identical limits and output contract. -/
def monomialProductsReference (input : ProductInput) := consumeProducts input false

/-- Adaptive slices at 22 variables, with every product already present. -/
def productWide (input : ProductInput) := consumeProducts input true

/-- The same wider monomials through per-term native lookup. -/
def productWideReference (input : ProductInput) := consumeProducts input false

/-- Last-term misses include deferred prefix work and scalar insertion fallback.
Every mutated support, arena, metadata, workspace and index byte is consumed. -/
def productMisses (input : ProductInput) := consumeProductMisses input true

/-- The same insertions through original per-term native operations. -/
def productMissesReference (input : ProductInput) := consumeProductMisses input false

#guard (#[0,1,63,64,65,256,512,1024,2048,4096].all fun n =>
  let input := prepareProducts n
  (monomialProducts input).1 && monomialProducts input == monomialProductsReference input)

#guard (#[0,1,63,64,65,256,512,1024,2048,4096].all fun n =>
  let input := prepareProducts22 n
  (productWide input).1 && productWide input == productWideReference input)

#guard (#[0,1,63,64,65,256,512,1024,2048,4096].all fun n =>
  let input := prepareProductMisses n
  (productMisses input).1 && productMisses input == productMissesReference input)

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

-- O(n) expected bounded lookup/fallback plus amortized insertion and hashing.
setup_benchmark productMisses n => n
  with prep := prepareProductMisses
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- Identical insertions and complete output consumption cost expected O(n).
setup_benchmark productMissesReference n => n
  with prep := prepareProductMisses
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- O(n) expected lookup and output consumption at fixed arity 22.
setup_benchmark productWide n => n
  with prep := prepareProducts22
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

-- Identical monomials and complete output consumption through scalar lookups.
setup_benchmark productWideReference n => n
  with prep := prepareProducts22
  where {
    paramFloor := 256
    paramCeiling := 4096
    paramSchedule := .custom #[256,512,1024,2048,4096]
    targetInnerNanos := 500000000
    maxSecondsPerCall := 8.0
  }

end Hex.Groebner.Bench
