/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.ColumnMap
import LeanBench

namespace Hex.Groebner.Bench

/-- Input generation is excluded from map construction and row translation. -/
structure ColumnInput where
  ids : Array Nat
  support : ByteArray
  deriving Hashable

private def columns (n stride : Nat) : ColumnInput := Id.run do
  let ids := (Array.range n).map (fun i => i*stride)
  let mut support := ByteArray.emptyWithCapacity (n*4)
  for id in ids do support := Packed.push .u32 support id.toUInt64
  return ⟨ids,support⟩

/-- Dense identifier prefix, requiring exactly n direct position slots. -/
def prepareColumns (n : Nat) : ColumnInput := columns n 1

/-- Widely spaced u32 IDs select the packed exact hash layout. Verification
parameters zero and one use two entries so they exercise the indexed route. -/
def prepareColumnIndex (n : Nat) : ColumnInput := columns (max 2 n) 997

private def columnMap (input : ColumnInput) (indexed : Bool) :
    Bool × Nat × ByteArray × ByteArray := Id.run do
  let workspace : Workspace := { table := { arity := 0 } }
  let (.ok positions,_) := (ColumnMap.build { work := 1000000000,packedBytes := 1000000000 }
      input.ids).run workspace | return (false,0,{},{})
  let (payload,probes,route) := match positions with
    | .packed bytes => (bytes,1,!indexed)
    | .indexed bytes probes => (bytes,probes,indexed)
    | .hashed _ => ({},0,false)
  if !route || (indexed && probes == 0) || (!indexed && payload.size != input.ids.size*4) then
    return (false,probes,payload,{})
  let some encoded := positions.encode input.support true | return (false,probes,payload,{})
  let mut valid := encoded.size == input.ids.size*4
  for i in [:input.ids.size] do
    if Packed.read .u32 encoded i != i.toUInt64 then valid := false
  return (valid,probes,payload,encoded)

/-- Direct map initialization, construction, bounded translation and validation,
including full structural hashing of both packed map and translated support. -/
def columnDirect (input : ColumnInput) := columnMap input false

/-- Exact sparse-ID hash construction and translation under the same contract. -/
def columnIndex (input : ColumnInput) := columnMap input true

#guard (columnDirect (prepareColumns 16)).1
#guard (columnIndex (prepareColumnIndex 16)).1
#guard (columnIndex (prepareColumnIndex 0)).1
#guard (columnIndex (prepareColumnIndex 1)).1
#guard !(columnIndex (prepareColumns 16)).1
#guard !(columnDirect (prepareColumnIndex 16)).1
#guard (#[1024,1536,2048,3072,4096,8192,16384,32768,65536].all fun n =>
  (columnDirect (prepareColumns n)).1 && (columnIndex (prepareColumnIndex n)).1)

-- Both models are O(n): direct initialization visits n slots; the hash table
-- has capacity less than 4*n and every insertion/lookup uses at most 64 probes.
-- Row translation, independent output validation and structural hashing visit
-- O(n) logical bytes. Copying the whole growing table per insertion would
-- instead give quadratic behavior, which this fixed schedule can expose.
setup_benchmark columnDirect n => n
  with prep := prepareColumns
  where {
    paramFloor := 1024
    paramCeiling := 65536
    paramSchedule := .custom #[1024,1536,2048,3072,4096,8192,16384,32768,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 20.0
  }

-- At load at most one half, initialization visits fewer than 4*n buckets.
-- Each insertion and lookup is capped at 64 probes; translation, validation
-- and hashing also visit O(n) bytes. Non-power-of-two sizes vary the load.
setup_benchmark columnIndex n => n
  with prep := prepareColumnIndex
  where {
    paramFloor := 1024
    paramCeiling := 65536
    paramSchedule := .custom #[1024,1536,2048,3072,4096,8192,16384,32768,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 20.0
  }

end Hex.Groebner.Bench
