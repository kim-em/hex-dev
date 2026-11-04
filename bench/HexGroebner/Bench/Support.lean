/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Packed
import HexGroebner.Native
import LeanBench

namespace Hex.Groebner.Bench

/-- Packed IDs with three occurrences of each monomial in interleaved order.
Input construction is excluded; bitmap initialization is measured. -/
structure SupportInput where
  count : Nat
  ids : ByteArray
  deriving Hashable

/-- The odd multiplier permutes each power-of-two arena used by the schedule. -/
def prepareSupport (n : Nat) : SupportInput := Id.run do
  let n := max 1 n
  let mut ids := ByteArray.emptyWithCapacity (12*n)
  for i in [:3*n] do ids := Packed.push .u32 ids ((17*i)%n).toUInt64
  return ⟨n,ids⟩

private def queueSupport (input : SupportInput) (native : Bool) := Id.run do
  let mut bits := ByteArray.emptyWithCapacity ((input.count+7)/8)
  for _ in [:(input.count+7)/8] do bits := bits.push 0
  let mut pending : Array Nat := #[]
  let terms := input.ids.size/4
  for chunk in [:(terms+4095)/4096] do
    let start := chunk*4096
    let n := min 4096 (terms-start)
    let some (next,queued) := if native then
        Native.Support.queue input.count.toUInt64 input.ids start n bits pending
      else Native.Support.queuePortable input.count.toUInt64 input.ids start n bits pending |
        return (false,bits,pending)
    bits := next
    pending := queued
  let mut valid := pending.size == input.count
  for i in [:pending.size] do
    if pending[i]! != (17*i)%input.count then valid := false
  return (valid,bits,pending)

/-- Bounded native queue, including initialization, validation and full output
hashing of the bitmap and ordered ID array. -/
def supportNative (input : SupportInput) := queueSupport input true

/-- The same input, chunking, output contract and validation in portable Lean. -/
def supportPortable (input : SupportInput) := queueSupport input false


/-- Original support HashSet membership and ordered queue, including insertion
and rehashing. Complete queue validation and hashing match `supportPacked`. -/
def supportHashSet (input : SupportInput) : Bool × Array Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut pending := #[]
  for i in [:input.ids.size/4] do
    let id := (Packed.read .u32 input.ids i).toNat
    if !seen.contains id then
      seen := seen.insert id
      pending := pending.push id
  let mut valid := pending.size == input.count
  for i in [:pending.size] do
    if pending[i]! != (17*i)%input.count then valid := false
  return (valid,pending)

/-- Native bitmap membership under the same ordered-queue result contract as
`supportHashSet`. Initialization and output validation are included. -/
def supportPacked (input : SupportInput) : Bool × Array Nat :=
  let (valid,_,pending) := queueSupport input true
  (valid,pending)

#guard (#[1,8,64,256,4096].all fun n =>
  let input := prepareSupport n
  (supportHashSet input).1 && supportHashSet input == supportPacked input)

-- Expected O(n) membership, amortized HashSet rehashing, n ordered appends,
-- full queue validation and hashing for the original representation.
setup_benchmark supportHashSet n => n
  with prep := prepareSupport
  where {
    paramFloor := 256
    paramCeiling := 65536
    paramSchedule := .custom #[256,512,1024,2048,4096,8192,16384,32768,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 20.0
  }

-- O(n) bitmap initialization, bounded support slices, n appends, complete
-- ordered-queue validation and hashing under the same result contract.
setup_benchmark supportPacked n => n
  with prep := prepareSupport
  where {
    paramFloor := 256
    paramCeiling := 65536
    paramSchedule := .custom #[256,512,1024,2048,4096,8192,16384,32768,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 20.0
  }

#guard (#[0,1,8,64,256,4096].all fun n =>
  let input := prepareSupport n
  (supportNative input).1 && supportNative input == supportPortable input)

-- O(n): initialize ceil(n/8) bitmap bytes, visit 3*n IDs, append n distinct
-- identifiers, validate n IDs and structurally hash both complete outputs.
setup_benchmark supportNative n => n
  with prep := prepareSupport
  where {
    paramFloor := 256
    paramCeiling := 65536
    paramSchedule := .custom #[256,512,1024,2048,4096,8192,16384,32768,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 20.0
  }

-- The portable implementation performs the identical O(n) bitmap, queue,
-- output-validation and structural-hashing work with the same call bounds.
setup_benchmark supportPortable n => n
  with prep := prepareSupport
  where {
    paramFloor := 256
    paramCeiling := 65536
    paramSchedule := .custom #[256,512,1024,2048,4096,8192,16384,32768,65536]
    targetInnerNanos := 4000000000
    maxSecondsPerCall := 20.0
  }

end Hex.Groebner.Bench
