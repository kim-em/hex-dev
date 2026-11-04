/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Native

namespace Hex.Groebner.SupportConformance

private def packed (ids : Array Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for id in ids do
    for j in [:4] do out := out.push ((id / 256^j)%256).toUInt8
  return out

private def zeroes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

private def initialBits (n seed : Nat) : ByteArray := ⟨Array.replicate n (seed%256).toUInt8⟩

/-- Exact first-occurrence order, existing bits, arbitrary pending prefixes,
byte/slice boundaries, malformed IDs and geometry, sharing and borrowed aliases.
The seed comes from IO in the compiled sanitizer harness. -/
def queueChecks (seed : Nat) : Bool := Id.run do
  for count in [0,1,7,8,9,63,64,65,4097] do
    let n := if count == 0 then 0 else min 80 (count+10)
    let values := (Array.range n).map fun i => (i*17+seed)%count
    let ids := packed values
    let bits := initialBits ((count+7)/8) seed
    let pendingStart := #[seed,2^100]
    for start in [0,n/2,n,n+1,2^100] do
      for terms in [0,1,n/2,n,4097,2^100] do
        let expected := Native.Support.queuePortable count.toUInt64 ids start terms bits pendingStart
        let actual := Native.Support.queue count.toUInt64 ids start terms bits pendingStart
        if actual != expected then return false
        if bits != initialBits ((count+7)/8) seed then return false
        if pendingStart != #[seed,2^100] || ids != packed values then return false
  -- Explicit expectation independently checks deduplication and preserved order.
  let ids := packed #[8,0,8,7,9,7,1]
  let some (bits,queued) := Native.Support.queue 10 ids 0 7 (zeroes 2) #[999] | return false
  if bits != ⟨#[131,3]⟩ || queued != #[999,8,0,7,9,1] then return false
  -- Maximum slice is accepted; the next term is rejected rather than truncated.
  let ids := packed ((Array.range 4097).map fun i => (i+seed)%65)
  let expected := Native.Support.queuePortable 65 ids 0 4096 (zeroes 9) #[]
  if expected.isNone || Native.Support.queue 65 ids 0 4096 (zeroes 9) #[] != expected then return false
  if (Native.Support.queue 65 ids 0 4097 (zeroes 9) #[]).isSome then return false
  -- The bitmap aliases the borrowed ID bytes. Setting bit 33 would alter the next
  -- ID if the native implementation mutated the borrowed storage in place.
  let alias := packed #[33,0]
  let snapshot := packed #[33,0]
  let expected := Native.Support.queuePortable 64 alias 0 2 alias #[seed]
  if Native.Support.queue 64 alias 0 2 alias #[seed] != expected || alias != snapshot then return false
  for (count,ids,bits) in [
      (8,packed #[0,8],zeroes 1), (8,⟨#[0,0,0]⟩,zeroes 1),
      (8,packed #[0],zeroes 0), (4294967297,ByteArray.empty,ByteArray.empty)] do
    if (Native.Support.queue count.toUInt64 ids 0 (ids.size/4) bits #[seed]).isSome then return false
  return true


/-- Clearing rejects malformed slices and IDs and preserves every other bit,
including duplicates, empty slices and a bitmap shared with an observer. -/
def clearChecks (seed : Nat) : Bool := Id.run do
  let bits : ByteArray := ⟨Array.replicate 9 255⟩
  let queue := #[0,7,8,31,32,63,63,64,seed%65]
  for start in [0,1,queue.size,queue.size+1,2^100] do
    for terms in [0,1,queue.size,4096,4097,2^100] do
      let expected := Native.Support.clearPortable bits queue start terms
      if Native.Support.clear bits queue start terms != expected then return false
      if bits != (⟨Array.replicate 9 255⟩ : ByteArray) then return false
  let some actual := Native.Support.clear bits #[0,7,8,31,32,63,63] 0 7 | return false
  if actual != (⟨#[126,254,255,127,254,255,255,127,255]⟩ : ByteArray) then return false
  for queue in [#[72],#[2^32],#[2^100]] do
    if (Native.Support.clear bits queue 0 1).isSome then return false
  let queue := (Array.range 4097).map fun i => (i+seed)%65
  let expected := Native.Support.clearPortable bits queue 0 4096
  if expected.isNone || Native.Support.clear bits queue 0 4096 != expected then return false
  return (Native.Support.clear bits queue 0 4097).isNone

#guard clearChecks 0
#guard clearChecks 17

#guard queueChecks 0
#guard queueChecks 17

end Hex.Groebner.SupportConformance
