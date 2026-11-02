/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.ColumnMap

namespace Hex.Groebner.ColumnMapConformance

private def copy (bytes : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity bytes.size
  for i in [:bytes.size] do out := out.push bytes[i]!
  return out

private def buffer (n : Nat) (value : Nat → UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (4*n)
  for i in [:n] do out := Packed.push .u32 out (value i)
  return out

/-- Exact native/model agreement across full chunks, malformed geometry,
absent entries, large scalar arguments, and every borrowed/output alias. -/
def remapChecks (seed : Nat) : Bool := Id.run do
  for n in [0,7,5001] do
    let positions := buffer n (fun i => (i + 1 + seed%17).toUInt64)
    let support := buffer n (fun i => i.toUInt64)
    for start in [0,3,n,n+1,2^80] do
      for count in [0,1,7,4095,4096,4097,2^80] do
        for initialOutput in [ByteArray.empty,positions,support] do
          let expected := Native.Columns.remapPortable (copy positions) (copy support)
            start count (copy initialOutput)
          let actual := Native.Columns.remap positions support start count initialOutput
          if actual != expected then return false
    if n > 0 then
      for broken in [positions.push 1,Packed.set .u32 positions (n-1) 0] do
        let expected := Native.Columns.remapPortable (copy broken) (copy support) 0 (min n 4096) {}
        if Native.Columns.remap broken support 0 (min n 4096) {} != expected then return false
      let support := Packed.set .u32 support 0 n.toUInt64
      if (Native.Columns.remap positions support 0 1 {}).isSome then return false
  let permuted := buffer 13 (fun i => ((i*7+3)%13+1).toUInt64)
  let repeated := buffer 31 (fun i => (i%13).toUInt64)
  for initialOutput in [ByteArray.empty,permuted,repeated] do
    let expected := Native.Columns.remapPortable (copy permuted) (copy repeated) 0 31 (copy initialOutput)
    if Native.Columns.remap permuted repeated 0 31 initialOutput != expected then return false
  let positions := buffer 3 (fun i => (i+1).toUInt64)
  let support := (buffer 3 (fun i => i.toUInt64)).push 77
  if Native.Columns.remap positions support 0 3 {} !=
      Native.Columns.remapPortable positions support 0 3 {} then return false
  return true

/-- Compare all layouts with a separate hash-map oracle, retain exact full-run
charges under smaller limits and test both sides of packed allocation bounds. -/
def checks (seed : Nat) : Bool := Id.run do
  let table := ({ arity := 1 } : MonomialTable).internOwned #[0] 1000 10000 10000
  for initialTable in [({ arity := 0 } : MonomialTable),table.table] do
    for columns in [#[],#[0],#[0,1,2],#[4,1,4,0],#[7],#[8],#[4294967295],
        #[100,300,500,100],(Array.range 300).map (fun i => i*997),
        #[2^80],(Array.range 257).map fun i => (i * 17 + seed) % 257] do
      let mut expected : Std.HashMap Nat Nat := {}
      for i in [:columns.size] do expected := expected.insert columns[i]! i
      let workspace : Workspace := { table := initialTable }
      let (.ok expectedMap,full) := (ColumnMap.build { work := 100000,packedBytes := 100000 } columns).run workspace
        | return false
      for work in [0,1,2,3,10,100,1000,10000,full.statistics.work-1,full.statistics.work,full.statistics.work+1] do
        for bytes in [initialTable.bytes,full.statistics.allocatedBytes+initialTable.bytes-1,
            full.statistics.allocatedBytes+initialTable.bytes,100000] do
          if bytes < initialTable.bytes then continue
          let limits : Limits := { work, packedBytes := bytes }
          let (result,state) := (ColumnMap.build limits columns).run workspace
          if state.statistics.work > work || state.statistics.allocatedBytes + state.table.bytes > bytes then
            return false
          let enough := work >= full.statistics.work && bytes >= full.statistics.allocatedBytes+initialTable.bytes
          if result.isOk != enough then return false
          match result with
          | .error (.exhausted .work) => pure ()
          | .error (.exhausted .packedBytes) => pure ()
          | .error _ => return false
          | .ok positions =>
            if state.statistics.work != full.statistics.work ||
                state.statistics.allocatedBytes != full.statistics.allocatedBytes then return false
            for id in [0,1,2,3,4,7,8,257,4294967295,2^80] ++ columns.toList do
              if positions.get? id != expected[id]? || positions.get? id != expectedMap.get? id then return false
  let workspace : Workspace := { table := { arity := 0 } }
  let (.ok (.indexed _ probes),state) := (ColumnMap.build {} #[4294967295]).run workspace | return false
  if probes != 1 || state.statistics.work != 18 || state.statistics.allocatedBytes != 128 then return false
  let (.ok (.packed _),state) := (ColumnMap.build {} #[0,2,1]).run workspace | return false
  if state.statistics.work != 9 || state.statistics.allocatedBytes != 12 then return false
  return true

/-- Bounded index and zero-append providers preserve all aliases and malformed
input behavior, including probe and chunk limits on both sides. -/
def indexChecks (seed : Nat) : Bool := Id.run do
  let workspace : Workspace := { table := { arity := 0 } }
  for columns in [#[8],#[4294967295],#[100,300,500,100],
      (Array.range 5001).map fun i => i*997+seed%997] do
    let (.ok positions,_) := (ColumnMap.build { work := 1000000,packedBytes := 1000000 } columns).run workspace
      | return false
    let .indexed slots probes := positions | return false
    let mut oracle : Std.HashMap Nat Nat := {}
    for i in [:columns.size] do oracle := oracle.insert columns[i]! i
    for id in columns.toList ++ [0,1,4294967295] do
      if positions.get? id != oracle[id]? then return false
    let expected := buffer columns.size (fun i => (oracle.getD columns[i]! 0).toUInt64)
    let support := buffer columns.size (fun i => columns[i]!.toUInt64)
    if positions.encode support true != some expected || positions.encode support false != some expected then
      return false
    for start in [0,1,columns.size,columns.size+1,2^80] do
      for count in [0,1,4095,4096,4097,2^80] do
        for q in [0,probes,64,65,2^80] do
          for initialOutput in [ByteArray.empty,slots,support] do
            let expected := Native.Columns.remapIndexPortable (copy slots) (copy support) start count q (copy initialOutput)
            if Native.Columns.remapIndex slots support start count q initialOutput != expected then return false
    for broken in [ByteArray.empty,slots.push 0,buffer 6 (fun _ => 0),buffer 32 (fun _ => 0)] do
      if Native.Columns.remapIndex broken support 0 1 64 {} !=
          Native.Columns.remapIndexPortable (copy broken) (copy support) 0 1 64 {} then return false
  for output in [ByteArray.empty,buffer 13 (fun i => (i+seed).toUInt64)] do
    for count in [0,1,4095,4096,4097,2^80] do
      if Native.Columns.zeros output count != Native.Columns.zerosPortable (copy output) count then return false
  return true

/-- Exact collisions reach the 64-probe cap; the next colliding insertion
retains the full charged attempt and builds the lawful hash-map fallback. -/
def collisionChecks : Bool := Id.run do
  let colliders : Array Nat := #[143,582,861,1164,1462,1586,1941,1997,2090,2328,2752,3429,3664,4296,4373,4631,4739,5136,5546,5571,5590,5748,5918,6261,6314,6462,6479,6711,6725,6914,7391,7408,7521,7552,7949,8238,8592,8957,9161,9279,9306,9341,9478,9584,9987,10456,10702,10770,11035,11231,11269,11350,11477,11496,11836,11949,11979,12275,12389,13067,13201,13255,13291,13412,13726]
  let workspace : Workspace := { table := { arity := 0 } }
  for native in [false,true] do
    let limits : Limits := { work := 10000,packedBytes := 10000,nativeRows := native }
    let first := colliders.extract 0 64
    let (.ok (.indexed slots probes),state) := (ColumnMap.build limits first).run workspace | return false
    if probes != 64 || state.statistics.work != 2272 || state.statistics.allocatedBytes != 1024 then
      return false
    let support := buffer 64 (fun i => first[i]!.toUInt64)
    let expected := buffer 64 (fun i => i.toUInt64)
    if Native.Columns.remapIndex slots support 0 64 64 {} != some expected then return false
    if Native.Columns.remapIndex slots (buffer 1 (fun _ => colliders[64]!.toUInt64)) 0 1 64 {} != none then
      return false
    for (ids,n,capacity,attempt,complete) in [(first,64,128,2272,2272),(colliders,65,256,2465,2530)] do
      let payload := capacity*8
      for work in [0,n-1,n,n+capacity-1,n+capacity,n+capacity+1,n+capacity+2,
          attempt-2,attempt-1,attempt,attempt+1,complete-1,complete,complete+1] do
        for bytes in [0,payload-1,payload,payload+1] do
          let (result,state) := (ColumnMap.build { limits with work,packedBytes := bytes } ids).run workspace
          let charged := if work < n then 0 else if work < n+capacity then n else
            if bytes < payload then n+capacity else if work < complete then min work attempt else complete
          let allocated := if work >= n+capacity && bytes >= payload then payload else 0
          if state.statistics.work != charged || state.statistics.allocatedBytes != allocated then return false
          if result.isOk != (work >= complete && bytes >= payload) then return false
    let (.ok (.hashed positions),state) := (ColumnMap.build limits colliders).run workspace | return false
    if state.statistics.work != 2530 || state.statistics.allocatedBytes != 2048 then return false
    for i in [:colliders.size] do
      if positions[colliders[i]!]? != some i then return false
  return true

#guard checks 0
#guard remapChecks 0
#guard indexChecks 0
#guard collisionChecks

end Hex.Groebner.ColumnMapConformance
