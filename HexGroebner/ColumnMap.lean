/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Runtime

public section

namespace Hex.Groebner

/-- A matrix column map. Dense identifier intervals use packed u32 positions
plus one; sparse u32 IDs use exact packed hashing, with a hash-map fallback
for excessive collision chains or unsupported geometry. Zero denotes absence. -/
inductive ColumnMap where
  | packed (positions : ByteArray)
  | indexed (slots : ByteArray) (probes : Nat)
  | hashed (positions : Std.HashMap Nat Nat)

namespace ColumnMap

@[inline] def get? (positions : @& ColumnMap) (id : Nat) : Option Nat :=
  match positions with
  | .indexed slots probes => Native.Columns.lookup slots probes id
  | .hashed positions => positions[id]?
  | .packed positions =>
    if id >= positions.size / 4 then none else
    let value := (Packed.read .u32 positions id).toNat
    if value == 0 then none else some (value - 1)

@[inline] def getD (positions : @& ColumnMap) (id fallback : Nat) : Nat :=
  (positions.get? id).getD fallback

/-- Maximum per-key probe count. Rows charge per key; each sort comparison
charges two such lookups. -/
@[inline] def lookupCost : ColumnMap → Nat
  | .indexed _ probes => max 1 probes
  | _ => 1

/-- Encode a polynomial support in the fixed matrix columns. Packed maps use
bounded native direct or exact hash slices; the scalar and hash-map routes preserve the same
missing-ID behavior and ignore unused trailing support bytes. -/
def encode (positions : @& ColumnMap) (support : @& ByteArray) (native : Bool) :
    Option ByteArray := Id.run do
  let mut output := ByteArray.emptyWithCapacity support.size
  match positions with
  | .indexed slots probes =>
    let count := support.size / 4
    for chunk in [:(count + 4095) / 4096] do
      let start := chunk * 4096
      let size := min 4096 (count - start)
      let result := if native then Native.Columns.remapIndex slots support start size probes output
        else Native.Columns.remapIndexPortable slots support start size probes output
      let some next := result | return none
      output := next
  | .packed positions =>
    let count := support.size / 4
    for chunk in [:(count + 4095) / 4096] do
      let start := chunk * 4096
      let size := min 4096 (count - start)
      let result := if native then Native.Columns.remap positions support start size output
        else Native.Columns.remapPortable positions support start size output
      let some next := result | return none
      output := next
  | .hashed positions =>
    for i in [:support.size / 4] do
      let id := (Packed.read .u32 support i).toNat
      let some column := positions[id]? | return none
      if column >= 4294967296 then return none
      output := Packed.push .u32 output column.toUInt64
  return some output

-- Callers have charged payload and ensured size < USize.size; a provider
-- rejection here would violate the bounded slice/addressability invariant.
private def zeros (size : Nat) (native : Bool) : Computation ByteArray := do
  let mut out := ByteArray.emptyWithCapacity size
  for start in [:((size+4095)/4096)] do
    let count := min 4096 (size-start*4096)
    let some next := if native then Native.Columns.zeros out count
      else Native.Columns.zerosPortable out count | throw (.representation .address)
    out := next
  return out

private def buildHash (limits : Limits) (columns : Array Nat) : Computation ColumnMap := do
  Computation.spend limits columns.size
  let mut positions : Std.HashMap Nat Nat := {}
  for i in [:columns.size] do positions := positions.insert columns[i]! i
  return .hashed positions

private def index (limits : Limits) (columns : Array Nat) : Computation ColumnMap := do
  let capacity := max 16 (2*columns.size).nextPowerOfTwo
  if capacity*8 >= USize.size then return ← buildHash limits columns
  Computation.spend limits capacity
  Computation.allocate limits (capacity*8)
  let mut slots ← zeros (capacity*8) limits.nativeRows
  let mut probes := 0
  for i in [:columns.size] do
    let id := columns[i]!
    let mut bucket := Native.Columns.slot id.toUInt64 capacity
    let mut inserted := false
    for probe in [:64] do
      Computation.spend limits 1
      let value := Packed.read .u32 slots (bucket*2+1)
      if value == 0 || Packed.read .u32 slots (bucket*2) == id.toUInt64 then
        slots := Packed.set .u32 slots (bucket*2) id.toUInt64
        slots := Packed.set .u32 slots (bucket*2+1) (i+1).toUInt64
        probes := max probes (probe+1)
        inserted := true
        break
      bucket := (bucket+1) &&& (capacity-1)
    if !inserted then return ← buildHash limits columns
  return .indexed slots probes

/-- Build a column map with at most eight packed slots per column. Geometry
alone selects the layout; initialization and packed payload are charged before
allocation. Increasing an allowance cannot change the chosen layout or charges. Layout
and counters can differ between 32-bit and 64-bit address widths.
Indexed maps charge bucket initialization and every attempted insertion probe.
Chains longer than 64 retain the charged attempt and build the hash-map fallback;
addressability and non-u32 IDs also retain that route. Row construction charges
the maximum recorded probe count per entry; this conservative allowance may
exhaust sooner than a unit-cost hash-map computation. Repeated identifiers keep
the final position, as for `HashMap.insert`. -/
def build (limits : Limits) (columns : Array Nat) : Computation ColumnMap := do
  Computation.spend limits columns.size
  let count := columns.foldl (fun count id => max count (id + 1)) 0
  if columns.size < 4294967296 && count <= columns.size * 8 && count * 4 < USize.size then
    Computation.spend limits (count + columns.size)
    Computation.allocate limits (count * 4)
    let mut positions ← zeros (count*4) limits.nativeRows
    for i in [:columns.size] do
      positions := Packed.set .u32 positions columns[i]! (i + 1).toUInt64
    return .packed positions
  else if columns.size < 4294967296 && count <= 4294967296 then
    index limits columns
  else buildHash limits columns

end ColumnMap
end Hex.Groebner
