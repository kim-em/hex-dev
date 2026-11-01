/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.PackedWord

public section

namespace Hex.Groebner

/-- Packed hash buckets and collision links. Entries are stable identifiers plus
one; zero ends a chain. Hashes are filters, never an equality witness. -/
structure MonomialIndex where
  heads : ByteArray := {}
  links : ByteArray := {}

namespace MonomialIndex

@[inline] def capacity (index : @& MonomialIndex) : Nat := index.heads.size / 4

@[inline] def bytes (index : @& MonomialIndex) : Nat := index.heads.size + index.links.size

/-- The inexpensive structural invariant; links are checked when traversed. -/
def shape (index : @& MonomialIndex) (count : Nat) : Bool :=
  index.heads.size % 4 == 0 && index.links.size == count * 4 &&
    (if count == 0 then index.capacity == 0 else
      index.capacity ≥ count * 2 && index.capacity &&& (index.capacity - 1) == 0)

private def mix (hash : UInt64) : UInt64 :=
  let h := (hash ^^^ (hash >>> 30)) * 0xbf58476d1ce4e5b9
  let h := (h ^^^ (h >>> 27)) * 0x94d049bb133111eb
  h ^^^ (h >>> 31)

@[inline] private def slot (hash : UInt64) (capacity : Nat) : Nat :=
  (mix hash &&& (capacity - 1).toUInt64).toNat

@[inline] def head (index : @& MonomialIndex) (hash : UInt64) : Nat :=
  if index.capacity == 0 then 0 else
    (Packed.read .u32 index.heads (slot hash index.capacity)).toNat

@[inline] def next (index : @& MonomialIndex) (id : Nat) : Nat :=
  (Packed.read .u32 index.links id).toNat

private def setHead (heads : ByteArray) (hash : UInt64) (id : Nat) : ByteArray := Id.run do
  let offset := 4 * slot hash (heads.size / 4)
  let value := (id + 1).toUInt64
  let mut heads := heads
  for k in [:4] do
    heads := heads.set! (offset + k) ((value >>> (8*k).toUInt64).toUInt8)
  return heads

/-- Capacity and charged payload required after one insertion. -/
def grownCapacity (index : @& MonomialIndex) (count : Nat) : Nat :=
  if count + 1 > index.capacity / 2 then max 16 (index.capacity * 2) else index.capacity

/-- Peak index payload, including the old index while rebuilding. -/
def peak (index : @& MonomialIndex) (count : Nat) : Nat :=
  let capacity := index.grownCapacity count
  4 * capacity + 4 * (count + 1) + if capacity != index.capacity then index.bytes else 0

/-- Charge initialization, rehashing and packed-link insertion before mutation. -/
def work (index : @& MonomialIndex) (count : Nat) : Nat :=
  let capacity := index.grownCapacity count
  (if capacity != index.capacity then capacity + count * 3 else 0) + 2

/-- Insert a new stable identifier. The metadata hash accessor refers to the
old arena; rebuilding visits identifiers in increasing order, deterministically. -/
@[specialize] def insert (index : MonomialIndex) (count : Nat) (hash : UInt64)
    (hashAt : Nat → UInt64) : MonomialIndex := Id.run do
  let capacity := index.grownCapacity count
  let mut index := index
  if capacity != index.capacity then
    let mut heads := ByteArray.emptyWithCapacity (capacity * 4)
    for _ in [:capacity * 4] do heads := heads.push 0
    let mut rebuilt : MonomialIndex := ⟨heads, ByteArray.emptyWithCapacity (count * 4)⟩
    for id in [:count] do
      let hash := hashAt id
      let head := rebuilt.head hash
      let ⟨bucketHeads, chainLinks⟩ := rebuilt
      rebuilt := ⟨setHead bucketHeads hash id, Packed.push .u32 chainLinks head.toUInt64⟩
    index := rebuilt
  let head := index.head hash
  let ⟨heads, links⟩ := index
  return ⟨setHead heads hash count, Packed.push .u32 links head.toUInt64⟩

end MonomialIndex
end Hex.Groebner
