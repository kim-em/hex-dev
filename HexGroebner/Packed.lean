/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Field
public import HexArith.Barrett.Context

public section

/-! Packed scalar storage for finite-field Macaulay matrices. Byte order is
explicitly little endian, independent of the host. These buffers carry raw
data; matrix entry points validate their lengths and contents before use. -/

namespace Hex.Groebner

/-- Canonical residue storage, selected from the modulus rather than row values. -/
inductive Width where
  | u8 | u16 | u32
  deriving BEq, Repr, Inhabited

/-- Number of bytes in each encoded scalar. -/
@[expose] def Width.bytes : Width → Nat
  | .u8 => 1
  | .u16 => 2
  | .u32 => 4

/-- Finite prime-field metadata, with actual prime evidence. This is an encoding
context for the existing `ZMod64` field, not another field hierarchy. -/
structure PrimeField where
  modulus : UInt64
  prime : Hex.Nat.Prime modulus.toNat
  bound : modulus.toNat < 2 ^ 31

/-- Construct metadata from the existing lawful residue field. -/
@[expose] def PrimeField.ofZMod64 (p : Nat) [ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] : PrimeField where
  modulus := UInt64.ofNat p
  prime := by
    simpa only [UInt64.toNat_ofNat_of_lt' (ZMod64.Bounds.pLtWord p)] using
      ZMod64.PrimeModulus.prime (p := p)
  bound := by
    simpa only [UInt64.toNat_ofNat_of_lt' (ZMod64.Bounds.pLtWord p)] using
      ZMod64.Bounds.pLtR (p := p)

/-- Smallest fixed scalar width holding every residue of the field. -/
@[expose] def PrimeField.width (field : PrimeField) : Width :=
  if field.modulus ≤ 256 then .u8 else if field.modulus ≤ 65536 then .u16 else .u32

/-- Hoist the reciprocal out of all coefficient loops. -/
@[expose] def PrimeField.barrett (field : PrimeField) : BarrettCtx field.modulus :=
  BarrettCtx.mk field.modulus (by have := field.prime.two_le; omega)
    (Nat.lt_trans field.bound (by decide))

namespace Packed

/-- Read a scalar at an element index. Matrix validation establishes the byte
range before this operation is used in a hot loop. -/
@[expose] def read (width : Width) (data : @& ByteArray) (index : Nat) : UInt64 :=
  let offset := index * width.bytes
  let a := data[offset]!.toUInt64
  match width with
  | .u8 => a
  | .u16 => a ||| (data[offset + 1]!.toUInt64 <<< 8)
  | .u32 => a ||| (data[offset + 1]!.toUInt64 <<< 8) |||
      (data[offset + 2]!.toUInt64 <<< 16) ||| (data[offset + 3]!.toUInt64 <<< 24)

/-- Append the low bytes of a scalar. Callers validate its range before packing. -/
@[expose] def push (width : Width) (data : ByteArray) (value : UInt64) : ByteArray :=
  let data := data.push value.toUInt8
  match width with
  | .u8 => data
  | .u16 => data.push (value >>> 8).toUInt8
  | .u32 => ((data.push (value >>> 8).toUInt8).push (value >>> 16).toUInt8).push
      (value >>> 24).toUInt8

/-- Replace a scalar in a uniquely owned workspace. -/
@[expose] def set (width : Width) (data : ByteArray) (index : Nat)
    (value : UInt64) : ByteArray :=
  let offset := index * width.bytes
  let data := data.set! offset value.toUInt8
  match width with
  | .u8 => data
  | .u16 => data.set! (offset + 1) (value >>> 8).toUInt8
  | .u32 => ((data.set! (offset + 1) (value >>> 8).toUInt8).set!
      (offset + 2) (value >>> 16).toUInt8).set! (offset + 3) (value >>> 24).toUInt8

end Packed

/-- Sparse row in a fixed column map. Columns are increasing unsigned 32-bit
indices; coefficients have the width selected by the field. Empty rows encode
zero. Raw construction is allowed; elimination always validates it. -/
structure SparseRow where
  columns : ByteArray := ByteArray.empty
  coefficients : ByteArray := ByteArray.empty
  deriving Inhabited, Hashable

/-- Number of stored entries (exact once raw row lengths have been validated). -/
@[expose] def SparseRow.size (row : SparseRow) : Nat := row.columns.size / 4

/-- Checked interchange constructor. Rejects zeros, noncanonical residues,
unsorted/duplicate columns and indices outside the admitted 32-bit map. -/
@[expose] def SparseRow.ofEntries (field : PrimeField) (columnCount : Nat)
    (entries : Array (Nat × UInt64)) : Option SparseRow := Id.run do
  if columnCount ≥ 2 ^ 32 then return none
  if entries.size * (4 + field.width.bytes) ≥ USize.size then return none
  let mut row : SparseRow := {}
  let mut previous : Option Nat := none
  for (column, coefficient) in entries do
    if column ≥ columnCount || coefficient == 0 || coefficient ≥ field.modulus then
      return none
    if let some p := previous then
      if column ≤ p then return none
    row := {
      columns := Packed.push .u32 row.columns column.toUInt64
      coefficients := Packed.push field.width row.coefficients coefficient }
    previous := some column
  return some row

/-- Decode a row for interchange, diagnostics and independent tests. -/
@[expose] def SparseRow.entries (field : PrimeField) (row : SparseRow) : Array (Nat × UInt64) :=
  (Array.range row.size).map fun i =>
    ((Packed.read .u32 row.columns i).toNat, Packed.read field.width row.coefficients i)

end Hex.Groebner
