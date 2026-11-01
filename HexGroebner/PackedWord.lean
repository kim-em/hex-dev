/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Packed

public section

namespace Hex.Groebner.Packed

/-- Read an eight-byte little-endian word at a byte offset. Callers validate
its range, as for `Packed.read`. The kernel retains these byte reads. -/
@[expose] def read64 (bytes : @& ByteArray) (offset : Nat) : UInt64 :=
  let low := bytes[offset]!.toUInt64 ||| (bytes[offset+1]!.toUInt64 <<< 8) |||
    (bytes[offset+2]!.toUInt64 <<< 16) ||| (bytes[offset+3]!.toUInt64 <<< 24)
  let high := bytes[offset+4]!.toUInt64 ||| (bytes[offset+5]!.toUInt64 <<< 8) |||
    (bytes[offset+6]!.toUInt64 <<< 16) ||| (bytes[offset+7]!.toUInt64 <<< 24)
  low ||| (high <<< 32)

private theorem offset_eq (base step : Nat) (h : base + step < USize.size) :
    (USize.ofNat base + USize.ofNat step).toNat = base + step := by
  rw [USize.toNat_add,
    USize.toNat_ofNat_of_lt' (by omega : base < USize.size),
    USize.toNat_ofNat_of_lt' (by omega : step < USize.size)]
  exact Nat.mod_eq_of_lt h

/-- Checked unboxed implementation, selected through the proved compiler rewrite. -/
@[expose] def read64Fast (bytes : @& ByteArray) (offset : Nat) : UInt64 :=
  if h : offset + 8 ≤ bytes.size ∧ offset + 8 ≤ USize.size then
    let pos := USize.ofNat offset
    have boundAt (i : Nat) (hi : i < 8) : (pos + USize.ofNat i).toNat < bytes.size := by
      dsimp only [pos]
      rw [offset_eq _ _ (by omega)]
      omega
    let low := (bytes.uget (pos + USize.ofNat 0) (boundAt 0 (by decide))).toUInt64 |||
      ((bytes.uget (pos + USize.ofNat 1) (boundAt 1 (by decide))).toUInt64 <<< 8) |||
      ((bytes.uget (pos + USize.ofNat 2) (boundAt 2 (by decide))).toUInt64 <<< 16) |||
      ((bytes.uget (pos + USize.ofNat 3) (boundAt 3 (by decide))).toUInt64 <<< 24)
    let high := (bytes.uget (pos + USize.ofNat 4) (boundAt 4 (by decide))).toUInt64 |||
      ((bytes.uget (pos + USize.ofNat 5) (boundAt 5 (by decide))).toUInt64 <<< 8) |||
      ((bytes.uget (pos + USize.ofNat 6) (boundAt 6 (by decide))).toUInt64 <<< 16) |||
      ((bytes.uget (pos + USize.ofNat 7) (boundAt 7 (by decide))).toUInt64 <<< 24)
    low ||| (high <<< 32)
  else
    let low := bytes[offset]!.toUInt64 ||| (bytes[offset+1]!.toUInt64 <<< 8) |||
      (bytes[offset+2]!.toUInt64 <<< 16) ||| (bytes[offset+3]!.toUInt64 <<< 24)
    let high := bytes[offset+4]!.toUInt64 ||| (bytes[offset+5]!.toUInt64 <<< 8) |||
      (bytes[offset+6]!.toUInt64 <<< 16) ||| (bytes[offset+7]!.toUInt64 <<< 24)
    low ||| (high <<< 32)

private theorem read64Fast_model (bytes : ByteArray) (offset : Nat) :
    read64Fast bytes offset = read64 bytes offset := by
  cases bytes with
  | mk data =>
    unfold read64Fast
    dsimp only
    split
    · rename_i h
      simp only [ByteArray.size] at h
      have index_eq (i : Nat) (hi : i < 8) :
          (USize.ofNat (offset)+USize.ofNat i).toNat = offset + i :=
        offset_eq _ _ (by omega)
      simp (disch := (simp only [ByteArray.size] <;> omega)) only [read64,ByteArray.uget,
        Array.ugetElem_eq_getElem,ByteArray.size,ByteArray.getElem_eq_getElem_data,
        Nat.add_zero,
        index_eq 0 (by decide),index_eq 1 (by decide),index_eq 2 (by decide),index_eq 3 (by decide),
        index_eq 4 (by decide),index_eq 5 (by decide),index_eq 6 (by decide),index_eq 7 (by decide),
        getElem!_pos]
    · rfl

/-- Compile the reference to the proved-equivalent implementation with one
range check and unboxed indices. The kernel retains the reference definition. -/
@[csimp] theorem read64_eq : read64 = read64Fast := by
  funext bytes offset
  exact (read64Fast_model bytes offset).symm

/-- Agreement with the two adjacent packed 32-bit reads used by metadata. -/
theorem read64_eq_read32 (bytes : ByteArray) (index : Nat) :
    read64 bytes (index*4) =
      read .u32 bytes index ||| (read .u32 bytes (index+1) <<< 32) := by
  simp only [read64,read,Width.bytes,Nat.add_mul,Nat.one_mul,
    Nat.add_assoc,Nat.reduceAdd]

/-- info: 'Hex.Groebner.Packed.read64_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms read64_eq

end Hex.Groebner.Packed
