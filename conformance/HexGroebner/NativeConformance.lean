/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Native
import HexGroebner.Packed

/-!
Oracle: none (core); native results are compared with the portable Lean body.
Mode: always.
Covered operations: bounded modular sparse updates over packed row buffers.
Covered properties: exact residue arithmetic, slice bounds, ownership and
stable original reads when buffers alias.
Covered edge cases: 1/2/4-byte coefficients, maximal supported modulus, zero
slices, repeated columns, malformed buffers and rejection after partial work.
-/

namespace Hex.Groebner.NativeConformance

private def equal (a b : Option ByteArray) : Bool :=
  match a, b with
  | none, none => true
  | some a, some b => a.data == b.data
  | _, _ => false

private def encode (width : Width) (values : Array UInt64) : ByteArray :=
  values.foldl (Packed.push width) {}

private def check (p : UInt64) (dense columns coefficients : ByteArray)
    (start count : Nat) (factor : UInt64) : Bool :=
  -- Holding the original dense input for the portable call exercises copying.
  equal (Native.subtract p dense columns coefficients start count factor)
    (Native.subtractPortable p dense columns coefficients start count factor)

private def campaign : Bool := Id.run do
  for p in (#[2, 3, 251, 256, 257, 65521, 65536, 65537, 2147483647] : Array UInt64) do
    let width := if p ≤ 256 then Width.u8 else if p ≤ 65536 then .u16 else .u32
    for seed in [:70] do
      let mut dense := ByteArray.empty
      let mut columns := ByteArray.empty
      let mut coefficients := ByteArray.empty
      for i in [:37] do
        dense := Packed.push width dense ((i * 4349 + seed * 101 + 1).toUInt64 % p)
      for i in [:64] do
        columns := Packed.push .u32 columns ((i * 13 + seed) % 37).toUInt64
        coefficients := Packed.push width coefficients ((i * 13579 + seed * 31).toUInt64 % p)
      let start := seed % 65
      let count := min (64 - start) (seed + 1)
      let factor := (seed * 7919).toUInt64 % p
      if !check p dense columns coefficients start count factor then return false
      -- Compute the portable result first so the native update can consume a
      -- uniquely owned dense buffer after the reference result is constructed.
      let expected := Native.subtractPortable p dense columns coefficients 0 64 (p - 1)
      let actual := Native.subtract p dense columns coefficients 0 64 (p - 1)
      if !equal actual expected then return false
  return true

#guard campaign

-- Coefficient reads must observe the original buffer, not earlier updates.
#guard let dense := encode .u32 #[1, 2, 0]
  let columns := encode .u32 #[1, 2, 0]
  equal (Native.subtract 65537 dense columns dense 0 3 1)
    (some (encode .u32 #[1, 1, 65535]))

-- The first destination overlaps bytes of a later column index.
#guard let dense := encode .u32 #[4, 0, 1, 2]
  let coefficients := encode .u8 #[1, 2, 3, 4]
  let expected := encode .u8 #[2, 4, 3, 0, 6, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]
  equal (Native.subtract 7 dense dense coefficients 0 4 1) (some expected)

private def malformed : Bool := Id.run do
  let dense := encode .u8 #[1, 2]
  let columns := encode .u32 #[0, 1]
  let coefficients := encode .u8 #[3, 4]
  for p in (#[0, 1, 2147483648] : Array UInt64) do
    if (Native.subtract p dense columns coefficients 0 2 1).isSome then return false
  if (Native.subtract 7 dense columns coefficients 0 2 7).isSome then return false
  if (Native.subtract 7 dense (columns.push 0) coefficients 0 2 1).isSome then return false
  if (Native.subtract 7 dense columns (coefficients.push 1) 0 2 1).isSome then return false
  if (Native.subtract 257 dense columns coefficients 0 2 1).isSome then return false
  if (Native.subtract 7 dense columns coefficients 3 0 1).isSome then return false
  if (Native.subtract 7 dense columns coefficients 1 2 1).isSome then return false
  if (Native.subtract 7 dense columns coefficients (2 ^ 100) 0 1).isSome then return false
  let invalidColumns := encode .u32 #[0, 4294967295]
  if (Native.subtract 7 dense invalidColumns coefficients 0 2 1).isSome then return false
  if !check 7 dense invalidColumns coefficients 0 2 1 then return false
  if (Native.subtract 7 dense columns (encode .u8 #[1, 7]) 0 2 1).isSome then return false
  if !check 7 (encode .u8 #[1, 7]) columns coefficients 0 2 1 then return false
  -- Unaccessed malformed residues are irrelevant to a zero-length slice.
  if !equal (Native.subtract 7 dense columns (encode .u8 #[7, 7]) 2 0 1) (some dense) then return false
  let longColumns := encode .u32 (Array.replicate 4097 0)
  let longCoefficients := encode .u8 (Array.replicate 4097 1)
  if (Native.subtract 2 (encode .u8 #[0]) longColumns longCoefficients 0 4097 1).isSome then return false
  if !check 2 (encode .u8 #[0]) longColumns longCoefficients 0 4096 1 then return false
  return true

#guard malformed

-- Kernel reduction uses the portable body of the extern.
theorem row_example : (Native.subtract 7 (ByteArray.mk #[5])
    (ByteArray.mk #[0, 0, 0, 0]) (ByteArray.mk #[3]) 0 1 2).map (fun b => b[0]!.toNat) =
    some 6 := by decide

/-- info: 'Hex.Groebner.NativeConformance.row_example' does not depend on any axioms -/
#guard_msgs in #print axioms row_example

end Hex.Groebner.NativeConformance
