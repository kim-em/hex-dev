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
  if (Native.subtract 257 (encode .u8 #[1, 2, 3]) columns (encode .u16 #[1, 1]) 0 2 1).isSome then return false
  if (Native.subtract 7 dense columns coefficients 0 (2 ^ 100) 1).isSome then return false
  let invalidColumns := encode .u32 #[0, 4294967295]
  if (Native.subtract 7 dense invalidColumns coefficients 0 2 1).isSome then return false
  if !check 7 dense invalidColumns coefficients 0 2 1 then return false
  let rejected := Native.subtract 7 dense invalidColumns coefficients 0 2 1
  if rejected.isSome || dense.data != #[1, 2] then return false
  if (Native.subtract 7 dense columns (encode .u8 #[1, 7]) 0 2 1).isSome then return false
  if !check 7 (encode .u8 #[1, 7]) columns coefficients 0 2 1 then return false
  -- Unaccessed malformed residues are irrelevant to a zero-length slice.
  if !equal (Native.subtract 7 dense columns (encode .u8 #[7, 7]) 2 0 1) (some dense) then return false
  let longColumns := encode .u32 (Array.replicate 4097 0)
  let longCoefficients := encode .u8 (Array.replicate 4097 1)
  if (Native.subtract 2 (encode .u8 #[0]) longColumns longCoefficients 0 4097 1).isSome then return false
  let longDense := encode .u8 #[0]
  let rejected := Native.subtract 2 longDense longColumns longCoefficients 0 4097 1
  if rejected.isSome || longDense.data != #[0] then return false
  if !check 2 (encode .u8 #[0]) longColumns longCoefficients 0 4096 1 then return false
  return true

#guard malformed

-- Kernel reduction uses the portable body of the extern.
theorem row_example : (Native.subtract 7 (ByteArray.mk #[5])
    (ByteArray.mk #[0, 0, 0, 0]) (ByteArray.mk #[3]) 0 1 2).map (fun b => b[0]!.toNat) =
    some 6 := by decide

/-- info: 'Hex.Groebner.NativeConformance.row_example' does not depend on any axioms -/
#guard_msgs in #print axioms row_example

private def monomials : Bool := Id.run do
  for width in [Width.u8, .u16, .u32] do
    for arity in [1, 2, 3, 10, 65] do
      for seed in [:32] do
        let values := (Array.range (arity * 3)).map fun i =>
          ((i * 7919 + seed * 65537).toUInt64 % (if width == .u8 then 256 else if width == .u16 then 65536 else 4294967296))
        let source := encode width values
        for operation in ([0, 1, 2] : List UInt8) do
          let workspace := encode .u8 (Array.replicate (4 * arity + 28) 91)
          let expected := Native.Monomial.preparePortable operation width.bytes.toUInt8
            arity.toUInt64 3 (seed % 3).toUInt64 ((seed + 1) % 3).toUInt64 source workspace
          let actual := Native.Monomial.prepare operation width.bytes.toUInt8
            arity.toUInt64 3 (seed % 3).toUInt64 ((seed + 1) % 3).toUInt64 source workspace
          if !equal actual expected || workspace.data != Array.replicate (4 * arity + 28) 91 then return false
          if let some candidate := actual then
            for id in [:3] do
              if Native.Monomial.equal width.bytes.toUInt8 arity.toUInt64 id.toUInt64 source candidate !=
                  Native.Monomial.equalPortable width.bytes.toUInt8 arity.toUInt64 id.toUInt64 source candidate then
                return false
        let workspace := encode .u8 (Array.replicate (4 * arity + 28) 0)
        let some candidate := Native.Monomial.prepare 0 width.bytes.toUInt8 arity.toUInt64 3 0 0 source workspace
          | return false
        if !Native.Monomial.equal width.bytes.toUInt8 arity.toUInt64 0 source candidate then return false
        if source.data != (encode width values).data then return false
  return true

#guard monomials

private def aliasMonomial (native : Bool) (width : Width) (seed : Nat) : Option ByteArray :=
  let count := 8 / width.bytes
  let source := encode width ((Array.range (7 * count)).map fun i => (seed + i).toUInt64)
  -- No owner of source survives the call; the borrowed source aliases the
  -- consumed workspace, including bytes needed by later coordinates.
  if native then Native.Monomial.prepare 1 width.bytes.toUInt8 7 count.toUInt64 0 1 source source
  else Native.Monomial.preparePortable 1 width.bytes.toUInt8 7 count.toUInt64 0 1 source source

#guard [Width.u8, .u16].all fun width => (List.range 31).all fun seed =>
  [false, true].all fun native =>
    match aliasMonomial native width seed with
    | none => false
    | some result => (Array.range 7).all fun i =>
      Native.read result 4 (i * 4) == 2 * seed + 7 + 2 * i

private def monomialBounds : Bool := Id.run do
  let source := encode .u32 #[4294967295, 1, 0, 0, 0, 0, 0, 0]
  let copy := source.data
  -- Exact aliasing must preserve borrowed source bytes on success and failure.
  if !equal (Native.Monomial.prepare 0 4 1 8 0 1 source source)
      (Native.Monomial.preparePortable 0 4 1 8 0 1 source source) then return false
  if (Native.Monomial.prepare 1 4 1 8 0 1 source source).isSome || source.data != copy then return false
  let overflowSource := encode .u32 #[1, 4294967295, 2, 1]
  let shared := encode .u8 (Array.replicate 36 19)
  if (Native.Monomial.prepare 1 4 2 2 0 1 overflowSource shared).isSome ||
      shared.data != Array.replicate 36 19 then return false
  let workspace := encode .u8 (Array.replicate 32 0)
  for width in ([0, 3, 8] : List UInt8) do
    if (Native.Monomial.prepare 0 width 1 8 0 1 source workspace).isSome then return false
  for operation in ([3, 255] : List UInt8) do
    if (Native.Monomial.prepare operation 4 1 8 0 1 source workspace).isSome then return false
  for arity in ([0, 4097, 18446744073709551615] : List UInt64) do
    if (Native.Monomial.prepare 0 4 arity 8 0 1 source workspace).isSome then return false
  if (Native.Monomial.prepare 0 4 1 8 8 0 source workspace).isSome then return false
  if (Native.Monomial.prepare 0 4 1 8 0 8 source workspace).isSome then return false
  if (Native.Monomial.prepare 0 4 1 18446744073709551615 0 0 source workspace).isSome then return false
  if (Native.Monomial.prepare 0 4 1 8 0 1 (source.push 0) workspace).isSome then return false
  if (Native.Monomial.prepare 0 4 1 8 0 1 source (workspace.push 0)).isSome then return false
  for arity in [1, 65, 4096] do
    let source := encode .u32 (Array.replicate (arity * 2) 4294967295)
    let workspace := encode .u8 (Array.replicate (arity * 4 + 28) 0)
    let expected := Native.Monomial.preparePortable 0 4 arity.toUInt64 2 0 1 source workspace
    let actual := Native.Monomial.prepare 0 4 arity.toUInt64 2 0 1 source workspace
    if !equal actual expected then return false
    let some candidate := actual | return false
    if !Native.Monomial.equal 4 arity.toUInt64 0 source candidate then return false
    if Native.Monomial.equal 4 arity.toUInt64 2 source candidate then return false
    if Native.Monomial.equal 4 arity.toUInt64 18446744073709551615 source candidate then return false
    if Native.Monomial.equal 4 arity.toUInt64 0 (source.push 0) candidate then return false
    if Native.Monomial.equal 4 arity.toUInt64 0 source (candidate.push 0) then return false
  return true

#guard monomialBounds

/-- Literal packed monomial preparation reduces using the ordinary kernel body. -/
theorem monomial_example : (Native.Monomial.prepare 1 1 2 2 0 1
    (ByteArray.mk #[2, 3, 4, 5]) (ByteArray.mk (Array.replicate 36 0))).map
      (fun b => [Native.read b 4 0, Native.read b 4 4, Native.read b 8 8,
        Native.read b 8 16, Native.read b 8 24, Native.read b 4 32]) =
    some [6, 8, 14, 3, 588762121494699011, 8] := by decide

/-- info: 'Hex.Groebner.NativeConformance.monomial_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms monomial_example

end Hex.Groebner.NativeConformance
