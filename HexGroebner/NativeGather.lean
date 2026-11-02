/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Native

@[expose] public section

namespace Hex.Groebner.Native.Gather

/-- Layout mirrored in C (`matrix_scan.c`, `matrix_scan_impl.h`,
`matrix_eliminate.c`). -/
structure State where
  dense : ByteArray
  columns : ByteArray
  coefficients : ByteArray
  cursor : Nat

/-- Status: 0 quantum ended, 1 complete, 2 entries exhausted, 3 bytes exhausted,
4 work exhausted, 5 geometry/addressability, 6 noncanonical data. Work counts
normalization products; the caller separately charges the whole scan interval.
Layout mirrored in C (`matrix_scan.c`, `matrix_eliminate.c`). -/
structure Result where
  state : State
  entries : Nat := 0
  bytes : Nat := 0
  work : Nat := 0
  status : UInt8 := 0

def push (width : Nat) (bytes : ByteArray) (value : Nat) : ByteArray :=
  match width with
  | 0 => bytes
  | n+1 => push n (bytes.push value.toUInt8) (value/256)

/-- Append scaled nonzero accumulator entries in column order, clearing their
source slots. Calls inspect at most 4096 columns and preserve all charged prefix
counters on a failure. Arrays are owned and may alias at entry. -/
def portable (modulus : UInt64) (initial : State) (stop quantum entriesLimit bytesLimit workLimit : Nat)
    (factor : UInt64) : Result := Id.run do
  let p := modulus.toNat
  let w := Native.width p
  let size := initial.dense.size/w
  let count := initial.columns.size/4
  let mut out : Result := { state := initial }
  if p < 2 || p ≥ 2147483648 || factor == 0 || factor.toNat ≥ p || quantum > 4096 ||
      initial.dense.size%w != 0 || size > 4294967295 || initial.cursor > stop || stop > size ||
      initial.columns.size%4 != 0 || initial.coefficients.size != count*w then
    return { out with status := 5 }
  for _ in [:quantum] do
    let s := out.state
    if s.cursor ≥ stop then return { out with status := 1 }
    let a := Native.read s.dense w (s.cursor*w)
    if a ≥ p then return { out with status := 6 }
    if a != 0 then
      if s.columns.size > 0 && Native.read s.columns 4 (s.columns.size-4) ≥ s.cursor then
        return { out with status := 6 }
      if out.entries ≥ entriesLimit then return { out with status := 2 }
      out := { out with entries := out.entries+1 }
      if out.bytes+4+w > bytesLimit then return { out with status := 3 }
      out := { out with bytes := out.bytes+4+w }
      if s.columns.size+4 ≥ USize.size || s.coefficients.size+w ≥ USize.size then
        return { out with status := 5 }
      if factor != 1 then
        if out.work ≥ workLimit then return { out with status := 4 }
        out := { out with work := out.work+1 }
      let value := a*factor.toNat%p
      out := { out with state := ⟨Native.write s.dense w (s.cursor*w) 0,
        push 4 s.columns s.cursor,push w s.coefficients value,s.cursor+1⟩ }
    else out := { out with state := { s with cursor := s.cursor+1 } }
  return out

@[extern "lean_hex_gather"]
def gather (modulus : UInt64) (initial : State)
    (stop quantum entriesLimit bytesLimit workLimit : @& Nat) (factor : UInt64) : Result :=
  portable modulus initial stop quantum entriesLimit bytesLimit workLimit factor

end Hex.Groebner.Native.Gather
