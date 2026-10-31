/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public section

/-! Bounded packed modular row updates. This module imports no implementation
library, so its native carrier can resolve the C binding on every platform.
The byte layout and rejection behavior are part of the pure function's contract.
Matrix callers validate entire rows before calling it on chunks of at most
4096 entries; the native provider repeats shape and access checks defensively. -/

namespace Hex.Groebner.Native

/-- Minimal residue width for a modulus in the admitted range. -/
@[expose] def width (modulus : Nat) : Nat :=
  if modulus ≤ 256 then 1 else if modulus ≤ 65536 then 2 else 4

/-- Read a validated little-endian scalar by structural recursion. -/
@[expose] def read (bytes : @& ByteArray) (width offset : Nat) : Nat :=
  match width with
  | 0 => 0
  | n + 1 => bytes[offset]!.toNat + 256 * read bytes n (offset + 1)

/-- Write a validated little-endian scalar into owned storage. -/
@[expose] def write (bytes : ByteArray) (width offset value : Nat) : ByteArray :=
  match width with
  | 0 => bytes
  | n + 1 => write (bytes.set! offset (UInt8.ofNat value)) n (offset + 1) (value / 256)

/-- Structurally recursive logical update. Row reads use the original borrowed
buffers, while dense reads observe all preceding updates. -/
@[expose] def update (modulus factor width : Nat) (columns coefficients : @& ByteArray)
    (remaining start : Nat) (dense : ByteArray) : Option ByteArray :=
  match remaining with
  | 0 => some dense
  | n + 1 =>
    let column := read columns 4 (4 * start)
    if column ≥ dense.size / width then none else
    let b := read coefficients width (start * width)
    let a := read dense width (column * width)
    if b ≥ modulus || a ≥ modulus then none else
    let product := factor * b % modulus
    let difference := a + modulus - product
    let value := if difference ≥ modulus then difference - modulus else difference
    update modulus factor width columns coefficients n (start + 1)
      (write dense width (column * width) value)

/-- Portable specification of one modular sparse row update. The modulus lies
in `[2,2^31)`; its minimal residue width is 1, 2 or 4 bytes. Columns are little
endian u32 indices, coefficients/dense values use that residue width. The
selected slice has at most 4096 entries. Every accessed dense value and row
coefficient, and `factor`, must lie in `[0,p)`. Invalid shapes, slices, indices
or residues return `none`. Repeated columns are processed sequentially.

Success subtracts `factor * coefficients[i]` at each selected column modulo
`p`, preserving all other logical bytes. Input buffers may alias: column and
coefficient reads always observe the original input buffers. Capacity and
allocation identity are not observable parts of the result. -/
@[expose] def subtractPortable (modulus : UInt64) (dense : ByteArray)
    (columns coefficients : @& ByteArray) (start count : @& Nat) (factor : UInt64) :
    Option ByteArray :=
  let modulus := modulus.toNat
  let factor := factor.toNat
  if modulus < 2 || modulus ≥ 2147483648 || factor ≥ modulus || count > 4096 then none else
  let width := width modulus
  let rows := columns.size / 4
  if columns.size % 4 != 0 || coefficients.size != rows * width || dense.size % width != 0 then
    none
  else if start > rows || count > rows - start then none
  else update modulus factor width columns coefficients count start dense

/-- Native implementation of `subtractPortable`, with the same rejection and
aliasing semantics. Consumes `dense`, borrows the two row buffers, and mutates
only uniquely owned storage; shared or aliased inputs are copied first.
The C implementation uses exact uint64 products, Barrett reduction with a
uint128 high product where available, and exact remainder otherwise. It uses
no SIMD requirement, floating-point arithmetic, platform byte-order assumption
or unchecked pointer access. One call processes at most 4096 entries. -/
@[expose, extern "lean_hex_groebner_subtract_row"]
def subtract (modulus : UInt64) (dense : ByteArray)
    (columns coefficients : @& ByteArray) (start count : @& Nat) (factor : UInt64) :
    Option ByteArray :=
  subtractPortable modulus dense columns coefficients start count factor

end Hex.Groebner.Native
