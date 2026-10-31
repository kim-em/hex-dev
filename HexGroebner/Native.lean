/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public section

/-! Bounded packed modular row updates and monomial operations. This module imports no implementation
library, so its native carrier can resolve the C binding on every platform.
The byte layout and rejection behavior are part of the pure function's contract.
Matrix callers validate entire rows before calling it on chunks of at most
4096 entries; the native provider repeats shape and access checks defensively.
Monomial calls validate packed geometry and process at most 4096 coordinates,
reusing an owned preparation buffer. -/

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

namespace Monomial

/-- Fill a validated workspace with u32 coordinates and degree/mask/hash/max.
The remaining coordinate count bounds recursion and each compiled native call. -/
@[expose] def fill (operation width arity left right index : Nat) (source : @& ByteArray)
    (degree mask hash largest : UInt64) : Nat → ByteArray → Option ByteArray
  | 0, workspace =>
    let offset := arity * 4
    let workspace := write workspace 8 offset degree.toNat
    let workspace := write workspace 8 (offset + 8) mask.toNat
    let workspace := write workspace 8 (offset + 16) hash.toNat
    some (write workspace 4 (offset + 24) largest.toNat)
  | remaining + 1, workspace =>
    let x := (read source width ((left * arity + index) * width)).toUInt64
    let y := (read source width ((right * arity + index) * width)).toUInt64
    if (operation == 1 && x + y > 4294967295) || (operation == 2 && y > x) then none else
    let z := if operation == 0 then max x y else if operation == 1 then x + y else x - y
    let workspace := write workspace 4 (index * 4) z.toNat
    let mask := if z == 0 then mask else mask ||| ((1 : UInt64) <<< (index % 64).toUInt64)
    fill operation width arity left right (index + 1) source (degree + z) mask
      ((hash ^^^ z) * 1099511628211) (max largest z) remaining workspace

/-- Packed monomial operation: 0 = LCM, 1 = product, 2 = exact quotient.
Borrow `source`, consume `workspace`. Source stores exactly `count * arity`
little-endian exponents of width 1/2/4. Arity lies in `[1,4096]`; both identifiers
are below count. Workspace has `4*arity+28` bytes. Success writes u32 coordinates,
then u64 degree, support mask and FNV hash, then u32 maximum coordinate.
Overflow or inexact quotient, invalid geometry or opcode returns none.
The degree fits u64 because the admitted coordinate count is bounded.
Failure consumes the workspace and returns no partial buffer; a caller may
recreate it within its existing workspace reservation. -/
@[expose] def preparePortable (operation width : UInt8) (arity count left right : UInt64)
    (source : @& ByteArray) (workspace : ByteArray) : Option ByteArray :=
  let n := arity.toNat
  let w := width.toNat
  if operation.toNat > 2 || (w != 1 && w != 2 && w != 4) || n == 0 || n > 4096 ||
      left ≥ count || right ≥ count || source.size != count.toNat * n * w ||
      workspace.size != n * 4 + 28 then none else
    fill operation.toNat w n left.toNat right.toNat 0 source 0 0 14695981039346656037 0 n workspace

/-- Bounded native implementation of `preparePortable`. Mutates only uniquely
owned workspace storage, preserving original borrowed bytes even under aliasing.
It allocates no coordinate objects and retains no pointers across calls. -/
@[expose, extern "lean_hex_groebner_prepare_monomial"]
def prepare (operation width : UInt8) (arity count left right : UInt64)
    (source : @& ByteArray) (workspace : ByteArray) : Option ByteArray :=
  preparePortable operation width arity count left right source workspace

/-- Exact coordinate comparison after geometry validation. -/
@[expose] def equalAux (width arity id index : Nat) (source candidate : @& ByteArray) : Nat → Bool
  | 0 => true
  | remaining + 1 =>
    read source width ((id * arity + index) * width) == read candidate 4 (index * 4) &&
      equalAux width arity id (index + 1) source candidate remaining

/-- Compare a packed source monomial with the coordinates of a prepared result.
Candidate metadata is irrelevant to equality. Invalid geometry returns false. -/
@[expose] def equalPortable (width : UInt8) (arity id : UInt64)
    (source candidate : @& ByteArray) : Bool :=
  let n := arity.toNat
  let w := width.toNat
  if (w != 1 && w != 2 && w != 4) || n == 0 || n > 4096 ||
      source.size % (n * w) != 0 || id.toNat ≥ source.size / (n * w) ||
      candidate.size != n * 4 + 28 then false else
    equalAux w n id.toNat 0 source candidate n

/-- Native exact comparison, borrowing both buffers, with the portable rejection
contract. Hashes never replace this full coordinate comparison. -/
@[expose, extern "lean_hex_groebner_equal_monomial"]
def equal (width : UInt8) (arity id : UInt64) (source candidate : @& ByteArray) : Bool :=
  equalPortable width arity id source candidate

end Monomial

end Hex.Groebner.Native
