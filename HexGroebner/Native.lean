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
Monomial calls validate packed geometry and process at most 4096 coordinates.
Preparation reuses an owned buffer; comparisons borrow their source arrays. -/

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


namespace Bytes

/-- Exact equality of one borrowed byte slice, with a 4096-byte call bound.
Invalid offsets, lengths or a larger quantum return false, including empty
slices whose starting offset lies beyond either buffer. -/
@[expose] def equalPortable (left right : @& ByteArray) (start count : Nat) : Bool := Id.run do
  if count > 4096 || start > left.size || start > right.size ||
      count > left.size - start || count > right.size - start then return false
  for i in [:count] do
    if left[start+i]! != right[start+i]! then return false
  return true

/-- Bounded native byte comparison. Both buffers are borrowed and may alias.
The implementation checks the complete slice before access, mutates no bytes,
retains no pointers and makes no alignment or byte-order assumption. -/
@[expose, extern "lean_hex_groebner_equal_bytes"]
def equal (left right : @& ByteArray) (start count : @& Nat) : Bool :=
  equalPortable left right start count

end Bytes

namespace Monomial

/-- Check a slice of cached support products against the current monomial
arena. Geometry, identifiers and the 4096-coordinate comparison bound are
validated before access. Every result exponent must equal base plus multiplier. -/
@[expose] def productsPortable (width : UInt8) (arity count multiplier start terms : UInt64)
    (arena base result : @& ByteArray) : Bool := Id.run do
  let w := width.toNat
  let n := arity.toNat
  let count := count.toNat
  let start := start.toNat
  let terms := terms.toNat
  if (w != 1 && w != 2 && w != 4) || n == 0 || n > 4096 || terms*n > 4096 ||
      multiplier.toNat ≥ count || arena.size != count*n*w || base.size % 4 != 0 ||
      result.size != base.size || start > base.size/4 || terms > base.size/4-start then
    return false
  for i in [start:start+terms] do
    let a := read base 4 (4*i)
    let b := read result 4 (4*i)
    if a ≥ count || b ≥ count then return false
    for j in [:n] do
      if read arena w ((a*n+j)*w) + read arena w ((multiplier.toNat*n+j)*w) !=
          read arena w ((b*n+j)*w) then return false
  return true

/-- Borrow-only exact product validation. No pointers are retained, no storage
is mutated, and each call compares at most 4096 exponent coordinates. -/
@[expose, extern "lean_hex_groebner_equal_products"]
def products (width : UInt8) (arity count multiplier start terms : UInt64)
    (arena base result : @& ByteArray) : Bool :=
  productsPortable width arity count multiplier start terms arena base result

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

/-- Bounded packed comparisons: operation 0 is lexicographic, 1 is reverse
lexicographic with reversed inequality, and 2 is pointwise divisibility.
Results 0/1/2 mean less/equal/greater for orders and 0/1 mean false/true
for divisibility. Result 3 requests the unrestricted portable fallback.
Both rows must fit the arena; zero arity reads no bytes. -/
@[expose] def comparePortable (operation width : UInt8) (arity left right : Nat)
    (arena : @& ByteArray) : UInt8 := Id.run do
  let w := width.toNat
  if operation > 2 || (w != 1 && w != 2 && w != 4) || arity > 4096 ||
      left > 4294967295 || right > 4294967295 then return 3
  if arity == 0 then return 1
  let rowBytes := arity*w
  if (max left right + 1)*rowBytes > arena.size then return 3
  for k in [:arity] do
    let i := if operation == 1 then arity-1-k else k
    let a := read arena w ((left*arity+i)*w)
    let b := read arena w ((right*arity+i)*w)
    if operation == 2 then
      if a > b then return 0
    else if a != b then
      return if operation == 1 then (if b < a then 0 else 2)
        else (if a < b then 0 else 2)
  return 1

/-- Borrow-only native comparison, bounded to 4096 coordinates. No pointer or
allocation survives the call; unsupported shapes select the Lean fallback. -/
@[expose, extern "lean_hex_groebner_compare_monomials"]
def comparePacked (operation width : UInt8) (arity left right : UInt64)
    (arena : @& ByteArray) : UInt8 :=
  comparePortable operation width arity.toNat left.toNat right.toNat arena

/-- Validate arbitrary-precision dimensions before narrowing to the native ABI. -/
@[inline] def compareCode (operation width : UInt8) (arity left right : Nat)
    (arena : @& ByteArray) : UInt8 :=
  if arity > 4096 || left > 4294967295 || right > 4294967295 then 3 else
    comparePacked operation width arity.toUInt64 left.toUInt64 right.toUInt64 arena

/-- Checking the Nat bounds before narrowing preserves the portable operation. -/
theorem compareCode_eq (operation width : UInt8) (arity left right : Nat)
    (arena : ByteArray) :
    compareCode operation width arity left right arena =
      comparePortable operation width arity left right arena := by
  by_cases hn : arity > 4096
  · simp [compareCode, comparePortable, hn]
  by_cases hl : left > 4294967295
  · simp [compareCode, comparePortable, hl]
  by_cases hr : right > 4294967295
  · simp [compareCode, comparePortable, hr]
  have hn64 : arity < 2^64 := by omega
  have hl64 : left < 2^64 := by omega
  have hr64 : right < 2^64 := by omega
  simp [compareCode, comparePacked, hn, hl, hr, Nat.toUInt64,
    UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hr64]

/-- Typed monomial ordering, after the caller's optional degree comparison. -/
@[inline] def compare (reverse : Bool) (width : UInt8) (arity left right : Nat)
    (arena : @& ByteArray) : Option Ordering :=
  let code := compareCode (if reverse then 1 else 0) width arity left right arena
  if code == 0 then some .lt else if code == 1 then some .eq
  else if code == 2 then some .gt else none

/-- Typed pointwise divisibility, after the caller's degree and mask filters. -/
@[inline] def divides (width : UInt8) (arity left right : Nat)
    (arena : @& ByteArray) : Option Bool :=
  let code := compareCode 2 width arity left right arena
  if code < 2 then some (code == 1) else none

structure SearchResult where
  id : Nat
  link : Nat
  work : Nat
  status : UInt8
  deriving BEq

/-- Portable exact packed lookup. A call visits at most 4096 links and at most
4096 coordinates. Input buffers are borrowed and may alias. Zero link ends the
chain; other links encode stable identifiers plus one. No hash match alone
establishes equality. Invalid geometry is rejected before any reads. -/
@[expose] def searchPortable (width : UInt8) (arity count hash link quantum : UInt64)
    (exponents metadata links candidate : @& ByteArray) (allowance : @& Nat) : SearchResult := Id.run do
  let w := width.toNat
  let n := arity.toNat
  let c := count.toNat
  let q := quantum.toNat
  let mut link := link.toNat
  if (w != 1 && w != 2 && w != 4) || n == 0 || n > 4096 || c > 4294967295 ||
      link > 4294967295 || q > 4096 || q*n > 4096 ||
      exponents.size != c*n*w || metadata.size != c*24 || links.size != c*4 ||
      candidate.size != n*4+28 then return ⟨0,link,0,4⟩
  let mut work := 0
  for _ in [:q] do
    if link == 0 then return ⟨0,0,work,2⟩
    if work + 1 > allowance then return ⟨0,link,work,3⟩
    work := work + 1
    let id := link - 1
    if id ≥ c then return ⟨0,link,work,4⟩
    link := read links 4 (id*4)
    if (read metadata 8 (id*24+16)).toUInt64 != hash then continue
    if work + n > allowance then return ⟨0,link,work,3⟩
    work := work + n
    if equalPortable width arity id.toUInt64 exponents candidate then return ⟨id,link,work,1⟩
  return ⟨0,link,work,0⟩

/-- Native exact chain search with the same bounded reads and budget prefixes. -/
@[expose, extern "lean_hex_groebner_search_monomial"]
def search (width : UInt8) (arity count hash link quantum : UInt64)
    (exponents metadata links candidate : @& ByteArray) (allowance : @& Nat) : SearchResult :=
  searchPortable width arity count hash link quantum exponents metadata links candidate allowance


end Monomial

end Hex.Groebner.Native
