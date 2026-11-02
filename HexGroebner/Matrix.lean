/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Packed
public import HexGroebner.Native

@[expose] public section

/-! Shared prime-field matrix data, validation and resource accounting. -/

namespace Hex.Groebner

/-- Both representations choose the same minimal residue width. -/
theorem native_width (field : PrimeField) :
    Native.width field.modulus.toNat = field.width.bytes := by
  simp only [Native.width, PrimeField.width, UInt64.le_iff_toNat_le]
  simp only [show (256 : UInt64).toNat = 256 from rfl,
    show (65536 : UInt64).toNat = 65536 from rfl]
  split <;> (try split) <;> rfl

/-- Constructor indices are mirrored in `ffi/matrix_state.c`.
Resource categories. Packed bytes count logical input, workspace and output
payload and 64 logical bytes per recorded derivation operation, excluding
allocator capacity and other Lean object headers. Work counts row
visits, sparse entry updates (including their product), dense column visits,
normalization/inversion products and workspace bytes initialized. -/
inductive Resource where
  | columns | rows | inputEntries | outputEntries | packedBytes | work | traceNodes
  deriving BEq, Repr

/-- Constructor tags are mirrored in `ffi/matrix_state.c`.
Invalid serialized data, resource exhaustion and internal row-provider failure remain distinct. -/
inductive MatrixError where
  | dimensions
  /-- The checked native row provider rejected a validated row; internal invariant failure. -/
  | rowUpdate
  | rowLength (row : Nat)
  | column (row entry : Nat)
  | coefficient (row entry : Nat)
  | exhausted (resource : Resource)
  deriving BEq, Repr

/-- Bounds for one matrix call. All sizes use `Nat` arithmetic, so size products
are checked before narrowing or allocation. There is no unbounded fallback.
Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c` and `matrix_state.c`. -/
structure MatrixLimits where
  columns : Nat := 1000000
  rows : Nat := 100000
  inputEntries : Nat := 10000000
  outputEntries : Nat := 10000000
  packedBytes : Nat := 256 * 1024 * 1024
  work : Nat := 100000000
  traceNodes : Nat := 1000000
  deriving Inhabited

/-- Charged work is retained on failure as well as success.
Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c` and `matrix_state.c`. -/
structure MatrixStats where
  work : Nat := 0
  inputEntries : Nat := 0
  outputEntries : Nat := 0
  packedBytes : Nat := 0
  traceNodes : Nat := 0
  processedRows : Nat := 0
  reductions : Nat := 0
  zeroRows : Nat := 0
  deriving Repr, BEq, Inhabited

/-- Shared row provenance. Inputs are numbered reducers first, then targets.
Every operation refers only to earlier nodes. This is derivation data, not a
complete basis certificate and not a proof of any Gröbner property. Interpret
`addScaled l r c` as `l + c*r` and `scale r c` as `c*r` in the call's field
and fixed column map. Coefficients lie in `[1,p)`. The trace borrows that field
identity from the call; it is not a standalone serialized certificate. Nodes
for rows reducing to zero may be unreferenced by the output pivots. -/
inductive RowOp where
  | input (row : Nat)
  | addScaled (left right : Nat) (coefficient : UInt64)
  | scale (row : Nat) (coefficient : UInt64)
  deriving Repr, BEq

/-- A monic sparse pivot, optionally referring to its derivation. Target pivots
are precisely the rows adding dimension beyond the reducer row space.
Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c` and `matrix_state.c`. -/
structure Pivot where
  row : SparseRow
  fromTarget : Bool
  derivation : Option Nat
  /-- Scalar applied to the residual row when making this pivot monic. Retaining
  it allows a one-target triangular solve to return the unscaled remainder. -/
  multiplier : UInt64 := 1
  /-- Maximum propagated sugar label of the rows actually used in this pivot. -/
  sugar : Nat := 0
  deriving Inhabited

/-- Echelon rows in increasing pivot-column order, without permuting columns.
The reducer rank separates the reducer subspace from new target information.
No reduced-basis or polynomial-ideal conclusion is attached to this result.
Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c` and `matrix_state.c`. -/
structure Echelon where
  rows : Array Pivot
  reducerRank : Nat
  trace : Array RowOp

/-- An unscaled target remainder after reduction by the supplied reducer rows.
Targets are independent: none becomes a reducer for another target. Empty rows
retain their input position and optional zero derivation.
Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c` and `matrix_state.c`. -/
structure RemainderRow where
  row : SparseRow
  derivation : Option Nat
  sugar : Nat
  deriving Inhabited

/-- Independent target remainders in input order, including zeros. -/
structure Remainders where
  rows : Array RemainderRow
  trace : Array RowOp

/-- Bounded independent triangular solves, retaining charged counters on failure. -/
structure RemainderResult where
  result : Except MatrixError Remainders
  stats : MatrixStats

/-- Explicit success/failure with the counters charged against the caller's
allowance. Exhaustion exposes no incomplete matrix as a completed answer. -/
structure MatrixResult where
  result : Except MatrixError Echelon
  stats : MatrixStats

namespace Matrix

abbrev Work := ExceptT MatrixError (StateM MatrixStats)

def charge (resource : Resource) (amount limit : Nat)
    (getCount : MatrixStats → Nat) (setCount : MatrixStats → Nat → MatrixStats) : Work Unit := do
  let stats ← get
  let count := getCount stats + amount
  if count > limit then throw (.exhausted resource)
  set (setCount stats count)

def work (limits : MatrixLimits) (amount : Nat) : Work Unit :=
  charge .work amount limits.work (·.work) fun s n => { s with work := n }

def packedBytes (limits : MatrixLimits) (amount : Nat) : Work Unit :=
  charge .packedBytes amount limits.packedBytes (·.packedBytes)
    fun s n => { s with packedBytes := n }

def validate (field : PrimeField) (limits : MatrixLimits)
    (columns index : Nat) (row : SparseRow) : Work Unit := do
  work limits 1
  if row.columns.size % 4 != 0 || row.coefficients.size != row.size * field.width.bytes then
    throw (.rowLength index)
  charge .inputEntries row.size limits.inputEntries (·.inputEntries)
    fun s n => { s with inputEntries := n }
  packedBytes limits (row.columns.size + row.coefficients.size)
  work limits row.size
  let mut previous : Option Nat := none
  for i in [:row.size] do
    let column := (Packed.read .u32 row.columns i).toNat
    if column ≥ columns then throw (.column index i)
    if let some p := previous then
      if column ≤ p then throw (.column index i)
    let c := Packed.read field.width row.coefficients i
    if c == 0 || c ≥ field.modulus then throw (.coefficient index i)
    previous := some column

def zeros (size : Nat) : ByteArray := Id.run do
  let mut data := ByteArray.emptyWithCapacity size
  for _ in [:size] do data := data.push 0
  return data

/-- Square-and-multiply, with each multiply charged to the parent allowance.
The modulus bit length bounds the loop; `PrimeField.bound` makes it at most
31 bits. Fermat inversion also covers characteristic two. -/
def inverse (field : PrimeField) (ctx : BarrettCtx field.modulus)
    (limits : MatrixLimits) (a : UInt64) : Work UInt64 := do
  if a == 1 then return 1
  let mut exponent := field.modulus.toNat - 2
  let mut a := a
  let mut value : UInt64 := 1
  for _ in [:field.modulus.toNat.log2 + 1] do
    if exponent == 0 then break
    if exponent % 2 == 1 then
      work limits 1
      value := ctx.mulMod value a
    exponent := exponent / 2
    if exponent > 0 then
      work limits 1
      a := ctx.mulMod a a
  return value

/-- Install a known sparse reducer without scattering or scanning empty columns.
Its free leading column guarantees independence of the preceding pivots; its
tail need not be reduced to maintain forward echelon form. -/
def scaleSparse (field : PrimeField) (ctx : BarrettCtx field.modulus)
    (limits : MatrixLimits) (row : SparseRow) (inverse : UInt64) : Work SparseRow := do
  charge .outputEntries row.size limits.outputEntries (·.outputEntries)
    fun s n => { s with outputEntries := n }
  packedBytes limits (row.columns.size + row.coefficients.size)
  if inverse == 1 then return row
  work limits row.size
  let width := field.width
  let mut coefficients := ByteArray.emptyWithCapacity row.coefficients.size
  for i in [:row.size] do
    coefficients := Packed.push width coefficients
      (ctx.mulMod (Packed.read width row.coefficients i) inverse)
  return ⟨row.columns, coefficients⟩

end Matrix
end Hex.Groebner
