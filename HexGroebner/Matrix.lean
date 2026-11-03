/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Packed
public import HexGroebner.NativeDense

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

/-- Constructor indices are mirrored in `ffi/matrix_state.c` and `matrix_eliminate.c`.
Resource categories. Packed bytes count logical input, workspace and output
payload and 64 logical bytes per recorded derivation operation, excluding
allocator capacity and other Lean object headers. Work counts row
visits, sparse entry updates (including their product), dense column visits,
normalization/inversion products and workspace bytes initialized. -/
inductive Resource where
  | columns | rows | inputEntries | outputEntries | packedBytes | work | traceNodes
  deriving BEq, Repr

/-- Constructor tags are mirrored in `ffi/matrix_state.c` and `matrix_eliminate.c`.
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
Layout mirrored in `HexGroebner/ffi/matrix_eliminate.c` and `matrix_state.c`:
seven object fields followed by the densePivots Bool. -/
structure MatrixLimits where
  columns : Nat := 1000000
  rows : Nat := 100000
  inputEntries : Nat := 10000000
  outputEntries : Nat := 10000000
  packedBytes : Nat := 256 * 1024 * 1024
  work : Nat := 100000000
  traceNodes : Nat := 1000000
  /-- Optional checked M31 dense pivot buffers, charged to these same bounds. -/
  densePivots : Bool := false
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

/-- A failed charge leaves the exact previously charged prefix unchanged. -/
theorem charge_run (resource : Resource) (amount limit : Nat)
    (getCount : MatrixStats → Nat) (setCount : MatrixStats → Nat → MatrixStats)
    (stats : MatrixStats) :
    (charge resource amount limit getCount setCount).run stats =
      if getCount stats + amount > limit then
        (.error (.exhausted resource), stats)
      else (.ok (), setCount stats (getCount stats + amount)) := by
  dsimp [charge, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
    ExceptT.mk, StateT.bind, StateT.get, StateT.set, StateT.pure,
    Bind.bind, MonadState.get, MonadStateOf.get, MonadStateOf.set,
    MonadExcept.throw, MonadExceptOf.throw, liftM,
    MonadLiftT.monadLift, MonadLift.monadLift, getThe, throwThe,
    StateT.map, StateT.mk, Functor.map, Pure.pure]
  split <;> rfl

def work (limits : MatrixLimits) (amount : Nat) : Work Unit :=
  charge .work amount limits.work (·.work) fun s n => { s with work := n }

def packedBytes (limits : MatrixLimits) (amount : Nat) : Work Unit :=
  charge .packedBytes amount limits.packedBytes (·.packedBytes)
    fun s n => { s with packedBytes := n }

/-- Dense pivot optimization currently specializes only the M31 field. -/
@[inline] def cacheEnabled (field : PrimeField) (limits : MatrixLimits) : Bool :=
  limits.densePivots && field.modulus == 2147483647

/-- Optional pivot materialization reserves all of its preparation and payload
within the caller's remaining bounds. Refusal leaves sparse execution available. -/
@[inline] def preparePivot (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (source : Native.Scan.Pivot) (stats : MatrixStats) :
    Native.Dense.Result field.modulus columns source
      (limits.work-stats.work) (limits.packedBytes-stats.packedBytes) :=
  let raw := Native.Dense.Row.raw field.modulus columns source
  if !cacheEnabled field limits then ⟨raw,0,0,rfl,Nat.zero_le _,Nat.zero_le _⟩ else
    let n := source.columns.size/4
    let span := Native.read source.columns 4 (4*(n-1))-Native.read source.columns 4 0+1
    if columns ≤ 65536 && 128 ≤ n && n ≤ 4096 && n < span && 3*span ≤ 4*n then
      Native.Dense.prepare field.modulus columns source
        (limits.work-stats.work) (limits.packedBytes-stats.packedBytes)
    else ⟨raw,0,0,rfl,Nat.zero_le _,Nat.zero_le _⟩

/-- Shared exact preparation counters for the reference and continuation. -/
@[inline] def cacheStats (stats : MatrixStats) (work bytes : Nat) : MatrixStats :=
  { stats with work := stats.work+work,packedBytes := stats.packedBytes+bytes }

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

/-- Bounded native row validation. `PrimeField` is its UInt64 modulus; all
remaining inputs are borrowed Lean records, Nat indices and packed byte arrays.
Native code returns `some` exactly on the admitted 64-bit geometry: at most
`2^32−1` columns and 65537 entries, with counters below `2^62`. This caps one
uninterruptible row call at 65537 entry inspections and 524296 payload bytes.
Larger allowances saturate above every reachable total; error indices remain
arbitrary Nat. A decline happens before charges and uses the original validator.

The owned result is `Option (Except MatrixError Unit × MatrixStats)`, with
standard Option/Except/Prod tags and fresh result/statistics records. An error
retains the borrowed input index by reference; every other input stays immutable,
including aliased row buffers and records. The result contains the exact original
validator error and charged prefix. -/
@[extern "lean_hex_matrix_validate"]
def attemptValidation (field : PrimeField) (limits : @& MatrixLimits)
    (columns index : @& Nat) (row : @& SparseRow) (stats : @& MatrixStats) :
    Option (Except MatrixError Unit × MatrixStats) :=
  if USize.size != 2^64 || columns > 4294967295 || row.size > 65537 ||
      stats.work > 2^62-1 || stats.inputEntries > 2^62-1 ||
      stats.outputEntries > 2^62-1 || stats.packedBytes > 2^62-1 ||
      stats.traceNodes > 2^62-1 || stats.processedRows > 2^62-1 ||
      stats.reductions > 2^62-1 || stats.zeroRows > 2^62-1 then none
  else some ((validate field limits columns index row).run stats)

/-- Validate a row using the bounded native provider where admitted. -/
def validateWith (field : PrimeField) (limits : MatrixLimits)
    (columns index : Nat) (row : SparseRow) : Work Unit := ExceptT.mk fun stats =>
  match attemptValidation field limits columns index row stats with
  | some result => result
  | none => (validate field limits columns index row).run stats

/-- The original validation action, including every failure prefix, is preserved. -/
theorem validateWith_spec (field : PrimeField) (limits : MatrixLimits)
    (columns index : Nat) (row : SparseRow) :
    validateWith field limits columns index row = validate field limits columns index row := by
  funext stats
  simp only [validateWith, attemptValidation, ExceptT.mk]
  split <;> split at * <;> simp_all [ExceptT.run]

def zeros (size : Nat) : ByteArray := Id.run do
  let mut data := ByteArray.emptyWithCapacity size
  for _ in [:size] do data := data.push 0
  return data

/-- Bounded native allocation/initialization of at most one MiB per call. The
borrowed Nat size admits exactly `size≤1048576`, on every supported platform;
this fixed cap bounds uninterruptible zeroing work. The owned Option contains a
fresh byte array of that size with every byte zero. `none` allocates no buffer
and the caller uses the original implementation; there are no borrowed buffers
to mutate or alias. Larger-workspace native initialization remains future work. -/
@[extern "lean_hex_matrix_zeros"]
def attemptZeros (size : @& Nat) : Option ByteArray :=
  if size > 1048576 then none else some (zeros size)

/-- Allocate a zeroed workspace, with portable allocation outside the native cap. -/
def zerosWith (size : Nat) : ByteArray :=
  match attemptZeros size with
  | some bytes => bytes
  | none => zeros size

@[simp] theorem zerosWith_spec (size : Nat) : zerosWith size = zeros size := by
  simp only [zerosWith, attemptZeros]
  split <;> split at * <;> simp_all

/-- Shared Fermat-exponent schedule over an explicit multiplication operation. -/
@[inline] def inverseWith {m : Type → Type} [Monad m] (modulus : UInt64)
    (a : UInt64) (multiply : UInt64 → UInt64 → m UInt64) : m UInt64 := do
  if a == 1 then return 1
  let mut exponent := modulus.toNat-2
  let mut a := a
  let mut value : UInt64 := 1
  for _ in [:modulus.toNat.log2+1] do
    if exponent == 0 then break
    if exponent%2 == 1 then value ← multiply value a
    exponent := exponent/2
    if exponent > 0 then a ← multiply a a
  return value

/-- Multiplication count of `inverse`, using its identical control loop with a
counting multiplication. Field values cannot affect the exponent schedule. -/
def inverseCost (field : PrimeField) (a : UInt64) : Nat :=
  ((inverseWith field.modulus a (fun _ _ => do
    modify (·+1)
    return 0) : StateM Nat UInt64).run 0).2

/-- Square-and-multiply, with each multiply charged to the parent allowance.
The modulus bit length bounds the loop; `PrimeField.bound` makes it at most
31 bits. Fermat inversion also covers characteristic two. -/
def inverse (field : PrimeField) (ctx : BarrettCtx field.modulus)
    (limits : MatrixLimits) (a : UInt64) : Work UInt64 :=
  inverseWith field.modulus a fun x y => do
    work limits 1
    return ctx.mulMod x y

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
