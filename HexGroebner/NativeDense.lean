/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.NativeScan

@[expose] public section

namespace Hex.Groebner.Native.Dense

/-- Check a monic sparse pivot and every stored coefficient and column. -/
def validSparse (modulus : UInt64) (columns : Nat) (row : Scan.Pivot) : Bool := Id.run do
  let p := modulus.toNat
  let w := Native.width p
  let some n := Scan.rowSize w row | return false
  if p < 2 || p ≥ 2147483648 || columns > 4294967295 then return false
  let mut valid := Native.read row.coefficients w 0 == 1
  let mut previous := 0
  for i in [:n] do
    let column := Native.read row.columns 4 (4*i)
    let value := Native.read row.coefficients w (w*i)
    valid := valid && column < columns && (i == 0 || previous < column) &&
      value != 0 && value < p
    previous := column
  return valid

/-- A nonempty dense buffer represents exactly the sparse pivot, including its
zero gaps. Empty buffers retain the ordinary, potentially unvalidated row. -/
def valid (modulus : UInt64) (columns : Nat) (row : Scan.Pivot)
    (dense : ByteArray) (first size : UInt32) : Bool := Id.run do
  if dense.isEmpty then return first == 0 && size == 0
  if !validSparse modulus columns row then return false
  let n := size.toNat
  let w := Native.width modulus.toNat
  if row.columns.size != n*4 || first.toNat != Native.read row.columns 4 0 then return false
  let last := Native.read row.columns 4 (4*(n-1))
  let span := last-first.toNat+1
  if span > 16384 || span > 2*n || dense.size != span*w then return false
  let mut cursor := 0
  let mut equal := true
  for i in [:span] do
    let present := cursor < n && Native.read row.columns 4 (4*cursor) == first.toNat+i
    let expected := if present then Native.read row.coefficients w (w*cursor) else 0
    equal := equal && Native.read dense w (w*i) == expected
    if present then cursor := cursor+1
  return equal && cursor == n

/-- Checked immutable optimization data. The source row remains available for
ordinary sparse execution and for the kernel-reducible reference function. -/
structure Row (modulus : UInt64) (columns : Nat) where
  source : Scan.Pivot
  dense : ByteArray
  first : UInt32
  size : UInt32
  lawful : valid modulus columns source dense first size = true

namespace Row

def raw (modulus : UInt64) (columns : Nat) (source : Scan.Pivot) : Row modulus columns :=
  ⟨source,{},0,0,by rfl⟩

def check (modulus : UInt64) (columns : Nat) (source : Scan.Pivot)
    (dense : ByteArray) (first size : UInt32) : Option (Row modulus columns) :=
  if h : valid modulus columns source dense first size = true then
    some ⟨source,dense,first,size,h⟩
  else none

theorem check_source {modulus : UInt64} {columns : Nat} {source : Scan.Pivot}
    {dense : ByteArray} {first size : UInt32} {row : Row modulus columns}
    (h : check modulus columns source dense first size = some row) : row.source = source := by
  unfold check at h
  split at h
  · cases h; rfl
  · contradiction

end Row

/-- Cache preparation reports its own parent work and logical packed bytes.
Work counts two sparse validations, sparse writes, initialized bytes and dense
comparison cells. A refused admission performs no row traversal or payload allocation. -/
structure Result (modulus : UInt64) (columns : Nat) (source : Scan.Pivot)
    (workBudget bytesBudget : Nat) where
  row : Row modulus columns
  work : Nat := 0
  packedBytes : Nat := 0
  source_eq : row.source = source
  work_le : work ≤ workBudget
  bytes_le : packedBytes ≤ bytesBudget

def zeros (n : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity n
  for _ in [:n] do bytes := bytes.push 0
  return bytes

/-- Opt-in M31 dense pivots, at least half full, with 128–4096 sparse entries.
The factory admits at most 8192 coefficients: at most 4096 entries and
a span at most twice their count.
The checked Row format separately permits spans up to 16384. Admission reserves the
entire bounded preparation before any traversal; source inputs stay immutable.
Other fields and unsupported shapes retain the ordinary sparse row. -/
def preparePortable (modulus : UInt64) (columns : Nat) (source : Scan.Pivot)
    (workBudget bytesBudget : Nat) : Result modulus columns source workBudget bytesBudget := Id.run do
  let fallback : Result modulus columns source workBudget bytesBudget := {
    row := Row.raw modulus columns source
    source_eq := rfl
    work_le := Nat.zero_le _
    bytes_le := Nat.zero_le _ }
  let w := Native.width modulus.toNat
  let n := source.columns.size/4
  if modulus != 2147483647 || columns > 4294967295 || n < 128 || n > 4096 ||
      source.columns.size%4 != 0 || source.coefficients.size != n*w then return fallback
  let first := Native.read source.columns 4 0
  let last := Native.read source.columns 4 (4*(n-1))
  if last < first || last ≥ columns then return fallback
  let span := last-first+1
  let bytes := span*w
  let cost := bytes+3*n+span+2
  if span > 2*n then return fallback
  if hbudget : cost ≤ workBudget ∧ bytes ≤ bytesBudget then
    if !validSparse modulus columns source then
      return { fallback with work := n+1,work_le := by omega }
    let mut dense := zeros bytes
    for i in [:n] do
      let column := Native.read source.columns 4 (4*i)
      dense := Native.write dense w ((column-first)*w) (Native.read source.coefficients w (w*i))
    match h : Row.check modulus columns source dense first.toUInt32 n.toUInt32 with
    | some row => return ⟨row,cost,bytes,Row.check_source h,by omega,by omega⟩
    | none => return { fallback with work := cost,packedBytes := bytes,work_le := by omega,bytes_le := by omega }
  else return fallback

/-- Bounded native materialization of checked dense pivots. The sparse source
is borrowed; output owns its optimization buffer. The Row ABI is two objects
(source, dense), followed by UInt32 first/size; Result is three object fields. -/
@[extern "lean_hex_prepare_dense"]
def prepare (modulus : UInt64) (columns : @& Nat) (source : @& Scan.Pivot)
    (workBudget bytesBudget : @& Nat) : Result modulus columns source workBudget bytesBudget :=
  preparePortable modulus columns source workBudget bytesBudget

/-- Checked caches for exactly this immutable sparse pivot array. -/
structure Cache (modulus : UInt64) (columns : Nat) (sources : Array Scan.Pivot) where
  rows : Array (Row modulus columns)
  active : Bool
  source_eq : rows.map (·.source) = sources
  active_eq : active = rows.any (fun row => !row.dense.isEmpty)

namespace Cache

def empty (modulus : UInt64) (columns : Nat) : Cache modulus columns #[] := ⟨#[],false,by simp,by simp⟩

def push {modulus : UInt64} {columns : Nat} {sources : Array Scan.Pivot}
    (cache : Cache modulus columns sources) {source : Scan.Pivot}
    {workBudget bytesBudget : Nat}
    (prepared : Result modulus columns source workBudget bytesBudget) : Cache modulus columns (sources.push source) :=
  ⟨cache.rows.push prepared.row,cache.active || !prepared.row.dense.isEmpty,
    by simp only [Array.map_push,prepared.source_eq,cache.source_eq],
    by simp only [Array.any_push,cache.active_eq]⟩

end Cache

/-- The scalar semantics visit only sparse entries. Cached zero gaps never
consume logical update steps or change failure prefixes. The ambient dimension
is checked even for raw rows, so every nonempty cache has this call's geometry. -/
def portable (modulus : UInt64) (columns : Nat) (slots : ByteArray)
    (pivots : Array (Row modulus columns)) (initial : Scan.State)
    (quantum workLimit traceLimit : Nat) (provenance : Bool) : Scan.Result :=
  if columns != initial.dense.size / Native.width modulus.toNat then
    { state := initial,status := 4 }
  else Scan.portableWith modulus slots pivots.size (fun i =>
    (pivots[i]?.map (·.source)).getD default) initial quantum workLimit traceLimit provenance

/-- Checked cache provenance recovers the ordinary sparse scalar semantics. -/
theorem portable_cache (modulus : UInt64) (columns : Nat) (slots : ByteArray)
    (sources : Array Scan.Pivot) (cache : Cache modulus columns sources)
    (initial : Scan.State) (quantum workLimit traceLimit : Nat) (provenance : Bool)
    (hcolumns : columns = initial.dense.size / Native.width modulus.toNat) :
    portable modulus columns slots cache.rows initial quantum workLimit traceLimit provenance =
      Scan.portable modulus slots sources initial quantum workLimit traceLimit provenance := by
  have hdim : (columns != initial.dense.size / Native.width modulus.toNat) = false := by simp [hcolumns]
  simp only [portable,hdim,Bool.false_eq_true,ite_false,Scan.portable]
  have hsize := congrArg Array.size cache.source_eq
  simp only [Array.size_map] at hsize
  have hat : (fun (i : Nat) => (cache.rows[i]?.map (fun row : Row modulus columns => row.source)).getD default) = (fun i => sources[i]!) := by
    funext i
    have hget := congrArg (fun (rows : Array Scan.Pivot) => rows[i]!) cache.source_eq
    simpa only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,Array.getElem?_map] using hget
  rw [hsize,hat]

/-- Dense-aware native transition. Immutable checked pivot buffers permit
contiguous M31 updates; unsupported fields and locally sparse packets retain
sparse execution. Each call has at most 4096 logical updates and twice that many dense
cells. The Row proof licenses cache reads without revalidating whole pivots. -/
@[extern "lean_hex_dense_transition"]
def transition (modulus : UInt64) (columns : @& Nat) (slots : @& ByteArray)
    (pivots : @& Array (Row modulus columns)) (initial : Scan.State)
    (quantum workLimit traceLimit : @& Nat) (provenance : Bool) : Scan.Result :=
  portable modulus columns slots pivots initial quantum workLimit traceLimit provenance

end Hex.Groebner.Native.Dense
