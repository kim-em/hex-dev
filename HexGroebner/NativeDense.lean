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

end Row

/-- Cache preparation reports its own parent work and logical packed bytes.
Work counts two sparse validations, sparse writes, initialized bytes and dense
comparison cells. A refused admission performs no row traversal or allocation. -/
structure Result (modulus : UInt64) (columns : Nat) where
  row : Row modulus columns
  work : Nat := 0
  packedBytes : Nat := 0

def zeros (n : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity n
  for _ in [:n] do bytes := bytes.push 0
  return bytes

/-- Opt-in M31 dense pivots, at least half full, with 128–4096 sparse entries.
The complete dense span has at most 16384 coefficients. Admission reserves the
entire bounded preparation before any traversal; source inputs stay immutable.
Other fields and unsupported shapes retain the ordinary sparse row. -/
def preparePortable (modulus : UInt64) (columns : Nat) (source : Scan.Pivot)
    (workBudget bytesBudget : Nat) : Result modulus columns := Id.run do
  let fallback : Result modulus columns := { row := Row.raw modulus columns source }
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
  if span > 16384 || span > 2*n || cost > workBudget || bytes > bytesBudget then return fallback
  if !validSparse modulus columns source then return { fallback with work := n+1 }
  let mut dense := zeros bytes
  for i in [:n] do
    let column := Native.read source.columns 4 (4*i)
    dense := Native.write dense w ((column-first)*w) (Native.read source.coefficients w (w*i))
  match Row.check modulus columns source dense first.toUInt32 n.toUInt32 with
  | some row => return ⟨row,cost,bytes⟩
  | none => return { fallback with work := cost,packedBytes := bytes }

/-- Bounded native materialization of checked dense pivots. The sparse source
is borrowed; output owns its optimization buffer. The Row ABI is two objects
(source, dense), followed by UInt32 first/size; Result is three object fields. -/
@[extern "lean_hex_prepare_dense"]
def prepare (modulus : UInt64) (columns : @& Nat) (source : @& Scan.Pivot)
    (workBudget bytesBudget : @& Nat) : Result modulus columns :=
  preparePortable modulus columns source workBudget bytesBudget

end Hex.Groebner.Native.Dense
