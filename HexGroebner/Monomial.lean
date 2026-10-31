/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Packed
public import HexMvPoly.Mono
public import Std.Data.HashMap

public section

/-! Packed monomial hash-consing. Identifiers index append-only metadata, never
hash buckets. Hashes and divisibility masks are filters; equality and division
always inspect every exponent. Width changes preserve identifiers and hashes. -/

namespace Hex.Groebner

/-- Supported named global orders, with their existing Hex order laws. -/
inductive TermOrder where
  | lex | grlex | grevlex
  deriving BEq, Repr, Inhabited

/-- The mathematical comparator carried by a named order. -/
def TermOrder.cmp (order : TermOrder) (n : Nat) : Mono n → Mono n → Ordering :=
  match order with
  | .lex => Mono.lex
  | .grlex => Mono.grlex
  | .grevlex => Mono.grevlex

/-- Named orders carry all global monomial-order laws, including well-foundedness. -/
instance (order : TermOrder) (n : Nat) : IsMonomialOrder (order.cmp n) := by
  cases order <;> dsimp [TermOrder.cmp] <;> infer_instance

/-- Representation errors are distinct from the caller's resource allowance. -/
inductive MonomialError where
  | arity | index | exponent | degree | address
  | exhausted | work
  deriving BEq, Repr

/-- Failed monomial operations retain their charged work, including validation
and collision scans before a representation or allocation bound is reached. -/
structure MonomialFailure where
  error : MonomialError
  work : Nat
  deriving BEq, Repr

/-- Cached degree, support mask and semantic hash occupy 24 bytes per monomial. -/
structure MonomialTable where
  arity : Nat
  width : Width := .u8
  exponents : ByteArray := {}
  metadata : ByteArray := {}
  count : Nat := 0
  buckets : Std.HashMap UInt64 (Array Nat) := {}
  /-- Reducing hash bits is useful for exact-collision conformance tests. -/
  hashBits : Nat := 64
  /-- Cumulative exponent visits and collision comparisons. -/
  work : Nat := 0

/-- Owned operations always return the table, on success and failure. This
avoids retaining a rollback alias while growing its packed buffers/hash map. -/
structure InternResult where
  result : Except MonomialFailure Nat
  table : MonomialTable

namespace MonomialTable

private def read64 (bytes : @& ByteArray) (index : Nat) : UInt64 :=
  Packed.read .u32 bytes (2 * index) ||| (Packed.read .u32 bytes (2 * index + 1) <<< 32)

private def push64 (bytes : ByteArray) (value : UInt64) : ByteArray :=
  Packed.push .u32 (Packed.push .u32 bytes (value &&& 0xffffffff)) (value >>> 32)

/-- Read one exponent; callers must supply valid identifiers and variable indices. -/
@[inline] def exponent (table : @& MonomialTable) (id coordinate : Nat) : UInt64 :=
  Packed.read table.width table.exponents (id * table.arity + coordinate)

/-- Cached total degree. -/
@[inline] def degree (table : @& MonomialTable) (id : Nat) : Nat :=
  (read64 table.metadata (3 * id)).toNat

/-- Cached support mask. A failed subset test disproves divisibility. -/
@[inline] def mask (table : @& MonomialTable) (id : Nat) : UInt64 :=
  read64 table.metadata (3 * id + 1)

/-- Cached hash, independent of the selected exponent width. -/
@[inline] def hashAt (table : @& MonomialTable) (id : Nat) : UInt64 :=
  read64 table.metadata (3 * id + 2)

/-- Decode only at an interchange boundary. Hot operations read packed exponents. -/
def exponentsAt (table : MonomialTable) (id : Nat) : Array Nat :=
  (Array.range table.arity).map fun i => (table.exponent id i).toNat

/-- Exact divisibility after the cheap degree and support-mask filters. -/
def divides (table : @& MonomialTable) (a b : Nat) : Bool := Id.run do
  if a ≥ table.count || b ≥ table.count then return false
  if table.degree a > table.degree b || table.mask a &&& table.mask b != table.mask a then
    return false
  for i in [:table.arity] do
    if table.exponent a i > table.exponent b i then return false
  return true

/-- Direct packed comparison in the chosen global order. Columns use its
decreasing order, while identifiers retain insertion order. -/
def compare (table : @& MonomialTable) (order : TermOrder) (a b : Nat) : Ordering := Id.run do
  if a == b then return .eq
  if order != .lex then
    let d := Ord.compare (table.degree a) (table.degree b)
    if d != .eq then return d
  for k in [:table.arity] do
    let i := if order == .grevlex then table.arity - 1 - k else k
    let x := table.exponent a i
    let y := table.exponent b i
    if x != y then
      return if order == .grevlex then Ord.compare y x else Ord.compare x y
  return .eq

private def equal (table : @& MonomialTable) (id : Nat) (values : @& Array UInt64) : Bool := Id.run do
  for i in [:table.arity] do
    if table.exponent id i != values[i]! then return false
  return true

private def widen (table : MonomialTable) (width : Width) : MonomialTable := Id.run do
  let mut exponents := ByteArray.emptyWithCapacity (table.count * table.arity * width.bytes)
  for id in [:table.count] do
    for i in [:table.arity] do
      exponents := Packed.push width exponents (table.exponent id i)
  return { table with width, exponents }

/-- Hash-cons exponents with checked widening and exact collision handling.
The byte allowance bounds both old and new arenas during re-encoding, excluding
hash-table/array headers. The count allowance is checked before append. -/
def internOwned (table : MonomialTable) (values : Array UInt64)
    (maxCount maxBytes : Nat) (maxWork : Nat := 100000000) :
    InternResult := Id.run do
  if values.size != table.arity then return ⟨.error ⟨.arity, table.work⟩, table⟩
  let mut work := table.work + values.size
  if work > maxWork then return ⟨.error ⟨.work, maxWork⟩, table⟩
  let mut width := table.width
  let mut degree : Nat := 0
  let mut mask : UInt64 := 0
  let mut hash : UInt64 := 14695981039346656037
  for i in [:values.size] do
    let x := values[i]!
    -- `> 0xffffffff` avoids per-visit Nat-literal parsing (lean4#16007).
    if x > 4294967295 then return ⟨.error ⟨.exponent, work⟩, table⟩
    if x > 65535 then width := .u32
    else if x > 255 && width == .u8 then width := .u16
    degree := degree + x.toNat
    if x != 0 then mask := mask ||| ((1 : UInt64) <<< (i % 64).toUInt64)
    hash := (hash ^^^ x) * 1099511628211
  if degree ≥ 2 ^ 64 then return ⟨.error ⟨.degree, work⟩, table⟩
  if table.hashBits < 64 then hash := hash &&& (((1 : UInt64) <<< table.hashBits.toUInt64) - 1)
  let bucket := table.buckets[hash]?.getD #[]
  for id in bucket do
    work := work + table.arity
    if work > maxWork then return ⟨.error ⟨.work, maxWork⟩, table⟩
    if table.equal id values then return ⟨.ok id, { table with work }⟩
  if table.count ≥ maxCount then return ⟨.error ⟨.exhausted, work⟩, table⟩
  if table.count + 1 > 4294967295 then return ⟨.error ⟨.index, work⟩, table⟩
  let size := (table.count + 1) * table.arity * width.bytes + (table.count + 1) * 24
  let peak := size + if width != table.width then table.exponents.size else 0
  if peak > maxBytes then return ⟨.error ⟨.exhausted, work⟩, table⟩
  if peak ≥ USize.size then return ⟨.error ⟨.address, work⟩, table⟩
  work := work + table.arity + if width != table.width then table.count * table.arity else 0
  if work > maxWork then return ⟨.error ⟨.work, maxWork⟩, table⟩
  let mut table := if width == table.width then table else table.widen width
  let id := table.count
  let mut exponents := table.exponents
  for x in values do exponents := Packed.push width exponents x
  let metadata := push64 (push64 (push64 table.metadata degree.toUInt64) mask) hash
  let buckets := table.buckets.insert hash (bucket.push id)
  table := { table with exponents, metadata, buckets, count := id + 1, work }
  return ⟨.ok id, table⟩

/-- Non-resumable convenience projection. Performance-sensitive callers use
`internOwned` and install its returned table before inspecting the status. -/
def intern (table : MonomialTable) (values : Array UInt64)
    (maxCount maxBytes : Nat) (maxWork : Nat := 100000000) :
    Except MonomialFailure (Nat × MonomialTable) :=
  let outcome := internOwned table values maxCount maxBytes maxWork
  outcome.result.map fun id => (id, outcome.table)

/-- Checked LCM, product or quotient on stable identifiers. For quotient,
the first argument is the dividend; a nondivisor is an explicit error. -/
inductive Operation where
  | lcm | product | quotient
  deriving BEq

/-- Perform a packed exponent operation and intern its result. -/
def combineOwned (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes : Nat) (maxWork : Nat := 100000000) :
    InternResult := Id.run do
  if a ≥ table.count || b ≥ table.count then return ⟨.error ⟨.index, table.work⟩, table⟩
  let work := table.work + table.arity
  if work > maxWork then return ⟨.error ⟨.work, maxWork⟩, table⟩
  let mut values := Array.emptyWithCapacity table.arity
  for i in [:table.arity] do
    let x := table.exponent a i
    let y := table.exponent b i
    -- Packed coordinates are at most 2^32-1, so their UInt64 sum cannot wrap.
    if operation == .product && x + y > 4294967295 then
      return ⟨.error ⟨.exponent, work⟩, table⟩
    if operation == .quotient && y > x then
      return ⟨.error ⟨.exponent, work⟩, table⟩
    let z := match operation with
      | .lcm => max x y
      | .product => x + y
      | .quotient => x - y
    values := values.push z
  return { table with work }.internOwned values maxCount maxBytes maxWork

/-- Convenience projection of the ownership-preserving monomial operation. -/
def combine (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes : Nat) (maxWork : Nat := 100000000) :
    Except MonomialFailure (Nat × MonomialTable) :=
  let outcome := combineOwned table operation a b maxCount maxBytes maxWork
  outcome.result.map fun id => (id, outcome.table)

end MonomialTable
end Hex.Groebner
