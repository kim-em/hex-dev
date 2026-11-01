/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.MonomialIndex
public import HexGroebner.Native
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
  deriving BEq, Repr, DecidableEq, Inhabited

/-- The mathematical comparator carried by a named order. -/
@[expose] def TermOrder.cmp (order : TermOrder) (n : Nat) : Mono n → Mono n → Ordering :=
  match order with
  | .lex => Mono.lex
  | .grlex => Mono.grlex
  | .grevlex => Mono.grevlex

/-- Named orders carry all global monomial-order laws, including well-foundedness. -/
instance (order : TermOrder) (n : Nat) : IsMonomialOrder (order.cmp n) := by
  cases order <;> dsimp [TermOrder.cmp] <;> infer_instance

/-- Representation errors are distinct from the caller's resource allowance. -/
inductive MonomialError where
  | arity | index | exponent | degree | address | storage
  | monomials | packedBytes | work
  deriving BEq, Repr

/-- Failed monomial operations retain their charged work, including validation
and collision scans before a representation or allocation bound is reached. -/
structure MonomialFailure where
  error : MonomialError
  work : Nat
  deriving BEq, Repr

/-- Cached degree, support mask and semantic hash occupy 24 bytes per monomial.
Operations require arenas and bucket identifiers produced by this API; raw
record fabrication does not establish these internal invariants. -/
structure MonomialTable where
  arity : Nat
  width : Width := .u8
  exponents : ByteArray := {}
  metadata : ByteArray := {}
  count : Nat := 0
  /-- Reusable prepared-coordinate buffer, included in packed payload bounds. -/
  workspace : ByteArray := {}
  index : MonomialIndex := {}
  /-- Reducing hash bits is useful for exact-collision conformance tests. -/
  hashBits : Nat := 64
  /-- Cumulative work: one unit per visited exponent or chain link, two per
  insertion, and `capacity + 3 * count` when rebuilding the packed index.
  Validation, preparation and widening each charge their exponent visits. -/
  work : Nat := 0

/-- Owned operations always return the table, on success and failure. This
avoids retaining a rollback alias while growing its packed buffers and index.
On failure, `MonomialFailure.work` is the full charged counter; `table.work`
retains the portable interning boundary's counter. -/
structure InternResult where
  result : Except MonomialFailure Nat
  table : MonomialTable

namespace MonomialTable

private def metaWord (bytes : @& ByteArray) (index : Nat) : UInt64 :=
  Packed.read64 bytes (index*8)

@[inline] private def reserve (arity : Nat) : Nat :=
  if arity > 0 && arity ≤ 4096 then arity * 4 + 28 else 0

@[inline] private def workspaceBytes (table : @& MonomialTable) : Nat :=
  max table.workspace.size (if table.count == 0 then 0 else reserve table.arity)

/-- Packed arenas plus a common workspace reservation in both backends. The
reservation begins with the first monomial and remains after a failed operation,
even if the physical workspace must be recreated. -/
@[inline] def bytes (table : @& MonomialTable) : Nat :=
  table.exponents.size + table.metadata.size + table.workspaceBytes + table.index.bytes

@[inline] private def shape (table : @& MonomialTable) : Bool :=
  table.exponents.size == table.count * table.arity * table.width.bytes &&
    table.metadata.size == table.count * 24 && table.index.shape table.count

private def push64 (bytes : ByteArray) (value : UInt64) : ByteArray :=
  Packed.push .u32 (Packed.push .u32 bytes (value &&& 0xffffffff)) (value >>> 32)

/-- Read one exponent; callers must supply valid identifiers and variable indices. -/
@[inline] def exponent (table : @& MonomialTable) (id coordinate : Nat) : UInt64 :=
  Packed.read table.width table.exponents (id * table.arity + coordinate)

/-- Cached total degree. -/
@[inline] def degree (table : @& MonomialTable) (id : Nat) : Nat :=
  (metaWord table.metadata (3 * id)).toNat

/-- Cached support mask. A failed subset test disproves divisibility. -/
@[inline] def mask (table : @& MonomialTable) (id : Nat) : UInt64 :=
  metaWord table.metadata (3 * id + 1)

/-- Cached hash, independent of the selected exponent width. -/
@[inline] def hashAt (table : @& MonomialTable) (id : Nat) : UInt64 :=
  metaWord table.metadata (3 * id + 2)

/-- Decode only at an interchange boundary. Hot operations read packed exponents. -/
def exponentsAt (table : MonomialTable) (id : Nat) : Array Nat :=
  (Array.range table.arity).map fun i => (table.exponent id i).toNat

/-- Exact divisibility after the cheap degree and support-mask filters. -/
def divides (table : @& MonomialTable) (a b : Nat) : Bool := Id.run do
  if a ≥ table.count || b ≥ table.count then return false
  if table.degree a > table.degree b || table.mask a &&& table.mask b != table.mask a then
    return false
  if let some result := Native.Monomial.divides table.width.bytes.toUInt8 table.arity a b table.exponents then
    return result
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
  if let some result := Native.Monomial.compare (order == .grevlex)
      table.width.bytes.toUInt8 table.arity a b table.exponents then return result
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

/-- Shared checked append for array and packed-coordinate interning. -/
@[specialize] private def append (table : MonomialTable) (width : Width)
    (degree mask hash : UInt64) (coordinate : Nat → UInt64)
    (work maxCount maxBytes maxWork : Nat) : InternResult := Id.run do
  if table.count ≥ maxCount then return ⟨.error ⟨.monomials, work⟩, table⟩
  if table.count + 1 > 4294967295 then return ⟨.error ⟨.index, work⟩, table⟩
  let size := (table.count + 1) * table.arity * width.bytes + (table.count + 1) * 24
  let peak := size + max table.workspace.size (reserve table.arity) + table.index.peak table.count +
    if width != table.width then table.exponents.size else 0
  if peak > maxBytes then return ⟨.error ⟨.packedBytes, work⟩, table⟩
  if peak ≥ USize.size then return ⟨.error ⟨.address, work⟩, table⟩
  let work := work + table.arity + table.index.work table.count +
    if width != table.width then table.count * table.arity else 0
  if work > maxWork then return ⟨.error ⟨.work, maxWork⟩, table⟩
  let table := if width == table.width then table else table.widen width
  let id := table.count
  let arity := table.arity
  let exponents := table.exponents
  let metadata := table.metadata
  let index := table.index
  -- Move mutable payloads out before growing them. The hash accessor borrows
  -- metadata only during reindexing, before its own append.
  let table := { table with exponents := {}, metadata := {}, index := {} }
  let index := index.insert id hash (fun i => metaWord metadata (3*i+2))
  let metadata := push64 (push64 (push64 metadata degree) mask) hash
  let mut exponents := exponents
  for i in [:arity] do exponents := Packed.push width exponents (coordinate i)
  return ⟨.ok id, { table with exponents, metadata, index, count := id + 1, work }⟩

/-- Hash-cons exponents with checked widening and exact collision handling.
The byte allowance bounds both old and new arenas during re-encoding, excluding
hash-table/array headers. The count allowance is checked before append. -/
def internOwned (table : MonomialTable) (values : Array UInt64)
    (maxCount maxBytes : Nat) (maxWork : Nat := 100000000) :
    InternResult := Id.run do
  if values.size != table.arity then return ⟨.error ⟨.arity, table.work⟩, table⟩
  if !table.shape then return ⟨.error ⟨.storage, table.work⟩, table⟩
  let mut work := table.work + values.size
  if work > maxWork then return ⟨.error ⟨.work, maxWork⟩, table⟩
  if table.bytes > maxBytes then return ⟨.error ⟨.packedBytes, work⟩, table⟩
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
  let mut link := table.index.head hash
  for _ in [:table.count] do
    if link == 0 then break
    let id := link - 1
    work := work + 1
    if work > maxWork then return ⟨.error ⟨.work, maxWork⟩, table⟩
    if id ≥ table.count then return ⟨.error ⟨.storage, work⟩, table⟩
    link := table.index.next id
    if table.hashAt id != hash then continue
    work := work + table.arity
    if work > maxWork then return ⟨.error ⟨.work, maxWork⟩, table⟩
    if id ≥ table.count then return ⟨.error ⟨.storage, work⟩, table⟩
    if table.equal id values then return ⟨.ok id, { table with work }⟩
  if link != 0 then return ⟨.error ⟨.storage, work⟩, table⟩
  return append table width degree.toUInt64 mask hash (fun i => values[i]!)
    work maxCount maxBytes maxWork

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
private def combinePortable (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes maxWork work : Nat) : InternResult := Id.run do
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

private def zeros (size : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity size
  for _ in [:size] do bytes := bytes.push 0
  return bytes

private def combinePacked (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes maxWork initialWork : Nat) : InternResult := Id.run do
  let mut work := initialWork
  let size := table.arity * 4 + 28
  let workspace := if table.workspace.size == size then table.workspace else zeros size
  -- Move the reusable buffer out before the native call, preserving ownership.
  let table := { table with workspace := {} }
  let code : UInt8 := match operation with | .lcm => 0 | .product => 1 | .quotient => 2
  let some prepared := Native.Monomial.prepare code table.width.bytes.toUInt8 table.arity.toUInt64
      table.count.toUInt64 a.toUInt64 b.toUInt64 table.exponents workspace
    | return ⟨.error ⟨.exponent, work⟩, table⟩
  -- Match the portable call's state when entering its intern operation.
  let table := { table with work }
  work := work + table.arity
  if work > maxWork then return ⟨.error ⟨.work, maxWork⟩, { table with workspace := prepared }⟩
  let degree := Packed.read64 prepared (table.arity * 4)
  let mask := Packed.read64 prepared ((table.arity + 2) * 4)
  let mut hash := Packed.read64 prepared ((table.arity + 4) * 4)
  let largest := Packed.read .u32 prepared (table.arity + 6)
  let width := if largest > 65535 then Width.u32 else
    if largest > 255 && table.width == .u8 then Width.u16 else table.width
  if table.hashBits < 64 then hash := hash &&& (((1 : UInt64) <<< table.hashBits.toUInt64) - 1)
  let mut link := table.index.head hash
  let mut remaining := table.count
  for _ in [:table.count+1] do
    let quantum := min remaining (4096 / table.arity)
    let found := Native.Monomial.search table.width.bytes.toUInt8 table.arity.toUInt64
      table.count.toUInt64 hash link.toUInt64 quantum.toUInt64 table.exponents
      table.metadata table.index.links prepared (maxWork-work)
    work := work + found.work
    if found.status == 1 then return ⟨.ok found.id, { table with work, workspace := prepared }⟩
    if found.status == 2 then
      link := 0
      break
    if found.status == 3 then return ⟨.error ⟨.work, maxWork⟩, { table with workspace := prepared }⟩
    if found.status == 4 then return ⟨.error ⟨.storage, work⟩, { table with workspace := prepared }⟩
    link := found.link
    remaining := remaining - quantum
    if remaining == 0 then break
  if link != 0 then return ⟨.error ⟨.storage, work⟩, { table with workspace := prepared }⟩
  return append { table with workspace := prepared } width degree mask hash
    (fun i => Packed.read .u32 prepared i) work maxCount maxBytes maxWork

/-- Portable packed operation used after a bounded native attempt defers. -/
def packedReference (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes maxWork work : Nat) : InternResult :=
  combinePacked table operation a b maxCount maxBytes maxWork work

/-- Packed native preparation and exact comparison for arities 1 through 4096.
Larger arities, zero variables and `native := false` retain the portable
coordinate-array route. A bounded workspace reservation is counted in both backends alongside the
arenas; exponent/degree overflow and collision handling remain exact. -/
def combineReference (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes : Nat) (maxWork : Nat := 100000000) (native := true) : InternResult :=
  if a ≥ table.count || b ≥ table.count then ⟨.error ⟨.index, table.work⟩, table⟩ else
  if !table.shape then ⟨.error ⟨.storage, table.work⟩, table⟩ else
  let work := table.work + table.arity
  if work > maxWork then ⟨.error ⟨.work, maxWork⟩, table⟩ else
  if table.bytes > maxBytes then ⟨.error ⟨.packedBytes, work⟩, table⟩ else
  if table.bytes ≥ USize.size then ⟨.error ⟨.address, work⟩, table⟩ else
  if native && table.arity > 0 && table.arity ≤ 4096 && table.count ≤ 4294967295 then
    packedReference table operation a b maxCount maxBytes maxWork work
  else combinePortable table operation a b maxCount maxBytes maxWork work

/-- A native attempt either completes the exact operation or returns its
unchanged input. Deferred reference work begins after the native call returns. -/
inductive Attempt where
  | accepted (result : InternResult)
  | deferred (table : MonomialTable)

/-- Portable model of the bounded native fast path. Eligibility is deliberately
restricted to successful operations whose complete reference state fits the
same exponent width, index capacity and bounded work quantum. -/
@[expose] def attemptPortable (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes maxWork : Nat) (native : Bool) : Attempt := Id.run do
  let small := fun n : Nat => n < USize.size / 2
  let shape := table.exponents.size == table.count * table.arity * table.width.bytes &&
    table.metadata.size == table.count * 24 && table.index.shape table.count
  if !native || !small table.arity || !small table.count || !small table.hashBits ||
      !small table.work || !small a || !small b || !small maxBytes || !small maxWork ||
      table.arity == 0 || table.arity > 2047 || table.count == 0 || table.count > 4294967295 ||
      table.hashBits > 64 || a ≥ table.count || b ≥ table.count || !shape ||
      table.work + table.arity > maxWork || table.bytes > maxBytes ||
      table.bytes + 1 ≥ USize.size then return .deferred table
  let outcome := table.combineReference operation a b maxCount maxBytes maxWork true
  match outcome.result with
  | .error _ => return .deferred table
  | .ok _ =>
    if outcome.table.width != table.width ||
        outcome.table.index.heads.size != table.index.heads.size ||
        outcome.table.work - (table.work + table.arity) > 4096 ||
        (outcome.table.count != table.count &&
          (!small maxCount || outcome.table.bytes + 1 ≥ USize.size)) then
      return .deferred table
    return .accepted outcome

/-- The reference model accepts exactly its reference outcome or defers the
unchanged table. Native conformance separately checks the C provider. -/
theorem attemptPortable_spec (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes maxWork : Nat) (native : Bool) :
    match attemptPortable table operation a b maxCount maxBytes maxWork native with
    | .accepted result => result = table.combineReference operation a b maxCount maxBytes maxWork true
    | .deferred returned => returned = table := by
  unfold attemptPortable
  simp only [Id.run, pure]
  split <;> rename_i h
  all_goals
    repeat' first | split at h | (cases h <;> rfl)

/-- Bounded native validation, exact lookup and insertion. All unsupported cases
return the original table for the caller's ordinary Lean reference computation. -/
@[extern "lean_hex_groebner_combine_owned"]
def attempt (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes maxWork : Nat) (native : Bool) : Attempt :=
  attemptPortable table operation a b maxCount maxBytes maxWork native

/-- Ownership-preserving operation with bounded native attempts and explicit
portable fallback outside the native frame. -/
def combineOwned (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes : Nat) (maxWork : Nat := 100000000) (native := true) : InternResult :=
  if !native then table.combineReference operation a b maxCount maxBytes maxWork false else
  match attempt table operation a b maxCount maxBytes maxWork true with
  | .accepted result => result
  | .deferred table => table.combineReference operation a b maxCount maxBytes maxWork native

/-- The executable wrapper retains the complete reference state and failure
contract. This proves the pure model; native provider equality is tested. -/
theorem combineOwned_spec (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes maxWork : Nat) (native : Bool) :
    combineOwned table operation a b maxCount maxBytes maxWork native =
      table.combineReference operation a b maxCount maxBytes maxWork native := by
  cases native with
  | false => rfl
  | true =>
    change (match attempt table operation a b maxCount maxBytes maxWork true with
      | .accepted result => result
      | .deferred returned => returned.combineReference operation a b maxCount maxBytes maxWork true) = _
    have contract := attemptPortable_spec table operation a b maxCount maxBytes maxWork true
    change (match attempt table operation a b maxCount maxBytes maxWork true with
      | .accepted result => result = table.combineReference operation a b maxCount maxBytes maxWork true
      | .deferred returned => returned = table) at contract
    cases h : attempt table operation a b maxCount maxBytes maxWork true with
    | accepted result => simpa only [h] using contract
    | deferred returned =>
      have eq : returned = table := by simpa only [h] using contract
      simp only [eq]

/-- info: 'Hex.Groebner.MonomialTable.combineOwned_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms combineOwned_spec

/-- Convenience projection of the ownership-preserving monomial operation. -/
def combine (table : MonomialTable) (operation : Operation) (a b : Nat)
    (maxCount maxBytes : Nat) (maxWork : Nat := 100000000) :
    Except MonomialFailure (Nat × MonomialTable) :=
  let outcome := combineOwned table operation a b maxCount maxBytes maxWork
  outcome.result.map fun id => (id, outcome.table)

end MonomialTable
end Hex.Groebner
