/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Monomial
public import HexGroebner.Elimination

public section

/-! Shared allowances for polynomial, symbolic and matrix work. Every nested
call consumes the remaining parent allowance; failures preserve charged work. -/

namespace Hex.Groebner

/-- Exact prime-field and variable/order identity for one computation. -/
structure Context where
  field : PrimeField
  variables : Nat
  order : TermOrder := .grevlex
  deriving DecidableEq

/-- One raw interchange term, with arbitrary-precision input exponents. -/
structure RawTerm where
  exponents : Array Nat
  coefficient : UInt64
  deriving Repr, BEq, Inhabited, Hashable

/-- A raw polynomial is normalized by combining repeated monomials. -/
abbrev RawPolynomial := Array RawTerm

/-- Internal packed polynomials require canonical coefficients and identifiers
from their associated workspace; raw construction does not enforce this invariant.
Supports use stable monomial identifiers in decreasing
mathematical order. Unlike matrix columns, identifiers need not be increasing. -/
structure Polynomial where
  support : ByteArray := {}
  coefficients : ByteArray := {}
  deriving Inhabited

/-- Number of terms in a canonical packed polynomial. -/
@[inline] def Polynomial.size (p : Polynomial) : Nat := p.support.size / 4

/-- Stable identifier of a term; callers supply an index below `size`. -/
@[inline] def Polynomial.monomial (p : @& Polynomial) (i : Nat) : Nat :=
  (Packed.read .u32 p.support i).toNat

/-- Canonical residue of a term. -/
@[inline] def Polynomial.coefficient (p : @& Polynomial) (field : PrimeField) (i : Nat) : UInt64 :=
  Packed.read field.width p.coefficients i

/-- Whole-computation resource categories. -/
inductive F4Resource where
  | work | packedBytes | monomials | pairs | rounds | matrixEntries | matrixRows | basis | variables
  deriving BEq, Repr

/-- Invalid input, representation exhaustion and consumed allowances are
distinct. Matrix errors indicate a broken invariant at the internal checked
matrix boundary. -/
inductive ComputeError where
  | arity (polynomial term : Nat)
  | coefficient (polynomial term : Nat)
  | representation (error : MonomialError)
  | exhausted (resource : F4Resource)
  | matrix (error : MatrixError)
  deriving BEq, Repr

/-- Deterministic critical-pair batching. Both orders break ties by stable
basis indices; propagated sugar labels remain available with either strategy. -/
inductive Scheduling where
  | degree | sugar
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Absolute cumulative allowances, also used when resuming a computation.
`packedBytes` counts monomial arenas and a common workspace reservation plus cumulative polynomial/matrix packed
payload, plus growth of the reusable symbolic support bitmap, including eight
logical bytes per reducer-cache insertion and
64 logical bytes per recorded row-derivation operation.
It excludes other object headers and allocator capacity. Pair attempts bound
pair metadata, including attempts in retried stages. The basis limit bounds
basis metadata. Work units include exponent visits,
hash operations, sort comparison reservations, scalar operations and the matrix
kernel's work units. No timing result is implied by these operational limits. -/
structure Limits where
  work : Nat := 100000000
  packedBytes : Nat := 256 * 1024 * 1024
  monomials : Nat := 1000000
  pairs : Nat := 1000000
  rounds : Nat := 10000
  matrixEntries : Nat := 10000000
  matrixRows : Nat := 10000000
  basis : Nat := 100000
  variables : Nat := 10000
  batchSize : Nat := 1024
  /-- Fixed when a computation starts; resumption retains the original choice. -/
  scheduling : Scheduling := .degree
  /-- Use bounded native row translation and elimination; false selects Lean models. -/
  nativeRows : Bool := true
  /-- Prepare checked dense M31 pivots in deterministic untraced matrices,
  within the parent work/memory bounds. Certificate and sampled routes retain
  their existing sparse pivots. -/
  densePivots : Bool := false
  /-- Optional private packed F2 pivots in bounded untraced matrix frames. -/
  binaryPivots : Bool := false
  /-- Use bounded packed monomial preparation and exact collision comparison. -/
  nativeMonomials : Bool := true
  /-- Enable minimal-LCM installation and proper-LCM chain pruning. -/
  gebauerMoller : Bool := true
  /-- Share symbolic preprocessing across independent final tail reductions. -/
  batchInterreduce : Bool := true
  deriving Inhabited

/-- Cumulative counters survive failure and resumption. -/
structure Statistics where
  work : Nat := 0
  allocatedBytes : Nat := 0
  pairs : Nat := 0
  rounds : Nat := 0
  matrixEntries : Nat := 0
  matrixRows : Nat := 0
  matrixCalls : Nat := 0
  /-- Targets in calls that reach the elimination kernel, including retried stages. -/
  matrixTargets : Nat := 0
  /-- Completed pivot applications, including charged prefixes of failed calls. -/
  matrixReductions : Nat := 0
  /-- Rows found zero, including empty inputs and failed-call prefixes.
  F4 symbolic reducers have distinct leading columns, so successful F4
  computations count zero rows only among targets. -/
  matrixZeroRows : Nat := 0
  /-- Largest number of reducer and target rows supplied to one matrix call. -/
  peakMatrixRows : Nat := 0
  /-- Largest logical validated input-plus-output entry count of one matrix call. -/
  peakMatrixEntries : Nat := 0
  /-- Largest selected critical-pair batch, including exhausted attempts. -/
  largestBatch : Nat := 0
  productPairs : Nat := 0
  chainPairs : Nat := 0
  gmPairs : Nat := 0
  deriving Repr, BEq, Inhabited

/-- Merge one matrix call's counters, preserving consumed prefixes on failure.
Input payload is already live; only workspace/output bytes are newly allocated. -/
@[inline] def Statistics.recordMatrix (s : Statistics) (stats : MatrixStats)
    (inputBytes rows targets : Nat) : Statistics := { s with
  work := s.work + stats.work
  allocatedBytes := s.allocatedBytes + (stats.packedBytes - inputBytes)
  matrixEntries := s.matrixEntries + stats.inputEntries + stats.outputEntries
  matrixRows := s.matrixRows + rows
  matrixCalls := s.matrixCalls + 1
  matrixTargets := s.matrixTargets + targets
  matrixReductions := s.matrixReductions + stats.reductions
  matrixZeroRows := s.matrixZeroRows + stats.zeroRows
  peakMatrixRows := max s.peakMatrixRows rows
  peakMatrixEntries := max s.peakMatrixEntries (stats.inputEntries + stats.outputEntries) }

/-- Reusable symbolic membership storage. Only the computation operations can
construct nonempty scratch, preserving that every marked bit has a queued ID. -/
structure SupportWorkspace where
  private mk ::
  bits : ByteArray
  queue : Array Nat

/-- Empty scratch can be supplied to any fresh or reset workspace. -/
def SupportWorkspace.empty : SupportWorkspace := ⟨{},#[]⟩

/-- Mutable logical workspace, separate from the immutable computation identity. -/
structure Workspace where
  table : MonomialTable
  statistics : Statistics := {}
  /-- Scratch survives checkpoints; its payload is charged only on growth. -/
  support : SupportWorkspace := .empty

/-- The shared bounded computation monad. -/
abbrev Computation := ExceptT ComputeError (StateM Workspace)

namespace Computation

/-- Charge work before executing a bounded block. -/
@[inline] def spend (limits : Limits) (amount : Nat) : Computation Unit := do
  let s ← get
  let work := s.statistics.work + amount
  if work > limits.work then throw (.exhausted .work)
  set { s with statistics.work := work }

/-- Reserve packed payload before allocation, including current monomial arenas. -/
def allocate (limits : Limits) (amount : Nat) : Computation Unit := do
  let s ← get
  let allocated := s.statistics.allocatedBytes + amount
  let total := allocated + s.table.bytes
  if total > limits.packedBytes then throw (.exhausted .packedBytes)
  if amount ≥ USize.size then throw (.representation .address)
  set { s with statistics.allocatedBytes := allocated }

/-- Move scratch buffers out of the state before calling an owned operation.
Invalid internal geometry discards scratch only; charged state is preserved. -/
private def supportStep (operation : ByteArray → Array Nat → Option (ByteArray × Array Nat)) :
    Computation Unit := ExceptT.mk fun state =>
  let bits := state.support.bits
  let queue := state.support.queue
  let state := { state with support := .empty }
  match operation bits queue with
  | some (bits,queue) => (.ok (),{ state with support := ⟨bits,queue⟩ })
  | none => (.error (.representation .index),state)

/-- Reset only the previous preparation's visited IDs. An exhausted attempt
retains both scratch buffers, so resumption reuses their paid-for payload. -/
def resetSupport (limits : Limits) : Computation Unit := do
  let count := (← get).support.queue.size
  spend limits count
  for chunk in [:(count+4095)/4096] do
    let start := chunk*4096
    let terms := min 4096 (count-start)
    supportStep fun bits queue => do
      let bits ← if limits.nativeMonomials then Native.Support.clear bits queue start terms
        else Native.Support.clearPortable bits queue start terms
      return (bits,queue)
  modify fun state => { state with support := ⟨state.support.bits,#[]⟩ }

/-- Queue each arena identifier once, growing the reusable bitmap only when
necessary. Growth and clearing work count against the parent allowances. -/
def queueSupport (limits : Limits) (support : ByteArray) : Computation Unit := do
  if support.size%4 != 0 then throw (.representation .index)
  if support.isEmpty then return
  let count := (← get).table.count
  let size := (count+7)/8
  if size ≥ USize.size then throw (.representation .address)
  let oldSize := (← get).support.bits.size
  if oldSize < size then
    let extra := size-oldSize
    spend limits extra
    allocate limits extra
    for chunk in [:(extra+4095)/4096] do
      let amount := min 4096 (extra-chunk*4096)
      supportStep fun bits queue => do
        let bits ← if limits.nativeMonomials then Native.Columns.zeros bits amount
          else Native.Columns.zerosPortable bits amount
        return (bits,queue)
  for chunk in [:((support.size/4)+4095)/4096] do
    let start := chunk*4096
    let terms := min 4096 ((support.size/4)-start)
    supportStep fun bits queue => if limits.nativeMonomials then
        Native.Support.queue count.toUInt64 support start terms bits queue
      else Native.Support.queuePortable count.toUInt64 support start terms bits queue

@[inline] private def tableError : MonomialError → ComputeError
  | .work => .exhausted .work
  | .monomials => .exhausted .monomials
  | .packedBytes => .exhausted .packedBytes
  | error => .representation error

private def tableResult (limits : Limits)
    (operation : MonomialTable → Nat → Nat → Nat → InternResult) : Computation Nat :=
  ExceptT.mk fun state =>
    let statistics := state.statistics
    let table := { state.table with work := statistics.work }
    let outcome := operation table limits.monomials
      (limits.packedBytes - statistics.allocatedBytes) limits.work
    match outcome.result with
    | .ok id =>
      (.ok id, { state with table := outcome.table, statistics := { statistics with work := outcome.table.work } })
    | .error failure =>
      let error := tableError failure.error
      (.error error, { state with table := outcome.table, statistics := { statistics with work := failure.work } })

/-- Multiply one support slice against the remaining parent allowance. Batch
failures retain the scalar table prefix and its separately charged failure work.
The caller reserves the complete output support before processing any slice. -/
def products (limits : Limits) (support : ByteArray) (monomial start count : Nat) :
    Computation ByteArray :=
  ExceptT.mk fun state =>
    let statistics := state.statistics
    let table := { state.table with work := statistics.work }
    let outcome := table.productsWith support monomial start count limits.monomials
      (limits.packedBytes-statistics.allocatedBytes) limits.work limits.nativeMonomials
    match outcome.result with
    | .ok support =>
      (.ok support, { state with table := outcome.table, statistics := { statistics with work := outcome.table.work } })
    | .error failure =>
      let error := tableError failure.error
      (.error error, { state with table := outcome.table, statistics := { statistics with work := failure.work } })

/-- Intern a raw monomial using the remaining shared allowance. -/
def intern (limits : Limits) (values : Array UInt64) : Computation Nat :=
  tableResult limits fun table count bytes work => table.internOwned values count bytes work

/-- Multiply, divide or take an LCM without wrapping exponents. -/
def combine (limits : Limits) (operation : MonomialTable.Operation) (a b : Nat) : Computation Nat :=
  tableResult limits fun table count bytes work => table.combineOwned operation a b count bytes work limits.nativeMonomials

/-- Exact multiplicative inverse, with all products charged to the parent. -/
def inverse (field : PrimeField) (limits : Limits) (a : UInt64) : Computation UInt64 := do
  if a == 1 then return 1
  let ctx := field.barrett
  let mut a := a
  let mut exponent := field.modulus.toNat - 2
  let mut result : UInt64 := 1
  for _ in [:field.modulus.toNat.log2 + 1] do
    if exponent == 0 then break
    if exponent % 2 == 1 then
      spend limits 1
      result := ctx.mulMod result a
    exponent := exponent / 2
    if exponent > 0 then
      spend limits 1
      a := ctx.mulMod a a
  return result

/-- Bottom-up stable merge sort of identifiers. Reserves the worst-case number
of exponent comparisons before sorting; it never allocates exponent vectors. -/
def sort (context : Context) (limits : Limits) (ids : Array Nat) : Computation (Array Nat) := do
  let table := (← get).table
  spend limits (ids.size * (ids.size.log2 + 1) * (context.variables + 1))
  let mut source := ids
  let mut destination := Array.replicate ids.size 0
  let mut width := 1
  for _ in [:ids.size.log2 + 1] do
    if width ≥ ids.size then break
    for block in [:((ids.size + 2 * width - 1) / (2 * width))] do
      let start := block * 2 * width
      let middle := min (start + width) ids.size
      let stop := min (start + 2 * width) ids.size
      let mut left := start
      let mut right := middle
      for out in [start:stop] do
        if left < middle && (right ≥ stop || table.compare context.order source[left]! source[right]! != .lt) then
          destination := destination.set! out source[left]!
          left := left + 1
        else
          destination := destination.set! out source[right]!
          right := right + 1
    let old := source
    source := destination
    destination := old
    width := width * 2
  return source

end Computation
end Hex.Groebner
