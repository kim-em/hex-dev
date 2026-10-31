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

/-- Absolute cumulative allowances, also used when resuming a computation.
`packedBytes` counts monomial arenas plus cumulative polynomial/matrix packed
payload. It excludes object headers and allocator capacity. Pair attempts bound
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
  batchSize : Nat := 64
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
  productPairs : Nat := 0
  chainPairs : Nat := 0
  deriving Repr, Inhabited

/-- Mutable logical workspace, separate from the immutable computation identity. -/
structure Workspace where
  table : MonomialTable
  statistics : Statistics := {}

/-- The shared bounded computation monad. -/
abbrev Computation := ExceptT ComputeError (StateM Workspace)

namespace Computation

/-- Charge work before executing a bounded block. -/
def spend (limits : Limits) (amount : Nat) : Computation Unit := do
  let s ← get
  let work := s.statistics.work + amount
  if work > limits.work then throw (.exhausted .work)
  set { s with statistics.work := work }

/-- Reserve packed payload before allocation, including current monomial arenas. -/
def allocate (limits : Limits) (amount : Nat) : Computation Unit := do
  let s ← get
  let allocated := s.statistics.allocatedBytes + amount
  let total := allocated + s.table.exponents.size + s.table.metadata.size
  if total > limits.packedBytes then throw (.exhausted .packedBytes)
  if total ≥ USize.size then throw (.representation .address)
  set { s with statistics.allocatedBytes := allocated }

private def tableResult (limits : Limits)
    (operation : MonomialTable → Nat → Nat → Nat → InternResult) : Computation Nat :=
  ExceptT.mk fun state =>
    let statistics := state.statistics
    let table := { state.table with work := statistics.work }
    let outcome := operation table limits.monomials
      (limits.packedBytes - statistics.allocatedBytes) limits.work
    match outcome.result with
    | .ok id =>
      (.ok id, ⟨outcome.table, { statistics with work := outcome.table.work }⟩)
    | .error failure =>
      let error := match failure.error with
        | .work => ComputeError.exhausted .work
        | .exhausted => if outcome.table.count ≥ limits.monomials then
            ComputeError.exhausted .monomials else .exhausted .packedBytes
        | e => ComputeError.representation e
      (.error error, ⟨outcome.table, { statistics with work := failure.work }⟩)

/-- Intern a raw monomial using the remaining shared allowance. -/
def intern (limits : Limits) (values : Array UInt64) : Computation Nat :=
  tableResult limits fun table count bytes work => table.internOwned values count bytes work

/-- Multiply, divide or take an LCM without wrapping exponents. -/
def combine (limits : Limits) (operation : MonomialTable.Operation) (a b : Nat) : Computation Nat :=
  tableResult limits fun table count bytes work => table.combineOwned operation a b count bytes work

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
