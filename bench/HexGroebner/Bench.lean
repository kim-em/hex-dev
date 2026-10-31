/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexArith.Montgomery.Context
import LeanBench

/-! Full-rank Hilbert matrices (a Cauchy family) exercise dense pivot tails.
Sparse rectangular matrices exercise known pivots and rank defects. Preparation
is excluded; validation, workspace allocation, elimination and output decoding
are included. Fixed cyclic and Katsura cases measure full F4 candidate production separately. -/

namespace Hex.Groebner.Bench

/-- A prime just above the 16-bit storage boundary. -/
def field : PrimeField :=
  ⟨65537, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩

/-- Immutable packed input, with the first half of the rows serving as reducers. -/
structure Input where
  columns : Nat
  reducers : Array SparseRow
  targets : Array SparseRow
  deriving Hashable

/-- Hilbert entries `1 / (i + j + 1)` over the prime field. For the registered
domain `2*n < p`, all square minors are nonzero. Every elimination update visits
a dense trailing support, without rank defects or accidental zero pivots. -/
def prepare (n : Nat) : Input := Id.run do
  let mut rows := #[]
  for i in [:n] do
    let mut row : SparseRow := {}
    for j in [:n] do
      let c := (HexArith.powMod (i + j + 1) 65535 65537).toUInt64
      row := {
        columns := Packed.push .u32 row.columns j.toUInt64
        coefficients := Packed.push .u32 row.coefficients c }
    rows := rows.push row
  return ⟨n, rows.extract 0 (n / 2), rows.extract (n / 2) n⟩

/-- Return the actual decoded result for structural hashing, including an
explicit failure flag. No parameter-only digest replaces the matrix output. -/
def cauchy (input : Input) : Bool × Array (Array (Nat × UInt64)) :=
  match (eliminateWith field { work := 1000000000 } input.columns input.reducers input.targets).result with
  | .ok e => (e.rows.size == input.columns, e.rows.map (·.row.entries field))
  | .error _ => (false, #[])

/-- Identical matrix/allowances with scalar Lean row updates. -/
def cauchyPortable (input : Input) : Bool × Array (Array (Nat × UInt64)) :=
  match (eliminateWith field { work := 1000000000 } input.columns input.reducers input.targets
      false #[] false).result with
  | .ok e => (e.rows.size == input.columns, e.rows.map (·.row.entries field))
  | .error _ => (false, #[])

private def wireOp : RowOp → Array UInt64
  | .input i => #[0, i.toUInt64]
  | .addScaled l r c => #[1, l.toUInt64, r.toUInt64, c]
  | .scale i c => #[2, i.toUInt64, c]

/-- The same dense elimination with shared provenance generation and full
structural hashing of the derivation as well as the decoded matrix. -/
def cauchyTrace (input : Input) :
    Bool × Array (Array (Nat × UInt64)) × Array (Array UInt64) :=
  match (eliminateWith field { work := 1000000000 } input.columns input.reducers input.targets true).result with
  | .ok e => (e.rows.size == input.columns, e.rows.map (·.row.entries field), e.trace.map wireOp)
  | .error _ => (false, #[], #[])

/-- Rectangular matrices with six nonzeros per row and a large zero prefix.
The targets duplicate the independent reducers, so their rank contribution is
zero. Nonunit leading coefficients exercise inversion and normalization; tails
overlap later pivots. Both dimensions grow with `n`, with fixed support size. -/
def prepareSparse (n : Nat) : Input := Id.run do
  let columns := n * 256
  let mut rows := #[]
  for i in [:n] do
    let first := columns / 2 + i * 4
    let mut row : SparseRow := {}
    for j in [:6] do
      row := {
        columns := Packed.push .u32 row.columns (first + j).toUInt64
        coefficients := Packed.push .u32 row.coefficients (j + 2).toUInt64 }
    rows := rows.push row
  return ⟨columns, rows, rows⟩

/-- Sparse supports reaching the final column expose the dense interval scan
cost independently of the clustered-support family. -/
def prepareSpread (n : Nat) : Input := Id.run do
  let columns := n * 256
  let mut rows := #[]
  for i in [:n] do
    let first := columns / 2 + i * 4
    let mut row : SparseRow := {}
    for (j, c) in #[(first, 2), (first + 1, 1), (columns - 1, 1)] do
      row := {
        columns := Packed.push .u32 row.columns j.toUInt64
        coefficients := Packed.push .u32 row.coefficients c }
    rows := rows.push row
  return ⟨columns, rows, rows⟩

/-- Sparse rank-deficient matrix output, structurally hashed. -/
def sparse (input : Input) : Bool × Array (Array (Nat × UInt64)) :=
  match (eliminateWith field { work := 1000000000 } input.columns input.reducers input.targets).result with
  | .ok e => (e.reducerRank == input.reducers.size && e.rows.size == e.reducerRank,
      e.rows.map (·.row.entries field))
  | .error _ => (false, #[])

#guard (cauchy (prepare 0)).1
#guard (cauchy (prepare 4)).1
#guard (cauchy (prepare 16)).1
#guard (cauchyTrace (prepare 16)).1
#guard (sparse (prepareSparse 16)).1
#guard (sparse (prepareSpread 16)).1

-- Independently derived model: n full-rank Cauchy rows encounter n monic pivots
-- with trailing supports of lengths n-j. Sum_i sum_{j<i} (n-j) = Theta(n^3)
-- fixed-word updates. Validation, dense scans, output decoding and structural
-- hashing each take O(n^2), and n bounded-exponent inversions take O(n).
setup_benchmark cauchy n => n * n * n
  with prep := prepare
  where {
    paramFloor := 32
    paramCeiling := 512
    paramSchedule := .custom #[32, 64, 128, 256, 512]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

-- The same cubic fixed-word updates as cauchy, plus O(n^2) shared trace
-- insertions and structural hashing. Amortized constant-time push is required;
-- copying the whole trace at each node would instead introduce O(n^4) work.
setup_benchmark cauchyTrace n => n * n * n
  with prep := prepare
  where {
    paramFloor := 32
    paramCeiling := 512
    paramSchedule := .custom #[32, 64, 128, 256, 512]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

-- Independently derived model: 256*n columns need O(n) workspace initialization
-- and one final pivot scan. Each of 2*n rows has six nonzeros. Reducers install
-- directly and targets cancel in one six-entry update, so validation, actual
-- support work, bounded inversion, decoding and structural hashing are O(n).
setup_benchmark sparse n => n
  with prep := prepareSparse
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 64, 128, 256]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

/-- Identical sparse matrix/allowances with scalar Lean row updates. -/
def sparsePortable (input : Input) : Bool × Array (Array (Nat × UInt64)) :=
  match (eliminateWith field { work := 1000000000 } input.columns input.reducers input.targets
      false #[] false).result with
  | .ok e => (e.reducerRank == input.reducers.size && e.rows.size == e.reducerRank,
      e.rows.map (·.row.entries field))
  | .error _ => (false, #[])

-- The same exact (n^3-n)/3 updates and O(n^2) validation/scans/output as cauchy.
setup_benchmark cauchyPortable n => n * n * n
  with prep := prepare
  where {
    paramFloor := 32
    paramCeiling := 512
    paramSchedule := .custom #[32, 64, 128, 256, 512]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

-- The same O(n) initialized bytes and six nonzeros per row as sparse.
setup_benchmark sparsePortable n => n
  with prep := prepareSparse
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 64, 128, 256]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

/-- The sparse runner applied to the spread-support family. -/
def spread (input : Input) : Bool × Array (Array (Nat × UInt64)) := sparse input

-- Independently derived model: n dependent targets have three stored entries
-- each, but their active interval reaches the final column among 256*n columns.
-- They inspect Theta(n^2) positions in total, despite cancelling to zero after
-- one sparse update. Setup, normalization, decoding and hashing are only O(n).
setup_benchmark spread n => n * n
  with prep := prepareSpread
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 64, 128, 256]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

/-- Append-only monomial hash-consing, including exponent-width changes and a
structural hash of the complete packed arena and metadata. -/
def internMonomials (n : Nat) : Bool × Nat × ByteArray × ByteArray := Id.run do
  let mut table : MonomialTable := { arity := 3 }
  for i in [:n] do
    let outcome := table.internOwned #[i.toUInt64, (i % 17).toUInt64, (i % 31).toUInt64]
      (n + 1) 1000000000 1000000000
    table := outcome.table
    match outcome.result with
    | .error _ => return (false, 0, {}, {})
    | .ok id =>
      if id != i then return (false, 0, {}, {})
  return (true, table.width.bytes, table.exponents, table.metadata)

-- Expected amortized work: n hash-cons insertions at fixed arity, exact
-- collision checks, and geometrically growing arenas take O(n); each width
-- transition re-encodes at most the current arena once. Hashing all logical
-- output bytes is also O(n). Hash collisions retain exact comparisons.
setup_benchmark internMonomials n => n
  where {
    paramFloor := 2048
    paramCeiling := 32768
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 4000000000
  }

private def term (p : UInt64) (coefficient : Int) (exponents : Array Nat) : RawTerm :=
  ⟨exponents, (coefficient % (p.toNat : Int)).toNat.toUInt64⟩

/-- Standard cyclic polynomial systems, without added field equations. -/
def cyclic (n : Nat) : Array RawPolynomial := Id.run do
  let mut generators := #[]
  for length in [1:n] do
    let mut polynomial := #[]
    for start in [:n] do
      let mut powers := Array.replicate n 0
      for offset in [:length] do powers := powers.modify ((start + offset) % n) (· + 1)
      polynomial := polynomial.push (term field.modulus 1 powers)
    generators := generators.push polynomial
  generators := generators.push #[term field.modulus 1 (Array.replicate n 1),
    term field.modulus (-1) (Array.replicate n 0)]
  return generators

/-- Standard Katsura-n system in n+1 variables, with the symmetric convolution
written as raw terms so duplicate coefficients are normalized by the entry API. -/
def katsura (n : Nat) : Array RawPolynomial := Id.run do
  let size := n + 1
  let mut linear := #[term field.modulus (-1) (Array.replicate size 0)]
  for i in [:size] do
    linear := linear.push (term field.modulus (if i == 0 then 1 else 2)
      ((Array.replicate size 0).set! i 1))
  let mut generators := #[linear]
  for m in [:n] do
    let mut polynomial := #[term field.modulus (-1) ((Array.replicate size 0).set! m 1)]
    for k in [:2 * n + 1] do
      let i : Int := (k : Int) - n
      let j : Int := (m : Int) - i
      if j.natAbs ≤ n then
        let powers := ((Array.replicate size 0).modify i.natAbs (· + 1)).modify j.natAbs (· + 1)
        polynomial := polynomial.push (term field.modulus 1 powers)
    generators := generators.push polynomial
  return generators

/-- Reimer-n with alternating ±2 pure powers of degrees 2 through n+1. -/
private def reimer (n : Nat) : Array RawPolynomial := Id.run do
  let mut generators := #[]
  for degree in [2:n + 2] do
    let mut polynomial := #[]
    for coordinate in [:n] do
      let powers := (Array.replicate n 0).set! coordinate degree
      polynomial := polynomial.push ⟨powers, if coordinate % 2 == 0 then 2 else field.modulus - 2⟩
    polynomial := polynomial.push ⟨Array.replicate n 0, field.modulus - 1⟩
    generators := generators.push polynomial
  return generators

initialize reimer5Input : IO.Ref (Array RawPolynomial) ← IO.mkRef (reimer 5)

initialize cyclic4Input : IO.Ref (Array RawPolynomial) ← IO.mkRef (cyclic 4)
initialize cyclic5Input : IO.Ref (Array RawPolynomial) ← IO.mkRef (cyclic 5)
initialize cyclic6Input : IO.Ref (Array RawPolynomial) ← IO.mkRef (cyclic 6)
initialize katsura3Input : IO.Ref (Array RawPolynomial) ← IO.mkRef (katsura 3)

private def compute (variables : Nat) (input : Array RawPolynomial) (nativeRows := true) (gebauerMoller := true) (batchInterreduce := true) (nativeMonomials := true) : IO (Array RawPolynomial) := do
  match computeWith ⟨field, variables, .grevlex⟩ { nativeRows, gebauerMoller, batchInterreduce, nativeMonomials, work := 1000000000 } input with
  | .candidate candidate _ => return candidate.polynomials
  | .exhausted r _ => throw (IO.userError s!"F4 exhausted {reprStr r}")
  | .representation r _ => throw (IO.userError s!"F4 representation {reprStr r}")
  | .internal e _ => throw (IO.userError s!"F4 internal {reprStr e}")
  | .invalid e _ => throw (IO.userError s!"F4 invalid {reprStr e}")

/-- Candidate-only cyclic-4; input generation is excluded, canonicalization and
final interreduction included. IO.Ref reads prevent cached pure results. -/
def cyclic4 (_ : Unit) : IO (Array RawPolynomial) := do compute 4 (← cyclic4Input.get)

/-- Candidate-only cyclic-5 under the same field, order and output contract. -/
def cyclic5 (_ : Unit) : IO (Array RawPolynomial) := do compute 5 (← cyclic5Input.get)

/-- Candidate-only cyclic-6, with a larger matrix/pair sequence. -/
def cyclic6 (_ : Unit) : IO (Array RawPolynomial) := do compute 6 (← cyclic6Input.get)

/-- Identical cyclic-6 candidate call using scalar Lean row updates. -/
def cyclic6Portable (_ : Unit) : IO (Array RawPolynomial) := do compute 6 (← cyclic6Input.get) (nativeRows := false)

/-- Candidate-only Katsura-3 under the same field, order and output contract. -/
def katsura3 (_ : Unit) : IO (Array RawPolynomial) := do compute 4 (← katsura3Input.get)

/-- Cyclic-5 reference using only product/resolved chain criteria. -/
def cyclic5Buchberger (_ : Unit) : IO (Array RawPolynomial) := do
  compute 5 (← cyclic5Input.get) (gebauerMoller := false)

/-- Cyclic-6 reference under identical input, arithmetic and resource allowances. -/
def cyclic6Buchberger (_ : Unit) : IO (Array RawPolynomial) := do
  compute 6 (← cyclic6Input.get) (gebauerMoller := false)

/-- Katsura-3 reference without Gebauer–Möller pruning. -/
def katsura3Buchberger (_ : Unit) : IO (Array RawPolynomial) := do
  compute 4 (← katsura3Input.get) (gebauerMoller := false)

/-- Reimer-5 candidate with the full input and output contract. -/
def reimer5 (_ : Unit) : IO (Array RawPolynomial) := do compute 5 (← reimer5Input.get)

/-- Reimer-5 reference without Gebauer–Möller pruning. -/
def reimer5Buchberger (_ : Unit) : IO (Array RawPolynomial) := do
  compute 5 (← reimer5Input.get) (gebauerMoller := false)

/-- Identical cyclic5 candidate using separate final tail reductions. -/
def cyclic5Separate (_ : Unit) : IO (Array RawPolynomial) := do
  compute 5 (← cyclic5Input.get) (batchInterreduce := false)

/-- Identical cyclic6 candidate using separate final tail reductions. -/
def cyclic6Separate (_ : Unit) : IO (Array RawPolynomial) := do
  compute 6 (← cyclic6Input.get) (batchInterreduce := false)

/-- Identical katsura3 candidate using separate final tail reductions. -/
def katsura3Separate (_ : Unit) : IO (Array RawPolynomial) := do
  compute 4 (← katsura3Input.get) (batchInterreduce := false)

/-- Identical reimer5 candidate using separate final tail reductions. -/
def reimer5Separate (_ : Unit) : IO (Array RawPolynomial) := do
  compute 5 (← reimer5Input.get) (batchInterreduce := false)

/-- Identical cyclic5 candidate using portable coordinate-array monomial operations. -/
def cyclic5Arrays (_ : Unit) : IO (Array RawPolynomial) := do
  compute 5 (← cyclic5Input.get) (nativeMonomials := false)

/-- Identical cyclic6 candidate using portable coordinate-array monomial operations. -/
def cyclic6Arrays (_ : Unit) : IO (Array RawPolynomial) := do
  compute 6 (← cyclic6Input.get) (nativeMonomials := false)

/-- Identical katsura3 candidate using portable coordinate-array monomial operations. -/
def katsura3Arrays (_ : Unit) : IO (Array RawPolynomial) := do
  compute 4 (← katsura3Input.get) (nativeMonomials := false)

/-- Identical reimer5 candidate using portable coordinate-array monomial operations. -/
def reimer5Arrays (_ : Unit) : IO (Array RawPolynomial) := do
  compute 5 (← reimer5Input.get) (nativeMonomials := false)

-- Fixed full-system calls make no polynomial-time claim in variable count.
-- Every registration hashes the full canonical basis and reports exhaustion as
-- a failed call. Certification and kernel checking are not performed here.
setup_fixed_benchmark cyclic4 where { repeats := 5 }
setup_fixed_benchmark cyclic5 where { repeats := 5 }
setup_fixed_benchmark cyclic6 where { repeats := 5 }
setup_fixed_benchmark cyclic6Portable where { repeats := 5 }
setup_fixed_benchmark katsura3 where { repeats := 5 }
setup_fixed_benchmark cyclic5Buchberger where { repeats := 5 }
setup_fixed_benchmark cyclic6Buchberger where { repeats := 5 }
setup_fixed_benchmark katsura3Buchberger where { repeats := 5 }
setup_fixed_benchmark reimer5 where { repeats := 5 }
setup_fixed_benchmark reimer5Buchberger where { repeats := 5 }

setup_fixed_benchmark cyclic5Separate where { repeats := 5 }
setup_fixed_benchmark cyclic6Separate where { repeats := 5 }
setup_fixed_benchmark katsura3Separate where { repeats := 5 }
setup_fixed_benchmark reimer5Separate where { repeats := 5 }

setup_fixed_benchmark cyclic5Arrays where { repeats := 5 }
setup_fixed_benchmark cyclic6Arrays where { repeats := 5 }
setup_fixed_benchmark katsura3Arrays where { repeats := 5 }
setup_fixed_benchmark reimer5Arrays where { repeats := 5 }

end Hex.Groebner.Bench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
