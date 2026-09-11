/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRank
import HexResultant.ExactDiv
import HexMvGcd
import Lean.Data.Json
import LeanBench

/-!
Benchmark registrations for `hex-rank`.

The input families follow `HexRank/SPEC/hex-rank.md §Benchmarking`, each
seeded and deterministic. Every family registers the producer's first pass
(`rowReduceWith`), the two-pass certificate (`rankCertWith`), and the checker
(`checkRank`, with certificate construction hoisted into `prep`) as separate
targets, so that the ratio between producer and checker is a recorded number.

Scientific registrations and declared models:

* `dense-full-rank`: square matrices of small random entries, rank `n`.
  Mode 2, one-sided upper bound `n^5`: the operation count is `Θ(n^3)` and
  every operand is a minor of size up to `n`, whose bit length grows
  linearly in `n` by Hadamard's bound, so the schoolbook cost of one
  operation is bounded by a further `n^2`.
* `low-rank-large-coefficients`: products of `n × r` and `r × n` matrices at
  fixed `r ∈ {2, 8}` with 64- and 1024-bit entries. Mode 1, `n^2`: the count
  is `Θ(r · n · n)` and every operand is a minor of size at most `r` of a
  matrix with entries of fixed bit size.
* `rank-deficient-by-construction`: square products of rank `n - 1` and
  `n / 2` with small entries, including a variant whose pivot columns are
  not the leading columns, so that the skip path is on the measured route.
  Mode 1, `n^3`: the count is `Θ(r · n · n)` with `r` proportional to `n`.
* `polynomial`: `DensePoly Rat` and `MvPoly 2 Int` matrices of small fixed
  support, full rank and rank deficient. Mode 3, fixed registrations.

The external comparators (FLINT `fmpz_mat.rank` and `fmpq_mat.rank`, SymPy
`DomainMatrix.rank` over the exact polynomial domain) are `informational`
per the SPEC and are not yet wired; the Phase 4 report will add them.
-/

namespace Hex.RankBench

open Hex Hex.Matrix

/-! Deterministic entry generators. -/

/-- A 64-bit linear congruential step. -/
def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Small entries in `[-5, 5]`. -/
def smallEntry (salt i j : Nat) : Int :=
  ((lcg (salt * 1000003 + i * 1009 + j) / 2 ^ 20) % 11 : Nat) - 5

/-- An entry of about `bits` bits, assembled from 60-bit chunks. -/
def bigEntry (bits salt i j : Nat) : Int :=
  let chunks := bits / 60 + 1
  let value := (List.range chunks).foldl
    (fun acc k => acc * 2 ^ 60 + lcg (salt * 7919 + i * 104729 + j * 1299709 + k) / 2 ^ 4) 0
  let value := value % 2 ^ bits
  if (i + j) % 2 = 0 then value else -value

/-! Inputs. Matrices are flattened row-major so the input types derive the
instances the bench harness needs; the matrix is rebuilt inside the timed
call, an `O(n · m)` copy that is dominated by the measured elimination. -/

/-- A flattened `n × m` integer matrix. -/
structure MatInput where
  n : Nat
  m : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- A flattened integer certificate, for the checker targets. -/
structure CertInput where
  mat : MatInput
  rank : Nat
  rows : Array Nat
  cols : Array Nat
  denom : Int
  adj : Array Int
  deriving Repr, BEq, Hashable

def matrixOfFlat (n m : Nat) (entries : Array Int) : Matrix Int n m :=
  Matrix.ofFn fun i j => entries.getD (i.val * m + j.val) 0

def flatOfMatrix {n m : Nat} (M : Matrix Int n m) : Array Int :=
  (M.rows.toArray.map fun row => row.toArray).flatten

def toMatInput {n m : Nat} (M : Matrix Int n m) : MatInput :=
  { n := n, m := m, entries := flatOfMatrix M }

def toCertInput {n m : Nat} (M : Matrix Int n m) : CertInput :=
  let c := rankCert M
  { mat := toMatInput M
    rank := c.rank
    rows := c.rows.toArray.map Fin.val
    cols := c.cols.toArray.map Fin.val
    denom := c.denom
    adj := flatOfMatrix c.adj }

/-- Rebuild the certificate of a flattened input. Every family has positive
dimensions; the empty shapes fall back to `none`. -/
def certOfInput (input : CertInput) : Option (RankCert Int input.mat.n input.mat.m) :=
  if hn : 0 < input.mat.n then
    if hm : 0 < input.mat.m then
      some
        { rank := input.rank
          rows := Vector.ofFn fun k => ⟨input.rows.getD k.val 0 % input.mat.n, Nat.mod_lt _ hn⟩
          cols := Vector.ofFn fun k => ⟨input.cols.getD k.val 0 % input.mat.m, Nat.mod_lt _ hm⟩
          denom := input.denom
          adj := matrixOfFlat input.rank input.rank input.adj }
    else none
  else none

/-! Families. Every generator fixes the rank by construction: a product of
unit triangular factors has determinant `1`, and a product `L * Rm` of an
`n × r` factor whose first `r` rows are the identity and an `r × n` factor
carrying an identity block has rank exactly `r`. Random products only bound
the rank from above. -/

/-- `dense-full-rank`: an `n × n` product of a unit lower and a unit upper
triangular matrix of small random entries, so `det = 1` and the rank is `n`. -/
def prepDense (n : Nat) : MatInput :=
  let L : Matrix Int n n := Matrix.ofFn fun i j =>
    if i = j then 1 else if j.val < i.val then smallEntry 1 i.val j.val else 0
  let U : Matrix Int n n := Matrix.ofFn fun i j =>
    if i = j then 1 else if i.val < j.val then smallEntry 2 i.val j.val else 0
  toMatInput (L * U)

/-- An `n × r` factor of rank `r`: the identity in its first `r` rows, `entry`
below. -/
def leftFactor (n r : Nat) (entry : Nat → Nat → Int) : Matrix Int n r :=
  Matrix.ofFn fun i j => if i.val < r then (if i.val = j.val then 1 else 0) else entry i.val j.val

/-- An `r × n` factor of rank `r`: zero in the first `shift` columns, the
identity in the next `r`, `entry` after them. With `shift > 0` the pivot
columns of the product are not its leading columns. -/
def rightFactor (r n shift : Nat) (entry : Nat → Nat → Int) : Matrix Int r n :=
  Matrix.ofFn fun i j =>
    if j.val < shift then 0
    else if j.val < shift + r then (if i.val + shift = j.val then 1 else 0)
    else entry i.val j.val

/-- `low-rank-large-coefficients`: an `n × n` product of rank `r` with entries
of `bits` bits. -/
def prepLowRank (r bits n : Nat) : MatInput :=
  toMatInput (leftFactor n r (bigEntry bits 3) * rightFactor r n 0 (bigEntry bits 5))

/-- `rank-deficient-by-construction`: an `n × n` product of rank `rankOf n`
with small entries; `shift` moves the pivot columns off the leading columns,
so that the skip path runs first. -/
def prepDeficient (rankOf : Nat → Nat) (shift : Bool) (n : Nat) : MatInput :=
  let r := rankOf n
  toMatInput
    (leftFactor n r (smallEntry 7) * rightFactor r n (if shift then n - r else 0) (smallEntry 11))

def prepDenseCert (n : Nat) : CertInput :=
  let input := prepDense n
  toCertInput (matrixOfFlat input.n input.m input.entries)
def prepLowRankCert (r bits n : Nat) : CertInput :=
  let input := prepLowRank r bits n
  toCertInput (matrixOfFlat input.n input.m input.entries)
def prepDeficientCert (rankOf : Nat → Nat) (shift : Bool) (n : Nat) : CertInput :=
  let input := prepDeficient rankOf shift n
  toCertInput (matrixOfFlat input.n input.m input.entries)

/-- The mode-2 upper bound `n^5 (log n + log B)^2` of the dense and
rank-deficient families, with `log B ≤ 3` for the small entries used. -/
def hadamardBound (n : Nat) : Nat :=
  n * n * n * n * n * (Nat.log2 n + 3) * (Nat.log2 n + 3)

/-! Targets. -/

def runRowReduce (input : MatInput) : Nat :=
  (rowReduceFF (matrixOfFlat input.n input.m input.entries)).profile.rank
def runRankCert (input : MatInput) : Nat :=
  (rankCert (matrixOfFlat input.n input.m input.entries)).rank
def runCheckRank (input : CertInput) : Bool :=
  match certOfInput input with
  | some c => checkRank (matrixOfFlat input.mat.n input.mat.m input.mat.entries) c
  | none => false

/-! Per-family bindings. -/

def prepLowRank2At64 := prepLowRank 2 64
def prepLowRank8At64 := prepLowRank 8 64
def prepLowRank2At1024 := prepLowRank 2 1024
def prepLowRank8At1024 := prepLowRank 8 1024
def prepLowRank2At64Cert := prepLowRankCert 2 64
def prepLowRank8At1024Cert := prepLowRankCert 8 1024
def prepDeficientMinusOne := prepDeficient (fun n => n - 1) false
def prepDeficientHalf := prepDeficient (fun n => n / 2) false
def prepDeficientHalfShifted := prepDeficient (fun n => n / 2) true
def prepDeficientMinusOneCert := prepDeficientCert (fun n => n - 1) false
def prepDeficientHalfShiftedCert := prepDeficientCert (fun n => n / 2) true

def runRowReduceDense := runRowReduce
def runRankCertDense := runRankCert
def runCheckRankDense := runCheckRank
def runRowReduceLowRank2At64 := runRowReduce
def runRowReduceLowRank8At64 := runRowReduce
def runRowReduceLowRank2At1024 := runRowReduce
def runRowReduceLowRank8At1024 := runRowReduce
def runRankCertLowRank2At64 := runRankCert
def runRankCertLowRank8At1024 := runRankCert
def runCheckRankLowRank2At64 := runCheckRank
def runCheckRankLowRank8At1024 := runCheckRank
def runRowReduceDeficientMinusOne := runRowReduce
def runRowReduceDeficientHalf := runRowReduce
def runRowReduceDeficientHalfShifted := runRowReduce
def runRankCertDeficientMinusOne := runRankCert
def runRankCertDeficientHalfShifted := runRankCert
def runCheckRankDeficientMinusOne := runCheckRank
def runCheckRankDeficientHalfShifted := runCheckRank

/-! `dense-full-rank`: `Θ(n^3)` operations on operands of `O(n (log n + log B))`
bits, so the declared one-sided upper bound is `n^5 (log n + log B)^2`
(mode 2). -/
-- Cost model: `Θ(n^3)` ring operations, each on operands of `O(n (log n + log B))`
-- bits by Hadamard's bound, at schoolbook cost quadratic in the bit size, so the
-- declared one-sided upper bound is `n^5 (log n + log B)^2` (mode 2); `B ≤ 8`
-- here, so `log B ≤ 3`.
setup_benchmark runRowReduceDense n => hadamardBound n
  with prep := prepDense
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 32, 64]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(n^3)` ring operations, each on operands of `O(n (log n + log B))`
-- bits by Hadamard's bound, at schoolbook cost quadratic in the bit size, so the
-- declared one-sided upper bound is `n^5 (log n + log B)^2` (mode 2); `B ≤ 8`
-- here, so `log B ≤ 3`.
setup_benchmark runRankCertDense n => hadamardBound n
  with prep := prepDense
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 32, 64]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(n^3)` ring operations, each on operands of `O(n (log n + log B))`
-- bits by Hadamard's bound, at schoolbook cost quadratic in the bit size, so the
-- declared one-sided upper bound is `n^5 (log n + log B)^2` (mode 2); `B ≤ 8`
-- here, so `log B ≤ 3`.
setup_benchmark runCheckRankDense n => hadamardBound n
  with prep := prepDenseCert
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 32, 64]
    maxSecondsPerCall := 3.0
  }

/-! `low-rank-large-coefficients`: `Θ(r · n · n)` operations at fixed `r` on
operands of fixed bit size, so the declared model is `n^2` (mode 1). -/
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRowReduceLowRank2At64 n => n * n
  with prep := prepLowRank2At64
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 32, 64, 128]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRowReduceLowRank8At64 n => n * n
  with prep := prepLowRank8At64
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 32, 64, 128]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRowReduceLowRank2At1024 n => n * n
  with prep := prepLowRank2At1024
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 32, 64, 128]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRowReduceLowRank8At1024 n => n * n
  with prep := prepLowRank8At1024
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 32, 64, 128]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRankCertLowRank2At64 n => n * n
  with prep := prepLowRank2At64
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 32, 64, 128]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRankCertLowRank8At1024 n => n * n
  with prep := prepLowRank8At1024
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 32, 64, 128]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runCheckRankLowRank2At64 n => n * n
  with prep := prepLowRank2At64Cert
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 32, 64, 128]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runCheckRankLowRank8At1024 n => n * n
  with prep := prepLowRank8At1024Cert
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 32, 64, 128]
    maxSecondsPerCall := 3.0
  }

/-! `rank-deficient-by-construction`: `Θ(r · n · n)` operations with `r`
proportional to `n`, on minors whose bit size grows linearly in `n`, so the
declared one-sided upper bound is `n^5 (log n + log B)^2` (mode 2). -/
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runRowReduceDeficientMinusOne n => hadamardBound n
  with prep := prepDeficientMinusOne
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 32, 64]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runRowReduceDeficientHalf n => hadamardBound n
  with prep := prepDeficientHalf
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 32, 64]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runRowReduceDeficientHalfShifted n => hadamardBound n
  with prep := prepDeficientHalfShifted
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 32, 64]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runRankCertDeficientMinusOne n => hadamardBound n
  with prep := prepDeficientMinusOne
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 32, 64]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runRankCertDeficientHalfShifted n => hadamardBound n
  with prep := prepDeficientHalfShifted
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 32, 64]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runCheckRankDeficientMinusOne n => hadamardBound n
  with prep := prepDeficientMinusOneCert
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 32, 64]
    maxSecondsPerCall := 3.0
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runCheckRankDeficientHalfShifted n => hadamardBound n
  with prep := prepDeficientHalfShiftedCert
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 32, 64]
    maxSecondsPerCall := 3.0
  }

/-! `polynomial`: fixed registrations (mode 3). Entries have support at most
two, so the cost of a minor depends on the support and no one-parameter
model is claimed. -/

def ratPolyEntry (i j : Nat) : DensePoly Rat :=
  DensePoly.ofList [(smallEntry 13 i j : Rat) / (1 + (i + j) % 3 : Nat), (smallEntry 17 i j : Rat)]

def ratPolyMatrix (k : Nat) : Matrix (DensePoly Rat) k k :=
  Matrix.ofFn fun i j => ratPolyEntry i.val j.val

def ratPolyDeficient (k : Nat) : Matrix (DensePoly Rat) k k :=
  let L : Matrix (DensePoly Rat) k (k / 2) := Matrix.ofFn fun i j => ratPolyEntry i.val (j.val + 7)
  let Rm : Matrix (DensePoly Rat) (k / 2) k := Matrix.ofFn fun i j => ratPolyEntry (i.val + 3) j.val
  L * Rm

def mvEntry (i j : Nat) : MvPoly 2 Int Mono.lex :=
  MvPoly.C (smallEntry 19 i j) + MvPoly.C (smallEntry 23 i j) * MvPoly.X ⟨(i + j) % 2, by omega⟩

def mvMatrix (k : Nat) : Matrix (MvPoly 2 Int Mono.lex) k k :=
  Matrix.ofFn fun i j => mvEntry i.val j.val

def mvDeficient (k : Nat) : Matrix (MvPoly 2 Int Mono.lex) k k :=
  let L : Matrix (MvPoly 2 Int Mono.lex) k (k / 2) :=
    Matrix.ofFn fun i j => mvEntry i.val (j.val + 5)
  let Rm : Matrix (MvPoly 2 Int Mono.lex) (k / 2) k :=
    Matrix.ofFn fun i j => mvEntry (i.val + 2) j.val
  L * Rm

def runRatPolyRankAt (k : Nat) : Unit → IO Nat :=
  let A := ratPolyMatrix k
  fun _ => return rankWith Hex.exactDiv A
def runRatPolyDeficientRankAt (k : Nat) : Unit → IO Nat :=
  let A := ratPolyDeficient k
  fun _ => return rankWith Hex.exactDiv A
def runRatPolyCertAt (k : Nat) : Unit → IO Nat :=
  let A := ratPolyMatrix k
  fun _ => return (rankCertWith Hex.exactDiv A).rank
/-- The checker alone: the certificate is built in the closure's preparation. -/
def runRatPolyCheckAt (k : Nat) : Unit → IO Bool :=
  let A := ratPolyMatrix k
  let c := rankCertWith Hex.exactDiv A
  fun _ => return checkRank A c
def runMvRankAt (k : Nat) : Unit → IO Nat :=
  let A := mvMatrix k
  fun _ => return rankWith Hex.exactDiv A
def runMvDeficientRankAt (k : Nat) : Unit → IO Nat :=
  let A := mvDeficient k
  fun _ => return rankWith Hex.exactDiv A
def runMvCertAt (k : Nat) : Unit → IO Nat :=
  let A := mvMatrix k
  fun _ => return (rankCertWith Hex.exactDiv A).rank
/-- The checker alone: the certificate is built in the closure's preparation. -/
def runMvCheckAt (k : Nat) : Unit → IO Bool :=
  let A := mvMatrix k
  let c := rankCertWith Hex.exactDiv A
  fun _ => return checkRank A c

def runRatPolyRank4 := runRatPolyRankAt 4
def runRatPolyRank8 := runRatPolyRankAt 8
def runRatPolyRank12 := runRatPolyRankAt 12
def runRatPolyDeficientRank8 := runRatPolyDeficientRankAt 8
def runRatPolyCert8 := runRatPolyCertAt 8
def runRatPolyCheck8 := runRatPolyCheckAt 8
def runMvRank4 := runMvRankAt 4
def runMvRank8 := runMvRankAt 8
def runMvDeficientRank8 := runMvDeficientRankAt 8
def runMvCert4 := runMvCertAt 4
def runMvCheck4 := runMvCheckAt 4

def polyConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 6.0, minTotalSeconds := 0.2, warmupFirstIter := true }

setup_fixed_benchmark runRatPolyRank4 where polyConfig
setup_fixed_benchmark runRatPolyRank8 where polyConfig
setup_fixed_benchmark runRatPolyRank12 where polyConfig
setup_fixed_benchmark runRatPolyDeficientRank8 where polyConfig
setup_fixed_benchmark runRatPolyCert8 where polyConfig
setup_fixed_benchmark runRatPolyCheck8 where polyConfig
setup_fixed_benchmark runMvRank4 where polyConfig
setup_fixed_benchmark runMvRank8 where polyConfig
setup_fixed_benchmark runMvDeficientRank8 where polyConfig
setup_fixed_benchmark runMvCert4 where polyConfig
setup_fixed_benchmark runMvCheck4 where polyConfig

end Hex.RankBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
