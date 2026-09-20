/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRank
import HexRank.Bench.Quotient
import HexBasic.Rand
import Hex.BenchOracle.Flint
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

Scientific integer parameters are 16, 24, 32, 48, 64, 96, 128, 192, 256,
with six trial-major outer trials. Preparation validates rank and certificates;
shifted fixtures validate the first pivot after their zero-column prefix.

* `dense-full-rank`: splitmix64 entries in `[-5,5]`, checked full rank.
  Mode 2, `hadamardBound n`: arbitrary growing minors and GMP's changing
  arithmetic regimes prevent a tight family-specific time power law.
* `low-rank-large-coefficients`: products of dense factors with fixed
  `r ∈ {2,8}` and factor bit sizes 64 or 1024. Mode 1, `n * n`: both
  operand sizes and r are independent of n.
* `rank-deficient-by-construction`: dense products with r=n-1 or n/2,
  including a zero-column prefix variant. Mode 2, `productBound n`,
  accounting for both growing minors and the product entry bound B≤25n.
* `polynomial`: `DensePoly Rat` and `MvPoly 2 Int` at fixed small support,
  full rank and deficient. Fixed registrations use the recorded comparator-derived absolute budgets.

The external comparators (FLINT `fmpz_mat.rank` and `fmpq_mat.rank`, SymPy
`DomainMatrix.rank` over the exact polynomial domain) are `informational`
per the SPEC. Their fixed shared-input anchors are tagged `comparison`;
external anchors are scheduled-only and excluded from default verification.
-/

namespace Hex.RankBench

open Hex Hex.Matrix

/-! Deterministic entry generators. -/

/-- A 64-bit linear congruential step. -/
def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Small entries in `[-5, 5]`. -/
def smallEntry (salt i j : Nat) : Int :=
  ((lcg (salt * 1000003 + i * 1009 + j) / 2 ^ 20) % 11 : Nat) - 5

/-- Small integer entries use splitmix64, independently of the polynomial
fixtures' retained LCG. The seed and coordinates determine every entry. -/
def intEntry (salt i j : Nat) : Int :=
  (((Rand.ofSeed (salt * 1000003 + i * 1009 + j)).next.1.toNat % 11 : Nat) : Int) - 5

/-- Signed large entries from splitmix64 words, with exactly `bits` bits in
absolute value when `bits > 0`. Factor size is independent of the dimension. -/
def bigEntry (bits salt i j : Nat) : Int :=
  let words := (Rand.ofSeed (salt * 7919 + i * 104729 + j * 1299709)).words ((bits + 63) / 64)
  let value := words.1 % 2 ^ bits
  let value := if bits == 0 then 0 else value ||| (1 <<< (bits - 1))
  if (i + j) % 2 = 0 then (value : Int) else -(value : Int)

/-! Inputs. Matrices are flattened row-major so the input types derive the
instances the bench harness needs; the matrix is rebuilt inside the timed
call, an `O(n · m)` copy that is dominated by the measured elimination. -/

/-- A flattened `n × m` integer matrix. -/
structure MatInput where
  n : Nat
  m : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable, Inhabited

/-- A flattened integer certificate, for the checker targets. -/
structure CertInput where
  mat : MatInput
  rank : Nat
  rows : Array Nat
  cols : Array Nat
  denom : Int
  adj : Array Int
  deriving Repr, BEq, Hashable, Inhabited

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
  if input.mat.entries.size != input.mat.n * input.mat.m ||
      input.rows.size != input.rank || input.cols.size != input.rank ||
      input.adj.size != input.rank * input.rank ||
      !input.rows.all (· < input.mat.n) || !input.cols.all (· < input.mat.m) then none
  else if hn : 0 < input.mat.n then
    if hm : 0 < input.mat.m then
      some
        { rank := input.rank
          rows := Vector.ofFn fun k => ⟨input.rows.getD k.val 0 % input.mat.n, Nat.mod_lt _ hn⟩
          cols := Vector.ofFn fun k => ⟨input.cols.getD k.val 0 % input.mat.m, Nat.mod_lt _ hm⟩
          denom := input.denom
          adj := matrixOfFlat input.rank input.rank input.adj }
    else none
  else none

/-! Integer scientific fixtures. Preparation checks the expected rank and
certificate. The shifted family also checks that the first pivot follows the
prescribed zero-column prefix. Verification's parameters 0 and 1 use n=16;
scientific parameters are unchanged. -/

/-- Fail a benchmark child on a malformed family rather than time the wrong
rank. This work is forced by the harness before its timed loop. -/
def checkedCert (expected shift : Nat) (input : MatInput) : CertInput :=
  let A := matrixOfFlat input.n input.m input.entries
  let c := rankCert A
  if c.rank == expected && checkRank A c &&
      (shift == 0 || c.cols.toArray[0]?.map Fin.val == some shift) then
    { mat := input, rank := c.rank, rows := c.rows.toArray.map Fin.val,
      cols := c.cols.toArray.map Fin.val, denom := c.denom, adj := flatOfMatrix c.adj }
  else panic! s!"integer fixture: expected rank {expected}, first pivot {shift}, got rank {c.rank}"

/-- Dense square matrix with entries in `[-5,5]`. Full rank is checked in prep,
not obtained by prescribing a unit triangular factorization. -/
def prepDenseCert (param : Nat) : CertInput :=
  let n := max 16 param
  checkedCert n 0 <| toMatInput <|
    (Matrix.ofFn fun i j => intEntry 1 i.val j.val : Matrix Int n n)

/-- A dense n by r factor; its product's exact rank is checked in prep. -/
def leftFactor (n r : Nat) (entry : Nat → Nat → Int) : Matrix Int n r :=
  Matrix.ofFn fun i j => entry i.val j.val

/-- A dense r by n factor with a prescribed zero-column prefix. No identity
pivot block is inserted: the elimination must compute nontrivial minors. -/
def rightFactor (r n shift : Nat) (entry : Nat → Nat → Int) : Matrix Int r n :=
  Matrix.ofFn fun i j => if j.val < shift then 0 else entry i.val j.val

/-- Fixed-rank product. Factors have `bits`-bit entries; matrix entries can
have up to `2 * bits + ceil(log₂ r)` bits. -/
def prepLowRankCert (r bits param : Nat) : CertInput :=
  let n := max 16 param
  checkedCert r 0 <| toMatInput
    (leftFactor n r (bigEntry bits 3) * rightFactor r n 0 (bigEntry bits 5))

/-- Variable-rank product of small factors, with entries bounded by 25r. -/
def prepDeficientCert (rankOf : Nat → Nat) (shifted : Bool) (param : Nat) : CertInput :=
  let n := max 16 param
  let r := rankOf n
  let shift := if shifted then n - r else 0
  checkedCert r shift <| toMatInput
    (leftFactor n r (intEntry 7) * rightFactor r n shift (intEntry 11))

def prepDense (n : Nat) : MatInput := (prepDenseCert n).mat
def prepLowRank (r bits n : Nat) : MatInput := (prepLowRankCert r bits n).mat
def prepDeficient (rankOf : Nat → Nat) (shift : Bool) (n : Nat) : MatInput :=
  (prepDeficientCert rankOf shift n).mat

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

/-- A checked canonical polynomial input. Construction and validation run once
per child, in the fixed runner's `warmupFirstIter` call, before timing. -/
structure PolyInput (R : Type) where
  dim : Nat
  matrix : Matrix R dim dim
  cert : RankCert R dim dim

initialize ratPolyInputs : IO.Ref (Array (Nat × Bool × PolyInput (DensePoly Rat))) ← IO.mkRef #[]
initialize mvInputs : IO.Ref (Array (Nat × Bool × PolyInput (MvPoly 2 Int Mono.lex))) ← IO.mkRef #[]

/-- Cache the actual matrix and certificate, rather than a closure whose pure
captures the compiler can move into each invocation. A bad fixture fails the
child before any sample is accepted. -/
def preparePoly [Lean.Grind.CommRing R] [DecidableEq R]
    (cache : IO.Ref (Array (Nat × Bool × PolyInput R)))
    (quot : R → R → R) (full deficient : (k : Nat) → Matrix R k k)
    (k : Nat) (singular : Bool) : IO (PolyInput R) := do
  if let some (_, _, input) := (← cache.get).find? (fun (n, d, _) => n == k && d == singular) then
    return input
  let A := if singular then deficient k else full k
  let c := rankCertWith quot A
  let expected := if singular then k / 2 else k
  unless c.rank == expected && checkRank A c do
    throw <| IO.userError s!"polynomial fixture: dimension {k}, deficient {singular}, expected rank {expected}, got {c.rank}"
  let input := PolyInput.mk k A c
  cache.modify (·.push (k, singular, input))
  return input

def prepareRatPoly := preparePoly ratPolyInputs Hex.exactDiv ratPolyMatrix ratPolyDeficient
def prepareMv := preparePoly mvInputs Hex.exactDiv mvMatrix mvDeficient



/-- Hadamard (Bareiss 1968, SPEC Complexity): n³ operations on
O(n(log n + log B))-bit integers, with schoolbook quadratic arithmetic.
For dense entries B ≤ 5, this gives O(n⁵(log n + 3)²). -/
def hadamardBound (n : Nat) : Nat :=
  n * n * n * n * n * (Nat.log2 n + 3) * (Nat.log2 n + 3)

/-- Product entries satisfy B ≤ 25r ≤ 25n, so the same published bound
has log n + log B = O(2 log n + 5). The random pivot blocks have growing
minors; a tight bit-cost power law is not assumed for GMP. -/
def productBound (n : Nat) : Nat :=
  n * n * n * n * n * (2 * Nat.log2 n + 5) * (2 * Nat.log2 n + 5)

/-! Targets. -/

def runRowReduce (input : MatInput) : Nat :=
  (rowReduceFF (matrixOfFlat input.n input.m input.entries)).profile.rank
def runRankCert (input : MatInput) : Nat :=
  (rankCert (matrixOfFlat input.n input.m input.entries)).rank
def runCheckRank (input : CertInput) : Bool :=
  match certOfInput input with
  | some c =>
    if checkRank (matrixOfFlat input.mat.n input.mat.m input.mat.entries) c then true
    else panic! "integer checker rejected its prepared certificate"
  | none => panic! "malformed flattened integer certificate"

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
-- declared one-sided upper bound is `O(n^5 (log n + 3)^2)` (mode 2):
-- dense entries satisfy `B ≤ 5`, independently of n.
setup_benchmark runRowReduceDense n => hadamardBound n
  with prep := prepDense
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(n^3)` ring operations, each on operands of `O(n (log n + log B))`
-- bits by Hadamard's bound, at schoolbook cost quadratic in the bit size, so the
-- declared one-sided upper bound is `O(n^5 (log n + 3)^2)` (mode 2):
-- dense entries satisfy `B ≤ 5`, independently of n.
setup_benchmark runRankCertDense n => hadamardBound n
  with prep := prepDense
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(n^3)` ring operations, each on operands of `O(n (log n + log B))`
-- bits by Hadamard's bound, at schoolbook cost quadratic in the bit size, so the
-- declared one-sided upper bound is `O(n^5 (log n + 3)^2)` (mode 2):
-- dense entries satisfy `B ≤ 5`, independently of n.
setup_benchmark runCheckRankDense n => hadamardBound n
  with prep := prepDenseCert
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

/-! `low-rank-large-coefficients`: `Θ(r · n · n)` operations at fixed `r` on
operands of fixed bit size, so the declared model is `n^2` (mode 1). -/
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRowReduceLowRank2At64 n => n * n
  with prep := prepLowRank2At64
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRowReduceLowRank8At64 n => n * n
  with prep := prepLowRank8At64
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRowReduceLowRank2At1024 n => n * n
  with prep := prepLowRank2At1024
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRowReduceLowRank8At1024 n => n * n
  with prep := prepLowRank8At1024
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRankCertLowRank2At64 n => n * n
  with prep := prepLowRank2At64
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runRankCertLowRank8At1024 n => n * n
  with prep := prepLowRank8At1024
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runCheckRankLowRank2At64 n => n * n
  with prep := prepLowRank2At64Cert
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations at fixed `r` on operands whose
-- size is bounded independently of `n`, so the declared model is `n^2` (mode 1).
setup_benchmark runCheckRankLowRank8At1024 n => n * n
  with prep := prepLowRank8At1024Cert
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

/-! `rank-deficient-by-construction`: `Θ(r · n · n)` operations with `r`
proportional to `n`, on minors whose bit size grows linearly in `n`, so the
declared one-sided upper bound is `n^5 (log n + log B)^2` (mode 2). -/
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runRowReduceDeficientMinusOne n => productBound n
  with prep := prepDeficientMinusOne
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runRowReduceDeficientHalf n => productBound n
  with prep := prepDeficientHalf
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runRowReduceDeficientHalfShifted n => productBound n
  with prep := prepDeficientHalfShifted
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runRankCertDeficientMinusOne n => productBound n
  with prep := prepDeficientMinusOne
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runRankCertDeficientHalfShifted n => productBound n
  with prep := prepDeficientHalfShifted
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
    targetInnerNanos := 4000000000
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runCheckRankDeficientMinusOne n => productBound n
  with prep := prepDeficientMinusOneCert
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }
-- Cost model: `Θ(r · n · n)` ring operations with `r` proportional to `n`; the
-- operands are minors of size up to `r`, of `O(n (log n + log B))` bits by
-- Hadamard's bound, so the declared one-sided upper bound is
-- `n^5 (log n + log B)^2` (mode 2), as for the dense family; input entries are
-- small but the intermediate minors are not.
setup_benchmark runCheckRankDeficientHalfShifted n => productBound n
  with prep := prepDeficientHalfShiftedCert
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def prepLowRank8At64Cert := prepLowRankCert 8 64

def runRankCertLowRank8At64 := runRankCert

-- Cost model: Fixed r and factor bit size bound every minor independently of n; Θ(n²) operations.
setup_benchmark runRankCertLowRank8At64 n => n * n
  with prep := prepLowRank8At64
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def runCheckRankLowRank8At64 := runCheckRank

-- Cost model: Fixed r and factor bit size bound every minor independently of n; Θ(n²) operations.
setup_benchmark runCheckRankLowRank8At64 n => n * n
  with prep := prepLowRank8At64Cert
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def prepLowRank2At1024Cert := prepLowRankCert 2 1024

def runRankCertLowRank2At1024 := runRankCert

-- Cost model: Fixed r and factor bit size bound every minor independently of n; Θ(n²) operations.
setup_benchmark runRankCertLowRank2At1024 n => n * n
  with prep := prepLowRank2At1024
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def runCheckRankLowRank2At1024 := runCheckRank

-- Cost model: Fixed r and factor bit size bound every minor independently of n; Θ(n²) operations.
setup_benchmark runCheckRankLowRank2At1024 n => n * n
  with prep := prepLowRank2At1024Cert
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
    -- The 0.5 s batch target was below the measured 10× spawn floor.
    targetInnerNanos := 2000000000
  }

def prepDeficientHalfCert := prepDeficientCert (fun n => n / 2) false

def runRankCertDeficientHalf := runRankCert

-- Cost model: Variable r=Θ(n), B≤25n: n³ operations at the Hadamard schoolbook bit bound (mode 2).
setup_benchmark runRankCertDeficientHalf n => productBound n
  with prep := prepDeficientHalf
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def runCheckRankDeficientHalf := runCheckRank

-- Cost model: Variable r=Θ(n), B≤25n: n³ operations at the Hadamard schoolbook bit bound (mode 2).
setup_benchmark runCheckRankDeficientHalf n => productBound n
  with prep := prepDeficientHalfCert
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

/-! `polynomial`: fixed registrations (mode 3), as specified by HexRank.
Full-rank entries have degree one and support at most two. The deficient
products have degree two, with support at most three (Rat) or five (Mv).
Dimension alone does not control minor support or coefficient bit length;
no tight wall-time model is claimed for these exact-division paths.
The operation-specific absolute budgets below give up asymptotic regression
detection, rather than treating a timeout as a complexity claim. -/

/-- First pass, on a runtime input read from the prepared cache. -/
def runRatPolyRankAt (k : Nat) (singular := false) : Unit → IO Nat := fun _ => do
  let input ← prepareRatPoly k singular
  return (rowReduceWith Hex.exactDiv input.matrix).profile.rank

def runRatPolyDeficientRankAt (k : Nat) := runRatPolyRankAt k true

def runRatPolyCertAt (k : Nat) (singular := false) : Unit → IO Nat := fun _ => do
  let input ← prepareRatPoly k singular
  return (rankCertWith Hex.exactDiv input.matrix).rank

/-- Checker only. The cached certificate is produced and validated before the
runner's timed region, and is never reconstructed inside it. -/
def runRatPolyCheckAt (k : Nat) (singular := false) : Unit → IO Bool := fun _ => do
  let input ← prepareRatPoly k singular
  return checkRank input.matrix input.cert

def runMvRankAt (k : Nat) (singular := false) : Unit → IO Nat := fun _ => do
  let input ← prepareMv k singular
  return (rowReduceWith Hex.exactDiv input.matrix).profile.rank

def runMvDeficientRankAt (k : Nat) := runMvRankAt k true

def runMvCertAt (k : Nat) (singular := false) : Unit → IO Nat := fun _ => do
  let input ← prepareMv k singular
  return (rankCertWith Hex.exactDiv input.matrix).rank

def runMvCheckAt (k : Nat) (singular := false) : Unit → IO Bool := fun _ => do
  let input ← prepareMv k singular
  return checkRank input.matrix input.cert

def runRatPolyRank4 := runRatPolyRankAt 4 false
def runRatPolyRank8 := runRatPolyRankAt 8 false
def runRatPolyRank12 := runRatPolyRankAt 12 false
def runRatPolyDeficientRank8 := runRatPolyDeficientRankAt 8
def runRatPolyCert8 := runRatPolyCertAt 8 false
def runRatPolyCheck8 := runRatPolyCheckAt 8 false
def runMvRank4 := runMvRankAt 4 false
def runMvRank8 := runMvRankAt 8 false
def runMvDeficientRank8 := runMvDeficientRankAt 8
def runMvCert4 := runMvCertAt 4 false
def runMvCheck4 := runMvCheckAt 4 false

def runRatPolyCert4 := runRatPolyCertAt 4 false
def runRatPolyCert12 := runRatPolyCertAt 12 false
def runRatPolyCheck4 := runRatPolyCheckAt 4 false
def runRatPolyCheck12 := runRatPolyCheckAt 12 false
def runRatPolyDeficientRank4 := runRatPolyRankAt 4 true
def runRatPolyDeficientRank12 := runRatPolyRankAt 12 true
def runRatPolyDeficientCert4 := runRatPolyCertAt 4 true
def runRatPolyDeficientCert8 := runRatPolyCertAt 8 true
def runRatPolyDeficientCert12 := runRatPolyCertAt 12 true
def runRatPolyDeficientCheck4 := runRatPolyCheckAt 4 true
def runRatPolyDeficientCheck8 := runRatPolyCheckAt 8 true
def runRatPolyDeficientCheck12 := runRatPolyCheckAt 12 true
def runMvRank12 := runMvRankAt 12 false
def runMvCert8 := runMvCertAt 8 false
def runMvCert12 := runMvCertAt 12 false
def runMvCheck8 := runMvCheckAt 8 false
def runMvCheck12 := runMvCheckAt 12 false
def runMvDeficientRank4 := runMvRankAt 4 true
def runMvDeficientRank12 := runMvRankAt 12 true
def runMvDeficientCert4 := runMvCertAt 4 true
def runMvDeficientCert8 := runMvCertAt 8 true
def runMvDeficientCert12 := runMvCertAt 12 true
def runMvDeficientCheck4 := runMvCheckAt 4 true
def runMvDeficientCheck8 := runMvCheckAt 8 true
def runMvDeficientCheck12 := runMvCheckAt 12 true

/-- Operational timeout only; the scientific ceilings are separate.
Canonical inputs: the deterministic generators above at dimensions 4/8/12.
Absolute budgets (ms, rounded here; exact nanoseconds in
`reports/bench-results/hex-rank-10352/polynomial-budgets.json`):

carrier rank       n  Rank  Second  Cert  Check  Certify
RatPoly Full       4  8.170479  31.780128  39.950607  4.365994  44.316601
RatPoly Full       8  170.195670  570.012225  740.207895  52.992657  793.200552
RatPoly Full      12  823.390906  3938.039233  4761.430139  310.112770  5071.542909
RatPoly Deficient  4  8.520291  3.673725  12.194016  2.583800  14.777816
RatPoly Deficient  8  127.696458  62.037331  189.733789  29.581834  219.315623
RatPoly Deficient 12  723.186850  384.390410  1107.577260  148.282890  1255.860150
Mv      Full       4  12.626816  38.454207  51.081023  2.293589  53.374612
Mv      Full       8  326.878744  2289.756000  2616.634744  40.408428  2657.043172
Mv      Full      12  4819.874186  39588.956926  44408.831112  325.527219  44734.358331
Mv      Deficient  4  8.204937  2.880788  11.085725  0.975751  12.061476
Mv      Deficient  8  284.134366  178.755312  462.889678  28.453816  491.343494
Mv      Deficient 12  3409.085161  3743.866786  7152.951947  229.560188  7382.512135

Each ceiling is twice the applicable sum of the six paired SymPy reference
medians: rank, augmented pivot-block rank, and exact certificate identities.
The margin and reference mapping precede the stage measurements; the report's
analysis links all raw reference times. Future results use these frozen
ceilings, independently of the 60-second child safety cap. -/
def polyConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 60.0, minTotalSeconds := 0.2, warmupFirstIter := true, tags := #["polynomial"] }

setup_fixed_benchmark runRatPolyRank4 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runRatPolyRank8 where { polyConfig with expectedHash := some (hash (8 : Nat)) }
setup_fixed_benchmark runRatPolyRank12 where { polyConfig with expectedHash := some (hash (12 : Nat)) }
setup_fixed_benchmark runRatPolyCert4 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runRatPolyCert8 where { polyConfig with expectedHash := some (hash (8 : Nat)) }
setup_fixed_benchmark runRatPolyCert12 where { polyConfig with expectedHash := some (hash (12 : Nat)) }
setup_fixed_benchmark runRatPolyCheck4 where { polyConfig with expectedHash := some (hash true), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runRatPolyCheck8 where { polyConfig with expectedHash := some (hash true) }
setup_fixed_benchmark runRatPolyCheck12 where { polyConfig with expectedHash := some (hash true) }
setup_fixed_benchmark runRatPolyDeficientRank4 where { polyConfig with expectedHash := some (hash (2 : Nat)), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runRatPolyDeficientRank8 where { polyConfig with expectedHash := some (hash (4 : Nat)) }
setup_fixed_benchmark runRatPolyDeficientRank12 where { polyConfig with expectedHash := some (hash (6 : Nat)) }
setup_fixed_benchmark runRatPolyDeficientCert4 where { polyConfig with expectedHash := some (hash (2 : Nat)), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runRatPolyDeficientCert8 where { polyConfig with expectedHash := some (hash (4 : Nat)) }
setup_fixed_benchmark runRatPolyDeficientCert12 where { polyConfig with expectedHash := some (hash (6 : Nat)) }
setup_fixed_benchmark runRatPolyDeficientCheck4 where { polyConfig with expectedHash := some (hash true), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runRatPolyDeficientCheck8 where { polyConfig with expectedHash := some (hash true) }
setup_fixed_benchmark runRatPolyDeficientCheck12 where { polyConfig with expectedHash := some (hash true) }
setup_fixed_benchmark runMvRank4 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runMvRank8 where { polyConfig with expectedHash := some (hash (8 : Nat)) }
setup_fixed_benchmark runMvRank12 where { polyConfig with expectedHash := some (hash (12 : Nat)) }
setup_fixed_benchmark runMvCert4 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runMvCert8 where { polyConfig with expectedHash := some (hash (8 : Nat)) }
setup_fixed_benchmark runMvCert12 where { polyConfig with expectedHash := some (hash (12 : Nat)) }
setup_fixed_benchmark runMvCheck4 where { polyConfig with expectedHash := some (hash true), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runMvCheck8 where { polyConfig with expectedHash := some (hash true) }
setup_fixed_benchmark runMvCheck12 where { polyConfig with expectedHash := some (hash true) }
setup_fixed_benchmark runMvDeficientRank4 where { polyConfig with expectedHash := some (hash (2 : Nat)), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runMvDeficientRank8 where { polyConfig with expectedHash := some (hash (4 : Nat)) }
setup_fixed_benchmark runMvDeficientRank12 where { polyConfig with expectedHash := some (hash (6 : Nat)) }
setup_fixed_benchmark runMvDeficientCert4 where { polyConfig with expectedHash := some (hash (2 : Nat)), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runMvDeficientCert8 where { polyConfig with expectedHash := some (hash (4 : Nat)) }
setup_fixed_benchmark runMvDeficientCert12 where { polyConfig with expectedHash := some (hash (6 : Nat)) }
setup_fixed_benchmark runMvDeficientCheck4 where { polyConfig with expectedHash := some (hash true), tags := #["polynomial", "smoke"] }
setup_fixed_benchmark runMvDeficientCheck8 where { polyConfig with expectedHash := some (hash true) }
setup_fixed_benchmark runMvDeficientCheck12 where { polyConfig with expectedHash := some (hash true) }


/-! Separately attributable certificate assembly and end-to-end producers. -/

/-- A matrix and its prepared first pass. Retaining the matrix directly keeps
reconstruction and elimination out of the second pass's timed region. -/
structure FirstInput (R : Type) where
  dim : Nat
  matrix : Matrix R dim dim
  first : ReducedForm R dim dim

instance : Hashable (FirstInput Int) where
  hash input := hash (input.dim, flatOfMatrix input.matrix,
    input.first.profile.rank, flatOfMatrix input.first.matrix, input.first.denom)

def prepSecond (prep : Nat → MatInput) (n : Nat) : FirstInput Int :=
  let input := prep n
  let A := matrixOfFlat input.n input.n input.entries
  ⟨input.n, A, rowReduceFF A⟩

def runSecond (input : FirstInput Int) : Nat :=
  (rankCertOf HexArith.Int.exactDiv input.matrix input.first).rank

def runCertify (input : MatInput) : Nat :=
  match certifyRank (matrixOfFlat input.n input.m input.entries) with
  | some c => c.rank
  | none => panic! "certifyRank rejected a validated integer fixture"

def runWitness (input : MatInput) : Nat :=
  match rankWitness (matrixOfFlat input.n input.m input.entries) with
  | .ok w => w.rank
  | .error error => panic! s!"rankWitness: {error}"

namespace Second

def prepDense := prepSecond Hex.RankBench.prepDense
def dense := runSecond
/- The prepared first pass leaves an r by r pivot block and its
augmented reduction. At fixed r and bits this is constant in n; when
r grows, O(r³) arithmetic on Hadamard-sized minors has the same n⁵ bound. -/
setup_benchmark dense n => hadamardBound n
  with prep := prepDense
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def prepLowRank2At64 := prepSecond Hex.RankBench.prepLowRank2At64
def lowRank2At64 := runSecond
/- The prepared first pass leaves an r by r pivot block and its
augmented reduction. At fixed r and bits this is constant in n; when
r grows, O(r³) arithmetic on Hadamard-sized minors has the same n⁵ bound. -/
setup_benchmark lowRank2At64 _n => 1
  with prep := prepLowRank2At64
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def prepLowRank8At64 := prepSecond Hex.RankBench.prepLowRank8At64
def lowRank8At64 := runSecond
/- The prepared first pass leaves an r by r pivot block and its
augmented reduction. At fixed r and bits this is constant in n; when
r grows, O(r³) arithmetic on Hadamard-sized minors has the same n⁵ bound. -/
setup_benchmark lowRank8At64 _n => 1
  with prep := prepLowRank8At64
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def prepLowRank2At1024 := prepSecond Hex.RankBench.prepLowRank2At1024
def lowRank2At1024 := runSecond
/- The prepared first pass leaves an r by r pivot block and its
augmented reduction. At fixed r and bits this is constant in n; when
r grows, O(r³) arithmetic on Hadamard-sized minors has the same n⁵ bound. -/
setup_benchmark lowRank2At1024 _n => 1
  with prep := prepLowRank2At1024
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def prepLowRank8At1024 := prepSecond Hex.RankBench.prepLowRank8At1024
def lowRank8At1024 := runSecond
/- The prepared first pass leaves an r by r pivot block and its
augmented reduction. At fixed r and bits this is constant in n; when
r grows, O(r³) arithmetic on Hadamard-sized minors has the same n⁵ bound. -/
setup_benchmark lowRank8At1024 _n => 1
  with prep := prepLowRank8At1024
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def prepDeficientMinusOne := prepSecond Hex.RankBench.prepDeficientMinusOne
def deficientMinusOne := runSecond
/- The prepared first pass leaves an r by r pivot block and its
augmented reduction. At fixed r and bits this is constant in n; when
r grows, O(r³) arithmetic on Hadamard-sized minors has the same n⁵ bound. -/
setup_benchmark deficientMinusOne n => productBound n
  with prep := prepDeficientMinusOne
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
    targetInnerNanos := 4000000000
  }

def prepDeficientHalf := prepSecond Hex.RankBench.prepDeficientHalf
def deficientHalf := runSecond
/- The prepared first pass leaves an r by r pivot block and its
augmented reduction. At fixed r and bits this is constant in n; when
r grows, O(r³) arithmetic on Hadamard-sized minors has the same n⁵ bound. -/
setup_benchmark deficientHalf n => productBound n
  with prep := prepDeficientHalf
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def prepDeficientHalfShifted := prepSecond Hex.RankBench.prepDeficientHalfShifted
def deficientHalfShifted := runSecond
/- The prepared first pass leaves an r by r pivot block and its
augmented reduction. At fixed r and bits this is constant in n; when
r grows, O(r³) arithmetic on Hadamard-sized minors has the same n⁵ bound. -/
setup_benchmark deficientHalfShifted n => productBound n
  with prep := prepDeficientHalfShifted
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

end Second

namespace Certify

def dense := runCertify
/- Certificate production followed by checking sums the existing
operation counts: O(n²) at fixed r/bits, and the same Hadamard n⁵ bound
when r and minor bit lengths grow. No cost model is inferred from timing. -/
setup_benchmark dense n => hadamardBound n
  with prep := Hex.RankBench.prepDense
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def lowRank2At64 := runCertify
/- Certificate production followed by checking sums the existing
operation counts: O(n²) at fixed r/bits, and the same Hadamard n⁵ bound
when r and minor bit lengths grow. No cost model is inferred from timing. -/
setup_benchmark lowRank2At64 n => n * n
  with prep := Hex.RankBench.prepLowRank2At64
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def lowRank8At64 := runCertify
/- Certificate production followed by checking sums the existing
operation counts: O(n²) at fixed r/bits, and the same Hadamard n⁵ bound
when r and minor bit lengths grow. No cost model is inferred from timing. -/
setup_benchmark lowRank8At64 n => n * n
  with prep := Hex.RankBench.prepLowRank8At64
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def lowRank2At1024 := runCertify
/- Certificate production followed by checking sums the existing
operation counts: O(n²) at fixed r/bits, and the same Hadamard n⁵ bound
when r and minor bit lengths grow. No cost model is inferred from timing. -/
setup_benchmark lowRank2At1024 n => n * n
  with prep := Hex.RankBench.prepLowRank2At1024
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
    targetInnerNanos := 8000000000
  }

def lowRank8At1024 := runCertify
/- Certificate production followed by checking sums the existing
operation counts: O(n²) at fixed r/bits, and the same Hadamard n⁵ bound
when r and minor bit lengths grow. No cost model is inferred from timing. -/
setup_benchmark lowRank8At1024 n => n * n
  with prep := Hex.RankBench.prepLowRank8At1024
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def deficientMinusOne := runCertify
/- Certificate production followed by checking sums the existing
operation counts: O(n²) at fixed r/bits, and the same Hadamard n⁵ bound
when r and minor bit lengths grow. No cost model is inferred from timing. -/
setup_benchmark deficientMinusOne n => productBound n
  with prep := Hex.RankBench.prepDeficientMinusOne
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def deficientHalf := runCertify
/- Certificate production followed by checking sums the existing
operation counts: O(n²) at fixed r/bits, and the same Hadamard n⁵ bound
when r and minor bit lengths grow. No cost model is inferred from timing. -/
setup_benchmark deficientHalf n => productBound n
  with prep := Hex.RankBench.prepDeficientHalf
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    targetInnerNanos := 4_000_000_000
    outerTrials := 6
  }

def deficientHalfShifted := runCertify
/- Certificate production followed by checking sums the existing
operation counts: O(n²) at fixed r/bits, and the same Hadamard n⁵ bound
when r and minor bit lengths grow. No cost model is inferred from timing. -/
setup_benchmark deficientHalfShifted n => productBound n
  with prep := Hex.RankBench.prepDeficientHalfShifted
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

end Certify

namespace Witness

def dense := runWitness
/- The native witness adds O((n-r)r²) integer work and O(r³)
fixed-modulus arithmetic to certificate production (SPEC Complexity), plus
O(nm) list conversion and O((n-r)rm) work for the native list self-check.
The retry list of moduli has fixed length. These preserve n² at fixed r/bits and the Hadamard n⁵ upper bound otherwise. -/
setup_benchmark dense n => hadamardBound n
  with prep := Hex.RankBench.prepDense
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def lowRank2At64 := runWitness
/- The native witness adds O((n-r)r²) integer work and O(r³)
fixed-modulus arithmetic to certificate production (SPEC Complexity), plus
O(nm) list conversion and O((n-r)rm) work for the native list self-check.
The retry list of moduli has fixed length. These preserve n² at fixed r/bits and the Hadamard n⁵ upper bound otherwise. -/
setup_benchmark lowRank2At64 n => n * n
  with prep := Hex.RankBench.prepLowRank2At64
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def lowRank8At64 := runWitness
/- The native witness adds O((n-r)r²) integer work and O(r³)
fixed-modulus arithmetic to certificate production (SPEC Complexity), plus
O(nm) list conversion and O((n-r)rm) work for the native list self-check.
The retry list of moduli has fixed length. These preserve n² at fixed r/bits and the Hadamard n⁵ upper bound otherwise. -/
setup_benchmark lowRank8At64 n => n * n
  with prep := Hex.RankBench.prepLowRank8At64
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def lowRank2At1024 := runWitness
/- The native witness adds O((n-r)r²) integer work and O(r³)
fixed-modulus arithmetic to certificate production (SPEC Complexity), plus
O(nm) list conversion and O((n-r)rm) work for the native list self-check.
The retry list of moduli has fixed length. These preserve n² at fixed r/bits and the Hadamard n⁵ upper bound otherwise. -/
setup_benchmark lowRank2At1024 n => n * n
  with prep := Hex.RankBench.prepLowRank2At1024
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
    targetInnerNanos := 8000000000
  }

def lowRank8At1024 := runWitness
/- The native witness adds O((n-r)r²) integer work and O(r³)
fixed-modulus arithmetic to certificate production (SPEC Complexity), plus
O(nm) list conversion and O((n-r)rm) work for the native list self-check.
The retry list of moduli has fixed length. These preserve n² at fixed r/bits and the Hadamard n⁵ upper bound otherwise. -/
setup_benchmark lowRank8At1024 n => n * n
  with prep := Hex.RankBench.prepLowRank8At1024
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def deficientMinusOne := runWitness
/- The native witness adds O((n-r)r²) integer work and O(r³)
fixed-modulus arithmetic to certificate production (SPEC Complexity), plus
O(nm) list conversion and O((n-r)rm) work for the native list self-check.
The retry list of moduli has fixed length. These preserve n² at fixed r/bits and the Hadamard n⁵ upper bound otherwise. -/
setup_benchmark deficientMinusOne n => productBound n
  with prep := Hex.RankBench.prepDeficientMinusOne
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def deficientHalf := runWitness
/- The native witness adds O((n-r)r²) integer work and O(r³)
fixed-modulus arithmetic to certificate production (SPEC Complexity), plus
O(nm) list conversion and O((n-r)rm) work for the native list self-check.
The retry list of moduli has fixed length. These preserve n² at fixed r/bits and the Hadamard n⁵ upper bound otherwise. -/
setup_benchmark deficientHalf n => productBound n
  with prep := Hex.RankBench.prepDeficientHalf
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

def deficientHalfShifted := runWitness
/- The native witness adds O((n-r)r²) integer work and O(r³)
fixed-modulus arithmetic to certificate production (SPEC Complexity), plus
O(nm) list conversion and O((n-r)rm) work for the native list self-check.
The retry list of moduli has fixed length. These preserve n² at fixed r/bits and the Hadamard n⁵ upper bound otherwise. -/
setup_benchmark deficientHalfShifted n => productBound n
  with prep := Hex.RankBench.prepDeficientHalfShifted
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 120.0
    outerTrials := 6
  }

end Witness

initialize ratFirstInputs : IO.Ref (Array (Nat × Bool × FirstInput (DensePoly Rat))) ← IO.mkRef #[]
initialize mvFirstInputs : IO.Ref (Array (Nat × Bool × FirstInput (MvPoly 2 Int Mono.lex))) ← IO.mkRef #[]

def prepareFirst [Zero R] [One R] [Sub R] [Mul R] [DecidableEq R]
    (cache : IO.Ref (Array (Nat × Bool × FirstInput R))) (quot : R → R → R)
    (prepare : Nat → Bool → IO (PolyInput R)) (n : Nat) (singular : Bool) : IO (FirstInput R) := do
  if let some (_, _, input) := (← cache.get).find? (fun (k, d, _) => k == n && d == singular) then
    return input
  let input ← prepare n singular
  let first := FirstInput.mk input.dim input.matrix (rowReduceWith quot input.matrix)
  cache.modify (·.push (n, singular, first))
  return first

def runRatPolySecondAt (n : Nat) (singular : Bool) : IO Nat := do
  let input ← prepareFirst ratFirstInputs Hex.exactDiv prepareRatPoly n singular
  return (rankCertOf Hex.exactDiv input.matrix input.first).rank

def runMvSecondAt (n : Nat) (singular : Bool) : IO Nat := do
  let input ← prepareFirst mvFirstInputs Hex.exactDiv prepareMv n singular
  return (rankCertOf Hex.exactDiv input.matrix input.first).rank

def runRatPolyCertifyAt (n : Nat) (singular : Bool) : IO Nat := do
  let input ← prepareRatPoly n singular
  let some c := certifyRankWith Hex.exactDiv input.matrix |
    throw <| IO.userError "certifyRankWith rejected a validated rational polynomial fixture"
  return c.rank

def runMvCertifyAt (n : Nat) (singular : Bool) : IO Nat := do
  let input ← prepareMv n singular
  let some c := certifyRankWith Hex.exactDiv input.matrix |
    throw <| IO.userError "certifyRankWith rejected a validated multivariate fixture"
  return c.rank

def runRatPolySecond4 := runRatPolySecondAt 4 false
setup_fixed_benchmark runRatPolySecond4 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "attribution", "smoke"] }
def runRatPolySecond8 := runRatPolySecondAt 8 false
setup_fixed_benchmark runRatPolySecond8 where { polyConfig with expectedHash := some (hash (8 : Nat)), tags := #["polynomial", "attribution"] }
def runRatPolySecond12 := runRatPolySecondAt 12 false
setup_fixed_benchmark runRatPolySecond12 where { polyConfig with expectedHash := some (hash (12 : Nat)), tags := #["polynomial", "attribution"] }
def runRatPolyCertify4 := runRatPolyCertifyAt 4 false
setup_fixed_benchmark runRatPolyCertify4 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "attribution", "smoke"] }
def runRatPolyCertify8 := runRatPolyCertifyAt 8 false
setup_fixed_benchmark runRatPolyCertify8 where { polyConfig with expectedHash := some (hash (8 : Nat)), tags := #["polynomial", "attribution"] }
def runRatPolyCertify12 := runRatPolyCertifyAt 12 false
setup_fixed_benchmark runRatPolyCertify12 where { polyConfig with expectedHash := some (hash (12 : Nat)), tags := #["polynomial", "attribution"] }
def runRatPolyDeficientSecond4 := runRatPolySecondAt 4 true
setup_fixed_benchmark runRatPolyDeficientSecond4 where { polyConfig with expectedHash := some (hash (2 : Nat)), tags := #["polynomial", "attribution", "smoke"] }
def runRatPolyDeficientSecond8 := runRatPolySecondAt 8 true
setup_fixed_benchmark runRatPolyDeficientSecond8 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "attribution"] }
def runRatPolyDeficientSecond12 := runRatPolySecondAt 12 true
setup_fixed_benchmark runRatPolyDeficientSecond12 where { polyConfig with expectedHash := some (hash (6 : Nat)), tags := #["polynomial", "attribution"] }
def runRatPolyDeficientCertify4 := runRatPolyCertifyAt 4 true
setup_fixed_benchmark runRatPolyDeficientCertify4 where { polyConfig with expectedHash := some (hash (2 : Nat)), tags := #["polynomial", "attribution", "smoke"] }
def runRatPolyDeficientCertify8 := runRatPolyCertifyAt 8 true
setup_fixed_benchmark runRatPolyDeficientCertify8 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "attribution"] }
def runRatPolyDeficientCertify12 := runRatPolyCertifyAt 12 true
setup_fixed_benchmark runRatPolyDeficientCertify12 where { polyConfig with expectedHash := some (hash (6 : Nat)), tags := #["polynomial", "attribution"] }
def runMvSecond4 := runMvSecondAt 4 false
setup_fixed_benchmark runMvSecond4 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "attribution", "smoke"] }
def runMvSecond8 := runMvSecondAt 8 false
setup_fixed_benchmark runMvSecond8 where { polyConfig with expectedHash := some (hash (8 : Nat)), tags := #["polynomial", "attribution"] }
def runMvSecond12 := runMvSecondAt 12 false
setup_fixed_benchmark runMvSecond12 where { polyConfig with expectedHash := some (hash (12 : Nat)), tags := #["polynomial", "attribution"] }
def runMvCertify4 := runMvCertifyAt 4 false
setup_fixed_benchmark runMvCertify4 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "attribution", "smoke"] }
def runMvCertify8 := runMvCertifyAt 8 false
setup_fixed_benchmark runMvCertify8 where { polyConfig with expectedHash := some (hash (8 : Nat)), tags := #["polynomial", "attribution"] }
def runMvCertify12 := runMvCertifyAt 12 false
setup_fixed_benchmark runMvCertify12 where { polyConfig with expectedHash := some (hash (12 : Nat)), tags := #["polynomial", "attribution"] }
def runMvDeficientSecond4 := runMvSecondAt 4 true
setup_fixed_benchmark runMvDeficientSecond4 where { polyConfig with expectedHash := some (hash (2 : Nat)), tags := #["polynomial", "attribution", "smoke"] }
def runMvDeficientSecond8 := runMvSecondAt 8 true
setup_fixed_benchmark runMvDeficientSecond8 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "attribution"] }
def runMvDeficientSecond12 := runMvSecondAt 12 true
setup_fixed_benchmark runMvDeficientSecond12 where { polyConfig with expectedHash := some (hash (6 : Nat)), tags := #["polynomial", "attribution"] }
def runMvDeficientCertify4 := runMvCertifyAt 4 true
setup_fixed_benchmark runMvDeficientCertify4 where { polyConfig with expectedHash := some (hash (2 : Nat)), tags := #["polynomial", "attribution", "smoke"] }
def runMvDeficientCertify8 := runMvCertifyAt 8 true
setup_fixed_benchmark runMvDeficientCertify8 where { polyConfig with expectedHash := some (hash (4 : Nat)), tags := #["polynomial", "attribution"] }
def runMvDeficientCertify12 := runMvCertifyAt 12 true
setup_fixed_benchmark runMvDeficientCertify12 where { polyConfig with expectedHash := some (hash (6 : Nat)), tags := #["polynomial", "attribution"] }

/-! Persistent exact-domain comparators. A fixed anchor shares an actual Lean
matrix with the subprocess; serialization, decoding and validation are all in
warmup. Only a rank request/reply is in each external timed call. -/

open Lean in
def jsonValue (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError error

initialize comparator : IO.Ref (Option Hex.BenchOracle.Flint.PersistentComparator) ← IO.mkRef none
initialize comparatorKey : IO.Ref String ← IO.mkRef ""

def rankRequest (line : String) : IO Lean.Json := do
  let child ← match ← comparator.get with
    | some child => pure child
    | none => do
      let python := (← IO.getEnv "HEX_RANK_BENCH_PYTHON").getD "python3"
      let script ← match ← IO.getEnv "HEX_RANK_BENCH_DRIVER" with
        | some path => pure path
        | none => do
          let path := "scripts/oracle/rank_bench.py"
          if ← (System.FilePath.mk path).pathExists then pure path else pure ("../" ++ path)
      let child ← Hex.BenchOracle.Flint.PersistentComparator.spawn python #[script]
      comparator.set (some child)
      pure child
  -- Stream failure aborts the child; retrying would charge startup to timing.
  let reply ← jsonValue <| Lean.Json.parse (← child.requestLine line)
  unless ← jsonValue (reply.getObjValAs? Bool "ok") do
    throw <| IO.userError s!"rank comparator: {reply.compress}"
  jsonValue (reply.getObjVal? "result")

def externalRank (expected : Nat) : IO Nat := do
  let result ← jsonValue <| Lean.fromJson? (α := Nat) (← rankRequest "{\"op\":\"rank\"}")
  unless result == expected do
    throw <| IO.userError s!"rank comparator: expected {expected}, got {result}"
  return result

def installMatrix (key record : String) (expected : Nat) : IO Unit := do
  let _ ← rankRequest ("{\"op\":\"prepare\",\"record\":" ++ record ++ "}")
  let _ ← externalRank expected
  comparatorKey.set key

def jsonMatrix {R : Type} {n m : Nat} (encode : R → Lean.Json) (A : Matrix R n m) : Lean.Json :=
  .arr <| A.rows.toArray.map fun row => .arr (row.toArray.map encode)

def scalarFixture (family n : Nat) : MatInput :=
  match family with
  | 0 => prepDense n
  | 1 => prepLowRank 2 64 n
  | 2 => prepLowRank 8 64 n
  | 3 => prepLowRank 2 1024 n
  | 4 => prepLowRank 8 1024 n
  | 5 => prepDeficientMinusOne n
  | 6 => prepDeficientHalf n
  | _ => prepDeficientHalfShifted n

def scalarRank (family n : Nat) : Nat :=
  match family with
  | 0 => n
  | 1 | 3 => 2
  | 2 | 4 => 8
  | 5 => n - 1
  | _ => n / 2

structure ScalarInput where
  family : Nat
  dim : Nat
  integer : Matrix Int dim dim
  rational : Matrix Rat dim dim

initialize scalarInputs : IO.Ref (Array ScalarInput) ← IO.mkRef #[]

def prepareScalar (family n : Nat) : IO ScalarInput := do
  if let some input := (← scalarInputs.get).find? (fun input => input.family == family && input.dim == n) then
    return input
  let flat := scalarFixture family n
  let A := matrixOfFlat n n flat.entries
  -- Nonzero row scaling preserves rank, while exercising genuine denominators.
  let Q : Matrix Rat n n := Matrix.ofFn fun i j => (A[(i, j)] : Rat) / (1 + i.val % 7 : Nat)
  let input := ScalarInput.mk family n A Q
  scalarInputs.modify (·.push input)
  return input

def runScalarNative (family n : Nat) (rational : Bool) : IO Nat := do
  let input ← prepareScalar family n
  return if rational then rankWith Hex.exactDiv input.rational else rank input.integer

def runScalarExternal (family n : Nat) (rational : Bool) : IO Nat := do
  let expected := scalarRank family n
  let key := s!"scalar-{family}-{n}-{rational}"
  if (← comparatorKey.get) != key then
    let input ← prepareScalar family n
    let rows := if rational then jsonMatrix (fun q => Lean.toJson (q.num, q.den)) input.rational
      else jsonMatrix Lean.toJson input.integer
    let record := Lean.Json.mkObj [("kind", Lean.toJson (if rational then "ratmatrix" else "matrix")), ("rows", rows)]
    installMatrix key record.compress expected
  externalRank expected

def encodeRatPoly (f : DensePoly Rat) : Lean.Json :=
  Lean.Json.mkObj [("num", Lean.toJson (f.toArray.map (·.num))),
    ("den", Lean.toJson (f.toArray.map (·.den)))]

def encodeMv (f : MvPoly 2 Int Mono.lex) : Lean.Json :=
  Lean.toJson (f.termsList.map fun (mono, coeff) => (mono.toList, coeff))

def runPolyExternal (mv singular : Bool) (n : Nat) : IO Nat := do
  let expected := if singular then n / 2 else n
  let key := s!"poly-{mv}-{singular}-{n}"
  if (← comparatorKey.get) != key then
    let fields := [("rows", Lean.toJson n), ("cols", Lean.toJson n)]
    let record ← if mv then do
      let input ← prepareMv n singular
      pure <| Lean.Json.mkObj (fields ++ [("kind", Lean.toJson "mvpolymatrix"),
        ("arity", Lean.toJson (2 : Nat)), ("entries", jsonMatrix encodeMv input.matrix)])
    else do
      let input ← prepareRatPoly n singular
      pure <| Lean.Json.mkObj (fields ++ [("kind", Lean.toJson "polymatrix"),
        ("field", Lean.Json.mkObj [("type", Lean.toJson "Rat")]), ("entries", jsonMatrix encodeRatPoly input.matrix)])
    installMatrix key record.compress expected
  externalRank expected

/-- Serialize the already-produced certificate using the conformance entry
encoding. Only decoding is outside the reference checker's timed region;
submatrix selection and all three identities are evaluated on each call. -/
def jsonCertificate {R : Type} {n m : Nat} (encode : R → Lean.Json) (c : RankCert R n m) : Lean.Json :=
  Lean.Json.mkObj [("rank", Lean.toJson c.rank),
    ("rows", Lean.toJson (c.rows.toArray.map Fin.val)),
    ("cols", Lean.toJson (c.cols.toArray.map Fin.val)),
    ("denom", encode c.denom), ("adj", jsonMatrix encode c.adj)]

def preparePolyReference (mv singular : Bool) (n : Nat) : IO Unit := do
  let key := s!"certificate-{mv}-{singular}-{n}"
  if (← comparatorKey.get) == key then return
  let fields := [("rows", Lean.toJson n), ("cols", Lean.toJson n)]
  let (record, certificate) ← if mv then do
    let input ← prepareMv n singular
    pure (Lean.Json.mkObj (fields ++ [("kind", Lean.toJson "mvpolymatrix"),
      ("arity", Lean.toJson (2 : Nat)), ("entries", jsonMatrix encodeMv input.matrix)]),
      jsonCertificate encodeMv input.cert)
  else do
    let input ← prepareRatPoly n singular
    pure (Lean.Json.mkObj (fields ++ [("kind", Lean.toJson "polymatrix"),
      ("field", Lean.Json.mkObj [("type", Lean.toJson "Rat")]),
      ("entries", jsonMatrix encodeRatPoly input.matrix)]),
      jsonCertificate encodeRatPoly input.cert)
  let request := Lean.Json.mkObj [("op", Lean.toJson "prepare"),
    ("record", record), ("certificate", certificate)]
  let _ ← rankRequest request.compress
  let _ ← externalRank (if singular then n / 2 else n)
  let ok ← jsonValue <| Lean.fromJson? (α := Bool) (← rankRequest "{\"op\":\"check\"}")
  unless ok do throw <| IO.userError "SymPy rejected the prepared polynomial certificate"
  comparatorKey.set key

def runPolySecondExternal (mv singular : Bool) (n : Nat) : IO Nat := do
  preparePolyReference mv singular n
  let result ← jsonValue <| Lean.fromJson? (α := Nat) (← rankRequest "{\"op\":\"second\"}")
  unless result == (if singular then n / 2 else n) do
    throw <| IO.userError "SymPy augmented-block rank mismatch"
  return result

def runPolyCheckExternal (mv singular : Bool) (n : Nat) : IO Bool := do
  preparePolyReference mv singular n
  let result ← jsonValue <| Lean.fromJson? (α := Bool) (← rankRequest "{\"op\":\"check\"}")
  unless result do throw <| IO.userError "SymPy certificate identity mismatch"
  return result

def runProtocolOverhead : IO Nat := do
  jsonValue <| Lean.fromJson? (α := Nat) (← rankRequest "{\"op\":\"overhead\"}")

/-- Comparison anchors do not assert a fixed performance budget. External
calls include protocol cost, which has its own matched control. -/
def comparisonConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 6, maxSecondsPerCall := 120.0, minTotalSeconds := 0.2,
    warmupFirstIter := true, tags := #["comparison"] }

setup_fixed_benchmark runProtocolOverhead where
  { comparisonConfig with expectedHash := some (hash (0 : Nat)), tags := #["comparison", "external"] }

namespace Comparison

namespace Int.Dense

def native16 := runScalarNative 0 16 false
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 0 16 false
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 0 24 false
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 0 24 false
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 0 32 false
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 0 32 false
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 0 48 false
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 0 48 false
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 0 64 false
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 0 64 false
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 0 96 false
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 0 96 false
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 0 128 false
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 0 128 false
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 0 192 false
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (192 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 0 192 false
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (192 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 0 256 false
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (256 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 0 256 false
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (256 : Nat)), tags := #["comparison", "external"] }

end Int.Dense

namespace Int.LowRank2At64

def native16 := runScalarNative 1 16 false
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 1 16 false
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 1 24 false
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 1 24 false
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 1 32 false
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 1 32 false
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 1 48 false
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 1 48 false
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 1 64 false
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 1 64 false
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 1 96 false
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 1 96 false
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 1 128 false
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 1 128 false
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 1 192 false
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 1 192 false
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 1 256 false
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 1 256 false
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }

end Int.LowRank2At64

namespace Int.LowRank8At64

def native16 := runScalarNative 2 16 false
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 2 16 false
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 2 24 false
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 2 24 false
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 2 32 false
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 2 32 false
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 2 48 false
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 2 48 false
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 2 64 false
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 2 64 false
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 2 96 false
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 2 96 false
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 2 128 false
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 2 128 false
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 2 192 false
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 2 192 false
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 2 256 false
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 2 256 false
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }

end Int.LowRank8At64

namespace Int.LowRank2At1024

def native16 := runScalarNative 3 16 false
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 3 16 false
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 3 24 false
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 3 24 false
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 3 32 false
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 3 32 false
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 3 48 false
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 3 48 false
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 3 64 false
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 3 64 false
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 3 96 false
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 3 96 false
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 3 128 false
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 3 128 false
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 3 192 false
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 3 192 false
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 3 256 false
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 3 256 false
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }

end Int.LowRank2At1024

namespace Int.LowRank8At1024

def native16 := runScalarNative 4 16 false
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 4 16 false
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 4 24 false
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 4 24 false
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 4 32 false
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 4 32 false
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 4 48 false
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 4 48 false
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 4 64 false
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 4 64 false
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 4 96 false
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 4 96 false
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 4 128 false
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 4 128 false
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 4 192 false
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 4 192 false
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 4 256 false
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 4 256 false
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }

end Int.LowRank8At1024

namespace Int.DeficientMinusOne

def native16 := runScalarNative 5 16 false
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (15 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 5 16 false
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (15 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 5 24 false
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (23 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 5 24 false
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (23 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 5 32 false
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (31 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 5 32 false
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (31 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 5 48 false
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (47 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 5 48 false
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (47 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 5 64 false
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (63 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 5 64 false
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (63 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 5 96 false
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (95 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 5 96 false
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (95 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 5 128 false
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (127 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 5 128 false
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (127 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 5 192 false
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (191 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 5 192 false
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (191 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 5 256 false
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (255 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 5 256 false
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (255 : Nat)), tags := #["comparison", "external"] }

end Int.DeficientMinusOne

namespace Int.DeficientHalf

def native16 := runScalarNative 6 16 false
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 6 16 false
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 6 24 false
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 6 24 false
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 6 32 false
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 6 32 false
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 6 48 false
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 6 48 false
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 6 64 false
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 6 64 false
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 6 96 false
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 6 96 false
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 6 128 false
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 6 128 false
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 6 192 false
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 6 192 false
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 6 256 false
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 6 256 false
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "external"] }

end Int.DeficientHalf

namespace Int.DeficientHalfShifted

def native16 := runScalarNative 7 16 false
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 7 16 false
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 7 24 false
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 7 24 false
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 7 32 false
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 7 32 false
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 7 48 false
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 7 48 false
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 7 64 false
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 7 64 false
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 7 96 false
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 7 96 false
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 7 128 false
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 7 128 false
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 7 192 false
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 7 192 false
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 7 256 false
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 7 256 false
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "external"] }

end Int.DeficientHalfShifted

namespace Rat.Dense

def native16 := runScalarNative 0 16 true
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 0 16 true
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 0 24 true
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 0 24 true
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 0 32 true
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 0 32 true
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 0 48 true
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 0 48 true
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 0 64 true
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 0 64 true
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 0 96 true
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 0 96 true
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 0 128 true
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 0 128 true
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 0 192 true
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (192 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 0 192 true
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (192 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 0 256 true
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (256 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 0 256 true
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (256 : Nat)), tags := #["comparison", "external"] }

end Rat.Dense

namespace Rat.LowRank2At64

def native16 := runScalarNative 1 16 true
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 1 16 true
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 1 24 true
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 1 24 true
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 1 32 true
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 1 32 true
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 1 48 true
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 1 48 true
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 1 64 true
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 1 64 true
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 1 96 true
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 1 96 true
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 1 128 true
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 1 128 true
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 1 192 true
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 1 192 true
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 1 256 true
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 1 256 true
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }

end Rat.LowRank2At64

namespace Rat.LowRank8At64

def native16 := runScalarNative 2 16 true
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 2 16 true
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 2 24 true
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 2 24 true
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 2 32 true
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 2 32 true
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 2 48 true
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 2 48 true
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 2 64 true
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 2 64 true
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 2 96 true
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 2 96 true
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 2 128 true
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 2 128 true
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 2 192 true
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 2 192 true
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 2 256 true
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 2 256 true
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }

end Rat.LowRank8At64

namespace Rat.LowRank2At1024

def native16 := runScalarNative 3 16 true
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 3 16 true
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 3 24 true
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 3 24 true
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 3 32 true
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 3 32 true
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 3 48 true
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 3 48 true
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 3 64 true
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 3 64 true
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 3 96 true
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 3 96 true
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 3 128 true
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 3 128 true
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 3 192 true
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 3 192 true
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 3 256 true
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 3 256 true
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }

end Rat.LowRank2At1024

namespace Rat.LowRank8At1024

def native16 := runScalarNative 4 16 true
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 4 16 true
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 4 24 true
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 4 24 true
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 4 32 true
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 4 32 true
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 4 48 true
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 4 48 true
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 4 64 true
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 4 64 true
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 4 96 true
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 4 96 true
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 4 128 true
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 4 128 true
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 4 192 true
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 4 192 true
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 4 256 true
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 4 256 true
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }

end Rat.LowRank8At1024

namespace Rat.DeficientMinusOne

def native16 := runScalarNative 5 16 true
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (15 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 5 16 true
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (15 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 5 24 true
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (23 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 5 24 true
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (23 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 5 32 true
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (31 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 5 32 true
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (31 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 5 48 true
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (47 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 5 48 true
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (47 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 5 64 true
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (63 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 5 64 true
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (63 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 5 96 true
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (95 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 5 96 true
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (95 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 5 128 true
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (127 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 5 128 true
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (127 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 5 192 true
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (191 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 5 192 true
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (191 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 5 256 true
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (255 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 5 256 true
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (255 : Nat)), tags := #["comparison", "external"] }

end Rat.DeficientMinusOne

namespace Rat.DeficientHalf

def native16 := runScalarNative 6 16 true
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 6 16 true
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 6 24 true
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 6 24 true
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 6 32 true
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 6 32 true
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 6 48 true
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 6 48 true
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 6 64 true
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 6 64 true
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 6 96 true
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 6 96 true
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 6 128 true
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 6 128 true
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 6 192 true
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 6 192 true
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 6 256 true
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 6 256 true
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "external"] }

end Rat.DeficientHalf

namespace Rat.DeficientHalfShifted

def native16 := runScalarNative 7 16 true
setup_fixed_benchmark native16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "native", "smoke"] }
def external16 := runScalarExternal 7 16 true
setup_fixed_benchmark external16 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def native24 := runScalarNative 7 24 true
setup_fixed_benchmark native24 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "native"] }
def external24 := runScalarExternal 7 24 true
setup_fixed_benchmark external24 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "external"] }
def native32 := runScalarNative 7 32 true
setup_fixed_benchmark native32 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "native"] }
def external32 := runScalarExternal 7 32 true
setup_fixed_benchmark external32 where { comparisonConfig with expectedHash := some (hash (16 : Nat)), tags := #["comparison", "external"] }
def native48 := runScalarNative 7 48 true
setup_fixed_benchmark native48 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "native"] }
def external48 := runScalarExternal 7 48 true
setup_fixed_benchmark external48 where { comparisonConfig with expectedHash := some (hash (24 : Nat)), tags := #["comparison", "external"] }
def native64 := runScalarNative 7 64 true
setup_fixed_benchmark native64 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "native"] }
def external64 := runScalarExternal 7 64 true
setup_fixed_benchmark external64 where { comparisonConfig with expectedHash := some (hash (32 : Nat)), tags := #["comparison", "external"] }
def native96 := runScalarNative 7 96 true
setup_fixed_benchmark native96 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "native"] }
def external96 := runScalarExternal 7 96 true
setup_fixed_benchmark external96 where { comparisonConfig with expectedHash := some (hash (48 : Nat)), tags := #["comparison", "external"] }
def native128 := runScalarNative 7 128 true
setup_fixed_benchmark native128 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "native"] }
def external128 := runScalarExternal 7 128 true
setup_fixed_benchmark external128 where { comparisonConfig with expectedHash := some (hash (64 : Nat)), tags := #["comparison", "external"] }
def native192 := runScalarNative 7 192 true
setup_fixed_benchmark native192 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "native"] }
def external192 := runScalarExternal 7 192 true
setup_fixed_benchmark external192 where { comparisonConfig with expectedHash := some (hash (96 : Nat)), tags := #["comparison", "external"] }
def native256 := runScalarNative 7 256 true
setup_fixed_benchmark native256 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "native"] }
def external256 := runScalarExternal 7 256 true
setup_fixed_benchmark external256 where { comparisonConfig with expectedHash := some (hash (128 : Nat)), tags := #["comparison", "external"] }

end Rat.DeficientHalfShifted

namespace RatPoly.Full

def external4 := runPolyExternal false false 4
setup_fixed_benchmark external4 where { comparisonConfig with expectedHash := some (hash (4 : Nat)), tags := #["comparison", "external"] }
def external8 := runPolyExternal false false 8
setup_fixed_benchmark external8 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def external12 := runPolyExternal false false 12
setup_fixed_benchmark external12 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "external"] }

end RatPoly.Full

namespace RatPoly.Deficient

def external4 := runPolyExternal false true 4
setup_fixed_benchmark external4 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def external8 := runPolyExternal false true 8
setup_fixed_benchmark external8 where { comparisonConfig with expectedHash := some (hash (4 : Nat)), tags := #["comparison", "external"] }
def external12 := runPolyExternal false true 12
setup_fixed_benchmark external12 where { comparisonConfig with expectedHash := some (hash (6 : Nat)), tags := #["comparison", "external"] }

end RatPoly.Deficient

namespace Mv.Full

def external4 := runPolyExternal true false 4
setup_fixed_benchmark external4 where { comparisonConfig with expectedHash := some (hash (4 : Nat)), tags := #["comparison", "external"] }
def external8 := runPolyExternal true false 8
setup_fixed_benchmark external8 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external"] }
def external12 := runPolyExternal true false 12
setup_fixed_benchmark external12 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "external"] }

end Mv.Full

namespace Mv.Deficient

def external4 := runPolyExternal true true 4
setup_fixed_benchmark external4 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external"] }
def external8 := runPolyExternal true true 8
setup_fixed_benchmark external8 where { comparisonConfig with expectedHash := some (hash (4 : Nat)), tags := #["comparison", "external"] }
def external12 := runPolyExternal true true 12
setup_fixed_benchmark external12 where { comparisonConfig with expectedHash := some (hash (6 : Nat)), tags := #["comparison", "external"] }

end Mv.Deficient

namespace RatPoly.Full

def second4 := runPolySecondExternal false false 4
setup_fixed_benchmark second4 where { comparisonConfig with expectedHash := some (hash (4 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def second8 := runPolySecondExternal false false 8
setup_fixed_benchmark second8 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def second12 := runPolySecondExternal false false 12
setup_fixed_benchmark second12 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def check4 := runPolyCheckExternal false false 4
setup_fixed_benchmark check4 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }
def check8 := runPolyCheckExternal false false 8
setup_fixed_benchmark check8 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }
def check12 := runPolyCheckExternal false false 12
setup_fixed_benchmark check12 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }

end RatPoly.Full

namespace RatPoly.Deficient

def second4 := runPolySecondExternal false true 4
setup_fixed_benchmark second4 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def second8 := runPolySecondExternal false true 8
setup_fixed_benchmark second8 where { comparisonConfig with expectedHash := some (hash (4 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def second12 := runPolySecondExternal false true 12
setup_fixed_benchmark second12 where { comparisonConfig with expectedHash := some (hash (6 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def check4 := runPolyCheckExternal false true 4
setup_fixed_benchmark check4 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }
def check8 := runPolyCheckExternal false true 8
setup_fixed_benchmark check8 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }
def check12 := runPolyCheckExternal false true 12
setup_fixed_benchmark check12 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }

end RatPoly.Deficient

namespace Mv.Full

def second4 := runPolySecondExternal true false 4
setup_fixed_benchmark second4 where { comparisonConfig with expectedHash := some (hash (4 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def second8 := runPolySecondExternal true false 8
setup_fixed_benchmark second8 where { comparisonConfig with expectedHash := some (hash (8 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def second12 := runPolySecondExternal true false 12
setup_fixed_benchmark second12 where { comparisonConfig with expectedHash := some (hash (12 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def check4 := runPolyCheckExternal true false 4
setup_fixed_benchmark check4 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }
def check8 := runPolyCheckExternal true false 8
setup_fixed_benchmark check8 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }
def check12 := runPolyCheckExternal true false 12
setup_fixed_benchmark check12 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }

end Mv.Full

namespace Mv.Deficient

def second4 := runPolySecondExternal true true 4
setup_fixed_benchmark second4 where { comparisonConfig with expectedHash := some (hash (2 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def second8 := runPolySecondExternal true true 8
setup_fixed_benchmark second8 where { comparisonConfig with expectedHash := some (hash (4 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def second12 := runPolySecondExternal true true 12
setup_fixed_benchmark second12 where { comparisonConfig with expectedHash := some (hash (6 : Nat)), tags := #["comparison", "external", "poly-reference"] }
def check4 := runPolyCheckExternal true true 4
setup_fixed_benchmark check4 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }
def check8 := runPolyCheckExternal true true 8
setup_fixed_benchmark check8 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }
def check12 := runPolyCheckExternal true true 12
setup_fixed_benchmark check12 where { comparisonConfig with expectedHash := some (hash true), tags := #["comparison", "external", "poly-reference"] }

end Mv.Deficient

end Comparison

/-- Default CI verifies the smallest canonical polynomial rung of every
carrier/rank/operation combination. Larger fixed cases remain registered and
can be verified explicitly with `verify --tag polynomial`. -/
def verifyOrdinary : IO UInt32 := do
  let parametric ← LeanBench.allRuntimeEntries
  let fixed ← LeanBench.allFixedRuntimeEntries
  let names := (parametric.map (·.spec.name)).toList ++
    ((fixed.filter fun e => e.spec.config.tags.contains "smoke").map (·.spec.name)).toList
  let reports ← LeanBench.verify names
  IO.println (LeanBench.Format.fmtCombinedVerify reports)
  return if reports.passed then 0 else 1

end Hex.RankBench

/-- Runtime panic policy, matching Lean's own command-line driver. -/
@[extern "lean_internal_set_exit_on_panic"]
private opaque exitOnPanic (enabled : Bool) : BaseIO Unit

def main (args : List String) : IO UInt32 := do
  -- Pure parametric prep uses panic! on invalid fixtures; fail closed rather
  -- than allowing Lean's default panic value to become a timing sample.
  exitOnPanic true
  match args with
  | ["verify"] => Hex.RankBench.verifyOrdinary
  | _ => LeanBench.Cli.dispatch args
