/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvPolyBench.Corpus
import LeanBench

/-!
Native benchmark registrations for `hex-mv-poly`.

The registrations cover the five SPEC input families. Separable operations are
registered independently so a timing change is attributable to one algorithm:

* sparse addition under lex, grlex, and grevlex, `O(n log n)`;
* low- and high-collision sparse products, `O(n² log n)`;
* cancellation-heavy `Int` and genuine-fraction `Rat` identities,
  `O(n² log n)`;
* rename, partial evaluation, and substitution collisions, respectively
  `O(n)`, `O(n)`, and `O(n log n)`;
* sums of three genuinely multivariate squares, `O(n² log n)`.

Input construction is hoisted through `prep`. Timed targets return structural
hashes of the canonical outputs, so result traversal stays within the declared
operation cost and gives LeanBench a conformance signal.

`HexMvPolyBench.Corpus` owns the representation-independent deterministic term
generators. Phase 4's informational CompPoly and Mathlib `MvSparsePoly`
adapters consume those generators externally; neither comparator is imported
here, keeping the native executable Mathlib-free.

Each child batch autotunes to about 200 ms. The default 10x executable-spawn
floor would disqualify every row on this host, so
`signalFloorMultiplier := 1.0` keeps the autotuned in-process measurements.
-/

namespace Hex.MvPolyBench

open Hex
open Hex.MvPoly
open Corpus

abbrev LexP4 (R : Type) [Zero R] := MvPoly 4 R Mono.lex
abbrev GrlexP4 (R : Type) [Zero R] := MvPoly 4 R Mono.grlex
abbrev GrlexP8 (R : Type) [Zero R] := MvPoly 8 R Mono.grlex
abbrev GrevlexP4 (R : Type) [Zero R] := MvPoly 4 R Mono.grevlex
abbrev GrevlexP2 (R : Type) [Zero R] := MvPoly 2 R Mono.grevlex

/-- Stable structural hash of a canonical sparse polynomial. -/
def checksum [Zero R] [Hashable R] {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n R cmp) : UInt64 :=
  p.termsList.foldl
    (fun acc term => mixHash (mixHash acc (hash term.1.toList)) (hash term.2))
    0

instance [Zero R] [Hashable R] {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    Hashable (MvPoly n R cmp) where
  hash := checksum

def sparseInt {arity : Nat} (cmp : Mono arity → Mono arity → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (size salt : Nat) (key : Nat → Mono arity) : MvPoly arity Int cmp :=
  ofTerms (intTerms size salt key)

def sparseFrac {arity : Nat} (cmp : Mono arity → Mono arity → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (size salt : Nat) (key : Nat → Mono arity) : MvPoly arity Rat cmp :=
  ofTerms (fracTerms size salt key)

structure AdditionInput where
  lexLeft : LexP4 Int
  lexRight : LexP4 Int
  grlexLeft : GrlexP4 Int
  grlexRight : GrlexP4 Int
  grevlexLeft : GrevlexP4 Int
  grevlexRight : GrevlexP4 Int
  deriving Hashable

def prepSparseAddition (n : Nat) : AdditionInput :=
  { lexLeft := sparseInt Mono.lex n 3 (fun i => axisMono 0 i)
    lexRight := sparseInt Mono.lex n 5 (fun i => axisMono 0 (n + i))
    grlexLeft := sparseInt Mono.grlex n 7 (fun i => axisMono 0 (2 * i))
    grlexRight := sparseInt Mono.grlex n 11 (fun i => axisMono 0 (2 * i + 1))
    grevlexLeft := sparseInt Mono.grevlex n 13 (patternedMono n · 1)
    grevlexRight := sparseInt Mono.grevlex n 17 (patternedMono n · 5) }

def runSparseAdditionLex (input : AdditionInput) : UInt64 :=
  checksum (input.lexLeft + input.lexRight)

def runSparseAdditionGrlex (input : AdditionInput) : UInt64 :=
  checksum (input.grlexLeft + input.grlexRight)

def runSparseAdditionGrevlex (input : AdditionInput) : UInt64 :=
  checksum (input.grevlexLeft + input.grevlexRight)

structure MultiplicationInput where
  lowLeft : GrlexP8 Int
  lowRight : GrlexP8 Int
  highLeft : GrevlexP2 Rat
  highRight : GrevlexP2 Rat
  deriving Hashable

def prepSparseMultiplication (n : Nat) : MultiplicationInput :=
  { lowLeft := sparseInt Mono.grlex n 19 (axisMono 6)
    lowRight := sparseInt Mono.grlex n 23 (axisMono 7)
    highLeft := sparseFrac Mono.grevlex n 29 (axisMono 1)
    highRight := sparseFrac Mono.grevlex n 31 (axisMono 1) }

def runSparseMultiplicationLow (input : MultiplicationInput) : UInt64 :=
  checksum (input.lowLeft * input.lowRight)

def runSparseMultiplicationHigh (input : MultiplicationInput) : UInt64 :=
  checksum (input.highLeft * input.highRight)

structure CancellationInput where
  intLeft : LexP4 Int
  intRight : LexP4 Int
  ratLeft : GrevlexP4 Rat
  ratRight : GrevlexP4 Rat
  deriving Hashable

def prepCancellationArithmetic (n : Nat) : CancellationInput :=
  { intLeft := sparseInt Mono.lex n 37 (fun i => axisMono 0 (i + 1))
    intRight := sparseInt Mono.lex n 41 (fun i => axisMono 1 (i + 1))
    ratLeft := sparseFrac Mono.grevlex n 43 (fun i => axisMono 0 (i + 1))
    ratRight := sparseFrac Mono.grevlex n 47 (fun i => axisMono 1 (i + 1)) }

def runCancellationInt (input : CancellationInput) : UInt64 :=
  checksum <|
    (input.intLeft + input.intRight) * (input.intLeft + input.intRight) -
      (input.intLeft * input.intLeft + input.intRight * input.intRight)

def runCancellationRat (input : CancellationInput) : UInt64 :=
  checksum <|
    (input.ratLeft + input.ratRight) * (input.ratLeft + input.ratRight) -
      (input.ratLeft * input.ratLeft + input.ratRight * input.ratRight)

structure StructuralInput where
  collisionPoly : GrlexP4 Int
  partialPoly : GrlexP4 Int
  deriving Hashable

def prepStructuralCollisions (n : Nat) : StructuralInput :=
  { collisionPoly := sparseInt Mono.grlex n 53 (collisionMono n)
    partialPoly := sparseInt Mono.grlex n 71 partialEvalMono }

def runRenameCollisions (input : StructuralInput) : UInt64 :=
  let renamed : GrevlexP2 Int :=
    rename Mono.grevlex
      (fun i => if i.val % 2 = 0 then 0 else 1)
      input.collisionPoly
  checksum renamed

def runPartialEvalCollisions (input : StructuralInput) : UInt64 :=
  let partiallyEvaluated :=
    partialEval
      (fun i =>
        if i.val = 0 then some (2 : Int)
        else if i.val = 2 then some (-3)
        else none)
      input.partialPoly
  checksum partiallyEvaluated

def runSubstCollisions (input : StructuralInput) : UInt64 :=
  let substituted : GrevlexP2 Int :=
    subst (targetCmp := Mono.grevlex)
      (fun i => if i.val % 2 = 0 then X 0 else C 3 * X 1)
      input.collisionPoly
  checksum substituted

structure SumOfSquaresInput where
  first : GrevlexP4 Int
  second : GrevlexP4 Int
  third : GrevlexP4 Int
  deriving Hashable

def prepSumOfSquares (n : Nat) : SumOfSquaresInput :=
  { first := sparseInt Mono.grevlex n 59 (patternedMono n · 3)
    second := sparseInt Mono.grevlex n 61 (patternedMono n · 7)
    third := sparseInt Mono.grevlex n 67 (patternedMono n · 11) }

def runSumOfSquaresArithmetic (input : SumOfSquaresInput) : UInt64 :=
  checksum <|
    input.first * input.first +
      input.second * input.second +
      input.third * input.third

#guard
  let input := prepSumOfSquares 32
  termCount
      (input.first * input.first +
        input.second * input.second +
        input.third * input.third) =
    3 * 32 * 33 / 2

/- `mergeWith?` folds the smaller `n`-term lex tree into the larger one; each
`alter` is logarithmic. Structural hashing is linear in the output support. -/
setup_benchmark runSparseAdditionLex n => n * Nat.log2 (n + 1)
  with prep := prepSparseAddition
  where {
    paramSchedule := .custom #[128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- The same disjoint/interleaved addition under graded lexicographic order. -/
setup_benchmark runSparseAdditionGrlex n => n * Nat.log2 (n + 1)
  with prep := prepSparseAddition
  where {
    paramSchedule := .custom #[128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: graded reverse lexicographic addition performs the same `n`
logarithmic tree updates as the other orders, now on genuinely multivariate
monomials. -/
setup_benchmark runSparseAdditionGrevlex n => n * Nat.log2 (n + 1)
  with prep := prepSparseAddition
  where {
    paramSchedule := .custom #[128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- The low-collision output has `n²` terms and every Gustavson accumulator
update performs a logarithmic tree operation. -/
setup_benchmark runSparseMultiplicationLow n => n * n * Nat.log2 (n * n + 1)
  with prep := prepSparseMultiplication
  where {
    paramSchedule := .custom #[8, 12, 16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: the high-collision rational product visits `n²` source pairs but
accumulates into `2n-1` keys, so each accumulator update is logarithmic in `n`.
Bounded non-unit denominators exercise Rat normalization without changing the
sparse structural parameter. -/
setup_benchmark runSparseMultiplicationHigh n => n * n * Nat.log2 (n + 1)
  with prep := prepSparseMultiplication
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Expanding the integer identity `(a + b)² - (a² + b²)` performs three
sparse products and cancels both square components while retaining the `n²`
nonzero cross terms. Each accumulator update is logarithmic in an output of at
most `O(n²)` terms. -/
setup_benchmark runCancellationInt n => n * n * Nat.log2 (n * n + 1)
  with prep := prepCancellationArithmetic
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: the same cancellation identity over bounded genuine fractions
performs quadratically many sparse updates. Rat addition and multiplication
take nontrivial normalization paths; the finite denominator set keeps
coefficient bit-size subordinate to the `n²` sparse updates. -/
setup_benchmark runCancellationRat n => n * n * Nat.log2 (n * n + 1)
  with prep := prepCancellationArithmetic
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: rename maps `n` fixed-arity source monomials into eight
destination keys. Both monomial mapping and bounded-size tree updates are
constant per term, giving linear work. -/
setup_benchmark runRenameCollisions n => n
  with prep := prepStructuralCollisions
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 768, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Cost model: partial evaluation also combines `n` source terms into eight
keys. The evaluated exponents are bounded below 32, so non-unit coefficient
powers and destination-tree updates take constant work per source term, giving
linear work. -/
setup_benchmark runPartialEvalCollisions n => n
  with prep := prepStructuralCollisions
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 768, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Substitution maps every source variable to a single target monomial and
combines `n` terms into eight keys. Source exponents reach `O(n)`, so monomial
images are powered by repeated squaring in `O(log n)` steps per term. -/
setup_benchmark runSubstCollisions n => n * Nat.log2 (n + 1)
  with prep := prepStructuralCollisions
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 768, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- The target sums three squares of genuinely multivariate `n`-term
polynomials. It visits `3n²` source pairs and performs logarithmic updates into
the canonical output tree. -/
setup_benchmark runSumOfSquaresArithmetic n => n * n * Nat.log2 (n * n + 1)
  with prep := prepSumOfSquares
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

end Hex.MvPolyBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
