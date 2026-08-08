/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import CompPoly.Multivariate.CMvPolynomial
import HexMvPoly.Corpus
import LeanBench

/-!
External native comparator driver for CompPoly's `CMvPolynomial`.

Inputs come from `HexMvPoly.Corpus`; construction is outside the timed
region.  One representative operation covers each HexMvPoly Phase 4 family.
-/

namespace CompPoly.MvPolyBench

open CPoly
open Hex
open Hex.MvPolyBench.Corpus

abbrev P4 (R : Type) [Zero R] := CMvPolynomial 4 R
abbrev P8 (R : Type) [Zero R] := CMvPolynomial 8 R

def ofTerms [Zero R] [BEq R] [LawfulBEq R]
    (terms : List (Mono n × R)) : CMvPolynomial n R :=
  Lawful.fromUnlawful <| Unlawful.ofList terms

def checksum [Zero R] [Hashable R] (p : CMvPolynomial n R) : UInt64 :=
  p.1.toList.foldl
    (fun acc term => mixHash (mixHash acc (hash term.1.toList)) (hash term.2))
    0

structure AdditionInput where
  left : P4 Int
  right : P4 Int

instance : Hashable AdditionInput where
  hash input := mixHash (checksum input.left) (checksum input.right)

def prepSparseAddition (n : Nat) : AdditionInput :=
  { left := ofTerms (intTerms n 3 (fun i => axisMono 0 i))
    right := ofTerms (intTerms n 5 (fun i => axisMono 0 (n + i))) }

def runSparseAddition (input : AdditionInput) : UInt64 :=
  checksum (input.left + input.right)

structure MultiplicationInput where
  left : P8 Int
  right : P8 Int

instance : Hashable MultiplicationInput where
  hash input := mixHash (checksum input.left) (checksum input.right)

def prepSparseMultiplication (n : Nat) : MultiplicationInput :=
  { left := ofTerms (intTerms n 19 (axisMono 6))
    right := ofTerms (intTerms n 23 (axisMono 7)) }

def runSparseMultiplication (input : MultiplicationInput) : UInt64 :=
  checksum (input.left * input.right)

structure CancellationInput where
  left : P4 Int
  right : P4 Int

instance : Hashable CancellationInput where
  hash input := mixHash (checksum input.left) (checksum input.right)

def prepCancellationArithmetic (n : Nat) : CancellationInput :=
  { left := ofTerms (intTerms n 37 (fun i => axisMono 0 (i + 1)))
    right := ofTerms (intTerms n 41 (fun i => axisMono 1 (i + 1))) }

def runCancellationArithmetic (input : CancellationInput) : UInt64 :=
  checksum <|
    (input.left + input.right) * (input.left + input.right) -
      (input.left * input.left + input.right * input.right)

structure StructuralInput where
  polynomial : P4 Int

instance : Hashable StructuralInput where
  hash input := checksum input.polynomial

def prepStructuralCollisions (n : Nat) : StructuralInput :=
  { polynomial := ofTerms (intTerms n 53 (collisionMono n)) }

def rename [Zero R] [Add R] [BEq R] [LawfulBEq R]
    (f : Fin n → Fin m) (p : CMvPolynomial n R) : CMvPolynomial m R :=
  let renameMonomial (mono : Mono n) : Mono m :=
    Vector.ofFn fun j =>
      (Finset.univ.filter fun i => f i = j).sum fun i => mono.get i
  p.1.toList.foldl
    (fun acc term =>
      acc + CMvPolynomial.monomial (renameMonomial term.1) term.2)
    0

def runStructuralCollisions (input : StructuralInput) : UInt64 :=
  checksum <|
    rename
      (fun i : Fin 4 =>
        if i.val % 2 = 0 then (0 : Fin 2) else (1 : Fin 2))
      input.polynomial

structure SumOfSquaresInput where
  first : P4 Int
  second : P4 Int
  third : P4 Int

instance : Hashable SumOfSquaresInput where
  hash input :=
    mixHash (checksum input.first)
      (mixHash (checksum input.second) (checksum input.third))

def prepSumOfSquares (n : Nat) : SumOfSquaresInput :=
  { first := ofTerms (intTerms n 59 (patternedMono n · 3))
    second := ofTerms (intTerms n 61 (patternedMono n · 7))
    third := ofTerms (intTerms n 67 (patternedMono n · 11)) }

def runSumOfSquaresArithmetic (input : SumOfSquaresInput) : UInt64 :=
  checksum <|
    input.first * input.first +
      input.second * input.second +
      input.third * input.third

/- CompPoly addition uses one ExtTreeMap merge plus an output filter, both
linear in the two canonical `n`-term inputs. -/
setup_benchmark runSparseAddition n => (n)
  with prep := prepSparseAddition
  where {
    paramSchedule := .custom #[128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- CompPoly's nested fold computes `{term} + growingMap`, so every inner step
re-folds the growing right tree into a singleton. Summing those tree merges
over both input supports gives `O(n³ log n)` work. -/
setup_benchmark runSparseMultiplication n => (n * n * n * Nat.log2 (n + 1))
  with prep := prepSparseMultiplication
  where {
    paramSchedule := .custom #[8, 12, 16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- The identity performs three CompPoly nested-fold products. Each inherits the
`O(n³ log n)` growing-right-tree merge cost derived above. -/
setup_benchmark runCancellationArithmetic n => (n * n * n * Nat.log2 (n + 1))
  with prep := prepCancellationArithmetic
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Collision-heavy rename visits `n` source terms and merges them into a
bounded eight-key target map, so the work is linear. -/
setup_benchmark runStructuralCollisions n => (n)
  with prep := prepStructuralCollisions
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 768, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Three sparse squares use CompPoly's nested-fold multiplication and therefore
perform `O(n³ log n)` growing-right-tree merge work. -/
setup_benchmark runSumOfSquaresArithmetic n => (n * n * n * Nat.log2 (n + 1))
  with prep := prepSumOfSquares
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

end CompPoly.MvPolyBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
