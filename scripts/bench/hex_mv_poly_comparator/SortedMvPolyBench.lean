/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvPolyMathlib.ProofProbe.Support
import LeanBench

/-!
External native driver for the canonical sorted-list `MvSparsePoly` proxy.

The pinned Mathlib revision does not contain the still-open upstream
`MvSparsePoly` PR series. This driver measures the same local, balanced-merge
adapter used by the kernel representation sweep.
-/

namespace MvSparsePolyProxy.MvPolyBench

open Hex
open Hex.MvPolyBench.Corpus
open HexMvPolyMathlib.ProofProbe

abbrev P4 (R : Type) := Sorted.Poly 4 R
abbrev P8 (R : Type) := Sorted.Poly 8 R

def checksum [Hashable R] (p : Sorted.Poly n R) : UInt64 :=
  p.terms.foldl
    (fun acc term => mixHash (mixHash acc (hash term.1.toList)) (hash term.2))
    0

structure AdditionInput where
  left : P4 Int
  right : P4 Int

instance : Hashable AdditionInput where
  hash input := mixHash (checksum input.left) (checksum input.right)

def prepSparseAddition (n : Nat) : AdditionInput :=
  { left := Sorted.ofTerms (intTerms n 3 (fun i => axisMono 0 i))
    right := Sorted.ofTerms (intTerms n 5 (fun i => axisMono 0 (n + i))) }

def runSparseAddition (input : AdditionInput) : UInt64 :=
  checksum (input.left + input.right)

structure MultiplicationInput where
  left : P8 Int
  right : P8 Int

instance : Hashable MultiplicationInput where
  hash input := mixHash (checksum input.left) (checksum input.right)

def prepSparseMultiplication (n : Nat) : MultiplicationInput :=
  { left := Sorted.ofTerms (intTerms n 19 (axisMono 6))
    right := Sorted.ofTerms (intTerms n 23 (axisMono 7)) }

def runSparseMultiplication (input : MultiplicationInput) : UInt64 :=
  checksum (input.left * input.right)

structure CancellationInput where
  left : P4 Int
  right : P4 Int

instance : Hashable CancellationInput where
  hash input := mixHash (checksum input.left) (checksum input.right)

def prepCancellationArithmetic (n : Nat) : CancellationInput :=
  { left := Sorted.ofTerms (intTerms n 37 (fun i => axisMono 0 (i + 1)))
    right := Sorted.ofTerms (intTerms n 41 (fun i => axisMono 1 (i + 1))) }

def runCancellationArithmetic (input : CancellationInput) : UInt64 :=
  checksum <|
    (input.left + input.right) * (input.left + input.right) -
      (input.left * input.left + input.right * input.right)

structure StructuralInput where
  polynomial : P4 Int

instance : Hashable StructuralInput where
  hash input := checksum input.polynomial

def prepStructuralCollisions (n : Nat) : StructuralInput :=
  { polynomial := Sorted.ofTerms (intTerms n 53 (collisionMono n)) }

def runStructuralCollisions (input : StructuralInput) : UInt64 :=
  checksum <|
    Sorted.rename
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
  { first := Sorted.ofTerms (intTerms n 59 (patternedMono n · 3))
    second := Sorted.ofTerms (intTerms n 61 (patternedMono n · 7))
    third := Sorted.ofTerms (intTerms n 67 (patternedMono n · 11)) }

def runSumOfSquaresArithmetic (input : SumOfSquaresInput) : UInt64 :=
  checksum <|
    input.first * input.first +
      input.second * input.second +
      input.third * input.third

/- Sorted addition is one linear merge over two canonical `n`-term lists. -/
setup_benchmark runSparseAddition n => n
  with prep := prepSparseAddition
  where {
    paramSchedule := .custom #[128, 256, 512, 1024, 2048, 4096]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Multiplication creates `n` sorted rows of length `n` and combines them in
balanced merge rounds, for `O(n² log n)` work including output hashing. -/
setup_benchmark runSparseMultiplication n => n * n * Nat.log2 (n + 1)
  with prep := prepSparseMultiplication
  where {
    paramSchedule := .custom #[8, 12, 16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- The identity performs three sorted sparse products and linear merges, each
bounded by `O(n² log n)`. -/
setup_benchmark runCancellationArithmetic n => n * n * Nat.log2 (n + 1)
  with prep := prepCancellationArithmetic
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Rename visits `n` source terms and inserts into a target support bounded by
eight keys, giving linear work. -/
setup_benchmark runStructuralCollisions n => n
  with prep := prepStructuralCollisions
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 768, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Three sorted sparse squares visit `3n²` pairs and use balanced row merges,
for `O(n² log n)` work including the output hash. -/
setup_benchmark runSumOfSquaresArithmetic n => n * n * Nat.log2 (n + 1)
  with prep := prepSumOfSquares
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end MvSparsePolyProxy.MvPolyBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
