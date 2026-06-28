/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexModArith
import LeanBench

/-!
Benchmark registrations for `hex-mod-arith`.

This Phase 4 infrastructure slice measures the public `ZMod64` operation
surface over a fixed word-sized prime modulus, with deterministic prepared
inputs and compact checksums as observables.

Scientific registrations:

* `runConstructChecksum`: `ZMod64.ofNat`, `O(n)`.
* `runCastChecksum`: natural and integer casts, `O(n)`.
* `runAddChecksum`: `ZMod64.add`, `O(n)`.
* `runSubChecksum`: `ZMod64.sub`, `O(n)`.
* `runMulChecksum`: extern-backed `ZMod64.mul`, `O(n)`.
* `runPow`: exponentiation by squaring over an `n`-bit exponent, `O(n)`.
* `runInvChecksum`: `ZMod64.inv`, `O(n)` over fixed-word inputs.
* `runBarrettMulModChain`: `BarrettCtx.mulMod`, `O(n)`.
* `runMontToChecksum`: `MontCtx.toMont`, `O(n)`.
* `runMontMulChain`: `MontCtx.mulMont`, `O(n)`.
* `runMontFromChecksum`: `MontCtx.fromMont`, `O(n)`.
* `runBarrettCompareChain` / `runMontCompareChain`: common-domain
  Barrett/Montgomery multiplication comparison, `O(n)`.
-/

namespace Hex.ModArithBench

/-- Shared small odd prime modulus in the Barrett/Montgomery overlap. -/
def benchModulus : Nat :=
  65_537

private instance benchBounds : ZMod64.Bounds benchModulus :=
  ⟨by decide, by decide⟩

instance {p : Nat} [ZMod64.Bounds p] : Hashable (ZMod64 p) where
  hash a := hash a.toNat

instance {p : Nat} [ZMod64.Bounds p] : Hashable (MontResidue p) where
  hash a := hash a.toNat

/-- Shared executable modulus word. -/
def benchModulusWord : UInt64 :=
  UInt64.ofNat benchModulus

/-- Barrett context for the benchmark modulus. -/
def barrettCtx : BarrettCtx benchModulus :=
  { modulus := benchModulusWord
    modulus_eq := by decide
    toUInt64Ctx := _root_.BarrettCtx.mk benchModulusWord (by decide) (by decide) }

/-- Montgomery context for the benchmark modulus. -/
def montCtx : MontCtx benchModulus :=
  { modulus := benchModulusWord
    modulus_eq := by decide
    toUInt64Ctx := _root_.MontCtx.mk benchModulusWord (by decide) }

/-- One prepared binary-operation sample. -/
structure BinarySample where
  lhs : ZMod64 benchModulus
  rhs : ZMod64 benchModulus
  deriving Hashable

/-- Prepared natural representatives for construction and cast benchmarks. -/
structure ConstructInput where
  values : Array Nat
  deriving Hashable

/-- Prepared representatives for natural and integer cast benchmarks. -/
structure CastInput where
  natValues : Array Nat
  intValues : Array Int
  deriving Hashable

/-- Prepared samples for binary operations. -/
structure BinaryInput where
  samples : Array BinarySample
  deriving Hashable

/-- Prepared samples for unary residue operations. -/
structure UnaryInput where
  residues : Array (ZMod64 benchModulus)
  deriving Hashable

/-- Prepared input for exponentiation. -/
structure PowInput where
  base : ZMod64 benchModulus
  exponent : Nat
  deriving Hashable

/-- Prepared Montgomery-form residues for hot-loop benchmarks. -/
structure MontInput where
  residues : Array (ZMod64 benchModulus)
  montResidues : Array (MontResidue benchModulus)
  deriving Hashable

/-- Deterministic representative generator, intentionally spanning many wraps. -/
def rawValueAt (i salt : Nat) : Nat :=
  ((i + 1) * 1_103_515_245 +
    (i + 17) * 12_345 +
    (salt + 97) * 65_537 +
    i * i * 31) % 4_294_967_291

/-- Deterministic residue generator. -/
def residueAt (i salt : Nat) : ZMod64 benchModulus :=
  ZMod64.ofNat benchModulus (rawValueAt i salt)

/-- Deterministic wrapping mix for compact benchmark result summaries. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Hot-loop multiplier for very fast checksum-style benchmarks. -/
def checksumInnerRepeats : Nat :=
  2048

/-- Hot-loop multiplier for addition checksums. -/
def addInnerRepeats : Nat :=
  512

/-- Hot-loop multiplier for extern-backed multiplication checksums. -/
def mulInnerRepeats : Nat :=
  32

/-- Hot-loop multiplier for repeated exponentiation by squaring. -/
def powInnerRepeats : Nat :=
  256

/-- Hot-loop multiplier for the Barrett chain benchmark. -/
def barrettInnerRepeats : Nat :=
  256

/-- Stable checksum for standard residues. -/
def checksumZMod (acc : UInt64) (x : ZMod64 benchModulus) : UInt64 :=
  mixWord acc x.toUInt64

/-- Stable checksum for Montgomery-form residues. -/
def checksumMont (acc : UInt64) (x : MontResidue benchModulus) : UInt64 :=
  mixWord acc x.toUInt64

/-- Per-parameter fixture for construction benchmarks. -/
def prepConstructInput (n : Nat) : ConstructInput :=
  { values := (Array.range n).map fun i => rawValueAt i 11 }

/-- Per-parameter fixture for cast benchmarks. -/
def prepCastInput (n : Nat) : CastInput :=
  { natValues := (Array.range n).map fun i => rawValueAt i 23
    intValues := (Array.range n).map fun i =>
      let value := Int.ofNat (rawValueAt i 37)
      if i % 2 = 0 then value else -value }

/-- Per-parameter fixture for binary operation benchmarks. -/
def prepBinaryInput (n : Nat) : BinaryInput :=
  { samples := (Array.range n).map fun i =>
      { lhs := residueAt i 41
        rhs := residueAt i 83 } }

/-- Per-parameter fixture for unary operation benchmarks. -/
def prepUnaryInput (n : Nat) : UnaryInput :=
  { residues := (Array.range n).map fun i => residueAt i 127 }

/-- Per-parameter fixture for exponentiation by squaring. -/
def prepPowInput (n : Nat) : PowInput :=
  { base := residueAt n 149
    exponent := 2 ^ n - 1 }

/-- Per-parameter fixture for Montgomery conversion and multiplication. -/
def prepMontInput (n : Nat) : MontInput :=
  let residues := (Array.range n).map fun i => residueAt i 181
  { residues := residues
    montResidues := residues.map montCtx.toMont }

/-- One checksum pass constructing residues from natural representatives. -/
def constructChecksumOnce (input : ConstructInput) (seed : UInt64) : UInt64 :=
  input.values.foldl
    (fun acc n => checksumZMod acc (ZMod64.ofNat benchModulus n))
    seed

/-- Benchmark target: construct residues from natural representatives. -/
def runConstructChecksum (input : ConstructInput) : UInt64 :=
  let rec go (remaining : Nat) (acc : UInt64) : UInt64 :=
    match remaining with
    | 0 => acc
    | k + 1 => go k (constructChecksumOnce input acc)
  go checksumInnerRepeats 0

/-- Benchmark target: natural and integer casts. -/
def runCastChecksum (input : CastInput) : UInt64 :=
  let acc :=
    input.natValues.foldl
      (fun acc n => checksumZMod acc ((n : Nat) : ZMod64 benchModulus))
      0
  input.intValues.foldl
    (fun acc i => checksumZMod acc (ZMod64.intCast benchModulus i))
    acc

/-- One checksum pass for batched addition. -/
def addSampleChecksum (sample : BinarySample) (seed : UInt64) : UInt64 :=
  let rec go (remaining : Nat) (acc : UInt64) : UInt64 :=
    match remaining with
    | 0 => acc
    | k + 1 => go k (checksumZMod acc (sample.lhs + sample.rhs))
  go addInnerRepeats seed

/-- Benchmark target: batched addition. -/
def runAddChecksum (input : BinaryInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => addSampleChecksum sample acc)
    0

/-- One checksum pass for batched subtraction. -/
def subChecksumOnce (input : BinaryInput) (seed : UInt64) : UInt64 :=
  input.samples.foldl
    (fun acc sample => checksumZMod acc (sample.lhs - sample.rhs))
    seed

/-- Benchmark target: batched subtraction. -/
def runSubChecksum (input : BinaryInput) : UInt64 :=
  let rec go (remaining : Nat) (acc : UInt64) : UInt64 :=
    match remaining with
    | 0 => acc
    | k + 1 => go k (subChecksumOnce input acc)
  go checksumInnerRepeats 0

/-- One checksum pass for batched extern-backed multiplication. -/
def mulChecksumOnce (input : BinaryInput) (seed : UInt64) : UInt64 :=
  input.samples.foldl
    (fun acc sample => checksumZMod acc (sample.lhs * sample.rhs))
    seed

/-- Benchmark target: batched extern-backed multiplication. -/
def runMulChecksum (input : BinaryInput) : UInt64 :=
  let rec go (remaining : Nat) (acc : UInt64) : UInt64 :=
    match remaining with
    | 0 => acc
    | k + 1 => go k (mulChecksumOnce input acc)
  go mulInnerRepeats 0

/-- Benchmark target: exponentiation by squaring with an `n`-bit exponent. -/
def runPow (input : PowInput) : UInt64 :=
  let rec go (remaining : Nat) (acc : UInt64) : UInt64 :=
    match remaining with
    | 0 => acc
    | k + 1 =>
        let base := input.base + ZMod64.ofNat benchModulus acc.toNat
        go k (checksumZMod acc (base ^ input.exponent))
  go powInnerRepeats 0

/-- Benchmark target: batched modular inverse candidates. -/
def runInvChecksum (input : UnaryInput) : UInt64 :=
  input.residues.foldl
    (fun acc x => checksumZMod acc x.inv)
    0

/-- One Barrett-context multiplication chain. -/
def barrettMulModChainOnce (input : UnaryInput)
    (seed : ZMod64 benchModulus) : ZMod64 benchModulus :=
  let acc := input.residues.foldl
    (fun acc x => barrettCtx.mulMod acc x)
    seed
  acc

/-- Benchmark target: Barrett-context multiplication chain. -/
def runBarrettMulModChain (input : UnaryInput) : UInt64 :=
  let rec go (remaining : Nat) (acc : ZMod64 benchModulus) : ZMod64 benchModulus :=
    match remaining with
    | 0 => acc
    | k + 1 => go k (barrettMulModChainOnce input acc)
  (go barrettInnerRepeats (1 : ZMod64 benchModulus)).toUInt64

/-- Benchmark target: Montgomery conversion into hot-loop representation. -/
def runMontToChecksum (input : MontInput) : UInt64 :=
  input.residues.foldl
    (fun acc x => checksumMont acc (montCtx.toMont x))
    0

/-- Benchmark target: Montgomery-form multiplication chain. -/
def runMontMulChain (input : MontInput) : UInt64 :=
  let acc := input.montResidues.foldl
    (fun acc x => montCtx.mulMont acc x)
    (montCtx.toMont (1 : ZMod64 benchModulus))
  (montCtx.fromMont acc).toUInt64

/-- Benchmark target: conversion out of Montgomery representation. -/
def runMontFromChecksum (input : MontInput) : UInt64 :=
  input.montResidues.foldl
    (fun acc x => checksumZMod acc (montCtx.fromMont x))
    0

/-- Compare target: one Barrett multiplication chain over the Montgomery input. -/
def runBarrettCompareChain (input : MontInput) : UInt64 :=
  let acc := input.residues.foldl
    (fun acc x => barrettCtx.mulMod acc x)
    (1 : ZMod64 benchModulus)
  acc.toUInt64

/-- Compare target: one Montgomery multiplication chain over the same residues. -/
def runMontCompareChain (input : MontInput) : UInt64 :=
  runMontMulChain input

setup_benchmark runConstructChecksum n => n
  with prep := prepConstructInput
  where {
    paramFloor := 131072
    paramCeiling := 1048576
    paramSchedule := .custom #[131072, 262144, 524288, 1048576]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

setup_benchmark runCastChecksum n => n
  with prep := prepCastInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
  }

setup_benchmark runAddChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 65536
    paramCeiling := 262144
    paramSchedule := .custom #[65536, 131072, 262144]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

setup_benchmark runSubChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 131072
    paramCeiling := 1048576
    paramSchedule := .custom #[131072, 262144, 524288, 1048576]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

setup_benchmark runMulChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 131072
    paramCeiling := 524288
    paramSchedule := .custom #[131072, 262144, 524288]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

setup_benchmark runPow n => n
  with prep := prepPowInput
  where {
    paramFloor := 65536
    paramCeiling := 262144
    paramSchedule := .custom #[65536, 131072, 262144]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

setup_benchmark runInvChecksum n => n
  with prep := prepUnaryInput
  where {
    paramFloor := 2048
    paramCeiling := 32768
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 300000000
  }

setup_benchmark runBarrettMulModChain n => n
  with prep := prepUnaryInput
  where {
    paramFloor := 131072
    paramCeiling := 1048576
    paramSchedule := .custom #[131072, 262144, 524288, 1048576]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 500000000
  }

setup_benchmark runMontToChecksum n => n
  with prep := prepMontInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
  }

setup_benchmark runMontMulChain n => n
  with prep := prepMontInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
  }

setup_benchmark runMontFromChecksum n => n
  with prep := prepMontInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
  }

-- Cost model: one linear fold over `n` prepared residues; Barrett context prep is fixed.
setup_benchmark runBarrettCompareChain n => n
  with prep := prepMontInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
  }

-- Cost model: one linear fold over `n` prepared Montgomery residues plus one final conversion.
setup_benchmark runMontCompareChain n => n
  with prep := prepMontInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 300000000
  }

end Hex.ModArithBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
