/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvGcd.Families
import LeanBench

/-!
Fixed registrations for the `hex-mv-gcd` Phase 4 shape matrix.

The SPEC gives route-level probe bounds rather than a machine-operation model
for these families.  They are therefore named fixed rungs: the shape is part
of the stable registration name, and no asymptotic claim is inferred from
degree or arity alone.
-/

namespace Hex.MvGcdBench.Matrix

open Hex
open Hex.MvPoly
open Hex.MvGcdBench.Families

def runIntPair {n : Nat} (input : P n Int × P n Int) : UInt64 :=
  checksum (gcd input.1 input.2)

def runRatPair {n : Nat} (input : P n Rat × P n Rat) : UInt64 :=
  checksum (gcd input.1 input.2)

def runBrownPair {n : Nat} (input : P n Int × P n Int) : UInt64 :=
  match intBrownModularCert? GcdConfig.default input.1 input.2 with
  | none => 0
  | some cert => checksum cert.gcd

/-- Measure one bounded Brown image on a sparse input. A single prime cannot
stabilize CRT, so returning zero records an honest fast-backend decline
without sending the merge-gated smoke verifier into the mandatory dense PRS
fallback. Full end-to-end timeout measurements belong in the Phase 4 report. -/
def runSparseGapPair {n : Nat} (input : P n Int × P n Int) : UInt64 :=
  let cfg : GcdConfig :=
    { GcdConfig.default with brownPrimeFuel := 1, brownPointFuel := 2 }
  let cfg : GcdConfig := { cfg with heuristicBitBudget := 0 }
  match intConcreteProposal Mono.lex cfg input.1 input.2 |>.cert? with
  | none => 0
  | some cert => checksum cert.gcd

def runSquarefree {n : Nat} (input : P n Int) : UInt64 :=
  let decomp := sqfDecomp input
  decomp.factors.foldl
    (fun acc factor =>
      mixHash (mixHash acc (checksum factor.factor))
        (hash factor.multiplicity))
    (hash decomp.content)

def getCached (slot : IO.Ref (Option α)) (build : Unit → α) : IO α := do
  match ← slot.get with
  | some value => return value
  | none =>
      let value := build ()
      slot.set (some value)
      return value

def fixedConfig (expectedHash : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 3, maxSecondsPerCall := 12.0,
    warmupFirstIter := true, expectedHash := some expectedHash,
    tags := #[scheduledHardwareTag] }

def brownConfig (expectedHash : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 3, maxSecondsPerCall := 30.0,
    warmupFirstIter := true, expectedHash := some expectedHash,
    tags := #[scheduledHardwareTag] }

def stressConfig (expectedHash : UInt64) : LeanBench.FixedBenchmarkConfig :=
  { repeats := 3, maxSecondsPerCall := 30.0,
    warmupFirstIter := true, expectedHash := some expectedHash,
    tags := #[scheduledHardwareTag] }

initialize denseCoprime2 : IO.Ref (P 2 Int × P 2 Int) ←
  IO.mkRef (denseCoprime 2 1)
initialize denseCoprime3 : IO.Ref (P 3 Int × P 3 Int) ←
  IO.mkRef (denseCoprime 3 1)
initialize denseCoprime4 : IO.Ref (P 4 Int × P 4 Int) ←
  IO.mkRef (denseCoprime 4 1)
initialize denseCoprime5 : IO.Ref (P 5 Int × P 5 Int) ←
  IO.mkRef (denseCoprime 5 1)
initialize denseCoprime6 : IO.Ref (P 6 Int × P 6 Int) ←
  IO.mkRef (denseCoprime 6 1)
initialize denseCoprime7 : IO.Ref (P 7 Int × P 7 Int) ←
  IO.mkRef (denseCoprime 7 1)
initialize denseCoprime8 : IO.Ref (P 8 Int × P 8 Int) ←
  IO.mkRef (denseCoprime 8 1)

def runDenseCoprime2 (_ : Unit) : IO UInt64 :=
  return runIntPair (← denseCoprime2.get)
def runDenseCoprime3 (_ : Unit) : IO UInt64 :=
  return runIntPair (← denseCoprime3.get)
def runDenseCoprime4 (_ : Unit) : IO UInt64 :=
  return runIntPair (← denseCoprime4.get)
def runDenseCoprime5 (_ : Unit) : IO UInt64 :=
  return runIntPair (← denseCoprime5.get)
def runDenseCoprime6 (_ : Unit) : IO UInt64 :=
  return runIntPair (← denseCoprime6.get)
def runDenseCoprime7 (_ : Unit) : IO UInt64 :=
  return runIntPair (← denseCoprime7.get)
def runDenseCoprime8 (_ : Unit) : IO UInt64 :=
  return runIntPair (← denseCoprime8.get)

setup_fixed_benchmark runDenseCoprime2 where fixedConfig 0xc27ccbde88f7ee1a
setup_fixed_benchmark runDenseCoprime3 where fixedConfig 0x6a32dabd95a98e1c
setup_fixed_benchmark runDenseCoprime4 where fixedConfig 0xcb20c1eb884c258c
setup_fixed_benchmark runDenseCoprime5 where fixedConfig 0x72e28aef962316d6
setup_fixed_benchmark runDenseCoprime6 where fixedConfig 0xe471bb0a9f420adf
setup_fixed_benchmark runDenseCoprime7 where fixedConfig 0x7958e799d1931a08
setup_fixed_benchmark runDenseCoprime8 where fixedConfig 0x9389fe94a31dd629

initialize sparseCoprime2 : IO.Ref (P 2 Int × P 2 Int) ←
  IO.mkRef (sparseCoprime 2 128)
initialize sparseCoprime3 : IO.Ref (P 3 Int × P 3 Int) ←
  IO.mkRef (sparseCoprime 3 128)
initialize sparseCoprime4 : IO.Ref (P 4 Int × P 4 Int) ←
  IO.mkRef (sparseCoprime 4 128)
initialize sparseCoprime5 : IO.Ref (P 5 Int × P 5 Int) ←
  IO.mkRef (sparseCoprime 5 128)
initialize sparseCoprime6 : IO.Ref (P 6 Int × P 6 Int) ←
  IO.mkRef (sparseCoprime 6 128)
initialize sparseCoprime7 : IO.Ref (P 7 Int × P 7 Int) ←
  IO.mkRef (sparseCoprime 7 128)
initialize sparseCoprime8 : IO.Ref (P 8 Int × P 8 Int) ←
  IO.mkRef (sparseCoprime 8 128)

def runSparseCoprime2 (_ : Unit) : IO UInt64 :=
  return runIntPair (← sparseCoprime2.get)
def runSparseCoprime3 (_ : Unit) : IO UInt64 :=
  return runIntPair (← sparseCoprime3.get)
def runSparseCoprime4 (_ : Unit) : IO UInt64 :=
  return runIntPair (← sparseCoprime4.get)
def runSparseCoprime5 (_ : Unit) : IO UInt64 :=
  return runIntPair (← sparseCoprime5.get)
def runSparseCoprime6 (_ : Unit) : IO UInt64 :=
  return runIntPair (← sparseCoprime6.get)
def runSparseCoprime7 (_ : Unit) : IO UInt64 :=
  return runIntPair (← sparseCoprime7.get)
def runSparseCoprime8 (_ : Unit) : IO UInt64 :=
  return runIntPair (← sparseCoprime8.get)

setup_fixed_benchmark runSparseCoprime2 where fixedConfig 0xc27ccbde88f7ee1a
setup_fixed_benchmark runSparseCoprime3 where fixedConfig 0x6a32dabd95a98e1c
setup_fixed_benchmark runSparseCoprime4 where fixedConfig 0xcb20c1eb884c258c
setup_fixed_benchmark runSparseCoprime5 where fixedConfig 0x72e28aef962316d6
setup_fixed_benchmark runSparseCoprime6 where fixedConfig 0xe471bb0a9f420adf
setup_fixed_benchmark runSparseCoprime7 where fixedConfig 0x7958e799d1931a08
setup_fixed_benchmark runSparseCoprime8 where fixedConfig 0x9389fe94a31dd629

initialize sparseStress5d4096 : IO.Ref (P 5 Int × P 5 Int) ←
  IO.mkRef (sparseGapGcd 5 4096)
initialize sparseStress8d4096 : IO.Ref (P 8 Int × P 8 Int) ←
  IO.mkRef (sparseGapGcd 8 4096)
initialize sparseStress12d4096 : IO.Ref (P 12 Int × P 12 Int) ←
  IO.mkRef (sparseGapGcd 12 4096)

def runSparseStress5d4096 (_ : Unit) : IO UInt64 :=
  return runSparseGapPair (← sparseStress5d4096.get)
def runSparseStress8d4096 (_ : Unit) : IO UInt64 :=
  return runSparseGapPair (← sparseStress8d4096.get)
def runSparseStress12d4096 (_ : Unit) : IO UInt64 :=
  return runSparseGapPair (← sparseStress12d4096.get)

setup_fixed_benchmark runSparseStress5d4096 where
  stressConfig 0x0
setup_fixed_benchmark runSparseStress8d4096 where
  stressConfig 0x0
setup_fixed_benchmark runSparseStress12d4096 where
  stressConfig 0x0

initialize denseGcd3d5 : IO.Ref (P 3 Int × P 3 Int) ←
  IO.mkRef (denseGcd 3 5)
initialize denseGcd3d10 : IO.Ref (Option (P 3 Int × P 3 Int)) ←
  IO.mkRef none
initialize denseGcd3d20 : IO.Ref (Option (P 3 Int × P 3 Int)) ←
  IO.mkRef none
initialize denseGcd4d5 : IO.Ref (Option (P 4 Int × P 4 Int)) ←
  IO.mkRef none
initialize denseGcd5d5 : IO.Ref (Option (P 5 Int × P 5 Int)) ←
  IO.mkRef none

def runDenseGcd3d5 (_ : Unit) : IO UInt64 :=
  return runBrownPair (← denseGcd3d5.get)
def runDenseGcd3d10 (_ : Unit) : IO UInt64 :=
  return runBrownPair (← getCached denseGcd3d10 fun _ => denseGcd 3 10)
def runDenseGcd3d20 (_ : Unit) : IO UInt64 :=
  return runBrownPair (← getCached denseGcd3d20 fun _ => denseGcd 3 20)
def runDenseGcd4d5 (_ : Unit) : IO UInt64 :=
  return runBrownPair (← getCached denseGcd4d5 fun _ => denseGcd 4 5)
def runDenseGcd5d5 (_ : Unit) : IO UInt64 :=
  return runBrownPair (← getCached denseGcd5d5 fun _ => denseGcd 5 5)

setup_fixed_benchmark runDenseGcd3d5 where brownConfig 0x4a63cc50df074eb4
setup_fixed_benchmark runDenseGcd3d10 where brownConfig 0x4a63cc50df074eb4
setup_fixed_benchmark runDenseGcd3d20 where brownConfig 0x4a63cc50df074eb4
setup_fixed_benchmark runDenseGcd4d5 where brownConfig 0xa56be5fdc3e32b20
setup_fixed_benchmark runDenseGcd5d5 where brownConfig 0xbd6798d21ee1b1e0

initialize rationalGcd3d5 : IO.Ref (P 3 Rat × P 3 Rat) ←
  IO.mkRef (rationalGcd 3 5)
initialize rationalGcd3d10 : IO.Ref (Option (P 3 Rat × P 3 Rat)) ←
  IO.mkRef none
initialize rationalGcd3d20 : IO.Ref (Option (P 3 Rat × P 3 Rat)) ←
  IO.mkRef none
initialize rationalGcd4d5 : IO.Ref (Option (P 4 Rat × P 4 Rat)) ←
  IO.mkRef none
initialize rationalGcd5d5 : IO.Ref (Option (P 5 Rat × P 5 Rat)) ←
  IO.mkRef none

def runRationalGcd3d5 (_ : Unit) : IO UInt64 :=
  return runRatPair (← rationalGcd3d5.get)
def runRationalGcd3d10 (_ : Unit) : IO UInt64 :=
  return runRatPair (← getCached rationalGcd3d10 fun _ => rationalGcd 3 10)
def runRationalGcd3d20 (_ : Unit) : IO UInt64 :=
  return runRatPair (← getCached rationalGcd3d20 fun _ => rationalGcd 3 20)
def runRationalGcd4d5 (_ : Unit) : IO UInt64 :=
  return runRatPair (← getCached rationalGcd4d5 fun _ => rationalGcd 4 5)
def runRationalGcd5d5 (_ : Unit) : IO UInt64 :=
  return runRatPair (← getCached rationalGcd5d5 fun _ => rationalGcd 5 5)

setup_fixed_benchmark runRationalGcd3d5 where
  fixedConfig 0x13101c4072427dd1
setup_fixed_benchmark runRationalGcd3d10 where fixedConfig 0x13101c4072427dd1
setup_fixed_benchmark runRationalGcd3d20 where fixedConfig 0x13101c4072427dd1
setup_fixed_benchmark runRationalGcd4d5 where fixedConfig 0x7a6eed34dac1cd4b
setup_fixed_benchmark runRationalGcd5d5 where fixedConfig 0xcb197b68a2a27c66

initialize squarefree2m1 : IO.Ref (P 2 Int) ←
  IO.mkRef (squarefreeShape 2 [1])
initialize squarefree3m1to5 : IO.Ref (P 3 Int) ←
  IO.mkRef (squarefreeShape 3 [1, 2, 3, 4, 5])
initialize squarefree4m7 : IO.Ref (P 4 Int) ←
  IO.mkRef (squarefreeShape 4 [7])
initialize squarefree5m2357 : IO.Ref (Option (P 5 Int)) ← IO.mkRef none

def runSquarefree2m1 (_ : Unit) : IO UInt64 :=
  return runSquarefree (← squarefree2m1.get)
def runSquarefree3m1to5 (_ : Unit) : IO UInt64 :=
  return runSquarefree (← squarefree3m1to5.get)
def runSquarefree4m7 (_ : Unit) : IO UInt64 :=
  return runSquarefree (← squarefree4m7.get)
def runSquarefree5m2357 (_ : Unit) : IO UInt64 :=
  return runSquarefree
    (← getCached squarefree5m2357 fun _ => squarefreeStress5)

setup_fixed_benchmark runSquarefree2m1 where
  fixedConfig 0x64d98a7e1ba9194f
setup_fixed_benchmark runSquarefree3m1to5 where
  fixedConfig 0x664d8f4f4d3e40ef
setup_fixed_benchmark runSquarefree4m7 where
  fixedConfig 0xe04c869a010239a4
setup_fixed_benchmark runSquarefree5m2357 where
  stressConfig 0x4f644b92da420b36

end Hex.MvGcdBench.Matrix
