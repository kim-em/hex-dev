/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvGcd.Families
import LeanBench

/-!
Mode-3 registrations for the route-dependent `hex-mv-gcd` families.

The SPEC gives probe counts but no machine-operation model for these routes.
Each registration therefore uses one canonical hard input and an enforced
body-scoped ceiling.  Comparator and protocol anchors live separately and do
not count as performance evidence.
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

def mode3Config (expectedHash : UInt64) (maxSeconds : Float) :
    LeanBench.FixedBenchmarkConfig :=
  { repeats := 3, maxSecondsPerCall := maxSeconds,
    warmupFirstIter := true, expectedHash := some expectedHash,
    tags := #[scheduledHardwareTag] }

/-- Run one operation under its body-scoped mode-3 ceiling.  The process cap
in `mode3Config` is only a safety bound; returning the sentinel makes a body
budget violation fail the expected-hash check. -/
def budgeted (ceilingNanos : Nat) (work : IO UInt64) : IO UInt64 := do
  let start ← IO.monoNanosNow
  let value ← work
  let stop ← IO.monoNanosNow
  if stop - start ≤ ceilingNanos then return value else return 0xffffffffffffffff

/-- Require the prepared pair to bypass route 0 and succeed in the modular
coprimality producer before it can be used as a route-1 benchmark input. -/
def requireCoprimeRoute {n : Nat} (input : P n Int × P n Int) : P n Int × P n Int :=
  if (remainderCert? input.1 input.2).isNone &&
      (intFastProposal GcdConfig.default input.1 input.2).cert?.isSome then input
  else panic! "coprime benchmark input does not isolate route 1"

initialize denseCoprime8 : IO.Ref (P 8 Int × P 8 Int) ←
  IO.mkRef (requireCoprimeRoute (denseRouteCoprime 8))
initialize routeSparse8 : IO.Ref (P 8 Int × P 8 Int) ←
  IO.mkRef (requireCoprimeRoute (sparseRouteCoprime 8 128))

/- Comparator-only inputs.  These retain matched low/high endpoints for the
external ratio tables; they are semantic/hash anchors, not performance-mode
coverage. -/
initialize denseCoprime2 : IO.Ref (P 2 Int × P 2 Int) ←
  IO.mkRef (denseCoprime 2 1)
initialize sparseCoprime8 : IO.Ref (P 8 Int × P 8 Int) ←
  IO.mkRef (sparseCoprime 8 128)
initialize denseGcd3d5 : IO.Ref (P 3 Int × P 3 Int) ←
  IO.mkRef (denseGcd 3 5)
initialize denseGcd4d5 : IO.Ref (Option (P 4 Int × P 4 Int)) ← IO.mkRef none
initialize rationalGcd3d5 : IO.Ref (P 3 Rat × P 3 Rat) ←
  IO.mkRef (rationalGcd 3 5)
initialize rationalGcd4d5 : IO.Ref (Option (P 4 Rat × P 4 Rat)) ← IO.mkRef none
initialize squarefree2m1 : IO.Ref (P 2 Int) ←
  IO.mkRef (squarefreeShape 2 [1])
initialize squarefree4m7 : IO.Ref (P 4 Int) ←
  IO.mkRef (squarefreeShape 4 [7])

initialize denseGcd5d5 : IO.Ref (Option (P 5 Int × P 5 Int)) ← IO.mkRef none
initialize sparseStress5d16 : IO.Ref (Option (P 5 Int × P 5 Int)) ← IO.mkRef none
initialize rationalGcd5d5 : IO.Ref (Option (P 5 Rat × P 5 Rat)) ← IO.mkRef none
initialize squarefree3m1to5 : IO.Ref (P 3 Int) ←
  IO.mkRef (squarefreeShape 3 [1, 2, 3, 4, 5])

def runDenseCoprime8 (_ : Unit) : IO UInt64 := budgeted 1_000_000_000 do
  return runIntPair (← denseCoprime8.get)

def runSparseCoprime8 (_ : Unit) : IO UInt64 := budgeted 1_000_000_000 do
  return runIntPair (← routeSparse8.get)

def runDenseGcd5d5 (_ : Unit) : IO UInt64 := budgeted 25_000_000_000 do
  return runBrownPair (← getCached denseGcd5d5 fun _ => denseGcd 5 5)

def runSparseStress5d16 (_ : Unit) : IO UInt64 := budgeted 3_000_000_000 do
  return runIntPair (← getCached sparseStress5d16 fun _ => sparseGapGcd 5 16)

def runRationalGcd5d5 (_ : Unit) : IO UInt64 := budgeted 5_000_000_000 do
  return runRatPair (← getCached rationalGcd5d5 fun _ => rationalGcd 5 5)

def runSquarefree3m1to5 (_ : Unit) : IO UInt64 := budgeted 4_000_000_000 do
  return runSquarefree (← squarefree3m1to5.get)

/- Arity, degree, and support each change both image construction and the
univariate image-gcd operands, so the SPEC's `≤ n` probe count does not derive a
tight wall model.  The old `2..8` arity grid was also invalid: `(f, f + 1)`
fired route 0.  No cited bound covers image production plus certificate replay.
Mode 3 pins genuine route-1 dense and sparse arity-8 inputs; their 1 s ceilings
are 3.15× and 3.55× the clean calibration medians. -/
setup_fixed_benchmark runDenseCoprime8 where
  mode3Config 0x9389fe94a31dd629 4.0
setup_fixed_benchmark runSparseCoprime8 where
  mode3Config 0x9389fe94a31dd629 4.0

/- Brown's `O(D)` count omits the cost of every image gcd, interpolation, CRT,
and checked replay.  The attempted `3d5, 3d10, 3d20, 4d5, 5d5` grid varies
several of those costs at once, and no published bound covers this concrete
pipeline.  Mode 3 uses `5d5`; 25 s is 2.01× its clean 12.433 s median. -/
setup_fixed_benchmark runDenseGcd5d5 where
  mode3Config 0xbd6798d21ee1b1e0 35.0

/- The sparse family deliberately reaches the dispatcher and dense PRS
fallback, for which the SPEC gives no useful bound.  Degree-only endpoints do
not control coefficient swell, and the degree-4096 bounded declines measured
no completed gcd.  Mode 3 uses the complete `5d16` call; 4 s is 2.81× the
clean 1.425 s median. -/
setup_fixed_benchmark runSparseStress5d16 where
  mode3Config 0xbd6798d21ee1b1e0 8.0

/- Rational lifting adds denominator scans and scaling to a dispatcher whose
integer-route probe costs are already unmodelled.  The attempted five-shape
grid changes arity, dense size, and coefficient work together, and no cited
upper bound covers the profiled rational producer.  Mode 3 pins `5d5`; 5 s is
2.06× the clean 2.428 s median. -/
setup_fixed_benchmark runRationalGcd5d5 where
  mode3Config 0xcb197b68a2a27c66 10.0

/- Yun performs one dispatcher-dependent gcd per level and variable.  The
attempted multiplicity patterns vary arity, factor count, and missing levels,
so `n * M` probe count is not a wall model; no cited bound covers the gcd work.
Mode 3 pins the hardest observed `3m1-to-5` input; 4 s is 2.24× its clean
1.789 s median. -/
setup_fixed_benchmark runSquarefree3m1to5 where
  mode3Config 0x664d8f4f4d3e40ef 8.0

end Hex.MvGcdBench.Matrix
