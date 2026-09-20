/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexPrimality
import HexIntFactor.Construction
import Lean.Data.Json

/-! Offline standard-field investigation. Explicit budgets let the runner compare
policy candidates without changing the production tactic. ECM is diagnostic only;
this executable is never invoked by certificate construction. -/

namespace Hex.PrimalityFieldProbe
open Hex.Nat


/-- Native construction timing, excluding parsing, process startup, and
certificate formatting. The public construction route includes its self-check. -/
private def runConstruction (n maxBits maxFactors rhoSteps : Nat)
    (trace : Bool) (provider : FactorSearch := Construction.factorSearch) : IO UInt32 := do
  let input ← IO.mkRef n
  let n ← input.get
  let start ← IO.monoNanosNow
  let factor : FactorSearch := fun allocation m r =>
    let result := provider allocation m r
    if trace then
      dbg_trace "factor {m}: {repr result.raw}; attempts {result.attempts}; allowance {allocation.attemptLimit}"
      result
    else result
  let result ← IO.mkRef (Construction.run n (Hex.Rand.ofSeed n)
    { constructionBudget with
      maxBits := maxBits
      maxFactors := maxFactors
      factor := { constructionBudget.factor with
        primeBudget := { constructionBudget.factor.primeBudget with rhoSteps := rhoSteps } } } factor)
  let result ← result.get
  let stop ← IO.monoNanosNow
  let fields := [("nanos", Lean.toJson (stop - start)),
    ("bits", Lean.toJson (n.log2 + 1)), ("over_bit_limit", Lean.toJson (decide (n.log2 + 1 > maxBits)))]
  let fields ← match result with
    | .error f => pure (fields ++ [("status", Lean.toJson (reprStr f.stop)),
        ("attempts", Lean.toJson f.attempts)])
    | .ok s => do
        let cert ← IO.mkRef s.cert.raw
        let cert ← cert.get
        let checkStart ← IO.monoNanosNow
        let checked ← IO.mkRef (checkPrime cert)
        let checked ← checked.get
        let checkStop ← IO.monoNanosNow
        unless checked do throw (IO.userError "invalid certificate")
        pure (fields ++ [("status", Lean.toJson "ok"),
          ("attempts", Lean.toJson s.attempts),
          ("check_nanos", Lean.toJson (checkStop - checkStart)),
          ("certificate", Lean.toJson (reprStr cert))])
  IO.println (Lean.Json.mkObj fields).compress
  return 0

def run (args : List String) : IO UInt32 := do
  if args == ["verify-ecm2"] then
    for n in [4, 15, 1009, 1022117, 1000036000099, 2^127 - 1] do
      for sigma in [5:14] do
        for b in [0, 1, 16, 64, 256] do
          unless (Ecm.Internal.start n sigma b).1 == ecmStage1 n sigma b do
            throw (IO.userError "stage-1 mismatch")
    unless Ecm.Internal.flush 1081 0 #[0, 23] == (.factor 23, [1081, 23]) do
      throw (IO.userError "whole-leaf recovery")
    unless Ecm.Internal.flush 1081 0 #[0] == (.whole, [1081]) do
      throw (IO.userError "unrecoverable whole")
    for (n, b₁, b₂, expected) in [
        (1022117, 16, 16, EcmResult.noFactor),
        (1022117, 16, 1024, .factor 1013),
        (1009, 16, 1024, .whole),
        (1000036000099, 64, 8192, .factor 1000033)] do
      let some saved := (Ecm.Internal.start n 6 b₁).2 | throw (IO.userError "missing state")
      let result := Ecm.Internal.stage2 saved b₁ b₂ true
      unless result.result == expected && !result.oracleMismatch do
        throw (IO.userError s!"continuation fixture {n}: {repr result}")
    -- A prime modulus with a large surviving order reaches every requested prime.
    let some saved := (Ecm.Internal.start (2^127 - 1) 6 64).2 | throw (IO.userError "missing prime state")
    for endpoint in [67, 199, 211, 227, 229, 233, 419, 421, 431, 1021, 8191] do
      let result := Ecm.Internal.stage2 saved 64 endpoint true
      let primes := (primesBelow (endpoint + 1)).filter (64 < ·)
      unless result.result == .noFactor && !result.oracleMismatch &&
          result.candidates == primes.length && result.lastPrime == endpoint &&
          result.batches == (primes.length + 31) / 32 do
        throw (IO.userError s!"interval coverage {endpoint}: {repr result}")
    unless Ecm.search 1022117 6 16 1024 0 == (.noFactor, 0) &&
        Ecm.search 1022117 6 16 1024 1 == (.noFactor, 1) &&
        Ecm.search 1022117 6 16 1024 2 == (.factor 1013, 2) do
      throw (IO.userError "attempt allowance")
    unless (Ecm.Internal.start (2^127 - 1) 6 32768).1 ==
        ecmStage1 (2^127 - 1) 6 32768 do
      throw (IO.userError "shipped stage-1 bound")
    unless (Ecm.Internal.start 15 6 524288).1 == ecmStage1 15 6 524288 &&
        (Ecm.Internal.start 15 6 524289).1 == .noFactor &&
        Ecm.validBounds 524288 4194304 && !Ecm.validBounds 524289 4194304 &&
        !Ecm.validBounds 524288 4194305 &&
        Ecm.search 15 6 524289 4194304 2 == (.noFactor, 0) &&
        Ecm.search 15 6 524288 4194305 2 == (.noFactor, 0) do
      throw (IO.userError "bound caps")
    for n in [0, 1, 2, 1022117] do
      for allowance in [0, 1, 2, 3, 8, 32] do
        let a := { constructionBudget.factor with attemptLimit := some allowance }
        let result := ecmFactorSearch 16 1024 8 false a n (Hex.Rand.ofSeed 1)
        unless result.attempts ≤ allowance &&
            result.raw.factors.foldl (fun acc (q,e) => acc*q^e) result.raw.residual == n do
          throw (IO.userError "provider boundary")
    IO.println "ECM continuation checks passed"
    return 0
  if let ["ecm2", nArg, sigmaArg, b1Arg, b2Arg] := args then
    let some [n, sigma, b₁, b₂] := [nArg, sigmaArg, b1Arg, b2Arg].mapM String.toNat? | return 2
    unless Ecm.validBounds b₁ b₂ do return 2
    let input ← IO.mkRef (n, sigma, b₁, b₂)
    let (n, sigma, b₁, b₂) ← input.get
    let begin ← IO.monoNanosNow
    let saved ← IO.mkRef (Ecm.Internal.start n sigma b₁)
    let (first, saved) ← saved.get
    let middle ← IO.monoNanosNow
    let second ← IO.mkRef (saved.map fun s => Ecm.Internal.stage2 s b₁ b₂)
    let second ← second.get
    let endTime ← IO.monoNanosNow
    IO.println (Lean.Json.mkObj [
      ("stage1_ns", Lean.toJson (middle - begin)),
      ("stage2_ns", Lean.toJson (endTime - middle)),
      ("stage1", Lean.toJson (reprStr first)),
      ("stage2", Lean.toJson (reprStr second)),
      ("candidates", Lean.toJson (second.map (·.candidates) |>.getD 0)),
      ("advances", Lean.toJson (second.map (·.advances) |>.getD 0)),
      ("batches", Lean.toJson (second.map (·.batches) |>.getD 0)),
      ("result", Lean.toJson (reprStr (second.map (·.result) |>.getD first)))]).compress
    return 0
  if let [mode, nArg, b1Arg, b2Arg, curvesArg] := args then
    if mode == "construction2" || mode == "trace2" then
      let some [n, b₁, b₂, curves] := [nArg, b1Arg, b2Arg, curvesArg].mapM String.toNat? | return 2
      unless Ecm.validBounds b₁ b₂ && curves ≤ 64 do return 2
      return ← runConstruction n 521 32 32768 (mode == "trace2")
        (ecmFactorSearch b₁ b₂ curves (mode == "trace2"))
  if let "validate" :: nArg :: factorArgs := args then
    let some n := nArg.toNat? | return 2
    let some factors := factorArgs.mapM String.toNat? | return 2
    let valid := factors.prod == n && factors.all (fun d => 1 < d && d < n && n % d == 0)
    IO.println (Lean.Json.mkObj [("valid_factorization", Lean.toJson valid)]).compress
    return if valid then 0 else 1

  if let ["ecm", nArg, boundArg, curvesArg] := args then
    let some n := nArg.toNat? | return 2
    let some bound := boundArg.toNat? | return 2
    let some curves := curvesArg.toNat? | return 2
    for sigma in [6:6+curves] do
      let input ← IO.mkRef (n, sigma, bound)
      let (n, sigma, bound) ← input.get
      let start ← IO.monoNanosNow
      let result ← IO.mkRef (Hex.Nat.Internal.ecmTrace n sigma bound)
      let result ← result.get
      let stop ← IO.monoNanosNow
      IO.println s!"{sigma}: {repr result}; nanos {stop-start}"
      if let .factor _ := result.result then return 0
    return 0
  if let ["trace", nArg, bits, factors, steps] := args then
    let some n := nArg.toNat? | return 2
    let some bits := bits.toNat? | return 2
    let some factors := factors.toNat? | return 2
    let some steps := steps.toNat? | return 2
    return ← runConstruction n bits factors steps true
  if let ["construction", nArg, bits, factors, steps] := args then
    let some n := nArg.toNat? | return 2
    let some bits := bits.toNat? | return 2
    let some factors := factors.toNat? | return 2
    let some steps := steps.toNat? | return 2
    return ← runConstruction n bits factors steps false
  IO.eprintln "usage: hexprimality_field_probe (construction|trace) N BITS FACTORS RHO_STEPS; or ecm N BOUND CURVES"
  return 2

end Hex.PrimalityFieldProbe

public def main (args : List String) : IO UInt32 := Hex.PrimalityFieldProbe.run args
