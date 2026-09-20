/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality
import HexIntFactor.Ecm
import Lean.Data.Json

/-! Offline standard-field investigation. Explicit budgets let the runner compare
policy candidates without changing the production tactic. ECM is diagnostic only;
this executable is never invoked by certificate construction. -/

namespace Hex.PrimalityFieldProbe
open Hex.Nat

/-- Native construction timing, excluding parsing, process startup, and
certificate formatting. The public construction route includes its self-check. -/
private def runConstruction (n maxBits maxFactors rhoSteps : Nat)
    (trace : Bool) : IO UInt32 := do
  let input ← IO.mkRef n
  let n ← input.get
  let start ← IO.monoNanosNow
  let factor : FactorSearch := fun allocation m r =>
    let result := Construction.factorSearch allocation m r
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

def main (args : List String) : IO UInt32 := Hex.PrimalityFieldProbe.run args
