/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality

/-!
A native timing probe for the certificate-depth fuel policy. The controlled
runner is `scripts/bench/primality_fuel_sweep.py`; keeping the clock here
excludes process startup from the measured interval.
-/

namespace Hex.PrimalityFuelProbe

open Hex.Nat

inductive Allocation where
  | production
  | elaboration

private def allocationBudget : Allocation → PrimeCertBudget
  | .production => defaultPrimeCertBudget
  | .elaboration => ⟨2, 1 <<< 15⟩

private structure Observation where
  outcome : String
  attempts : Nat
  checksum : Nat
  valid : Bool

private def observe (allocation : Allocation) (n fuel : Nat) : Observation :=
  match Internal.primeCertCountedWith? (allocationBudget allocation) n
      (Hex.Rand.ofSeed n) fuel with
  | .ok success =>
      let valid := success.cert.raw.subject == n && checkPrime success.cert.raw
      ⟨"success", success.attempts,
        success.cert.raw.subject % 4294967296 + success.attempts, valid⟩
  | .error failure =>
      match failure.stop with
      | .composite => ⟨"composite", failure.attempts, failure.attempts + 1, true⟩
      | .exhausted => ⟨"exhausted", failure.attempts, failure.attempts + 2, true⟩

private def runBatch (allocation : Allocation) (n fuel repeats : Nat) :
    Except String Nat := do
  let expected := observe allocation n fuel
  if !expected.valid then
    throw "certificate search returned an invalid success"
  let mut checksum := 0
  for _ in [0:repeats] do
    let current := observe allocation n fuel
    if current.outcome != expected.outcome ||
        current.attempts != expected.attempts || !current.valid then
      throw "certificate search was not reproducible"
    checksum := checksum + current.checksum
  return checksum

private def parseAllocation : String → Option Allocation
  | "production" => some .production
  | "elaboration" => some .elaboration
  | _ => none

private def usage : String :=
  "usage: hexprimality_fuel_probe (production|elaboration) N FUEL REPEATS"

def run (args : List String) : IO UInt32 := do
  let [allocationArg, nArg, fuelArg, repeatsArg] := args
    | IO.eprintln usage; return 2
  let some allocation := parseAllocation allocationArg
    | IO.eprintln usage; return 2
  let some n := nArg.toNat?
    | IO.eprintln s!"invalid natural: {nArg}"; return 2
  let some fuel := fuelArg.toNat?
    | IO.eprintln s!"invalid fuel: {fuelArg}"; return 2
  let some repeats := repeatsArg.toNat?
    | IO.eprintln s!"invalid repeat count: {repeatsArg}"; return 2
  if repeats == 0 then
    IO.eprintln "REPEATS must be positive"
    return 2
  let observation := observe allocation n fuel
  if !observation.valid then
    IO.eprintln "certificate search returned an invalid success"
    return 1
  -- One untimed call establishes the same warm native state for every rung.
  match runBatch allocation n fuel 1 with
  | .error e => IO.eprintln e; return 1
  | .ok _ => pure ()
  let start ← IO.monoNanosNow
  let checksum ← match runBatch allocation n fuel repeats with
    | .error e => throw <| IO.userError e
    | .ok checksum => pure checksum
  let stop ← IO.monoNanosNow
  IO.println <| "{" ++
    s!"\"allocation\":\"{allocationArg}\",\"n\":{n},\"bits\":{n.log2 + 1}," ++
    s!"\"fuel\":{fuel},\"default_fuel\":{defaultPrimeFuel n}," ++
    s!"\"repeats\":{repeats},\"outcome\":\"{observation.outcome}\"," ++
    s!"\"attempts\":{observation.attempts},\"total_nanos\":{stop - start}," ++
    s!"\"checksum\":{checksum}" ++ "}"
  return 0

end Hex.PrimalityFuelProbe

def main (args : List String) : IO UInt32 :=
  Hex.PrimalityFuelProbe.run args
