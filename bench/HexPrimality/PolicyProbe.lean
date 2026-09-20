/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality
import HexPrimality.ProofProbe.Curve25519.Literal
import Lean.Data.Json

/-!
A deliberately small native timing probe for the production
Miller--Rabin-plus-`isPrimeTrial` arm versus `primeCert?` dispatch policy. The
controlled, counterbalanced runner lives in
`scripts/bench/primality_policy_sweep.py`; keeping the clock here excludes
process startup from the measured interval.
-/

namespace Hex.PrimalityPolicyProbe

open Hex.Nat

inductive Route where
  | trial
  | certificate

private def verdict : Route → Nat → Except String Bool
  | .trial, n =>
      match defaultBases.find? (fun a => !(millerRabin n a)) with
      | some _ => .ok false
      | none => .ok (isPrimeTrial n)
  | .certificate, n =>
      match primeCert? n (Hex.Rand.ofSeed n) (defaultPrimeFuel n) with
      | .ok _ => .ok true
      | .error f =>
          match f.stop with
          | .composite => .ok false
          | .exhausted => .error s!"certificate search exhausted after {f.attempts} attempts"

private def runBatch (route : Route) (n repeats : Nat) : Except String Nat := do
  let mut checksum := 0
  for _ in [0:repeats] do
    checksum := checksum + if (← verdict route n) then 1 else 0
  return checksum

private def parseRoute : String → Option Route
  | "trial" => some .trial
  | "certificate" => some .certificate
  | _ => none

private def usage : String :=
  "usage: hexprimality_policy_probe (trial|certificate) N REPEATS; or construction N; or curve-supplied"

/-- Native construction timing, excluding parsing, process startup, and
certificate formatting. The public construction route includes its self-check. -/
private def runConstruction (n : Nat) : IO UInt32 := do
  let input ← IO.mkRef n
  let n ← input.get
  let start ← IO.monoNanosNow
  let result ← IO.mkRef (Construction.run n (Hex.Rand.ofSeed n))
  let result ← result.get
  let stop ← IO.monoNanosNow
  let fields := [("nanos", Lean.toJson (stop - start))]
  let fields ← match result with
    | .error f => pure (fields ++ [("status", Lean.toJson "exhausted"),
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

/-- Retrieve and check the precompiled literal; compare with construction,
excluding initialization, process startup, and rendering. The IO references
keep the checker input and result in the timed IO computation. -/
private def runSupplied : IO UInt32 := do
  let input ← IO.mkRef (fun (_ : Unit) => Hex.PrimalityCurveProbe.certificate)
  let producer ← input.get
  let start ← IO.monoNanosNow
  let cert ← IO.mkRef (producer ())
  let cert ← cert.get
  let checked ← IO.mkRef (checkPrime cert)
  let checked ← checked.get
  let stop ← IO.monoNanosNow
  unless checked do throw (IO.userError "invalid supplied certificate")
  IO.println (Lean.Json.mkObj [("nanos", Lean.toJson (stop - start)),
    ("status", Lean.toJson "ok"), ("certificate", Lean.toJson (reprStr cert))]).compress
  return 0

def run (args : List String) : IO UInt32 := do
  if args == ["curve-supplied"] then return ← runSupplied
  if let ["construction", nArg] := args then
    let some n := nArg.toNat?
      | IO.eprintln s!"invalid natural: {nArg}"; return 2
    return ← runConstruction n
  let [routeArg, nArg, repeatsArg] := args
    | IO.eprintln usage; return 2
  let some route := parseRoute routeArg
    | IO.eprintln usage; return 2
  let some n := nArg.toNat?
    | IO.eprintln s!"invalid natural: {nArg}"; return 2
  let some repeats := repeatsArg.toNat?
    | IO.eprintln s!"invalid repeat count: {repeatsArg}"; return 2
  if repeats == 0 then
    IO.eprintln "REPEATS must be positive"
    return 2
  -- One untimed call establishes the same warm native state for both arms.
  match runBatch route n 1 with
  | .error e => IO.eprintln e; return 1
  | .ok _ => pure ()
  let start ← IO.monoNanosNow
  let checksum ← match runBatch route n repeats with
    | .error e => throw <| IO.userError e
    | .ok checksum => pure checksum
  let stop ← IO.monoNanosNow
  IO.println <| "{" ++
    s!"\"route\":\"{routeArg}\",\"n\":{n},\"repeats\":{repeats}," ++
    s!"\"total_nanos\":{stop - start},\"checksum\":{checksum}" ++ "}"
  return 0

end Hex.PrimalityPolicyProbe

def main (args : List String) : IO UInt32 :=
  Hex.PrimalityPolicyProbe.run args
