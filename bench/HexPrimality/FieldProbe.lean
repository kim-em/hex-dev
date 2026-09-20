/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexPrimality
import all HexPrimality.Construction
import all HexIntFactor.Ecm
import Lean.Data.Json

/-! Offline standard-field investigation. Explicit budgets let the runner compare
policy candidates without changing the production tactic. ECM is diagnostic only;
this executable is never invoked by certificate construction. -/

namespace Hex.PrimalityFieldProbe
open Hex.Nat
/-! Bounded offline ECM continuation. `import all` deliberately reuses the exact
stage-1 arithmetic without exporting a production API or changing dependencies. -/
namespace Ecm

structure State where
  n : Nat
  num : Nat
  den : Nat
  point : EcmPoint

-- Setup and stage 1 match the natural-number production backend exactly.
def start (n sigma b₁ : Nat) : EcmResult × Option State := Id.run do
  if n < 4 || sigma < 6 then return (.noFactor, none)
  let u := (sigma * sigma + n - 5) % n
  let v := 4 * sigma % n
  let u3 := u * u % n * u % n
  let v3 := v * v % n * v % n
  let vu := (v + n - u) % n
  let num := vu * vu % n * vu % n * ((3 * u + v) % n) % n
  let den := 4 * u3 % n * v % n
  let setup := classifyGcd n (Nat.gcd den n)
  if setup != .noFactor then return (setup, none)
  let den := 4 * den % n
  let point := stageMultiply n b₁ num den (primesBelow (b₁ + 1)) ⟨u3, v3⟩
  let result := classifyGcd n (Nat.gcd point.z n)
  return (result, if result == .noFactor then some ⟨n, num, den, point⟩ else none)

structure Trace where
  result : EcmResult := .noFactor
  candidates : Nat := 0
  advances : Nat := 0
  batches : Nat := 0
  recovery : List Nat := []
  lastPrime : Nat := 0
  oracleMismatch : Bool := false
  deriving Repr

-- A whole leaf does not mask a later proper leaf.
def flush (n product : Nat) (terms : Array Nat) : EcmResult × List Nat := Id.run do
  let result := classifyGcd n (Nat.gcd product n)
  if result != .whole then return (result, [])
  let mut recovery := []
  for t in terms do
    let g := Nat.gcd t n
    recovery := recovery ++ [g]
    if let .factor d := classifyGcd n g then return (.factor d, recovery)
  return (.whole, recovery)

/- Every prime in `(b₁,b₂]` is mapped to q = 210*i+j. Cross differences also
admit the opposite sign, but all exits still validate a proper divisor. For
small q (i=0), use `[q]Q.z` directly to avoid the point at infinity. -/
def stage2 (s : State) (b₁ b₂ : Nat) (checkGiants : Bool := false) : Trace := Id.run do
  if b₂ ≤ b₁ then return {}
  let primes := (primesBelow (b₂ + 1)).filter (b₁ < ·)
  if primes.isEmpty then return {}
  let mul := scalarMul s.n s.num s.den s.point
  let babies := (List.range 210).toArray.map mul
  let step := mul 210
  let mut previous : EcmPoint := ⟨1, 0⟩
  let mut giant := step
  let mut index := 1
  let mut terms := #[]
  let mut product := 1
  let mut trace : Trace := {}
  for q in primes do
    let i := q / 210
    let j := q % 210
    while index < i do
      let next := if index == 1 then xDouble s.n s.num s.den giant
        else xAdd s.n giant step previous
      previous := giant
      giant := next
      index := index + 1
      trace := { trace with advances := trace.advances + 1 }
    if checkGiants && i > 0 then
      let direct := mul (210 * i)
      if (direct.x * giant.z) % s.n != (giant.x * direct.z) % s.n then
        trace := { trace with oracleMismatch := true }
    let t := if i == 0 then (mul q).z else
      let baby := babies[j]' (by simp [babies, j]; omega)
      (giant.x * baby.z % s.n + s.n - baby.x * giant.z % s.n) % s.n
    product := product * t % s.n
    terms := terms.push t
    trace := { trace with candidates := trace.candidates + 1, lastPrime := q }
    if terms.size == 32 then
      let (result, recovery) := flush s.n product terms
      trace := { trace with batches := trace.batches + 1, result, recovery }
      if result != .noFactor then return trace
      terms := #[]
      product := 1
  if !terms.isEmpty then
    let (result, recovery) := flush s.n product terms
    trace := { trace with batches := trace.batches + 1, result, recovery }
  return trace

-- Requests are rejected rather than silently changed. Stage one has its existing cap.
def validBounds (b₁ b₂ : Nat) : Bool := b₁ ≤ 524288 && b₂ ≤ 4194304

def search (n sigma b₁ b₂ allowance : Nat) : EcmResult × Nat :=
  if allowance == 0 || !validBounds b₁ b₂ then (.noFactor, 0) else
  let (result, saved) := start n sigma b₁
  match saved with
  | some s => if b₂ > b₁ && allowance > 1 then ((stage2 s b₁ b₂).result, 2)
      else (result, 1)
  | none => (result, 1)

-- The experimental provider first uses the unchanged core portfolio, then
-- splits its residual with bounded ECM. Successful splits return to that same
-- core portfolio to discover prime candidates; it never consumes known factors.
def provider (b₁ b₂ curves : Nat) (trace : Bool) : FactorSearch := fun allocation n r => Id.run do
  let initial := Construction.factorSearch allocation n r
  let limit := allocation.attemptLimit.getD 1024
  let mut work := initial.attempts
  let mut rand := initial.rand
  let mut factors := initial.raw.factors
  let mut residual := 1
  let mut stack := [initial.raw.residual]
  for _ in [:allocation.factorFuel] do
    let m :: rest := stack | break
    stack := rest
    if m ≤ 1 then continue
    let mut divisor := 0
    for curve in [:min curves 64] do
      if work ≥ limit then break
      let (result, used) := search m (6 + curve) b₁ b₂ (limit - work)
      work := work + used
      if trace then
        dbg_trace "ecm {m}: sigma {6+curve}; bounds {b₁}/{b₂}; {repr result}; attempts {used}"
      if let .factor d := result then
        if 1 < d && d < m && m % d == 0 then
          divisor := d
          break
    if divisor == 0 then residual := residual * m
    else
      for part in [divisor, m / divisor] do
        let found := Construction.factorSearch { allocation with attemptLimit := some (limit - work) } part rand
        work := work + found.attempts
        rand := found.rand
        for (p, e) in found.raw.factors do
          factors := Construction.insert p e factors
        stack := found.raw.residual :: stack
  return ⟨⟨factors, stack.foldl (· * ·) residual⟩, rand, work⟩

end Ecm

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
          unless (Ecm.start n sigma b).1 == ecmStage1 n sigma b do
            throw (IO.userError "stage-1 mismatch")
    unless Ecm.flush 1081 0 #[0, 23] == (.factor 23, [1081, 23]) do
      throw (IO.userError "whole-leaf recovery")
    unless Ecm.flush 1081 0 #[0] == (.whole, [1081]) do
      throw (IO.userError "unrecoverable whole")
    for (n, b₁, b₂, expected) in [
        (1022117, 16, 16, EcmResult.noFactor),
        (1022117, 16, 1024, .factor 1013),
        (1009, 16, 1024, .whole),
        (1000036000099, 64, 8192, .factor 1000033)] do
      let some saved := (Ecm.start n 6 b₁).2 | throw (IO.userError "missing state")
      let result := Ecm.stage2 saved b₁ b₂ true
      unless result.result == expected && !result.oracleMismatch do
        throw (IO.userError s!"continuation fixture {n}: {repr result}")
    -- A prime modulus with a large surviving order reaches every requested prime.
    let some saved := (Ecm.start (2^127 - 1) 6 64).2 | throw (IO.userError "missing prime state")
    for endpoint in [67, 199, 211, 419, 1021, 8191] do
      let result := Ecm.stage2 saved 64 endpoint true
      let primes := (primesBelow (endpoint + 1)).filter (64 < ·)
      unless result.result == .noFactor && !result.oracleMismatch &&
          result.candidates == primes.length && result.lastPrime == endpoint &&
          result.batches == (primes.length + 31) / 32 do
        throw (IO.userError s!"interval coverage {endpoint}: {repr result}")
    unless Ecm.search 1022117 6 16 1024 0 == (.noFactor, 0) &&
        Ecm.search 1022117 6 16 1024 1 == (.noFactor, 1) &&
        Ecm.search 1022117 6 16 1024 2 == (.factor 1013, 2) do
      throw (IO.userError "attempt allowance")
    for allowance in [0, 1, 2, 3, 8, 32] do
      let a := { constructionBudget.factor with attemptLimit := some allowance }
      let result := Ecm.provider 16 1024 8 false a 1022117 (Hex.Rand.ofSeed 1)
      unless result.attempts ≤ allowance &&
          result.raw.factors.foldl (fun acc (q,e) => acc*q^e) result.raw.residual == 1022117 do
        throw (IO.userError "provider boundary")
    IO.println "ECM continuation checks passed"
    return 0
  if let ["ecm2", nArg, sigmaArg, b1Arg, b2Arg] := args then
    let some [n, sigma, b₁, b₂] := [nArg, sigmaArg, b1Arg, b2Arg].mapM String.toNat? | return 2
    unless Ecm.validBounds b₁ b₂ do return 2
    let input ← IO.mkRef (n, sigma, b₁, b₂)
    let (n, sigma, b₁, b₂) ← input.get
    let begin ← IO.monoNanosNow
    let saved ← IO.mkRef (Ecm.start n sigma b₁)
    let (first, saved) ← saved.get
    let middle ← IO.monoNanosNow
    let second ← IO.mkRef (saved.map fun s => Ecm.stage2 s b₁ b₂)
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
        (Ecm.provider b₁ b₂ curves (mode == "trace2"))
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
