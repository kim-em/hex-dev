/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality
import Lean

/-! Compiled raw-splitter measurements. The reversed policy calls the same
per-multiplier SQUFOF kernel as the public ascending policy. -/

open Hex.Nat
open Hex.Nat.Squfof

private def reversePolicy (n : Nat) (limits : Limits) : Result := Id.run do
  if n < 4 then return ⟨.noFactor, 0, 0, 0⟩
  if 2 ^ 64 ≤ n then return ⟨.unsupported, 0, 0, 0⟩
  if n % 2 = 0 ∨ Nat.sqrt n * Nat.sqrt n = n then return factor n limits
  if limits.multipliers = 0 ∨ limits.steps = 0 then return ⟨.exhausted, 0, 0, 0⟩
  let mut attempts := 0
  let mut steps := 0
  let mut peak := 0
  let mut exhausted : Bool := decide (limits.multipliers < 16)
  for k in (multipliers.reverse.take (min limits.multipliers 16)) do
    let a := runMultiplier n k limits
    attempts := attempts + 1
    steps := steps + a.steps
    peak := max peak a.peakQueue
    if a.stop == .exhausted || a.stop == .queueFull then exhausted := true
    if let some d := a.divisor then return ⟨.factor d.val, attempts, steps, peak⟩
  return ⟨if exhausted then .exhausted else .noFactor, attempts, steps, peak⟩

private def number (s : String) : Nat := s.toNat?.getD 0

private def outcome (r : Result) : String × Nat :=
  match r.outcome with
  | .factor d => ("factor", d)
  | .noFactor => ("noFactor", 0)
  | .exhausted => ("exhausted", 0)
  | .unsupported => ("unsupported", 0)

private def attemptJson (n k : Nat) (limits : Limits) : Lean.Json := Id.run do
  let a := runMultiplier n k limits
  return Lean.Json.mkObj [
    ("k", Lean.toJson k), ("stop", Lean.toJson (reprStr a.stop)),
    ("divisor", Lean.toJson (a.divisor.map Subtype.val |>.getD 0)),
    ("forwardSteps", Lean.toJson a.forwardSteps),
    ("reverseSteps", Lean.toJson a.reverseSteps),
    ("steps", Lean.toJson a.steps), ("remaining", Lean.toJson a.remaining),
    ("peakQueue", Lean.toJson a.peakQueue)]

private def attemptTrace (n : Nat) (limits : Limits) (arm : String) (count : Nat) : Lean.Json :=
  let order := if arm == "reverse" then multipliers.reverse else multipliers
  Lean.toJson ((order.take count).map (attemptJson n · limits))

private def measureCase (n : Nat) (arm : String) (limits : Limits) (seed restarts inner : Nat) : IO Unit := do
  if arm == "diagnose" then
    IO.println (Lean.Json.mkObj [
      ("arm", Lean.toJson arm), ("n", Lean.toJson n),
      ("multipliers", Lean.toJson limits.multipliers),
      ("stepCap", Lean.toJson limits.steps),
      ("queueCapacity", Lean.toJson limits.queueCapacity),
      ("attemptsDetail", attemptTrace n limits "squfof" (min limits.multipliers 16))]).compress
    return
  let start ← IO.monoNanosNow
  if arm == "rho" then
    let ref ← IO.mkRef (Internal.rhoFactorCountedWith? n (Hex.Rand.ofSeed seed) restarts inner)
    let result ← ref.get
    let stop ← IO.monoNanosNow
    let (status, divisor, attempts) := match result with
      | .ok s => ("factor", s.factor, s.attempts)
      | .error f => (reprStr f.stop, 0, f.attempts)
    IO.println (Lean.Json.mkObj [
      ("arm", Lean.toJson arm), ("n", Lean.toJson n),
      ("seed", Lean.toJson seed), ("restarts", Lean.toJson restarts),
      ("innerFuel", Lean.toJson inner),
      ("effectiveFuel", Lean.toJson (Internal.rhoRestartFuel n inner)),
      ("status", Lean.toJson status), ("divisor", Lean.toJson divisor),
      ("attempts", Lean.toJson attempts), ("nanos", Lean.toJson (stop - start))]).compress
  else
    let ref ← IO.mkRef (if arm == "reverse" then reversePolicy n limits else factor n limits)
    let result ← ref.get
    let stop ← IO.monoNanosNow
    let (status, divisor) := outcome result
    IO.println (Lean.Json.mkObj [
      ("arm", Lean.toJson arm), ("n", Lean.toJson n),
      ("multipliers", Lean.toJson limits.multipliers),
      ("stepCap", Lean.toJson limits.steps),
      ("queueCapacity", Lean.toJson limits.queueCapacity),
      ("status", Lean.toJson status), ("divisor", Lean.toJson divisor),
      ("attempts", Lean.toJson result.attempts),
      ("steps", Lean.toJson result.steps),
      ("peakQueue", Lean.toJson result.peakQueue),
      ("attemptsDetail", attemptTrace n limits arm result.attempts),
      ("nanos", Lean.toJson (stop - start))]).compress

def main (args : List String) : IO UInt32 := do
  match args with
  | [n, arm, steps, multipliers, queue, seed, restarts, inner] =>
    measureCase (number n) arm { steps := number steps, multipliers := number multipliers, queueCapacity := number queue }
      (number seed) (number restarts) (number inner)
    return 0
  | _ =>
    IO.eprintln "usage: hexprimality_squfof_measure N ARM STEPS MULTIPLIERS QUEUE SEED RESTARTS INNER"
    return 2
