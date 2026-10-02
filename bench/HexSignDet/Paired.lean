/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanBench
import LeanBench.Export

namespace Hex.SignDetBench
open LeanBench

/-- Run two registered custom schedules in adjacent, alternating arm order.
Sampling, child execution and statistical summaries use the shared harness.
Each completed arm is flushed before another child starts. -/
def paired (left right : Lean.Name) (path : String) : IO UInt32 := do
  let some l ← findRuntimeEntry left | throw (IO.userError "missing left registration")
  let some r ← findRuntimeEntry right | throw (IO.userError "missing right registration")
  let .custom params := l.spec.config.paramSchedule
    | throw (IO.userError "paired schedule must be explicit")
  let .custom rparams := r.spec.config.paramSchedule
    | throw (IO.userError "paired schedule must be explicit")
  let trials := l.spec.config.outerTrials
  unless params == rparams && trials == r.spec.config.outerTrials && trials > 0 && trials % 2 == 0 do
    throw (IO.userError "paired schedules must agree and have positive even round count")
  for entry in #[l, r] do
    match entry.spec.config.validate with
    | .error msg => throw (IO.userError msg)
    | .ok () => pure ()
  let env ← RunEnv.capture
  let floor ← measureSpawnFloor env
  let out ← IO.FS.Handle.mk path .write
  let emit (row : Lean.Json) : IO Unit := do
    out.putStrLn row.compress
    out.flush
  emit <| Lean.Json.mkObj [
    ("kind", Lean.toJson "header"), ("schema", Lean.toJson "hex-sign-det-paired-v1"),
    ("params", Lean.toJson params), ("trials", Lean.toJson trials),
    ("left", Lean.toJson left.toString), ("right", Lean.toJson right.toString),
    ("env", RunEnv.toJson env), ("spawnFloorNanos", Lean.toJson floor)]
  let mut lp : Array DataPoint := #[]
  let mut rp : Array DataPoint := #[]
  for trial in [:trials] do
    for param in params do
      let arms := if trial % 2 == 0 then #[false, true] else #[true, false]
      for isRight in arms do
        let entry := if isRight then r else l
        let point := { (← runOneBatch entry.spec param (some env)) with trialIndex := trial }
        emit <| Lean.Json.mkObj [
          ("kind", Lean.toJson "sample"), ("arm", Lean.toJson entry.spec.name.toString),
          ("point", Export.dataPointToJson point)]
        if isRight then rp := rp.push point else lp := lp.push point
  let mut ok := true
  for (entry, points) in #[(l, lp), (r, rp)] do
    let annotated := annotateBelowSignalFloor entry.spec.config.signalFloorMultiplier floor points
    let summary := { Stats.summarize entry.spec entry.complexity annotated with
      spawnFloorNanos? := floor, env? := some env }
    emit <| Lean.Json.mkObj [
      ("kind", Lean.toJson "summary"), ("result", Export.benchmarkResultToJson summary)]
    ok := ok && points.all (fun p => p.status == .ok) && summary.verdict != .inconclusive
  return if ok then 0 else 1

end Hex.SignDetBench
