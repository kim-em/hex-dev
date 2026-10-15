/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import LeanBench.Export
import LeanBench.Stats
-- Use the pinned runFixedBenchmark helper rather than a second median implementation.
import all LeanBench.Run

/-! Apply the pinned LeanBench regression rule to paired parent exports.
Parametric parents own signal-floor and verdict eligibility; their points and
trial summaries use LeanBench's existing implementation. Fixed results require
every declared repeat and use the pinned runner's integer per-call times and
upper-middle median. Integer division retains the runner's nanosecond rounding.
Optional historical expected hashes are checked when present; cross-source hash
agreement alone does not establish benchmark correctness or waive the SPEC's
expectedHash requirement for registrations. No new complexity verdict is supplied. -/

/-- Merge parent results, preserving their eligibility flags and recomputing
trial medians with the pinned runner. Refuse incomplete or mismatched inputs. -/
private def combine (paths : Array String) : IO LeanBench.BenchmarkResult := do
  let mut results : Array LeanBench.BenchmarkResult := #[]
  for path in paths do
    let (parametric, fixed, _) ← LeanBench.Export.loadBaseline path
    unless parametric.size == 1 && fixed.isEmpty do
      throw <| IO.userError "expected one parametric result per parent export"
    results := results.push parametric[0]!
  let first := results[0]!
  let .custom params := first.config.paramSchedule |
    throw <| IO.userError "expected the complete declared custom schedule"
  unless !params.isEmpty && params.toList.eraseDups.length == params.size do
    throw <| IO.userError "empty or duplicate declared parameters"
  let mut points := #[]
  for (result, trial) in results.zipIdx do
    unless result.function == first.function && !result.budgetTruncated &&
        result.config.outerTrials == 1 && result.config == first.config &&
        result.points.map (·.param) == params do
      throw <| IO.userError "mismatched function or truncated parent export"
    for point in result.points do
      unless point.status == .ok && point.resultHash.isSome &&
          point.trialIndex == 0 && point.innerRepeats > 0 && point.totalNanos > 0 &&
          point.perCallNanos > 0 && point.perCallNanos.isFinite do
        throw <| IO.userError "failed or unhashed point; no performance pass"
      points := points.push { point with trialIndex := trial }
  return { first with points, trialSummaries := LeanBench.Stats.trialSummariesFromPoints points }

/-- Compare four balanced alternating-block exports per source, independently
of the benchmark registration's default number of trials. -/
private def compareParametric (args : List String) : IO UInt32 := do
  unless args.length == 9 do
    throw <| IO.userError "usage: hexsturm_compare_exports OUT A0 A1 A2 A3 B0 B1 B2 B3"
  unless (args.drop 1).eraseDups.length == 8 do
    throw <| IO.userError "repeated export path"
  let trials := (args.length - 1) / 2
  let base ← combine (args.toArray.extract 1 (trials + 1))
  let current ← combine (args.toArray.extract (trials + 1) args.length)
  unless base.function == current.function && base.config == current.config do
    throw <| IO.userError "different benchmark functions or configurations"
  unless base.points.map (·.param) == current.points.map (·.param) do
    throw <| IO.userError "different parameter schedules"
  for point in base.points do
    let peers := current.points.filter (·.param == point.param)
    unless !peers.isEmpty && peers.all (·.resultHash == point.resultHash) do
      throw <| IO.userError "different parameters or result hashes"
  let report := LeanBench.Export.compareParametric base current 10.0
  IO.FS.writeFile args[0]! ((LeanBench.Export.baselineReportToJson report).pretty ++ "\n")
  IO.println (LeanBench.Export.fmtBaselineReport report)
  let .custom params := base.config.paramSchedule | return 2
  -- Preserve the runner flags. Ineligible rows cannot turn a partial comparison
  -- into a pass: every declared input needs all declared source trials.
  if report.paramComparisons.map (·.param) != params ||
      base.trialSummaries.any (·.okCount != trials) ||
      current.trialSummaries.any (·.okCount != trials) ||
      base.trialSummaries.size != params.size ||
      current.trialSummaries.size != params.size then return 2
  return if report.regressionCount == 0 then 0 else 1

/-- Combine four complete fixed-result exports using the pinned runner's
per-call integer times and upper-middle median, ignoring supplied summaries. -/
private def combineFixed (paths : Array String) : IO LeanBench.FixedResult := do
  let mut results : Array LeanBench.FixedResult := #[]
  for path in paths do
    let (parametric, fixed, _) ← LeanBench.Export.loadBaseline path
    unless parametric.isEmpty && fixed.size == 1 do
      throw <| IO.userError "expected one fixed result per parent export"
    results := results.push fixed[0]!
  let first := results[0]!
  match first.config.validate with
  | .error error => throw <| IO.userError error
  | .ok () => pure ()
  let minTotalNanos := (first.config.minTotalSeconds * 1_000_000_000.0).toUInt64.toNat
  let expected := first.points[0]?.bind (·.resultHash)
  unless expected.isSome do
    throw <| IO.userError "missing fixed result hash"
  let mut points := #[]
  for (result, block) in results.zipIdx do
    unless result.function == first.function && result.config == first.config &&
        result.hashable && result.hashesAgree && !result.budgetTruncated &&
        result.points.size == first.config.repeats && result.observedHash? == expected do
      throw <| IO.userError "mismatched or incomplete fixed parent export"
    for (point, index) in result.points.zipIdx do
      unless point.repeatIndex == index && point.status == .ok &&
          point.innerRepeats > 0 && point.totalNanos ≥ minTotalNanos &&
          point.totalNanos / point.innerRepeats > 0 &&
          point.resultHash == expected &&
          result.config.expectedHash.all (fun hash => point.resultHash == some hash) do
        throw <| IO.userError "failed, unhashed or reordered fixed repeat"
      points := points.push { point with repeatIndex := block * first.config.repeats + index }
  let sorted := (points.map fun point => point.totalNanos / point.innerRepeats).qsort (· < ·)
  return { first with
    points := points
    medianNanos? := LeanBench.medianNat sorted
    minNanos? := sorted[0]?
    maxNanos? := sorted[sorted.size - 1]? }

/-- Apply the pinned fixed-result comparison after exact source/hash agreement.
Fixed workloads retain their declared repeated calls in each source block. -/
private def compareFixed (args : List String) : IO UInt32 := do
  let base ← combineFixed (args.toArray.extract 1 5)
  let current ← combineFixed (args.toArray.extract 5 9)
  unless base.function == current.function && base.config == current.config &&
      base.observedHash? == current.observedHash? do
    throw <| IO.userError "different fixed functions, configurations or result hashes"
  let report := LeanBench.Export.compareFixed base current 10.0
  IO.FS.writeFile args[0]! ((LeanBench.Export.baselineReportToJson report).pretty ++ "\n")
  IO.println (LeanBench.Export.fmtBaselineReport report)
  return if report.regressionCount == 0 then 0 else 1

/-- Select exactly one result kind and preserve the four balanced source blocks. -/
private def compare (args : List String) : IO UInt32 := do
  unless args.length == 9 do
    throw <| IO.userError "usage: hexsturm_compare_exports OUT A0 A1 A2 A3 B0 B1 B2 B3"
  unless (args.drop 1).eraseDups.length == 8 do
    throw <| IO.userError "repeated export path"
  let (parametric, fixed, _) ← LeanBench.Export.loadBaseline args[1]!
  if parametric.size == 1 && fixed.isEmpty then
    compareParametric args
  else if parametric.isEmpty && fixed.size == 1 then
    compareFixed args
  else
    throw <| IO.userError "expected exactly one result kind in every source export"

/-- Exit 0 for a stable/improved comparison, 1 for a regression, 2 for
insufficient eligible parametric evidence, and 3 for invalid exports.
Incomplete fixed exports are invalid, not an inconclusive comparison. -/
public def main (args : List String) : IO UInt32 := do
  try compare args
  catch error =>
    IO.eprintln error.toString
    return 3
