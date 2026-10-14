/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import LeanBench.Export
import LeanBench.Stats

/-! Apply the pinned LeanBench regression rule to paired parent exports.
The parent owns signal-floor and verdict eligibility. This tool preserves its
points and computes trial summaries with LeanBench's existing implementation.
It does not supply a new complexity verdict. -/

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
private def compare (args : List String) : IO UInt32 := do
  unless args.length == 9 do
    throw <| IO.userError "usage: hexsturm_compare_exports OUT A0 A1 A2 A3 B0 B1 B2 B3"
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

/-- Return distinct statuses for regressions, insufficient evidence and invalid exports. -/
def main (args : List String) : IO UInt32 := do
  try compare args
  catch error =>
    IO.eprintln error.toString
    return 3
