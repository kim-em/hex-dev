/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PolicyFrontier

/-!
# Policy-frontier representation spike driver

This executable reports deterministic logical-work vectors for the complete
scan and maintained event-indexed priority frontier.  It deliberately does not
run an in-process timing loop: the columns have exact meanings, while machine
timing belongs in the repository's common benchmark harness once a production
adapter exists.
-/

namespace Hex.Interval.IntervalPolicyFrontierSpike

open Experiment.Propagator.PolicyFrontier

def workText (work : Work) : String :=
  s!"total={work.total} frontier-slots={work.frontierSlots} " ++
    s!"frontier-emits={work.frontierEmits} clock-sync={work.clockSyncSlots} " ++
    s!"suggestion-prune={work.suggestionPruneSlots} " ++
    s!"dependency-visits={work.dependencyVisits} event-visits={work.eventVisits} " ++
    s!"offer-rechecks={work.offerRechecks} " ++
    s!"selection-rechecks={work.selectionRechecks} " ++
    s!"semantic-items={work.semanticItems} " ++
    s!"priority-comparisons={work.priorityComparisons} " ++
    s!"priority-moves={work.priorityMoves}"

def resultText (mode : String) (result : Result) : String :=
  s!"{mode} stop={repr result.stop} decisions={result.decisions} " ++
    s!"calls={result.calls} improvements={result.improvements} " ++
    s!"dismissals={result.dismissals} insertions={result.queueInsertions} " ++
    s!"suppressed={result.suppressedInsertions} " ++
    s!"retained={result.retainedSuggestions} checksum={result.checksum} " ++
    workText result.work

def report (workload : Workload) : IO Bool := do
  let comparison := compare workload
  IO.println <| s!"workload={workload.name} roots={workload.roots} " ++
    s!"sinks={workload.sinks} churn={workload.churn} dense={workload.dense}"
  IO.println (resultText "scan" comparison.scan)
  IO.println (resultText "indexed" comparison.indexed)
  let valid := comparisonValid workload comparison &&
    (workload.sinks == 1 ||
      (nonFifoChoice workload comparison.scan &&
        nonFifoChoice workload comparison.indexed))
  if !valid then IO.eprintln "policy-frontier equivalence canary failed"
  return valid

def reportAll : List Workload -> IO Bool
  | [] => pure true
  | workload :: workloads => do
      let current <- report workload
      let rest <- reportAll workloads
      return current && rest

def usage : String :=
  "usage: hex_interval_policy_frontier_spike canary | " ++
    "fanout SINKS | dense WIDTH | churn SINKS SUGGESTIONS_PER_SINK"

end Hex.Interval.IntervalPolicyFrontierSpike

open Hex.Interval.Experiment.Propagator.PolicyFrontier
open Hex.Interval.IntervalPolicyFrontierSpike

def main (args : List String) : IO UInt32 := do
  let workload? : Option (List Workload) :=
    match args with
    | ["canary"] => some [fanoutCanary, denseCanary, churnCanary]
    | ["fanout", sinksText] => do
        let sinks <- sinksText.toNat?
        some [{ name := "fanout", roots := 1, sinks, churn := 0, dense := false }]
    | ["dense", widthText] => do
        let width <- widthText.toNat?
        some [{ name := "dense", roots := width, sinks := width, churn := 0, dense := true }]
    | ["churn", sinksText, churnText] => do
        let sinks <- sinksText.toNat?
        let churn <- churnText.toNat?
        some [{ name := "churn", roots := 1, sinks, churn, dense := false }]
    | _ => none
  match workload? with
  | none => IO.eprintln usage; return 2
  | some workloads =>
      if workloads.any (fun workload => !workload.valid) then
        IO.eprintln usage
        return 2
      return if <- reportAll workloads then 0 else 2
