/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Scale

/-!
Compiled driver for the centered-checker structural scaling experiment.

Every checker mode constructs one workload outside the timed loop, then times
only the complete checker. `build` reconstructs the exact requested size
inside the loop and observes the resulting certificate dimensions. Kernel
replay is kept in separate build-only modules.
-/

open Hex.Interval.Experiment.Center
open Hex.Interval.Experiment.Scale

/-- Resolve one deterministic workload family from its CLI name and size. -/
def workload? (kind : String) (size : Nat) : Option Workload :=
  match kind with
  | "dead-nodes" => deadNodes? size
  | "adjacent" => adjacent? size
  | "far" => far? size
  | "source-pad" => some (sourcePad size)
  | _ => none

/-- Keep certificate construction behind a generic compiled boundary. -/
@[noinline]
def buildWorkload? (kind : String) (size : Nat) : Option Workload :=
  workload? kind size

/-- Keep replay behind a generic compiled boundary so a fixed certificate is
not specialized to its known Boolean answer. -/
@[noinline]
def runCheck (workload : Workload) (limit : StructureLimit) : Bool :=
  workload.certificate.check fixtureLimit limit baseProgram.length
    fixtureSources fixtureTarget

/-- Exact acceptance on even calls, with one harmless extra lookup step on odd
calls. The caller precomputes every collection limit outside the timed loop. -/
def acceptWork (workload : Workload) (limit : StructureLimit)
    (iteration : Nat) : Bool :=
  runCheck workload
    { limit with maxLookupSteps := limit.maxLookupSteps + iteration % 2 }

/-- Exact one-step-short rejection. A harmless passing fact cap stays live. -/
def belowWork (workload : Workload) (limit : StructureLimit)
    (iteration : Nat) : Bool :=
  runCheck workload
    { limit with
      maxLookupSteps := limit.maxLookupSteps - 1
      maxFacts := limit.maxFacts + iteration % 2 }

/-- Preserve a fact's lookup shape while changing its valid claimed range. -/
def corruptFact (fact : Fact) : Fact :=
  { fact with
    row :=
      { fact.row with
        range := if fact.row.range == unitRange then quarterRange else unitRange } }

/-- Change exactly the last fact, rejecting an empty list. -/
def corruptLast : List Fact → Option (List Fact)
  | [] => none
  | [fact] => some [corruptFact fact]
  | fact :: tail => (corruptLast tail).map (fact :: ·)

/-- Corrupt only the last fact and recompute its exact indexed-lookup budget. -/
def badTail? (workload : Workload) : Option Workload :=
  match corruptLast workload.certificate.facts with
  | none => none
  | some facts =>
      let certificate :=
        { workload.certificate with
          facts }
      match certificateLookupSteps? certificate with
      | none => none
      | some lookupSteps => some { certificate, lookupSteps }

/-- A semantically bad final fact reaches the end of fact validation. -/
def badTailWork (workload : Workload) (limit : StructureLimit)
    (iteration : Nat) : Bool :=
  runCheck workload
    { limit with maxLookupSteps := limit.maxLookupSteps + iteration % 2 }

/-- Append one valid, result-irrelevant fact. This makes the fact table exactly
one constructor longer without invalidating the caller-selected result. -/
def overFactCap (workload : Workload) : Workload :=
  { certificate :=
      { workload.certificate with
        facts := workload.certificate.facts ++
          [{ row := ⟨node 0, unitRange⟩, derivation := .source 0 }] }
    lookupSteps := workload.lookupSteps + 1 }

/-- Reject one constructor beyond a collection cap precomputed by the caller. -/
def earlyWork (workload : Workload) (limit : StructureLimit)
    (iteration : Nat) : Bool :=
  runCheck workload
    { limit with maxLookupSteps := limit.maxLookupSteps + iteration % 2 }

/-- Mix one observed value into a deterministic machine-word sink. -/
def mix (acc value : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + value + 0xBF58476D1CE4E5B9

/-- Retain the iteration and full Boolean result in the timing checksum. -/
def observeCheck (acc : UInt64) (iteration : Nat) (result : Bool) : UInt64 :=
  mix (mix acc (UInt64.ofNat iteration)) (if result then 1 else 0)

/-- Observe enough fields to force construction of the workload payload. -/
def observeBuild (acc : UInt64) (iteration : Nat) : Option Workload → UInt64
  | none => mix (mix acc (UInt64.ofNat iteration)) 0
  | some workload =>
      let certificate := workload.certificate
      mix
        (mix
          (mix
            (mix acc (UInt64.ofNat iteration))
            (UInt64.ofNat certificate.program.length))
          (UInt64.ofNat certificate.facts.length))
        (UInt64.ofNat workload.lookupSteps)

/-- Stable checksum seed for the complete structural counters of one case. -/
def workloadSeed (workload : Workload) (counts : LookupCount) : UInt64 :=
  let certificate := workload.certificate
  let seed := mix
    (mix
      (mix
        (mix
          (mix
            (mix
              (mix
                (mix 0 (UInt64.ofNat certificate.program.length))
                (UInt64.ofNat certificate.facts.length))
              (UInt64.ofNat certificate.result))
            (UInt64.ofNat workload.lookupSteps))
          (UInt64.ofNat counts.program))
        (UInt64.ofNat counts.source))
      (UInt64.ofNat counts.edge))
    (UInt64.ofNat counts.prior)
  mix seed (UInt64.ofNat counts.result)

/-- Warm and time one preconstructed checker workload. -/
def timeCheck (kind : String) (size : Nat) (mode : String) (repeats : Nat)
    (workload : Workload) (expected : Bool) (work : Nat → Bool) : IO Bool := do
  if work 0 != expected || work 1 != expected then
    IO.eprintln s!"{kind} {size} {mode}: unexpected checker result"
    return false
  let certificate := workload.certificate
  let some counts := certificateLookupCounts? certificate
    | IO.eprintln s!"{kind} {size}: invalid lookup references"
      return false
  let mut sink := workloadSeed workload counts
  for i in [0:4] do
    sink := observeCheck sink i (work i)
  let start ← IO.monoNanosNow
  for i in [0:repeats] do
    sink := observeCheck sink i (work i)
  let stop ← IO.monoNanosNow
  IO.println <| s!"check {kind} {size} {mode} {certificate.program.length} " ++
    s!"{certificate.facts.length} {workload.lookupSteps} {repeats} {stop - start} {sink} " ++
    s!"{counts.program} {counts.source} {counts.edge} {counts.prior} {counts.result}"
  return true

/-- Warm and time compiled certificate construction at the exact reported
size. The parsed size and no-inline allocation boundary remain runtime inputs. -/
def timeBuild (kind : String) (size repeats : Nat) (base : Workload) : IO Bool := do
  let certificate := base.certificate
  let some counts := certificateLookupCounts? certificate
    | IO.eprintln s!"{kind} {size}: invalid lookup references"
      return false
  let mut sink := workloadSeed base counts
  for i in [0:4] do
    sink := observeBuild sink i (buildWorkload? kind size)
  let start ← IO.monoNanosNow
  for i in [0:repeats] do
    sink := observeBuild sink i (buildWorkload? kind size)
  let stop ← IO.monoNanosNow
  IO.println <| s!"build {kind} {size} build {certificate.program.length} " ++
    s!"{certificate.facts.length} {base.lookupSteps} {repeats} {stop - start} {sink} " ++
    s!"{counts.program} {counts.source} {counts.edge} {counts.prior} {counts.result}"
  return true

def usage : String :=
  "usage: hex_interval_scale_spike " ++
    "(dead-nodes|adjacent|far|source-pad) SIZE " ++
    "(accept|below|bad-tail|early|build) REPEATS"

def main (args : List String) : IO UInt32 := do
  match args with
  | [kind, sizeText, mode, repeatsText] =>
      let some size := sizeText.toNat?
        | IO.eprintln usage
          return 2
      let some repeats := repeatsText.toNat?
        | IO.eprintln usage
          return 2
      if repeats = 0 then
        IO.eprintln usage
        return 2
      let some workload := buildWorkload? kind size
        | IO.eprintln s!"invalid workload: {kind} {size}"
          return 2
      let success ←
        match mode with
        | "accept" =>
            let limit := workload.limitAt workload.lookupSteps
            timeCheck kind size mode repeats workload true (acceptWork workload limit)
        | "below" =>
            let limit := workload.limitAt workload.lookupSteps
            timeCheck kind size mode repeats workload false (belowWork workload limit)
        | "bad-tail" =>
            match badTail? workload with
            | some bad =>
                let limit := bad.limitAt bad.lookupSteps
                timeCheck kind size mode repeats bad false (badTailWork bad limit)
            | none =>
                IO.eprintln s!"cannot corrupt empty workload: {kind} {size}"
                pure false
        | "early" =>
            let early := if kind == "dead-nodes" then workload else overFactCap workload
            let passing := early.limitAt early.lookupSteps
            let limit :=
              if kind == "dead-nodes" then
                { passing with maxNodes := passing.maxNodes - 1 }
              else
                { passing with maxFacts := passing.maxFacts - 1 }
            timeCheck kind size mode repeats early false (earlyWork early limit)
        | "build" => timeBuild kind size repeats workload
        | _ =>
            IO.eprintln usage
            pure false
      return if success then 0 else 2
  | _ =>
      IO.eprintln usage
      return 2
