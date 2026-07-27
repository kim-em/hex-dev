/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Center

/-!
Compiled-code driver for the D2 centered-product checker experiment.

Each invocation times one checker outcome in one process. Adversarial
certificates and limits are constructed once outside the timed loop; the
measurement therefore covers repeated checker rejection rather than payload
construction. Kernel replay is measured by separate proof-facing modules.
-/

open Hex.Interval.Experiment.Center

/-- The selected centered witness with its required equality edge omitted. -/
def missingEdgeCert : Certificate :=
  { fixtureCert with edges := [] }

/-- Compact oversized literal used only by the whole-program literal
preflight rejection variant. -/
def farLiteral : Dyadic := .ofOdd 1 1000000000 (by decide)

/-- A certificate with one unused, over-budget literal appended. -/
def unusedLiteralCert : Certificate :=
  { fixtureCert with program := extendedProgram ++ [Prim.lit farLiteral] }

/-- Keep checker evaluation behind a generic compiled call. Without this
boundary the compiler can specialize a fully static certificate to its known
Boolean answer and hoist the check out of the timing loop. -/
@[noinline]
def runCheck (certificate : Certificate) (structureLimit : StructureLimit) : Bool :=
  certificate.check fixtureLimit structureLimit baseProgram.length
    fixtureSources fixtureTarget

/-- Accepted checker workload. Alternating between lookup budgets 74 and 75
keeps a harmless trusted input live on every iteration. -/
def acceptedWork (iteration : Nat) : Bool :=
  runCheck fixtureCert
    { fixtureStructureLimit with maxLookupSteps := 74 + iteration % 2 }

/-- Rejection exactly one lookup step below the required 74. A harmless
passing fact cap stays live so the call cannot collapse to a nullary value. -/
def lookupWork (iteration : Nat) : Bool :=
  runCheck fixtureCert
    { fixtureStructureLimit with
      maxFacts := 10 + iteration % 2
      maxLookupSteps := 73 }

/-- Cheap rejection because the exact selected centered edge is absent. The
passing node cap alternates so this call cannot collapse to a nullary value. -/
def missingEdgeWork (iteration : Nat) : Bool :=
  runCheck missingEdgeCert
    { fixtureStructureLimit with maxNodes := 9 + iteration % 2 }

/-- Rejection of a preconstructed unused literal at endpoint preflight. Both
alternating node caps admit the ten-node program. -/
def unusedLiteralWork (iteration : Nat) : Bool :=
  runCheck unusedLiteralCert
    { fixtureStructureLimit with maxNodes := 10 + iteration % 2 }

/-- Mix one observed result into a deterministic machine-word sink. -/
def mix (acc value : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + value + 0xBF58476D1CE4E5B9

/-- Retain the iteration and full Boolean result in the timing checksum. -/
def observe (acc : UInt64) (iteration : Nat) (result : Bool) : UInt64 :=
  mix (mix acc (UInt64.ofNat iteration)) (if result then 1 else 0)

/-- Warm one variant, verify its expected answer, then time repeated checks. -/
def timeWork (variant : String) (repeats : Nat) (expected : Bool)
    (work : Nat → Bool) : IO Bool := do
  if work 0 != expected then
    IO.eprintln s!"{variant}: unexpected checker result"
    return false
  let mut sink : UInt64 := 0
  for i in [0:4] do
    sink := observe sink i (work i)
  let start ← IO.monoNanosNow
  for i in [0:repeats] do
    sink := observe sink i (work i)
  let stop ← IO.monoNanosNow
  IO.println s!"{variant} {repeats} {stop - start} {sink}"
  return true

/-- Print the semantic answer associated with every compiled variant. -/
def printAnswers : IO Unit := do
  IO.println s!"accepted {acceptedWork 0}"
  IO.println s!"lookup-budget {lookupWork 0}"
  IO.println s!"missing-edge {missingEdgeWork 0}"
  IO.println s!"unused-literal {unusedLiteralWork 0}"

def usage : String :=
  "usage: hex_interval_center_spike answers | " ++
    "(accepted|lookup-budget|missing-edge|unused-literal) REPEATS"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["answers"] =>
      printAnswers
      return 0
  | [variant, repeatsText] =>
      let some repeats := repeatsText.toNat?
        | IO.eprintln usage
          return 2
      if repeats = 0 then
        IO.eprintln usage
        return 2
      let success ←
        match variant with
        | "accepted" => timeWork variant repeats true acceptedWork
        | "lookup-budget" => timeWork variant repeats false lookupWork
        | "missing-edge" => timeWork variant repeats false missingEdgeWork
        | "unused-literal" => timeWork variant repeats false unusedLiteralWork
        | _ =>
            IO.eprintln usage
            pure false
      return if success then 0 else 2
  | _ =>
      IO.eprintln usage
      return 2
