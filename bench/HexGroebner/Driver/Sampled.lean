/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.Driver.Run
public import HexGroebner.Driver.Run
public import HexGroebner.Sampled

public section

namespace Hex.Groebner.Driver.Sampled
open Lean

private def usage := "hexgroebner_sample [--seed N] [--block-rows N] [--zero-tests N] [ordinary hexgroebner_compute options] input.json"

private def options : List String → Nat → Sampling.Config → List String →
    Except String (String × Limits × Nat × Sampling.Config)
  | [filename],seed,config,ordinary => do
    let (filename,limits) ← Driver.options (ordinary.reverse++[filename]) {}
    return (filename,limits,seed,config)
  | key::value::rest,seed,config,ordinary => do
    if key == "--seed" || key == "--block-rows" || key == "--zero-tests" then
      let some n := value.toNat? | throw s!"{key}: expected a natural number"
      if key == "--seed" then
        if n ≥ 2^64 then throw "seed must fit UInt64"
        options rest n config ordinary
      else if key == "--block-rows" then options rest seed { config with blockRows := n } ordinary
      else options rest seed { config with zeroTests := n } ordinary
    else options rest seed config (value::key::ordinary)
  | _,_,_,_ => .error usage

private def sampling (s : Hex.Groebner.Sampled.Statistics) : Json := Json.mkObj [
  ("calls",toJson s.calls),("inputTargets",toJson s.inputTargets),("randomWords",toJson s.randomWords),
  ("combinations",toJson s.combinations),("combinationEntries",toJson s.combinationEntries),
  ("completedBlocks",toJson s.completedBlocks)]

private def error (kind text : String) (random : Hex.Rand)
    (stats : Statistics := {}) (samples : Hex.Groebner.Sampled.Statistics := {}) : String :=
  (Json.mkObj [("kind",toJson kind),("message",toJson text),
    ("statistics",Driver.statistics stats),("sampling",sampling samples),
    ("randomState",toJson random.state.toNat)]).compress

/-- A command-line computation continues cooperative suspensions under the same
absolute allowances; only the library caller chooses to retain a quantum. -/
def complete (limits : Limits) (initial : Hex.Groebner.Sampled.Result) : IO Hex.Groebner.Sampled.Result := do
  let mut result := initial
  while true do
    match result with
    | .suspended state => result := Hex.Groebner.Sampled.resumeWith limits state
    | _ => break
  return result

/-- Seeded candidate-only driver. Certification is a separate operation; even
successful sampled elimination produces an unchecked candidate. -/
def run (args : List String) : IO UInt32 := do
  if args == ["--help"] then IO.println usage; return 0
  let parsed := options args 0 {} []
  let .ok (filename,limits,seed,config) := parsed | do
    let .error message := parsed | return 2
    IO.println (error "invalid_input" message (Hex.Rand.ofSeed 0))
    return 2
  let random := Hex.Rand.ofSeed seed
  let raw ← try IO.FS.readFile filename catch e =>
    IO.println (error "invalid_input" e.toString random)
    return 2
  let parsed := Json.parse raw >>= Driver.parseInput
  let .ok (context,generators) := parsed | do
    let .error message := parsed | return 2
    IO.println (error "invalid_input" message random)
    return 2
  let start ← IO.monoNanosNow
  let result ← complete limits (Hex.Groebner.Sampled.computeWith context limits generators random config)
  let response ← match result with
    | .candidate value stats samples => do
      let stop ← IO.monoNanosNow
      let order := match context.order with | .lex => "lex" | .grlex => "grlex" | .grevlex => "grevlex"
      let metadata := (Json.mkObj [
        ("kind",toJson "unchecked_candidate"),("algorithm",toJson "f4-sampled"),
        ("p",toJson context.field.modulus.toNat),("variables",toJson context.variables),
        ("order",toJson order),("statistics",Driver.statistics stats),("sampling",sampling samples),
        ("seed",toJson value.initialRandom.state.toNat),("randomState",toJson value.randomState.toNat),
        ("blockRows",toJson value.config.blockRows),("totalZeroTests",toJson value.config.zeroTests),
        ("samplingModel",toJson "SplitMix64 full-field rejection draws; no probability bound"),
        ("candidateNanos",toJson (stop-start)),("batchSize",toJson value.batchSize),
        ("scheduling",toJson (match value.scheduling with | .degree => "degree" | .sugar => "sugar"))]).compress
      let output := Driver.appendBasis (metadata.dropEnd 1 |>.toString |>.append ",\"basis\":") value.polynomials
      pure (0,output.push '}')
    | .invalidConfig random => pure (2,error "invalid_configuration" "positive blockRows<=4096 and zeroTests required" random)
    | .invalid message stats samples random => pure (2,error "invalid_input" (reprStr message) random stats samples)
    | .internal message stats samples random => pure (5,error "internal_error" (reprStr message) random stats samples)
    | .exhausted resource state => pure (3,error "exhausted" (reprStr resource) state.random state.workspace.statistics state.statistics)
    | .representation message state => pure (4,error "representation" (reprStr message) state.random state.workspace.statistics state.statistics)
    | .suspended state => pure (6,error "suspended" "scheduling quantum ended" state.random state.workspace.statistics state.statistics)
  IO.println response.2
  return response.1

end Hex.Groebner.Driver.Sampled
