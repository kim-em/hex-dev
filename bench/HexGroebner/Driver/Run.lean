/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Driver.Input

public section

open Lean

namespace Hex.Groebner.Driver

private def usage := "hexgroebner_compute [--work N] [--packed-bytes N] [--monomials N] [--pairs N] [--rounds N] [--matrix-entries N] [--matrix-rows N] [--batch-size N] input.json"

private def options : List String → Limits → Except String (String × Limits)
  | [filename], limits =>
    if filename.startsWith "--" then .error usage else .ok (filename,limits)
  | key::value::rest, limits => do
    let some amount := value.toNat? | throw s!"{key}: expected a natural number"
    let limits ← match key with
      | "--work" => pure {limits with work := amount}
      | "--packed-bytes" => pure {limits with packedBytes := amount}
      | "--monomials" => pure {limits with monomials := amount}
      | "--pairs" => pure {limits with pairs := amount}
      | "--rounds" => pure {limits with rounds := amount}
      | "--matrix-entries" => pure {limits with matrixEntries := amount}
      | "--matrix-rows" => pure {limits with matrixRows := amount}
      | "--batch-size" => pure {limits with batchSize := amount}
      | _ => throw s!"unknown option {key}; {usage}"
    options rest limits
  | _, _ => .error usage

private def message (kind text : String) (stats : Statistics := {}) : Json :=
  Json.mkObj [("kind",toJson kind),("message",toJson text),("statistics",Driver.statistics stats)]

/-- This tool only produces unchecked candidates. It never promotes an output
to a checked basis, elaborates Lean source or invokes the interpreter. -/
def run (args : List String) : IO UInt32 := do
  if args == ["--help"] then
    IO.println usage
    return 0
  let .ok (filename,limits) := options args {} | do
    let .error error := options args {} | return 2
    IO.println (message "invalid_input" error).compress
    return 2
  let raw ← try IO.FS.readFile filename catch e =>
    IO.println (message "invalid_input" e.toString).compress
    return 2
  let parsed := Json.parse raw >>= Driver.parseInput
  let .ok (context,generators) := parsed | do
    let .error error := parsed | return 2
    IO.println (message "invalid_input" error).compress
    return 2
  let start ← IO.monoNanosNow
  let result := computeWith context limits generators
  let response ← match result with
    | .candidate candidate stats => do
      let stop ← IO.monoNanosNow
      let order := match context.order with | .lex => "lex" | .grlex => "grlex" | .grevlex => "grevlex"
      pure (0,Json.mkObj [("kind",toJson "unchecked_candidate"),
        ("p",toJson context.field.modulus.toNat),("variables",toJson context.variables),
        ("order",toJson order),("basis",.arr (candidate.polynomials.map Driver.polynomial)),
        ("statistics",Driver.statistics stats),("candidateNanos",toJson (stop-start)),
        ("batchSize",toJson candidate.batchSize),("randomState",toJson candidate.randomState.toNat)])
    | .invalid error stats => pure (2,message "invalid_input" (reprStr error) stats)
    | .exhausted resource state => pure (3,message "exhausted" (reprStr resource) state.workspace.statistics)
    | .representation error state => pure (4,message "representation" (reprStr error) state.workspace.statistics)
    | .internal error stats => pure (5,message "internal_error" (reprStr error) stats)
  IO.println response.2.compress
  return response.1

end Hex.Groebner.Driver
