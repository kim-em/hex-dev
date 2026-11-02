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

private def usage := "hexgroebner_compute [--scheduling degree|sugar] [--work N] [--packed-bytes N] [--monomials N] [--pairs N] [--rounds N] [--matrix-entries N] [--matrix-rows N] [--batch-size N] [--basis N] [--variables N] input.json"

private def options : List String → Limits → Except String (String × Limits)
  | [filename], limits =>
    if filename.startsWith "--" then .error usage else .ok (filename,limits)
  | "--scheduling"::value::rest, limits => do
    let scheduling ← match value with
      | "degree" => pure Scheduling.degree
      | "sugar" => pure Scheduling.sugar
      | _ => throw s!"unknown scheduling strategy {value}; {usage}"
    options rest { limits with scheduling }
  | key::value::rest, limits => do
    if !key.startsWith "--" then throw s!"options must precede the input filename; {usage}"
    let some amount := value.toNat? | throw s!"{key}: expected a natural number"
    let limits ← match key with
      | "--work" => pure {limits with work := amount}
      | "--packed-bytes" => pure {limits with packedBytes := amount}
      | "--monomials" => pure {limits with monomials := amount}
      | "--pairs" => pure {limits with pairs := amount}
      | "--rounds" => pure {limits with rounds := amount}
      | "--matrix-entries" => pure {limits with matrixEntries := amount}
      | "--matrix-rows" => pure {limits with matrixRows := amount}
      | "--batch-size" => pure {limits with batchSize := max 1 amount}
      | "--basis" => pure {limits with basis := amount}
      | "--variables" => pure {limits with variables := amount}
      | _ => throw s!"unknown option {key}; {usage}"
    options rest limits
  | _, _ => .error usage

private def message (kind text : String) (stats : Statistics := {}) : Json :=
  Json.mkObj [("kind",toJson kind),("message",toJson text),("statistics",Driver.statistics stats)]

private def appendNat (out : String) (n : Nat) : String :=
  if n < 10 then out.push (Char.ofNat (48+n)) else out ++ toString n

/-- Write the numeric interchange basis directly into the owned output string.
Only fixed JSON punctuation and natural numbers occur here; the metadata still
uses Lean's JSON encoder. This avoids an intermediate tree for every exponent. -/
private def appendBasis (out : String) (polynomials : Array RawPolynomial) : String := Id.run do
  let mut out := out.push '['
  for i in [:polynomials.size] do
    if i != 0 then out := out.push ','
    out := out.push '['
    let polynomial := polynomials[i]!
    for j in [:polynomial.size] do
      if j != 0 then out := out.push ','
      out := (out.push '[').push '['
      let term := polynomial[j]!
      for k in [:term.exponents.size] do
        if k != 0 then out := out.push ','
        out := appendNat out term.exponents[k]!
      out := (out.push ']').push ','
      out := appendNat out term.coefficient.toNat
      out := out.push ']'
    out := out.push ']'
  return out.push ']'

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
      let metadata := (Json.mkObj [("kind",toJson "unchecked_candidate"),
        ("p",toJson context.field.modulus.toNat),("variables",toJson context.variables),
        ("order",toJson order),
        ("statistics",Driver.statistics stats),("candidateNanos",toJson (stop-start)),
        ("scheduling",toJson (match candidate.scheduling with | .degree => "degree" | .sugar => "sugar")),
        ("batchSize",toJson candidate.batchSize),("randomState",toJson candidate.randomState.toNat)]).compress
      -- This fixed nonempty JSON object ends in `}`; insert the numeric basis there.
      -- JSON object field order is not part of the interchange contract.
      let output := appendBasis (metadata.dropEnd 1 |>.toString |>.append ",\"basis\":") candidate.polynomials
      pure (0,output.push '}')
    | .invalid error stats => pure (2,(message "invalid_input" (reprStr error) stats).compress)
    | .exhausted resource state => pure (3,(message "exhausted" (reprStr resource) state.workspace.statistics).compress)
    | .representation error state => pure (4,(message "representation" (reprStr error) state.workspace.statistics).compress)
    | .internal error stats => pure (5,(message "internal_error" (reprStr error) stats).compress)
  IO.println response.2
  return response.1

end Hex.Groebner.Driver
