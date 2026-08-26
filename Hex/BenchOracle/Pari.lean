/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.BenchOracle.Flint

/-!
# Shared PARI persistent-subprocess bench driver helper

This is the Lean-side companion to `scripts/oracle/pari_bench_driver.py`.
It reuses the process framing type from the FLINT helper while retaining an
independent cached child process.  The driver is persistent within one
LeanBench child batch, so importing cypari2 and initializing PARI are outside
the timed per-call region after warmup.

Environment overrides:

* `HEX_PARI_BENCH_DRIVER` — driver script path;
* `HEX_PARI_BENCH_PYTHON` — Python command (default `python3`).
-/

namespace Hex.BenchOracle.Pari

open Lean (Json JsonNumber)

private abbrev PersistentComparator :=
  Hex.BenchOracle.Flint.PersistentComparator

initialize pariDriverRef : IO.Ref (Option PersistentComparator) ←
  IO.mkRef none

private def envOr (name : String) (default : String) : IO String := do
  match (← IO.getEnv name) with
  | some value => return value
  | none => return default

private def driverPath : IO String := do
  if let some path ← IO.getEnv "HEX_PARI_BENCH_DRIVER" then
    return path
  let rootPath : System.FilePath := "scripts/oracle/pari_bench_driver.py"
  if ← rootPath.pathExists then
    return rootPath.toString
  return "../scripts/oracle/pari_bench_driver.py"

private def pythonCommand : IO String :=
  envOr "HEX_PARI_BENCH_PYTHON" "python3"

private def resolveDriver : IO PersistentComparator := do
  if let some child ← pariDriverRef.get then
    return child
  let child ← Hex.BenchOracle.Flint.PersistentComparator.spawn
    (← pythonCommand) #[← driverPath]
  pariDriverRef.set (some child)
  return child

private def sendRequestLine (line : String) : IO Json := do
  let reply ←
    try
      (← resolveDriver).requestLine line
    catch _ =>
      pariDriverRef.set none
      (← resolveDriver).requestLine line
  match Json.parse reply with
  | .ok value => return value
  | .error error =>
    throw <| IO.userError
      s!"pari_bench_driver reply not valid JSON: {error}; reply: {reply}"

private def resultOf (family op : String) (reply : Json) : IO Json := do
  match reply.getObjValAs? Bool "ok" with
  | Except.ok true =>
    match reply.getObjVal? "result" with
    | Except.ok result => return result
    | Except.error error =>
      throw <| IO.userError
        s!"pari_bench_driver: missing result: {error}; reply: {reply.compress}"
  | Except.ok false =>
    let error := (reply.getObjValAs? String "error").toOption.getD "(no error message)"
    throw <| IO.userError s!"pari_bench_driver: {family}/{op}: {error}"
  | Except.error error =>
    throw <| IO.userError
      s!"pari_bench_driver: reply missing/non-bool ok: {error}; reply: {reply.compress}"

/-- Run one operation through the persistent PARI comparison service. -/
def runOp (family op : String) (fields : Array (String × Json)) : IO Json := do
  let mut object : Array (String × Json) :=
    #[("family", Json.str family), ("op", Json.str op)]
  for field in fields do
    object := object.push field
  let reply ← sendRequestLine (Json.mkObj object.toList).compress
  resultOf family op reply

/-- Encode an array of rationals as the driver's `[[num, den], ...]`
JSON shape. `Rat` maintains `den > 0` and `gcd(num, den) = 1`, the
normal form the protocol requires. -/
def ratsToJson (qs : Array Rat) : Json :=
  Json.arr <| qs.map fun q =>
    Json.arr #[Json.num (JsonNumber.fromInt q.num),
      Json.num (JsonNumber.fromInt (q.den : Int))]

/-- Decode the driver's `[[num, den], ...]` shape back into an array of
rationals. Raises `IO.userError` on shape mismatch. -/
def jsonToRats (j : Json) : IO (Array Rat) := do
  match j.getArr? with
  | Except.error msg =>
    throw (IO.userError
      s!"pari_bench_driver: expected JSON array, got: {msg}; value: {j.compress}")
  | Except.ok arr =>
    let mut out : Array Rat := Array.mkEmpty arr.size
    for elt in arr do
      match elt.getArr? with
      | Except.error msg =>
        throw (IO.userError
          s!"pari_bench_driver: rational not a pair: {msg}; element: {elt.compress}")
      | Except.ok pair =>
        if h : pair.size = 2 then
          match pair[0].getInt?, pair[1].getInt? with
          | Except.ok num, Except.ok den =>
            if den ≤ 0 then
              throw (IO.userError
                s!"pari_bench_driver: nonpositive denominator: {elt.compress}")
            out := out.push (mkRat num den.toNat)
          | _, _ =>
            throw (IO.userError
              s!"pari_bench_driver: rational pair not integers: {elt.compress}")
        else
          throw (IO.userError
            s!"pari_bench_driver: rational pair had {pair.size} fields: {elt.compress}")
    return out

/-- Decode a `[[a, b], ...]` JSON array of natural-number pairs (the
`nf`/`factor_degrees` result shape). -/
def jsonToNatPairs (j : Json) : IO (Array (Nat × Nat)) := do
  match j.getArr? with
  | Except.error msg =>
    throw (IO.userError
      s!"pari_bench_driver: expected JSON array, got: {msg}; value: {j.compress}")
  | Except.ok arr =>
    let mut out : Array (Nat × Nat) := Array.mkEmpty arr.size
    for elt in arr do
      match elt.getArr? with
      | Except.error msg =>
        throw (IO.userError
          s!"pari_bench_driver: pair not an array: {msg}; element: {elt.compress}")
      | Except.ok pair =>
        if h : pair.size = 2 then
          match pair[0].getNat?, pair[1].getNat? with
          | Except.ok a, Except.ok b => out := out.push (a, b)
          | _, _ =>
            throw (IO.userError
              s!"pari_bench_driver: pair entries not naturals: {elt.compress}")
        else
          throw (IO.userError
            s!"pari_bench_driver: pair had {pair.size} fields: {elt.compress}")
    return out

end Hex.BenchOracle.Pari
