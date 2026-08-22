/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.BenchOracle.Flint

/-!
# Shared PARI persistent-subprocess bench driver helper

This module is the Lean-side companion to
`scripts/oracle/pari_bench_driver.py`, following the shape of
`Hex.BenchOracle.Flint` and reusing its `PersistentComparator`
plumbing. PARI comparators with non-negligible per-call overhead run
as a persistent subprocess: the driver loops on stdin (one JSON
request per line; see the driver's docstring for the framing
protocol and the rational `[num, den]` encoding). LeanBench starts a
fresh child for every outer fixed-benchmark warmup or repeat. Inside
that child, a `warmupFirstIter` call starts one driver before timing
and the auto-tuned inner-repeat batch reuses it, so the process is
persistent within a child batch, not across the whole
`lake exe hexfoo_bench run` invocation.

## Per-library use

Consuming libraries (HexNumberField, HexNumberFieldTower) call
`Hex.BenchOracle.Pari.runOp` from their `Bench.lean` and parse the
returned `Json` per their family's result schema.

## Configuration

* `HEX_PARI_BENCH_DRIVER` — path to the driver script, overriding
  automatic discovery. By default the helper checks
  `scripts/oracle/pari_bench_driver.py` and then
  `../scripts/oracle/pari_bench_driver.py`, covering both the
  development repository root and a released repository's `bench/`
  side project.
* `HEX_PARI_BENCH_PYTHON` — interpreter command (default `python3`).
  Useful when cypari2 lives in a virtual environment.
-/

namespace Hex.BenchOracle.Pari

open Lean (Json JsonNumber)
open Hex.BenchOracle.Flint (PersistentComparator)

/-- Module-level cache of the running PARI bench driver. Populated
lazily on first request; reset to `none` on stream error so the next
request re-spawns the driver. -/
initialize pariDriverRef : IO.Ref (Option PersistentComparator) ←
  IO.mkRef none

private def envOr (name : String) (default : String) : IO String := do
  match (← IO.getEnv name) with
  | some v => return v
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

/-- Lazily spawn the persistent PARI driver, or return the cached
handle. The driver is invoked as `<python> <driver-script>`. -/
def resolveDriver : IO PersistentComparator := do
  if let some ch ← pariDriverRef.get then
    return ch
  let py ← pythonCommand
  let script ← driverPath
  let ch ← PersistentComparator.spawn py #[script]
  pariDriverRef.set (some ch)
  return ch

/-- Send one already-compressed JSON request line and return the parsed
JSON reply. On any `IO` error from the stream (driver crash, pipe
close) the cached child handle is dropped, a fresh driver is spawned,
and the request is retried once. -/
def sendRequestLine (line : String) : IO Json := do
  let reply ←
    try
      (← resolveDriver).requestLine line
    catch _ =>
      pariDriverRef.set none
      (← resolveDriver).requestLine line
  match Json.parse reply with
  | .ok j => return j
  | .error err =>
    throw <| IO.userError
      s!"pari_bench_driver reply not valid JSON: {err}; reply: {reply}"

private def resultOf (family op : String) (reply : Json) : IO Json := do
  match reply.getObjValAs? Bool "ok" with
  | Except.ok true =>
    match reply.getObjVal? "result" with
    | Except.ok r => return r
    | Except.error msg =>
      throw (IO.userError
        s!"pari_bench_driver: missing 'result' in success reply: {msg}; reply: {reply.compress}")
  | Except.ok false =>
    let err := (reply.getObjValAs? String "error").toOption.getD "(no error message)"
    throw (IO.userError s!"pari_bench_driver: {family}/{op}: {err}")
  | Except.error msg =>
    throw (IO.userError
      s!"pari_bench_driver: reply missing/non-bool 'ok' field: {msg}; reply: {reply.compress}")

/-- Build the request JSON object from `family`, `op`, and extra
fields, send it through the driver, and return the unwrapped `result`
field on success. Raises `IO.userError` on a driver-side error frame
or on a reply that matches neither the success nor failure shape. -/
def runOp (family : String) (op : String) (fields : Array (String × Json))
    : IO Json := do
  let mut obj : Array (String × Json) :=
    #[("family", Json.str family), ("op", Json.str op)]
  for kv in fields do
    obj := obj.push kv
  resultOf family op (← sendRequestLine (Json.mkObj obj.toList).compress)

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
