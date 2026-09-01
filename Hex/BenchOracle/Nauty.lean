/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.BenchOracle.Flint

/-!
# Shared nauty persistent-subprocess bench driver helper

Lean-side companion to `scripts/oracle/nauty_bench_driver.py`. The
driver builds the conformance oracle's C shim against the
hash-verified pinned nauty 2.9.3 source once at startup; each request
canonicalizes one coloured graph through it. It reuses the process
framing type from the FLINT helper while retaining an independent
cached child process.

Environment overrides:

* `HEX_NAUTY_BENCH_DRIVER` — driver script path;
* `HEX_NAUTY_BENCH_PYTHON` — Python command (default `python3`).
-/

namespace Hex.BenchOracle.Nauty

open Lean (Json JsonNumber)

private abbrev PersistentComparator :=
  Hex.BenchOracle.Flint.PersistentComparator

initialize nautyDriverRef : IO.Ref (Option PersistentComparator) ←
  IO.mkRef none

private def envOr (name : String) (default : String) : IO String := do
  match (← IO.getEnv name) with
  | some value => return value
  | none => return default

private def driverPath : IO String := do
  if let some path ← IO.getEnv "HEX_NAUTY_BENCH_DRIVER" then
    return path
  let rootPath : System.FilePath := "scripts/oracle/nauty_bench_driver.py"
  if ← rootPath.pathExists then
    return rootPath.toString
  return "../scripts/oracle/nauty_bench_driver.py"

private def pythonCommand : IO String :=
  envOr "HEX_NAUTY_BENCH_PYTHON" "python3"

private def resolveDriver : IO PersistentComparator := do
  if let some child ← nautyDriverRef.get then
    return child
  let child ← Hex.BenchOracle.Flint.PersistentComparator.spawn
    (← pythonCommand) #[← driverPath]
  nautyDriverRef.set (some child)
  return child

private def sendRequestLine (line : String) : IO Json := do
  let reply ←
    try
      (← resolveDriver).requestLine line
    catch _ =>
      nautyDriverRef.set none
      (← resolveDriver).requestLine line
  match Json.parse reply with
  | .ok value => return value
  | .error error =>
    throw <| IO.userError
      s!"nauty_bench_driver reply not valid JSON: {error}; reply: {reply}"

private def resultOf (op : String) (reply : Json) : IO Json := do
  match reply.getObjValAs? Bool "ok" with
  | Except.ok true =>
    match reply.getObjVal? "result" with
    | Except.ok result => return result
    | Except.error error =>
      throw <| IO.userError
        s!"nauty_bench_driver: missing result: {error}; reply: {reply.compress}"
  | Except.ok false =>
    let error := (reply.getObjValAs? String "error").toOption.getD
      "(no error message)"
    throw <| IO.userError s!"nauty_bench_driver: {op}: {error}"
  | Except.error error =>
    throw <| IO.userError
      s!"nauty_bench_driver: reply missing/non-bool ok: {error}; reply: {reply.compress}"

/-- Canonicalize one coloured graph through the pinned nauty
comparator. `adj` lists each vertex's adjacency row as a `0`/`1`
string; the result carries the canonical label, the canonical
upper-triangle bits, and the visited-node count. -/
def canon (n k : Nat) (colors : List Nat) (adj : List String) :
    IO Json := do
  let request := Json.mkObj
    [("family", Json.str "nauty"), ("op", Json.str "canon"),
     ("n", Json.num (JsonNumber.fromNat n)),
     ("k", Json.num (JsonNumber.fromNat k)),
     ("colors", Json.arr (colors.map fun c =>
       Json.num (JsonNumber.fromNat c)).toArray),
     ("adj", Json.arr (adj.map Json.str).toArray)]
  let reply ← sendRequestLine request.compress
  resultOf "canon" reply

end Hex.BenchOracle.Nauty
