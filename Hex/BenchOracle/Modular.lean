/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.BenchOracle.Flint
import Lean.Data.Json

/-!
# Persistent external comparators for `hex-modular`

This is the Lean-side companion to
`scripts/oracle/modular_bench_driver.py`. The driver imports `gmpy2` and
python-flint once, then accepts one JSON request per line. A fixed LeanBench
child warms the driver before its timed inner-repeat batch, so process startup
and module import are excluded while JSON framing remains measurable.

Configuration:

* `HEX_MODULAR_BENCH_DRIVER` overrides the driver path.
* `HEX_MODULAR_BENCH_PYTHON` overrides the Python command.
-/

namespace Hex.BenchOracle.Modular

open Hex.BenchOracle.Flint (PersistentComparator)
open Lean (Json)

initialize driverRef : IO.Ref (Option PersistentComparator) ← IO.mkRef none

private def driverPath : IO String := do
  if let some path ← IO.getEnv "HEX_MODULAR_BENCH_DRIVER" then
    return path
  let rootPath : System.FilePath := "scripts/oracle/modular_bench_driver.py"
  if ← rootPath.pathExists then
    return rootPath.toString
  return "../scripts/oracle/modular_bench_driver.py"

private def pythonCommand : IO String := do
  return (← IO.getEnv "HEX_MODULAR_BENCH_PYTHON").getD "python3"

/-- Lazily start the modular comparator driver for this LeanBench child. -/
def resolveDriver : IO PersistentComparator := do
  if let some child ← driverRef.get then
    return child
  let child ← PersistentComparator.spawn (← pythonCommand) #[← driverPath]
  driverRef.set (some child)
  return child

/-- Send a precompressed request and parse its response, retrying once after a
broken pipe with a fresh persistent driver. -/
def sendLine (line : String) : IO Json := do
  let reply ←
    try
      (← resolveDriver).requestLine line
    catch _ =>
      driverRef.set none
      (← resolveDriver).requestLine line
  match Json.parse reply with
  | .ok json => return json
  | .error error =>
      throw <| IO.userError s!"modular comparator returned invalid JSON: {error}"

/-- Send a precompressed request and unwrap its successful `result` field. -/
def runLine (line : String) : IO Json := do
  let reply ← sendLine line
  match reply.getObjValAs? Bool "ok" with
  | .ok true =>
      match reply.getObjVal? "result" with
      | .ok result => return result
      | .error error =>
          throw <| IO.userError s!"modular comparator omitted result: {error}"
  | .ok false =>
      let error := (reply.getObjValAs? String "error").toOption.getD "unknown error"
      throw <| IO.userError s!"modular comparator failed: {error}"
  | .error error =>
      throw <| IO.userError s!"modular comparator returned malformed reply: {error}"

end Hex.BenchOracle.Modular
