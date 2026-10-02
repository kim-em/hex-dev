/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.BenchOracle.Flint

/-! Persistent exact matrix-carrier comparator, using the common transport. -/
namespace Hex.BenchOracle.Carriers
open Lean (Json)
open Hex.BenchOracle.Flint (PersistentComparator)

-- Each benchmark child sends requests sequentially on its benchmark thread.
initialize driverRef : IO.Ref (Option PersistentComparator) ← IO.mkRef none

private def resolveDriver : IO PersistentComparator := do
  if let some driver ← driverRef.get then return driver
  let python := (← IO.getEnv "HEX_CARRIER_BENCH_PYTHON").getD "python3"
  let path : String ← match ← IO.getEnv "HEX_CARRIER_BENCH_DRIVER" with
    | some path => pure path
    | none => do
      let path : System.FilePath := "scripts/oracle/matrix_carriers.py"
      let present ← path.pathExists
      pure (if present then path.toString else "../scripts/oracle/matrix_carriers.py")
  let driver ← PersistentComparator.spawn python #[path, "--server"]
  driverRef.set (some driver)
  return driver

/-- Send prepared input; return the complete canonical answer for hashing. -/
def runLine (line : String) : IO String := do
  let raw ←
    try
      (← resolveDriver).requestLine line
    catch _ =>
      driverRef.set none
      (← resolveDriver).requestLine line
  let reply ← match Json.parse raw with
    | .ok reply => pure reply
    | .error error => throw <| IO.userError s!"carrier reply: {error}"
  match reply.getObjValAs? Bool "ok" with
  | .ok true =>
    match reply.getObjVal? "result" with
    | .ok result => return result.compress
    | .error error => throw <| IO.userError s!"carrier result: {error}"
  | _ =>
    let error := (reply.getObjValAs? String "error").toOption.getD raw
    throw <| IO.userError s!"carrier oracle failed: {error}"

end Hex.BenchOracle.Carriers
