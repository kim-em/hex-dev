/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.Pari

open Hex.ECPP.Pari

private def fake (body : String) (act : String → IO Unit) : IO Unit := do
  let (handle, path) ← IO.FS.createTempFile
  handle.putStr ("#!/bin/sh\n" ++ body ++ "\n")
  handle.flush
  let status ← IO.Process.output { cmd := "chmod", args := #["+x", path.toString] }
  unless status.exitCode == 0 do throw <| IO.userError "could not create fake GP"
  try act path.toString finally IO.FS.removeFile path

private def fails (part : String) (act : IO String) : IO Unit := do
  let error ← try
    discard <| act
    pure none
  catch err => pure (some err.toString)
  unless error.any (fun text => (text.splitOn part).length > 1) do
    throw <| IO.userError s!"expected '{part}', got {error}"

private def timeoutCheck (path : String) : IO Unit := do
  let start ← IO.monoMsNow
  fails "timed out" (run 17 { timeoutMs := 100 } path)
  -- This operational watchdog is below the descendant's 20-second sleep.
  -- Time only the timeout/cleanup operation, excluding other subprocess tests.
  if (← IO.monoMsNow) - start ≥ 15000 then
    throw <| IO.userError "process cleanup waited for the sleeping descendant"

private def escapedCheck (path : String) (timeout : Bool) : IO Unit := do
  let readyFile := System.FilePath.mk (path ++ ".ready")
  let stopFile := System.FilePath.mk (path ++ ".stop")
  let token ← IO.CancelToken.new
  let task ← IO.asTask (run 17 { timeoutMs := if timeout then 1500 else 30000 }
    path (some token)) .dedicated
  try
    let start ← IO.monoMsNow
    -- The descendant records readiness after creating a new session. This
    -- makes the test exercise escaped pipes rather than a startup race.
    while !(← readyFile.pathExists) do
      if (← IO.monoMsNow) - start ≥ 1000 then
        throw <| IO.userError "escaped pipe-holder did not start"
      IO.sleep 10
    unless timeout do token.set
    while !(← IO.hasFinished task) do
      if (← IO.monoMsNow) - start ≥ 4000 then
        throw <| IO.userError "cleanup hung on an escaped pipe-holder"
      IO.sleep 10
    fails (if timeout then "timed out" else "cancelled") (IO.ofExcept (← IO.wait task))
  finally
    -- Ask the escaped holder to exit through a private file, avoiding signals
    -- to a process which the harness cannot keep unreaped. This also releases
    -- the pipes if a reader regression trips the watchdog.
    let holderReady ← readyFile.pathExists
    IO.FS.writeFile stopFile ""
    token.set
    discard <| IO.wait task
    if ← readyFile.pathExists then IO.FS.removeFile readyFile
    let stopStart ← IO.monoMsNow
    while holderReady && (← stopFile.pathExists) do
      if (← IO.monoMsNow) - stopStart ≥ 1000 then
        IO.FS.removeFile stopFile
        throw <| IO.userError "escaped pipe-holder did not acknowledge shutdown"
      IO.sleep 10
    if ← stopFile.pathExists then IO.FS.removeFile stopFile

private def processChecks : IO Unit := do
  fails "cannot start" (run 17 (executable := "/hex-missing-gp"))
  fake "test \"$1\" = '-q' && test \"$2\" = '-f' || exit 3\ncat >/dev/null\nprintf 'HEX_ECPP_BEGIN\\n17\\nHEX_ECPP_END\\n'" fun path => do
    unless (← run 17 (executable := path)) == "17" do
      throw <| IO.userError "incorrect PARI payload"
  fake "printf 'HEX_ECPP_BEGIN\\n0\\nHEX_ECPP_END\\n'" fun path =>
    fails "not prime" (run 35 (executable := path))
  fake "printf '17\\n'" fun path =>
    fails "framing" (run 17 (executable := path))
  fake "printf 'bad certificate\\n' >&2\nexit 7" fun path =>
    fails "exit 7" (run 17 (executable := path))
  fake "printf 'abcdefghijklmnopqrstuvwxyz'" fun path =>
    fails "exceeds 8 bytes" (run 17 { maxOutputBytes := 8 } path)
  fake "printf 'abcdefghijklmnopqrstuvwxyz' >&2" fun path =>
    fails "exceeds 8 bytes" (run 17 { maxErrorBytes := 8 } path)
  -- Both the parent and descendant ignore TERM; force cleanup must still finish.
  fake "trap '' TERM\nsleep 20 &\nwait" timeoutCheck
  -- Reaping the leader before these pipes close used to cause ECHILD.
  fake "sleep 20 &\nprintf 'HEX_ECPP_BEGIN\\n17\\nHEX_ECPP_END\\n'" timeoutCheck
  -- Cancel after the process has had time to create a pipe-holding child.
  fake "trap '' TERM\nsleep 20 &\nwait" fun path => do
    let token ← IO.CancelToken.new
    let cancellation ← IO.asTask (do IO.sleep 125; token.set) .dedicated
    let start ← IO.monoMsNow
    fails "cancelled" (run 17 (executable := path) (cancel := some token))
    discard <| IO.wait cancellation
    if (← IO.monoMsNow) - start ≥ 15000 then
      throw <| IO.userError "cancellation cleanup waited for the sleeping descendant"
  fake "sleep 20" fun path => do
    let token ← IO.CancelToken.new
    token.set
    fails "cancelled" (run 17 (executable := path) (cancel := some token))
  let escaped := "python3 -c 'import os,sys,time\nos.setsid()\nopen(sys.argv[1]+\".ready\",\"w\").close()\ndeadline=time.monotonic()+20\nwhile not os.path.exists(sys.argv[1]+\".stop\") and time.monotonic()<deadline:\n time.sleep(0.025)\nif os.path.exists(sys.argv[1]+\".stop\"):\n os.unlink(sys.argv[1]+\".stop\")\n' \"$0\" &\nwait"
  fake escaped (fun path => escapedCheck path false)
  fake escaped (fun path => escapedCheck path true)

#eval processChecks
