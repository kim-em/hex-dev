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
  fake "trap '' TERM\nsleep 20 &\nwait" fun path =>
    fails "timed out" (run 17 { timeoutMs := 100 } path)
  fake "sleep 20" fun path => do
    let token ← IO.CancelToken.new
    token.set
    fails "cancelled" (run 17 (executable := path) (cancel := some token))

#eval processChecks
