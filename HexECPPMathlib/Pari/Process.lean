/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Policy
public import HexECPPMathlib.Pari.IO
public import HexArith.Montgomery.Context

/-! # Bounded PARI process protocol

This module contains the ordinary IO API shared by the optional elaborators
and protocol conformance tests.
-/

public section

namespace Hex.ECPP.Pari

/-- Finite process limits; parser and proof limits apply independently. -/
structure ProcessBudget where
  /-- Elapsed time allowed for GP and pipe collection after spawning. -/
  timeoutMs : Nat := 30000
  /-- Maximum collected stdout bytes, including framing. -/
  maxOutputBytes : Nat := 16448
  /-- Maximum collected stderr bytes. Nonempty stderr rejects the result. -/
  maxErrorBytes : Nat := 4096
  /-- Initial GP stack size in bytes; startup configuration is ignored. -/
  stackBytes : Nat := 64000000
deriving Repr

private def readBounded (handle : IO.FS.Handle) (limit : Nat)
    (cancel : _root_.IO.CancelToken) : _root_.IO String := do
  let mut data := ByteArray.empty
  repeat
    if ← cancel.isSet then throw <| IO.userError "PARI: pipe collection stopped"
    let some chunk ← IO.pollRead handle | continue
    if chunk.isEmpty then
      let some text := String.fromUTF8? data
        | throw <| IO.userError "PARI output is not UTF-8"
      return text
    if data.size + chunk.size > limit then
      throw <| IO.userError s!"PARI output exceeds {limit} bytes"
    data := data ++ chunk

private def stop {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg)
    (stdout stderr : Task (Except IO.Error String))
    (cancel : _root_.IO.CancelToken) : _root_.IO Unit := do
  -- Keep the leader unreaped until both readers finish. A descendant may
  -- escape the group while retaining a pipe, so SIGKILL alone is insufficient.
  let killError ← try
    IO.killGroup child.pid
    pure none
  catch err => pure (some err)
  cancel.set
  -- Polling readers observe cancellation independently of EOF, including
  -- pipes held outside the process group. Collect failures before reaping.
  discard <| IO.wait stdout
  discard <| IO.wait stderr
  if let some err := killError then
    -- Reap an exited leader even if signalling failed. Waiting unconditionally
    -- after a failed kill could block on a live process and defeat the budget.
    try discard <| child.tryWait catch _ => pure ()
    throw err
  discard <| child.wait

private def requestFile (n : Nat) : IO System.FilePath := do
  let (handle, path) ← IO.FS.createTempFile
  try
    handle.putStr s!"print(\"HEX_ECPP_BEGIN\"); print(primecert({n})); print(\"HEX_ECPP_END\"); quit\n"
    handle.flush
    return path
  catch err =>
    IO.FS.removeFile path
    throw err

private def runFile (n : Nat) (request : System.FilePath) (budget : ProcessBudget)
    (executable : String) (cancel : Option IO.CancelToken) : IO String := do
  let child ← try
    IO.Process.spawn {
      cmd := executable
      args := #["-q", "-f", "-s", toString budget.stackBytes, request.toString]
      stdin := .null
      stdout := .piped
      stderr := .piped
      setsid := true }
  catch err =>
    throw <| IO.userError s!"PARI: cannot start `{executable}`; install PARI/GP and put `gp` on PATH ({err})"
  let readerCancel ← IO.CancelToken.new
  let stdout ← IO.asTask (readBounded child.stdout budget.maxOutputBytes readerCancel) .dedicated
  let stderr ← IO.asTask (readBounded child.stderr budget.maxErrorBytes readerCancel) .dedicated
  let start ← IO.monoMsNow
  let completed ← IO.mkRef false
  try
    repeat
      if let some cancel := cancel then
        if ← cancel.isSet then throw <| IO.userError "PARI: certificate generation cancelled"
      if (← IO.monoMsNow) - start ≥ budget.timeoutMs then
        throw <| IO.userError s!"PARI: certificate generation timed out after {budget.timeoutMs} ms"
      let outDone ← IO.hasFinished stdout
      let errDone ← IO.hasFinished stderr
      if outDone then
        if let .error err := stdout.get then throw err
      if errDone then
        if let .error err := stderr.get then throw err
      -- Do not reap the leader while a descendant still holds either pipe.
      -- Once reaped, there must be no subsequent wait or kill of this PID.
      if outDone && errDone then
        let output ← IO.ofExcept (← IO.wait stdout)
        let errors ← IO.ofExcept (← IO.wait stderr)
        if let some status ← child.tryWait then
          completed.set true
          if status == 255 && (errors.splitOn "could not execute external process").length > 1 then
            throw <| IO.userError s!"PARI: cannot start `{executable}`; install PARI/GP and put `gp` on PATH"
          if status != 0 || !errors.trimAscii.toString.isEmpty then
            throw <| IO.userError s!"PARI: gp failed (exit {status}): {errors}"
          let lines := output.trimAscii.toString.splitOn "\n"
          unless lines.head? == some "HEX_ECPP_BEGIN" && lines.getLast? == some "HEX_ECPP_END" do
            throw <| IO.userError "PARI: malformed or incomplete output framing"
          let payload := String.intercalate "\n" (lines.drop 1 |>.dropLast)
          if payload.trimAscii.toString == "0" then
            throw <| IO.userError s!"PARI: {n} is not prime"
          return payload
      IO.sleep 25
  catch err =>
    unless ← completed.get do
      try stop child stdout stderr readerCancel
      catch cleanupError =>
        throw <| IO.userError s!"{err}; PARI cleanup failed: {cleanupError}"
    throw err

/-- Run only the evaluated natural numeral, without a shell or user startup file.
Null stdin preserves the original process-group handle. The private GP input
file is removed on every exit path. The executable is injectable for tests. -/
def run (n : Nat) (budget : ProcessBudget := {}) (executable : String := "gp")
    (cancel : Option IO.CancelToken := none) : IO String := do
  if System.Platform.isWindows then
    throw <| IO.userError "PARI: process generation requires POSIX"
  if HexArith.bitLength n > maxBits then
    throw <| IO.userError s!"PARI: subject exceeds the {maxBits}-bit replay limit"
  let request ← requestFile n
  try runFile n request budget executable cancel
  finally IO.FS.removeFile request

end Hex.ECPP.Pari
