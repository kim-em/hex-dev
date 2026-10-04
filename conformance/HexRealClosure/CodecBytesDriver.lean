/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexRealClosure.CodecTests
public import HexSignDet.JsonBytes

public section

/-- The harness configures and verifies the native stack before these probes. -/
def main (args : List String) : IO UInt32 := do
  if args == ["--stack-canary"] then
    IO.println (← Hex.SignDet.JsonBytes.stackCanary 1000000)
    return 0
  if (← IO.getEnv "LEAN_MAIN_USE_THREAD") != some "0" ||
      (← IO.getEnv "LEAN_STACK_SIZE_KB") != some "8192" then
    throw (IO.userError "capacity probes require LEAN_MAIN_USE_THREAD=0 and LEAN_STACK_SIZE_KB=8192")
  let n := args.head?.bind String.toNat? |>.getD 1000000
  let observations := Hex.RealClosure.Tower.CodecTests.run n
  for result in observations do
    IO.println s!"{result.name}: accepted={result.accepted} bytes={result.bytes} hash={result.digest}"
  return if observations.all (·.accepted) then 0 else 1
