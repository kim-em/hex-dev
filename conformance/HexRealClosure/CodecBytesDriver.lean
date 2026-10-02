/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRealClosure.CodecTests

/-- Native probes keep the OS stack limit independent of Lean's elaborator. -/
def main (args : List String) : IO UInt32 := do
  let n := args.head?.bind String.toNat? |>.getD 1000000
  let observations := Hex.RealClosure.Tower.CodecTests.run n
  for result in observations do
    IO.println s!"{result.name}: accepted={result.accepted} bytes={result.bytes} hash={result.digest}"
  return if observations.all (·.accepted) then 0 else 1
