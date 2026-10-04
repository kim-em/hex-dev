/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexGraphIso.SparseCases

public section

open Lean

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let j ← IO.ofExcept (Json.parse line >>= Hex.GraphIso.SparseProbe.evaluate)
    output.putStrLn j.compress
