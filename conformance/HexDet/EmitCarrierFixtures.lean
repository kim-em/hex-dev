/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDet.Carriers

/-- Emit the symbolic carrier determinants dispatch returns. -/
def main : IO Unit := do
  let out ← IO.getStdout
  for record in Hex.DetCarriers.allFixtures do
    out.putStrLn record.compress
