/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminant.Carriers

/-- Emit complete symbolic determinants independently of the Bareiss emitters. -/
def main : IO Unit := do
  let out ← IO.getStdout
  for record in Hex.DeterminantCarriers.allFixtures do
    out.putStrLn record.compress
