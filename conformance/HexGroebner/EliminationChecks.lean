/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGroebner.EliminationConformance

def main : IO Unit := do
  if !Hex.Groebner.EliminationConformance.thresholdChecks ||
      !Hex.Groebner.EliminationConformance.sharedChecks 17 ||
      !Hex.Groebner.EliminationConformance.boundaryChecks || !Hex.Groebner.EliminationConformance.basic then
    throw (IO.userError "whole matrix/basic mismatch")
  if !Hex.Groebner.EliminationConformance.runtimeChecks 17 then
    throw (IO.userError "whole matrix/runtime mismatch")
  IO.println "whole matrix reference, borrowed inputs and budget comparisons passed"
