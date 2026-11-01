/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.ScanConformance
import HexGroebner.GatherConformance
import HexGroebner.MatrixNativeConformance
import HexGroebner.PackedWordConformance

namespace Hex.Groebner.NativeChecks

/-- Compiled checks for every native build variant. The harness verifies that
both native symbols were actually called, including in sanitizer builds. -/
def run : IO Unit := do
  if !PackedWordConformance.runtimeChecks then
    throw (IO.userError "compiled packed-word conformance mismatch")
  if ScanConformance.runtimeChecks && ScanConformance.runtimeWideChecks &&
      GatherConformance.gatherRuntimeChecks && GatherConformance.gatherMalformedChecks &&
      MatrixNativeConformance.engineRuntimeChecks then
    IO.println "native matrix checks: portable equality, aliases, malformed prefixes and budgets passed"
  else throw (IO.userError "native matrix conformance mismatch")

end Hex.Groebner.NativeChecks
