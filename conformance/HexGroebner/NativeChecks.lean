/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.ScanConformance
import HexGroebner.GatherConformance
import HexGroebner.MatrixNativeConformance
import HexGroebner.PackedWordConformance
import HexGroebner.ByteConformance
import HexGroebner.ProductConformance
import HexGroebner.ReducerCacheConformance

namespace Hex.Groebner.NativeChecks

/-- Compiled checks for every native build variant. The harness verifies that
native symbols were actually called, including in sanitizer builds. -/
def run : IO Unit := do
  let seed := ((← IO.getEnv "HEX_GROEBNER_TEST_SEED").getD "0").toNat?.getD 0
  if !ProductConformance.runtimeChecks seed then
    throw (IO.userError "compiled current-arena product conformance mismatch")
  if !ByteConformance.runtimeChecks then
    throw (IO.userError "compiled bounded-byte conformance mismatch")
  if !PackedWordConformance.runtimeChecks then
    throw (IO.userError "compiled packed-word conformance mismatch")
  if ScanConformance.runtimeChecks && ScanConformance.runtimeWideChecks &&
      GatherConformance.gatherRuntimeChecks && GatherConformance.gatherMalformedChecks &&
      MatrixNativeConformance.engineRuntimeChecks then
    IO.println "native matrix checks: portable equality, aliases, malformed prefixes and budgets passed"
  else throw (IO.userError "native matrix conformance mismatch")

/-- Exercise complete cached F4 calls under each instrumented native provider. -/
def runF4 : IO Unit := do
  let seed := ((← IO.getEnv "HEX_GROEBNER_TEST_SEED").getD "0").toNat?.getD 0
  if !(ReducerCacheConformance.f4Checks seed) then
    throw (IO.userError "compiled F4 cache conformance mismatch")

/-- Exercise cache comparisons crossing multiple bounded native chunks. -/
def runCache : IO Unit := do
  let seed := ((← IO.getEnv "HEX_GROEBNER_TEST_SEED").getD "0").toNat?.getD 0
  if !(ReducerCacheConformance.runtimeChecks seed) then
    throw (IO.userError "compiled reducer-cache conformance mismatch")

end Hex.Groebner.NativeChecks
