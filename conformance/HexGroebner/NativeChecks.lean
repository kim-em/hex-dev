/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.MonomialConformance
import HexGroebner.MonomialCompareConformance
import HexGroebner.TrieConformance
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
  if !(TrieConformance.runtimeChecks seed && TrieConformance.boundaryChecks) then
    throw (IO.userError "validated trie lookup mismatch")
  if !ScanConformance.zeroBoundaryChecks seed then
    throw (IO.userError "compiled zero-scan reservation boundary mismatch")
  if !ScanConformance.runtimeZeroChecks seed then
    throw (IO.userError "compiled zero-scan prefix mismatch")
  if !MonomialConformance.orderChecks then
    throw (IO.userError "compiled monomial table order mismatch")
  if !MonomialCompareConformance.runtimeChecks seed then
    throw (IO.userError "packed monomial comparison mismatch")
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

private def mersenneF4 (seed : Nat) : Bool := Id.run do
  let some field := Fixtures.fields.find? (·.modulus == 2147483647) | return false
  let context : Context := ⟨field,5,.grevlex⟩
  let mut generators : Array RawPolynomial := #[]
  for degree in [1:5] do
    let mut polynomial := #[]
    for start in [:5] do
      let mut exponents := Array.replicate 5 0
      for step in [:degree] do exponents := exponents.modify ((start+step)%5) (·+1)
      polynomial := polynomial.push ⟨exponents,1⟩
    generators := generators.push polynomial
  generators := generators.push #[⟨Array.replicate 5 1,1⟩,
    ⟨Array.replicate 5 0,field.modulus-(seed%1023+1).toUInt64⟩]
  let .candidate actual stats := computeWith context {} generators | return false
  let .candidate expected reference := computeWith context
    { nativeRows := false, nativeMonomials := false } generators | return false
  return actual.polynomials == expected.polynomials && stats == reference

/-- Exercise the wide-field specialized vector path during a complete F4 call. -/
def runMersenneF4 : IO Unit := do
  let seed := ((← IO.getEnv "HEX_GROEBNER_TEST_SEED").getD "0").toNat?.getD 0
  if !mersenneF4 seed then throw (IO.userError "compiled Mersenne F4/reference mismatch")

/-- Exercise cache comparisons crossing multiple bounded native chunks. -/
def runCache : IO Unit := do
  let seed := ((← IO.getEnv "HEX_GROEBNER_TEST_SEED").getD "0").toNat?.getD 0
  if !(ReducerCacheConformance.runtimeChecks seed) then
    throw (IO.userError "compiled reducer-cache conformance mismatch")

end Hex.Groebner.NativeChecks
