/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.MatrixPrimitiveConformance
import HexGroebner.MatrixLayout
import HexGroebner.MatrixStateConformance
import HexGroebner.EliminationConformance
import HexGroebner.ColumnMapConformance
import HexGroebner.SearchConformance
import HexGroebner.HitConformance
import HexGroebner.MonomialConformance
import HexGroebner.MonomialCompareConformance
import HexGroebner.TrieConformance
import HexGroebner.ScanConformance
import HexGroebner.GatherConformance
import HexGroebner.MatrixNativeConformance
import HexGroebner.PackedWordConformance
import HexGroebner.ByteConformance
import HexGroebner.PolynomialBatchConformance
import HexGroebner.ProductBatchConformance
import HexGroebner.ProductConformance
import HexGroebner.ReducerCacheConformance

namespace Hex.Groebner.NativeChecks

/-- Reproducible test input; malformed values are rejected explicitly. -/
def readSeed : IO Nat := do
  let value := (← IO.getEnv "HEX_GROEBNER_TEST_SEED").getD "0"
  let some seed := value.toNat? | throw (IO.userError s!"invalid HEX_GROEBNER_TEST_SEED: {value}")
  IO.println s!"native conformance seed: {seed}"
  return seed

/-- Direct exclusive-table comparison, separately instrumented by the harness. -/
def runOwned : IO Unit := do
  let seed ← readSeed
  if !HitConformance.ownedChecks seed then
    throw (IO.userError "exclusive monomial operation mismatch")

/-- Isolated successful adaptive multiplication for the provider-counter window. -/
def runProductWide : IO Unit := do
  let seed ← readSeed
  if !PolynomialBatchConformance.wide seed then
    throw (IO.userError "adaptive wide polynomial mismatch")

/-- Isolated last-term miss for the discarded-prefix counter window. -/
def runProductMiss : IO Unit := do
  let seed ← readSeed
  if !ProductBatchConformance.lastMiss seed then
    throw (IO.userError "last-term product miss mismatch")

/-- Isolated wide workspaces for the zero-provider admission-counter window. -/
def runWideWorkspaces : IO Unit := do
  let seed ← readSeed
  if !MatrixStateConformance.wideWorkspaces seed then
    throw (IO.userError "wide native matrix workspace boundaries mismatch")

/-- Compiled checks for every native build variant. The harness verifies that
native symbols were actually called, including in sanitizer builds. -/
def run : IO Unit := do
  let seed ← readSeed
  if !MatrixPrimitiveConformance.checked then
    throw (IO.userError s!"native matrix primitive mismatch: {MatrixPrimitiveConformance.failure.getD "unknown case"}")
  if !MatrixPrimitiveConformance.lengthChecks then
    throw (IO.userError "native matrix primitive row-length boundary mismatch")
  if !MatrixStateConformance.workspaceChecks then
    throw (IO.userError "native matrix workspace boundaries mismatch")
  if !MatrixStateConformance.validationChecks then
    throw (IO.userError "native matrix validation mismatch")
  if !MatrixStateConformance.checked || !MatrixStateConformance.boundaries ||
      !MatrixStateConformance.stepChecks || !MatrixStateConformance.largeChecks ||
      !MatrixStateConformance.resourceSteps || !MatrixStateConformance.pauseChecks then
    throw (IO.userError "native continuation mismatch")
  if !ColumnMapConformance.checks seed || !ColumnMapConformance.remapChecks seed ||
      !ColumnMapConformance.indexChecks seed || !ColumnMapConformance.collisionChecks then
    throw (IO.userError "packed column map mismatch")
  if !EliminationConformance.sizeChecks seed ||
      !EliminationConformance.thresholdChecks ||
      !EliminationConformance.sharedChecks seed ||
      !EliminationConformance.boundaryChecks || !EliminationConformance.basic || !EliminationConformance.runtimeChecks seed then
    throw (IO.userError "whole matrix conformance mismatch")
  if !HitConformance.runtimeChecks seed || !HitConformance.malformedChecks seed then
    throw (IO.userError "compiled fused monomial lookup mismatch")
  if !SearchConformance.runtimeChecks seed || !SearchConformance.longChecks (seed+2047) then
    throw (IO.userError "compiled packed-chain search mismatch")
  if !(TrieConformance.runtimeChecks seed && TrieConformance.boundaryChecks && TrieConformance.policyChecks) then
    throw (IO.userError "validated trie lookup mismatch")
  if !ScanConformance.zeroBoundaryChecks seed then
    throw (IO.userError "compiled zero-scan reservation boundary mismatch")
  if !ScanConformance.runtimeZeroChecks seed then
    throw (IO.userError "compiled zero-scan prefix mismatch")
  if !MonomialConformance.orderChecks then
    throw (IO.userError "compiled monomial table order mismatch")
  if !MonomialCompareConformance.runtimeChecks seed then
    throw (IO.userError "packed monomial comparison mismatch")
  if !PolynomialBatchConformance.checks seed then
    throw (IO.userError "compiled polynomial batch/scalar mismatch")
  if !ProductBatchConformance.capacityChecks then
    throw (IO.userError "exact batch capacity admission mismatch")
  if !ProductBatchConformance.checks seed || !ProductBatchConformance.boundaryChecks seed ||
      !ProductBatchConformance.malformedChecks seed then
    throw (IO.userError "compiled monomial-product batch mismatch")
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

private def budgetF4 (seed : Nat) : Bool := Id.run do
  let field : PrimeField := ⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩
  let context : Context := ⟨field,3,.grevlex⟩
  let coefficient := (seed%6+1).toUInt64
  let generators : Array RawPolynomial := #[
    #[⟨#[1,1,0],1⟩,⟨#[0,0,1],field.modulus-coefficient⟩],
    #[⟨#[1,0,1],1⟩,⟨#[0,1,0],6⟩]]
  let .candidate _ total := computeWith context {} generators | return false
  if total.work > 5000 then return false
  for work in [:total.work] do
    let actual := computeWith context { work } generators
    let expected := computeWith context
      { work, nativeRows := false, nativeMonomials := false } generators
    match actual,expected with
    | .candidate a sa,.candidate b sb =>
      if a.polynomials != b.polynomials || sa != sb then return false
    | .exhausted resource a,.exhausted expectedResource b =>
      if resource != expectedResource ||
          a.workspace.statistics != b.workspace.statistics then return false
    | _,_ => return false
  return true

/-- Exercise the public F4 option with every native row operation disabled. -/
def runPortableF4 (seed : Nat) : IO Unit := do
  let field : PrimeField := ⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩
  let context : Context := ⟨field,3,.grevlex⟩
  let coefficient := (seed%6+1).toUInt64
  let generators : Array RawPolynomial := #[
    #[⟨#[1,1,0],1⟩,⟨#[0,0,1],field.modulus-coefficient⟩],
    #[⟨#[1,0,1],1⟩,⟨#[0,1,0],6⟩]]
  let .candidate _ stats := computeWith context
    { nativeRows := false,nativeMonomials := false } generators |
    throw (IO.userError "compiled portable F4 failed")
  if stats.matrixCalls == 0 || stats.matrixRows == 0 || stats.matrixEntries == 0 then
    throw (IO.userError "portable F4 did not perform matrix elimination")

/-- The initial 65 target rows exceed the bulk frame's target cap. A complete
F4 candidate and all counters must agree with both native providers disabled. -/
def runOversizedF4 : IO Unit := do
  let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let context : Context := ⟨field,1,.grevlex⟩
  -- Equal leading terms collide. The first pair leaves constant 2, requiring
  -- inverse 4 in F7; subsequent collisions produce zero rows.
  let generators : Array RawPolynomial := (Array.range 65).map fun i =>
    #[⟨#[i/2+1],1⟩,⟨#[0],if i%2 == 0 then 2 else 4⟩]
  let .candidate actual stats := computeWith context {} generators |
    throw (IO.userError "oversized F4 did not complete")
  let .candidate expected reference := computeWith context
      { nativeRows := false,nativeMonomials := false } generators |
    throw (IO.userError "portable oversized F4 did not complete")
  if !ReducerCacheConformance.sameCandidate actual expected || stats != reference || stats.peakMatrixRows < 65 then
    throw (IO.userError "oversized F4 complete output/counter mismatch")

/-- Exercise complete cached F4 calls under each instrumented native provider. -/
def runF4 : IO Unit := do
  let seed ← readSeed
  for offset in [:6] do
    if !budgetF4 (seed+offset) then
      throw (IO.userError s!"compiled F4 work-boundary mismatch, seed={seed+offset}")
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
  let seed ← readSeed
  for offset in [:6] do
    if !mersenneF4 (seed+offset) then
      throw (IO.userError s!"compiled Mersenne F4/reference mismatch, seed={seed+offset}")

/-- Exercise cache comparisons crossing multiple bounded native chunks. -/
def runCache : IO Unit := do
  let seed ← readSeed
  if !(ReducerCacheConformance.runtimeChecks seed) then
    throw (IO.userError "compiled reducer-cache conformance mismatch")

end Hex.Groebner.NativeChecks
