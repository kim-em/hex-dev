/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteCoordinates
import HexRCF.FiniteSourceTactic
import HexRCF.ProofEvidence
import HexRCF.FiniteEvidence
import Lean
open Lean Meta
set_option maxHeartbeats 8000000

-- Actual composition rechecks do not recompute cached arithmetic auxiliaries.
run_meta withoutExporting do
  let roots := #[``Hex.RCF.FiniteCoordinates.values,
    ``Hex.RCF.FiniteCoordinates.quotient, ``Hex.RCF.FiniteCoordinates.quotient.guard,
    ``Hex.RCF.FiniteCoordinates.cancelled, ``Hex.RCF.FiniteCoordinates.cancelled.guard,
    ``Hex.RCF.FiniteSourceTactic.positive, ``Hex.RCF.FiniteSourceTactic.betweenRoots]
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for name in #[``Hex.RCF.RealCoefficients.Field.value_eq_zero,
      ``Hex.RCF.RealCoefficients.Field.value_div, ``Hex.RCF.RealCoefficients.Field.value_inv,
      ``Hex.RCF.RealCoefficients.Field.value_quotient,
      ``Hex.RCF.RealCoefficients.FieldBuild.buildTable,
      ``Hex.RCF.RealCoefficients.Field.prepareSign,
      ``Hex.RCF.RealCoefficients.FieldRootSigns.Table.build,
      ``Hex.RCF.RealCoefficients.RadicalCert.build,
      ``Hex.RCF.RealCoefficients.IsolationReplay.build,
      ``Hex.RCF.RealCoefficients.IsolationReplay.queryAt,
      ``Hex.TarskiCertificate.fromChains, ``Hex.SignedRemainderChain.build,
      ``Hex.RCF.RealCoefficients.FieldIsolate.propose?,
      ``Hex.Sturm.queryPrepared, ``Hex.QAdjoin.common] do
    if dependencies.contains name then throwError "forbidden finite source dependency: {name}"
  let sources := #[Hex.RCF.CertificationInputs.polynomial,
    Hex.RCF.RealCoefficients.SquareTwo.polynomial]
  let mut presentations : Nat := 0
  let fourth := ``Hex.RCF.FiniteSourceTactic.fourthRoot
  let fourthDependencies ← Hex.RCF.ProofEvidence.projectDependencies #[fourth]
  if fourthDependencies.contains ``Hex.ZPoly.CheckedIrreducible then
    throwError "finite fourth-root source proof quotes whole-field irreducibility"
  let mut bodies : Nat := 0
  for root in roots.push fourth do
    let required := if root == fourth then #[2] else #[8]
    presentations := presentations + (← Hex.RCF.FiniteEvidence.checkClasses root sources required)
    let axioms ← collectAxioms root
    unless axioms.toList.mergeSort Name.quickLt ==
        [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
      throwError "unexpected source axioms: {root}: {axioms}"
    let .thmInfo outer ← getConstInfo root | throwError "expected exported theorem"
    let some inner := outer.value.getAppFn.constName? | throwError "expected retained checked proof"
    for name in #[root,inner] do
      let .thmInfo info ← getConstInfo name | throwError "expected actual body"
      let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__finiteSourceBody}
      let options := (← getOptions).setBool `debug.skipKernelTC false
      let _ ← ofExceptKernelException <| (← getEnv).addDeclCore
        (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
        declaration none (doCheck := true)
      bodies := bodies+1
  unless bodies == 16 do throwError "missing source body rechecks"
  logInfo m!"FRESH_FINITE_SOURCE: roots=8; bodies={bodies}; dependencies={dependencies.size}; fourth_dependencies={fourthDependencies.size}; presentations={presentations}; standard_axioms_only"
