/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteDefault
import HexRCF.FiniteNestedSources
import HexRCF.FiniteCoordinates
import HexRCF.ProofEvidence
import HexRCF.FiniteEvidence
import Lean
open Lean Meta
set_option maxHeartbeats 8000000

-- Check actual theorem bodies and their full project dependencies. Arithmetic
-- auxiliaries were kernel-checked when emitted and are not recomputed here.
run_meta withoutExporting do
  let roots := #[``Hex.RCF.FiniteDefault.positive, ``Hex.RCF.FiniteDefault.betweenRoots,
    ``Hex.RCF.FiniteDefault.nested, ``Hex.RCF.FiniteNestedSources.octicBase,
    ``Hex.RCF.FiniteNestedSources.guardedBase]
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
      ``Hex.Sturm.queryPrepared, ``Hex.QAdjoin.common,
      ``Hex.RCF.RealCoefficients.FiniteLiteral.prove,
      ``Hex.RCF.RealCoefficients.CommonTactic.prepareCoordinates] do
    if dependencies.contains name then throwError "forbidden default proof dependency: {name}"
  let sources := #[Hex.RCF.CertificationInputs.polynomial,
    Hex.RCF.RealCoefficients.SquareTwo.polynomial]
  let mut presentations : Nat := 0
  for root in roots do
    let required := if root == ``Hex.RCF.FiniteDefault.positive ||
        root == ``Hex.RCF.FiniteDefault.betweenRoots then #[8]
      else if root == ``Hex.RCF.FiniteNestedSources.guardedBase then #[4]
      else #[8,16]
    presentations := presentations + (← Hex.RCF.FiniteEvidence.checkClasses root sources required)
  let mut bodies : Nat := 0
  for root in roots do
    let axioms ← collectAxioms root
    unless axioms.toList.mergeSort Name.quickLt ==
        [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
      throwError "unexpected default axioms: {root}: {axioms}"
    let .thmInfo outer ← getConstInfo root | throwError "expected exported theorem"
    let some inner := outer.value.getAppFn.constName? | throwError "expected retained checked proof"
    for name in #[root,inner] do
      let .thmInfo info ← getConstInfo name | throwError "expected actual body"
      let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__defaultBody}
      let options := (← getOptions).setBool `debug.skipKernelTC false
      let _ ← ofExceptKernelException <| (← getEnv).addDeclCore
        (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
        declaration none (doCheck := true)
      bodies := bodies+1
  unless bodies == 10 do throwError "missing default body rechecks"
  logInfo m!"FRESH_FINITE_DEFAULT: roots=5; bodies={bodies}; dependencies={dependencies.size}; presentations={presentations}; standard_axioms_only"
