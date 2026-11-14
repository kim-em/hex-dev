/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.QueryRing
import HexRCF.ProofEvidence
import Lean

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

open Lean Meta Hex Hex.RCF.RealCoefficients

run_meta withoutExporting do
  let laws := #[``QueryReplay.sign_spec, ``QueryReplay.cached_eq,
    ``QueryReplay.leading_spec, ``QueryReplay.transport, ``QueryReplay.checked,
    ``QueryReplay.missing_rejects, ``Hex.RCF.QueryRing.read_closed,
    ``Hex.RCF.QueryRing.lookup_spec, ``Hex.RCF.QueryRing.killed]
  let roots := #[``Hex.RCF.QueryRing.accepted, ``Hex.RCF.QueryRing.real_checked]
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies (laws ++ roots)
  for forbidden in #[``ZPoly.CheckedIrreducible, ``Field.value_eq_zero,
      ``Field.value_inv, ``Field.value_div, ``Field.prepareSign,
      ``FieldBuild.buildTable, ``FieldRootSigns.Table.build,
      ``RadicalCert.build, ``IsolationReplay.build, ``FieldIsolate.propose?,
      ``TarskiCertificate.certify, ``TarskiCertificate.fromChains,
      ``SignedRemainderChain.build, ``Sturm.queryPrepared, ``QAdjoin.common] do
    if dependencies.contains forbidden then
      throwError "coefficient-ring replay proof depends on a producer or field law: {forbidden}"
  let mut bodies := laws
  for root in roots do
    let .thmInfo outer ← getConstInfo root | throwError "expected exported query theorem"
    let some inner := outer.value.getAppFn.constName? |
      throwError "expected retained ordinary-kernel query proof"
    bodies := bodies ++ #[root, inner]
  let mut traces := 0
  for name in bodies do
    let axioms ← collectAxioms name
    unless axioms.all (fun name => [``propext, ``Classical.choice, ``Quot.sound].contains name) do
      throwError "unexpected coefficient-ring replay axioms: {name}: {axioms}"
    let .thmInfo info ← getConstInfo name | throwError "expected actual query theorem body"
    let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__queryBody}
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    unless (Kernel.getDiagnostics checked).unfoldCounter.isEmpty do traces := traces + 1
  unless bodies.size == 13 && traces == bodies.size do
    throwError "expected thirteen actual query body checks with nonempty traces: {bodies.size}/{traces}"
  logInfo m!"FRESH_QUERY_RING: bodies={bodies.size}; traces={traces}; dependencies={dependencies.size}; no source field, producer or nonstandard axiom"
