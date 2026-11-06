/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.PolynomialTactic
import HexRCF.ProofEvidence
import Lean

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Lean Meta Hex Hex.RCF.RealCoefficients

run_meta withoutExporting do
  let laws := #[``PolynomialBuild.values_spec, ``PolynomialBuild.point_spec,
    ``PolynomialBuild.query_eval, ``PolynomialBuild.check_spec, ``PolynomialBuild.check_sound,
    ``PolynomialBounds.closed_native, ``PolynomialBounds.value_neg]
  let roots := #[``Hex.RCF.PolynomialTactic.root, ``Hex.RCF.PolynomialTactic.repeated,
    ``Hex.RCF.PolynomialTactic.interval, ``Hex.RCF.PolynomialTactic.nonnegative]
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies (laws ++ roots)
  for forbidden in #[``PolynomialBuild.build, ``PolynomialBuild.buildResult, ``PolynomialRadical.build,
      ``PolynomialSigns.build?, ``LiteralSign.Index.build, ``FieldRootSigns.Table.buildWith,
      ``FieldIsolate.proposeWith?, ``TarskiCertificate.certify, ``TarskiCertificate.fromChains,
      ``SignedRemainderChain.build, ``Field.value_eq_zero, ``Field.value_inv,
      ``ZPoly.CheckedIrreducible] do
    if dependencies.contains forbidden then
      throwError "registered-root proof depends on a producer or source field law: {forbidden}"
  let mut bodies := laws
  for root in roots do
    let actual ← Hex.RCF.ProofEvidence.projectDependencies #[root]
    unless actual.contains ``PolynomialBuild.check_sound do
      throwError "actual tactic proof omitted polynomial cell replay: {root}"
    let .thmInfo outer ← getConstInfo root | throwError "expected original tactic theorem"
    let some inner := outer.value.getAppFn.constName? |
      throwError "expected retained ordinary-kernel tactic proof"
    bodies := bodies ++ #[root, inner]
  let mut traces : Nat := 0
  for name in bodies do
    let axioms ← collectAxioms name
    unless axioms.all (fun name => [``propext, ``Classical.choice, ``Quot.sound].contains name) do
      throwError "unexpected registered-root axioms: {name}: {axioms}"
    let .thmInfo info ← getConstInfo name | throwError "expected actual theorem body"
    let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__polynomialBody}
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    unless (Kernel.getDiagnostics checked).unfoldCounter.isEmpty do traces := traces + 1
  unless bodies.size == 15 && traces == bodies.size do
    throwError "expected fifteen actual registered-root body checks with nonempty traces"
  unless dependencies.contains ``PolynomialBuild.check_sound do
    throwError "registered root and universal proofs omitted the polynomial cell theorem"
  logInfo m!"FRESH_POLYNOMIAL_TACTIC: bodies={bodies.size}; traces={traces}; dependencies={dependencies.size}; original automatic pi-root, repeated-root, Ioc and universal goals; no producer, source field law or nonstandard axiom"
