/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteFieldCompile
import HexRCF.ProofEvidence
import Lean
open Lean Meta
set_option maxHeartbeats 4000000

-- Recheck actual exported/retained bodies. Diagnostic traces are not evidence
-- of recomputing arithmetic auxiliaries already checked when they were emitted.
run_meta withoutExporting do
  let roots := #[``Hex.RCF.FiniteFieldCompile.division,
    ``Hex.RCF.FiniteFieldCompile.inverse, ``Hex.RCF.FiniteFieldCompile.nested,
    ``Hex.RCF.FiniteFieldCompile.memoLeft, ``Hex.RCF.FiniteFieldCompile.memoRight]
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for name in #[``Hex.ZPoly.CheckedIrreducible,
      ``Hex.RCF.RealCoefficients.Field.value_eq_zero,
      ``Hex.RCF.RealCoefficients.Field.value_div,
      ``Hex.RCF.RealCoefficients.Field.value_inv,
      ``Hex.RCF.RealCoefficients.Field.value_quotient,
      ``Hex.RCF.RealCoefficients.FieldBuild.buildTable,
      ``Hex.Sturm.prepare, ``Hex.SignedRemainderChain.build] do
    if dependencies.contains name then throwError "forbidden finite division proof dependency: {name}"
  let mut bodies : Nat := 0
  for root in roots do
    let axioms ← collectAxioms root
    unless axioms.toList.mergeSort Name.quickLt ==
        [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
      throwError "unexpected finite division axioms: {root}: {axioms}"
    let .thmInfo outer ← getConstInfo root | throwError "expected exported theorem"
    let some inner := outer.value.getAppFn.constName? | throwError "expected checked retained proof"
    for name in #[root, inner] do
      let .thmInfo info ← getConstInfo name | throwError "expected actual theorem body"
      let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__divisionBody}
      let options := (← getOptions).setBool `debug.skipKernelTC false
      let _ ← ofExceptKernelException <| (← getEnv).addDeclCore
        (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
        declaration none (doCheck := true)
      bodies := bodies+1
  unless bodies == 2 * roots.size do throwError "missing finite division body recheck"
  logInfo m!"FRESH_FINITE_DIVISION: roots={roots.size}; bodies={bodies}; dependencies={dependencies.size}; standard_axioms_only"
