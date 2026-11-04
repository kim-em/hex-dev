/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteFieldCells
import HexRCF.FiniteFieldSource
import HexRCF.FiniteFieldGuards
import HexRCF.FiniteFieldCompatibility
import HexRCF.ProofEvidence
import Lean
open Lean Meta
set_option maxHeartbeats 4000000
private def returnsIrreducible : Expr → Bool
  | .forallE _ _ body _ => returnsIrreducible body
  | body => body.isAppOfArity ``Hex.ZPoly.CheckedIrreducible 1

/-- Inspect both explicit class predicates and closed applications returning
the class at the literal common polynomial or its reducible aliases.
Generic owner laws and the original quartic constructor remain allowed;
this audit does not evaluate source normalization searches. -/
private meta def commonIrreducible (names : NameHashSet) (common : Expr)
    (expressions : Array Expr := #[]) : MetaM Bool := do
  let visited ← IO.mkRef ({} : ExprMap Unit)
  let comparisons ← IO.mkRef ({} : ExprMap Bool)
  let providers ← IO.mkRef ({} : NameMap Bool)
  let found ← IO.mkRef false
  let rec scan (part : Expr) : MetaM Unit := do
    if (← found.get) || (← visited.get).contains part then return
    visited.modify (fun seen => seen.insert part ())
    let closed := !part.hasLooseBVars && !part.hasFVar && !part.hasMVar
    let mut candidate : Option Expr := none
    if closed && part.isAppOfArity ``Hex.ZPoly.CheckedIrreducible 1 then
      candidate := some part.getAppArgs[0]!
    else if closed then
      if let some name := part.getAppFn.constName? then
        let provider ← match (← providers.get).find? name with
          | some result => pure result
          | none => do
            let result := returnsIrreducible (← getConstInfo name).type
            providers.modify (fun seen => seen.insert name result)
            pure result
        if provider then
          let type ← inferType part
          if type.isAppOfArity ``Hex.ZPoly.CheckedIrreducible 1 then
            candidate := some type.getAppArgs[0]!
    if let some polynomial := candidate then
      let equal ← match (← comparisons.get).get? polynomial with
        | some result => pure result
        | none => do
          let result ← withoutModifyingState (withReducible (isDefEq polynomial common))
          comparisons.modify (fun seen => seen.insert polynomial result)
          pure result
      if equal then found.set true
    match part with
    | .app f a => scan f; scan a
    | .lam _ type body _ | .forallE _ type body _ => scan type; scan body
    | .letE _ type value body _ => scan type; scan value; scan body
    | .mdata _ body | .proj _ _ body => scan body
    | _ => pure ()
  for expression in expressions do scan expression
  let environment ← getEnv
  let modules := environment.header.moduleNames
  for name in names.toArray do
    if let some index := environment.getModuleIdxFor? name then
      if #[`Init,`Lean,`Std,`Batteries,`Mathlib,`Aesop,`Qq,`TauCeti].any
          (fun boundary => boundary.isPrefixOf modules[index]!) then continue
    let info ← getConstInfo name
    scan info.type
    if let some body := info.value? (allowOpaque := true) then scan body
  return ← found.get

run_meta withoutExporting do
  let roots := #[``Hex.RCF.FiniteFieldCells.universal,
    ``Hex.RCF.FiniteFieldGuards.accepted, ``Hex.RCF.FiniteFieldGuards.existsRoot,
    ``Hex.RCF.FiniteFieldGuards.falseUniversal]
  for root in roots do
    let axioms ← collectAxioms root
    unless axioms.toList.mergeSort Name.quickLt ==
        [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
      throwError "unexpected actual cell axioms: {root}: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for forbidden in #[``Hex.ZPoly.CheckedIrreducible,
      ``Hex.RCF.RealCoefficients.Field.value_eq_zero,
      ``Hex.RCF.RealCoefficients.Field.value_inv,
      ``Hex.RCF.RealCoefficients.Field.value_div,
      ``Hex.RCF.RealCoefficients.FieldBuild.isolateAt,
      ``Hex.RCF.RealCoefficients.FieldBuild.isolateAtWith,
      ``Hex.RCF.RealCoefficients.FieldBuild.buildTable,
      ``Hex.RCF.RealCoefficients.Field.prepareSign,
      ``Hex.RCF.RealCoefficients.FieldRootSigns.Table.build,
      ``Hex.RCF.RealCoefficients.RadicalCert.build,
      ``Hex.RCF.RealCoefficients.IsolationReplay.build,
      ``Hex.RCF.RealCoefficients.IsolationReplay.queryAt,
      ``Hex.TarskiCertificate.fromChains, ``Hex.SignedRemainderChain.build,
      ``Hex.RCF.RealCoefficients.FieldIsolate.propose?,
      ``Hex.Sturm.queryPrepared, ``Hex.QAdjoin.common] do
    if dependencies.contains forbidden then throwError "forbidden geometry proof dependency: {forbidden}"
  let mut bodies : Nat := 0
  let mut traces : Nat := 0
  for root in roots do
    let .thmInfo outer ← getConstInfo root | throwError "expected exported theorem"
    let some inner := outer.value.getAppFn.constName? | throwError "expected retained checked proof"
    for name in #[root, inner] do
      let .thmInfo info ← getConstInfo name | throwError "expected actual theorem body"
      let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__geometryBody}
      let options := (← getOptions).setBool `debug.skipKernelTC false
      let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
      let checked ← ofExceptKernelException <| environment.addDeclCore
        (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
        declaration none (doCheck := true)
      bodies := bodies + 1
      unless (Kernel.getDiagnostics checked).unfoldCounter.isEmpty do traces := traces+1
  unless bodies == 2 * roots.size && traces == bodies do
    throwError "expected actual kernel rechecks with nonempty traces for every body: {bodies}/{traces}"
  logInfo m!"FRESH_FINITE_FIELD_CELLS: roots={roots.size}; bodies={bodies}; traces={traces}; dependencies={dependencies.size}; standard_axioms_only"

run_meta withoutExporting do
  let root := ``Hex.RCF.FiniteFieldSource.original
  let axioms ← collectAxioms root
  unless axioms.toList.mergeSort Name.quickLt ==
      [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
    throwError "unexpected original-goal axioms: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[root]
  for forbidden in #[``Hex.RCF.RealCoefficients.Field.value_eq_zero,
      ``Hex.RCF.RealCoefficients.Field.value_inv, ``Hex.RCF.RealCoefficients.Field.value_div,
      ``Hex.RCF.RealCoefficients.FieldBuild.buildTable,
      ``Hex.RCF.RealCoefficients.Field.prepareSign,
      ``Hex.RCF.RealCoefficients.FieldRootSigns.Table.build,
      ``Hex.RCF.RealCoefficients.RadicalCert.build,
      ``Hex.RCF.RealCoefficients.IsolationReplay.build,
      ``Hex.RCF.RealCoefficients.IsolationReplay.queryAt,
      ``Hex.TarskiCertificate.fromChains, ``Hex.SignedRemainderChain.build,
      ``Hex.RCF.RealCoefficients.FieldIsolate.propose?,
      ``Hex.Sturm.queryPrepared, ``Hex.QAdjoin.common] do
    if dependencies.contains forbidden then throwError "unexpected original-goal dependency: {forbidden}"
  let cellType := (← getConstInfo ``Hex.RCF.FiniteFieldCells.universal).type
  let some presentation := cellType.find? (fun part =>
      part.isAppOfArity ``Hex.RCF.RealCoefficients.Field.literalRep 4) |
    throwError "missing literal common presentation in the checked cell target"
  let common := presentation.getAppArgs[0]!
  if ← commonIrreducible dependencies common then
    throwError "original-source proof quotes irreducibility of the new common presentation"
  let positive ← mkAppM ``Hex.ZPoly.CheckedIrreducible #[common]
  unless ← commonIrreducible {} common #[positive] do
    throwError "common-presentation irreducibility audit missed its positive control"
  let quartic ← mkAppM ``Hex.ZPoly.CheckedIrreducible
    #[mkConst ``Hex.RCF.CertificationInputs.polynomial]
  if ← commonIrreducible {} common #[quartic] then
    throwError "common-presentation audit rejected the distinct original quartic"
  let .thmInfo outer ← getConstInfo root | throwError "expected actual source theorem"
  let some inner := outer.value.getAppFn.constName? | throwError "expected retained source proof"
  let mut bodies : Nat := 0
  for name in #[root,inner] do
    let .thmInfo info ← getConstInfo name | throwError "expected actual source proof body"
    let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__sourceBody}
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    if (Kernel.getDiagnostics checked).unfoldCounter.isEmpty then
      throwError "source kernel recheck has no diagnostic trace"
    bodies := bodies+1
  logInfo m!"FRESH_FINITE_FIELD_SOURCE: bodies={bodies}; dependencies={dependencies.size}; actual_axioms={axioms}"

run_meta withoutExporting do
  let roots := #[``Hex.RCF.RealCoefficients.FieldCells.degrees,
    ``Hex.RCF.RealCoefficients.FieldCells.cells,
    ``Hex.RCF.RealCoefficients.FieldCells.specialize,
    ``Hex.RCF.RealCoefficients.FieldCells.forall_formula,
    ``Hex.RCF.RealCoefficients.FieldCells.exists_formula]
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for forbidden in #[``Hex.ZPoly.CheckedIrreducible,
      ``Hex.RCF.RealCoefficients.Field.value_eq_zero,
      ``Hex.RCF.RealCoefficients.Field.value_inv,
      ``Hex.RCF.RealCoefficients.Field.value_div] do
    if dependencies.contains forbidden then throwError "unexpected generic cell-law dependency: {forbidden}"
  for root in roots do
    let axioms ← collectAxioms root
    unless axioms.toList.mergeSort Name.quickLt ==
        [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
      throwError "unexpected cell-law axioms: {root}: {axioms}"
  logInfo m!"FINITE_FIELD_LAWS: roots={roots.size}; full_body_dependencies={dependencies.size}; standard_axioms_only"
