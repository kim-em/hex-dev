/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SourceIdentityControls
import HexRCF.SourceIdentityCases
import HexRCF.RealCoefficients.ScalarPacket
import HexRCF.ProofEvidence
import HexRCF.SelectedRoot.KernelCheck
import KernelReplay.AxiomClosure
meta section
open Lean Meta Hex.RealClosure Hex.RCF.RealCoefficients
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
run_meta do
  let roots := #[``Hex.RCF.SourceIdentityPacket.selected,``Hex.RCF.SourceIdentityPacket.coefficient,
    ``Hex.RCF.SourceIdentityControls.negative_read,``Hex.RCF.SourceIdentityControls.negative_sign]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
    throwError "quoted source identity has inadmissible dependencies"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``SourceIdentity.identify,``SourceIdentity.observe,``SourceIdentity.select,
      ``SourceIdentity.margin_eval,``RootQuote.option_eq,``ScalarPacket.fields,
      ``ScalarPacket.restore,``ScalarPacket.read_restore,``Hex.RealClosure.Algebraic.Context.signPoly_spec] do
    unless dependencies.contains required do throwError "quoted source omitted {required}"
  for forbidden in #[``Hex.RCF.SourceIdentityCases.equationFact,
      ``Hex.RCF.SourceIdentityCases.marginFact,``Hex.RCF.SourceIdentityCases.negativeMarginFact,
      ``Hex.RCF.SourceIdentityCases.source_zero,``Hex.RCF.SourceIdentityCases.source_margin,
      ``Hex.RCF.SourceIdentityCases.source_selected,``Hex.RCF.SourceIdentityCases.coefficient,
      ``Hex.RCF.SourceIdentityCases.observed,``Hex.RCF.SelectedRootTests.Data.alpha_value,
      ``Hex.RCF.SelectedRootTests.Data.selectedSqrt] do
    if dependencies.contains forbidden then throwError "quoted source reused {forbidden}"
  let selected ← Hex.RCF.ProofEvidence.projectDependencies #[``Hex.RCF.SourceIdentityPacket.selected]
  for forbidden in #[``Hex.RCF.SelectedRootTests.Data.selectedFacts,
      ``Hex.RCF.SelectedRootTests.Data.definingPoly,``Hex.RCF.SelectedRootTests.Data.lowerData] do
    if selected.contains forbidden then throwError "quoted selection reused {forbidden}"
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let modules := (← getEnv).header.moduleNames
  let allowed := #[`HexRCF.SourceIdentityPacket,`HexRCF.SourceIdentityControls,`HexRCF.SourceIdentityLiterals,
    `HexRCF.RealCoefficients.SourceIdentity,`HexRCF.RealCoefficients.SourceIdentityQuote,
    `HexRCF.RealCoefficients.RootQuote,`HexRCF.RealCoefficients.ScalarPacket]
  let mut theorems : Nat := 0
  let mut definitions : Nat := 0
  let mut traces : Nat := 0
  for name in dependencies.toArray do
    let some index := (← getEnv).getModuleIdxFor? name | continue
    unless allowed.contains modules[index]! do continue
    let declaration ← match ← getConstInfo name with
      | .thmInfo info =>
        theorems := theorems+1
        pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__treeBody})
      | .defnInfo info =>
        definitions := definitions+1
        pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__treeData})
      | _ => continue
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let diagnostics := Kernel.getDiagnostics checked
    unless diagnostics.enabled do throwError "quoted source identity diagnostics disabled"
    if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
        #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,
          ``Hex.SignDet.Descriptor.ofReplay?] then
      throwError "quoted source identity reduced producer {producer}: {count}; body={name}"
    if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
  unless theorems == 218 && definitions == 179 && traces == 385 do
    throwError "quoted source identity inventory changed: {theorems}/{definitions}/{traces}"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "quoted source identity audit retained copied declarations"
  logInfo m!"quoted source identity actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
