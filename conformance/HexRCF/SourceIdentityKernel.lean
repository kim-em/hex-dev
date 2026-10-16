/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SourceIdentityCases
import HexRCF.Tactic
import KernelReplay.AxiomClosure
open Hex.RCF.RealCoefficients Hex.RCF.SourceIdentityCases Lean Meta
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  let names := #[``SourceIdentity.observe, ``SourceIdentity.evaluate, ``SourceIdentity.equation,
    ``SourceIdentity.positive, ``SourceIdentity.margin_eval, ``SourceIdentity.select,
    ``source_zero, ``source_margin, ``source_selected, ``coefficient]
  for name in names do
    let .thmInfo declaration ← getConstInfo name | throwError "missing source-identity theorem: {name}"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
  let axioms ← Hex.RealClosure.Algebraic.KernelReplay.AxiomClosure.collect names
  unless axioms == (#[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt) do
    throwError "source identities have an unexpected complete axiom closure"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[``coefficient]
  for name in #[``SourceIdentity.select, ``SourceIdentity.margin_eval, ``equationFact,
      ``marginFact, ``HexRootsTheory.RefinedIsolation.eq_root_of_mem_closedDisc,
      ``Hex.RealClosure.Algebraic.Context.signPoly_spec] do
    unless dependencies.contains name do
      throwError "source identity omitted a checked selection bridge: {name}"
  for name in #[``Hex.RCF.SelectedRootTests.Data.alpha_value,
      ``Hex.RCF.SelectedRootTests.Data.selectedSqrt] do
    if dependencies.contains name then throwError "source identity reused fixture alias theorem: {name}"
  logInfo "fresh source identity bodies checked: literal equation and enclosure signs, exact selected root, no fixture alias identity; standard three axioms"
