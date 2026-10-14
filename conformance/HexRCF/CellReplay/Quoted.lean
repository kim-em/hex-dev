/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Quote
import HexRCF.CellReplay.Controls
import HexRCF.CellReplay.Valuation
import HexRCF.CellReplay.Zero
open Lean Meta
run_meta do
  for name in #[``Hex.RCF.RealCoefficients.CellReplayTests.Quote.original, ``Hex.RCF.RealCoefficients.CellReplayTests.Quote.universal, ``Hex.RCF.RealCoefficients.CellReplayTests.Quote.guarded,
      ``Hex.RCF.RealCoefficients.CellReplayTests.Valuation.source,
      ``Hex.RCF.RealCoefficients.CellReplayTests.Zero.source] do
    let .thmInfo source ← getConstInfo name | throwError "expected actual quoted source body"
    let _ ← Hex.RCF.checkProof name source.type source.value
    let seen ← Hex.RCF.ProofEvidence.projectDependencies #[name]
    for law in #[``Hex.RCF.RealCoefficients.CellReplay.check_sound,
        ``Hex.RCF.RealCoefficients.RootReplay.Result.coverage,
        ``Hex.SignDet.Descriptor.rootsFrom_coverage,
        ``Hex.RCF.RealCoefficients.RepresentationSpecialize.prepare_eval,
        ``Hex.RCF.RealCoefficients.SectorSamples.Sector.inside,
        ``Hex.RCF.RealCoefficients.PointRows.Packet.value,
        ``Hex.RCF.RealCoefficients.CellRead.read] do
      unless seen.contains law do throwError "original cell quotation omitted actual checked evidence: {law}"
    for forbidden in #[``Hex.RCF.RealCoefficients.CellReplayTests.Check.source,
        ``Hex.RCF.RealCoefficients.RootReplayOrdinaryConformance.source,
        ``Hex.RCF.RealCoefficients.RootReplayOrdinaryConformance.negative,
        ``Hex.RCF.RealCoefficients.Samples.run, ``Hex.RealClosure.Tower.Sample.family,
      ``Hex.RCF.RealCoefficients.SectionBuild.build, ``Hex.RCF.RealCoefficients.PointBuild.build,
      ``Hex.SignDet.Descriptor.build, ``Hex.SignDet.Descriptor.buildSigns,
        ``Hex.SignDet.Descriptor.buildRoots, ``Hex.SignDet.buildPrepared,
        ``Hex.SignDet.buildTree, ``Hex.SignDet.buildTreeFrom, ``Hex.SignDet.buildNode] do
      if seen.contains forbidden then throwError "fresh cell quotation reused production or an old witness: {forbidden}"
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected original cell-quotation axioms"
