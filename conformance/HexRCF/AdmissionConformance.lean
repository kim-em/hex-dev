/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.Tactic
public import HexRealRootsTheory.TarskiSoundness
public import HexSturmTheory.Soundness
public import HexRCF.RealCoefficients.FieldBuild

public section

/-! The optional tactic rejects every nonstandard axiom, including hidden
admissions in auxiliary proofs. The proved query bridge passes this audit. -/

namespace Hex.RCF.AdmissionConformance

open Lean Meta

run_meta do
  let bridge ← mkConstWithFreshMVarLevels ``HexRealRootsTheory.Tarski.check_rootSum
  checkAxioms (Name.mkSimple "bridgeProbe") bridge
  let helper ← mkAuxTheorem (← inferType bridge) bridge (cache := false)
  checkAxioms (Name.mkSimple "helperProbe") helper
  for name in #[``HexSturmTheory.check_sound,
      ``HexSturmTheory.queryPrepared_sound, ``HexSturmTheory.query_sound,
      ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound,
      ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound] do
    checkAxioms (Name.mkSimple "importedConsumerProbe")
      (← mkConstWithFreshMVarLevels name)
  let unrelated ← mkSorry (mkConst ``True) false
  unless (← observing? (checkAxioms (Name.mkSimple "unrelatedAdmissionProbe") unrelated)).isNone do
    throwError "an unrelated sorry passed the optional-handler axiom audit"

end Hex.RCF.AdmissionConformance
