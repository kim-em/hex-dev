/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.Tactic
public import HexRealRootsMathlib.TarskiSoundness
public import HexSturmMathlib.Soundness
public import HexRCF.RealCoefficients.FieldBuild

public section

/-! The optional tactic admission audit accepts only the exact #10389 bridge.
The ordinary rational tactic does not import that bridge. -/

namespace Hex.RCF.AdmissionConformance

open Lean Meta

run_meta do
  let bridge ← mkConstWithFreshMVarLevels ``HexRealRootsMathlib.Tarski.check_rootSum
  checkAxioms (Name.mkSimple "bridgeProbe") bridge
  let helper ← mkAuxTheorem (← inferType bridge) bridge (cache := false)
  checkAxioms (Name.mkSimple "helperProbe") helper
  for name in #[``HexSturmMathlib.check_sound,
      ``HexSturmMathlib.queryPrepared_sound, ``HexSturmMathlib.query_sound,
      ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound,
      ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound] do
    checkAxioms (Name.mkSimple "importedConsumerProbe")
      (← mkConstWithFreshMVarLevels name)
  let unrelated ← mkSorry (mkConst ``True) false
  unless (← observing? (checkAxioms (Name.mkSimple "unrelatedAdmissionProbe") unrelated)).isNone do
    throwError "an unrelated sorry passed the optional-handler axiom audit"

end Hex.RCF.AdmissionConformance
