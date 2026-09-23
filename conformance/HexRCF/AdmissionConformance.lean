/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.Tactic
public import HexRealRootsMathlib.TarskiSoundness

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

end Hex.RCF.AdmissionConformance
