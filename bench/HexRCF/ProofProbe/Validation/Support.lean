/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public meta import HexRCF.ProofEvidence
public section

/-! Matched fresh-module costs of redundant fresh-input validation. -/

namespace Hex.RCF.ProofProbe.Validation
open Lean Meta

/-- The checked arm retains the source-transport theorem beneath the final
kernel wrapper. The fresh arm submits its original Iff application directly. -/
meta def assertArm (name : Name) (checked : Bool) : MetaM Unit := do
  let info ← getConstInfo name
  let some proof := info.value? (allowOpaque := true) | throwError "missing probe proof"
  let some auxiliary := proof.consumeMData.getAppFn.constName? |
    throwError "probe proof lacks its final kernel wrapper"
  let info ← withoutExporting <| getConstInfo auxiliary
  let some body := info.value? (allowOpaque := true) | throwError "missing kernel wrapper body"
  let direct := body.consumeMData.getAppFn.isConstOf ``Iff.mp
  unless direct == !checked do
    throwError "probe did not use its selected validation arm"

end Hex.RCF.ProofProbe.Validation
