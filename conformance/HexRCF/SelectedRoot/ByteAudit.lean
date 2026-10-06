/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.ByteChecks
import Lean.Elab.Command

open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.SelectedRootTests.ByteAudit

private meta def primitives : Array Name := #[``UInt8.ofNat, ``UInt8.instOfNat]

private meta partial def data (moduleIndex : ModuleIdx) (seen : NameHashSet)
    (name : Name) : MetaM NameHashSet := do
  if seen.contains name then return seen
  let mut seen := seen.insert name
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) | throwError "missing byte literal body {name}"
  for called in body.getUsedConstants do
    if (← getEnv).getModuleIdxFor? called == some moduleIndex then
      seen ← data moduleIndex seen called
    else
      let info ← getConstInfo called
      let harmless := primitives.contains called ||
        ((← getEnv).getProjectionFnInfo? called).isSome ||
        match info with
        | .ctorInfo _ | .inductInfo _ | .recInfo _ | .thmInfo _ => true
        | _ => false
      unless harmless do throwError "byte literal {name} calls unlisted computation {called}"
  return seen

run_meta do
  let some index := (← getEnv).getModuleIdxFor? ``Hex.RCF.SelectedRootTests.ByteData.literal |
    throwError "byte literal module missing"
  let checked ← data index {} ``Hex.RCF.SelectedRootTests.ByteData.literal
  unless checked.size == 167 do
    throwError "byte literal definition count changed: {checked.size}, expected 167"
  logInfo m!"byte literal: complete definition closure checked ({checked.size} declarations)"
  for name in #[``Hex.RCF.SelectedRootTests.ByteProofs.decoded,
    ``Hex.RCF.SelectedRootTests.ByteProofs.rowChecked,
    ``Hex.RCF.SelectedRootTests.ByteProofs.bytesAccepted,
    ``Hex.RCF.SelectedRootTests.ByteChecks.falseAccepted,
    ``Hex.RCF.SelectedRootTests.ByteChecks.wrongCoefficient] do
    let .thmInfo info ← getConstInfo name | throwError "expected byte acceptance theorem {name}"
    KernelCheck.addChecked (← mkFreshUserName `__selectedBytesChecked) info.type info.value
  logInfo "byte acceptance: five proof bodies checked with active kernel diagnostics"
  for name in #[``SelectedFormula.checkBytesWith_eq, ``SelectedFormula.bytes_evidence,
    ``SelectedFormula.bytes_domains, ``SelectedFormula.bytes_sound, ``SelectedFormula.bytes_false,
    ``SelectedFormula.bytes_spec, ``SelectedFormula.bytes_decoded, ``SelectedFormula.bytes_rejected,
    ``SelectedFormula.bytes_zero, ``Hex.RCF.SelectedRootTests.ByteData.written,
    ``Hex.RCF.SelectedRootTests.ByteData.size,
    ``Hex.RCF.SelectedRootTests.ByteProofs.bounded, ``Hex.RCF.SelectedRootTests.ByteProofs.decoded,
    ``Hex.RCF.SelectedRootTests.ByteProofs.exists_nested, ``Hex.RCF.SelectedRootTests.ByteProofs.zeroFirst,
    ``Hex.RCF.SelectedRootTests.ByteChecks.falseAccepted, ``Hex.RCF.SelectedRootTests.ByteChecks.counterexample,
    ``Hex.RCF.SelectedRootTests.ByteChecks.wrongCoefficient] do
    Hex.RCF.checkAxioms name (mkConst name)
end Hex.RCF.SelectedRootTests.ByteAudit
