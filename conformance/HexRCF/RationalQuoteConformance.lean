/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RationalQuoteCases
import KernelReplay.AxiomClosure
import HexRCF.ProofEvidence
import HexRCF.SelectedRoot.KernelCheck

open Lean Meta Hex Hex.RealClosure Hex.SignDet
namespace Hex.RCF.RationalQuoteTests
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

run_meta do
  let fractions := (Array.range 5).flatMap fun index =>
    #[Name.num `Hex.RCF.RationalQuoteTests.fraction_decode index,
      Name.num `Hex.RCF.RationalQuoteTests.fraction_read index]
  let roots := fractions ++ #[``nativeRoot_read,``negative_decode,``negative_read]
  for name in roots do
    let .thmInfo declaration ← getConstInfo name | throwError "rational quotation theorem missing"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "rational quotation has an unexpected transitive axiom: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  let cubic ← Hex.RCF.ProofEvidence.projectDependencies #[``nativeRoot_read]
  unless (← getEnv).contains ``Hex.RCF.RootQuoteTests.decode_integer do
    throwError "old finite-callback law control is absent"
  if cubic.contains ``Hex.RCF.RootQuoteTests.decode_integer then
    throwError "generic cubic quotation reused the old finite-callback law"
  unless cubic.contains ``NumberField.decode_payload do
    throwError "generic cubic quotation did not use the public rational decoder equation"
  for previous in #[`Hex.RCF.RootQuoteTests.nativeRoot_read,`Hex.RCF.RootQuoteTests.reader_ok] do
    if (← getEnv).contains previous then
      throwError "independent quotation fixture imported a previous acceptance theorem: {previous}"
  let .defnInfo frozen ← getConstInfo ``negativeFraction | throwError "frozen fraction missing"
  for used in frozen.value.getUsedConstants do
    let harmless := #[``OfNat.ofNat,``instOfNatNat].contains used ||
      match ← getConstInfo used with
      | .ctorInfo _ | .inductInfo _ => true
      | _ => false
    unless harmless do throwError "frozen negative fraction calls computation: {used}"
  for required in #[``NumberField.decode_payload,``Dag.replay_eq,``Dag.step_eq,
      ``Node.check_eq,``checkMoment_eq,``TarskiCertificate.check_eq,``Replay.table_lookup] do
    unless dependencies.contains required do
      throwError "generic quotation omitted a public law: {required}"
  let some moduleIndex := (← getEnv).getModuleIdxFor? ``nativeRoot
    | throwError "rational quotation module missing"
  let mut checked : Nat := 0
  for name in dependencies.toArray do
    if (← getEnv).getModuleIdxFor? name == some moduleIndex then
      match ← getConstInfo name with
      | .thmInfo declaration =>
        Hex.RCF.SelectedRootTests.KernelCheck.addChecked
          (← mkFreshUserName `__rationalQuoteBody) declaration.type declaration.value
        checked := checked + 1
      | .defnInfo declaration =>
        let statement ← mkEq declaration.value declaration.value
        Hex.RCF.SelectedRootTests.KernelCheck.addChecked
          (← mkFreshUserName `__rationalQuoteValue) statement (← mkEqRefl declaration.value)
      | _ => pure ()
  unless checked == 188 do
    throwError "rational quotation body coverage changed: {checked}"
  logInfo m!"generic rational quotation: {checked} actual theorem bodies under kernel producer diagnostics; complete axiom closure {axioms}"

end Hex.RCF.RationalQuoteTests
