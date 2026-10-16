/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RootQuoteSource
import KernelReplay.AxiomClosure
import HexRCF.ProofEvidence
import HexRCF.SelectedRoot.KernelCheck
open Lean Meta Hex Hex.RealClosure Hex.SignDet
namespace Hex.RCF.RootQuoteTests
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

/-- Inspect the literal data independently of reader and proof code. -/
private meta partial def literalData (moduleIndex : ModuleIdx) (seen : NameHashSet)
    (name : Name) : MetaM NameHashSet := do
  if seen.contains name then return seen
  let mut seen := seen.insert name
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true)
    | throwError "missing literal body {name}"
  for called in body.getUsedConstants do
    if (← getEnv).getModuleIdxFor? called == some moduleIndex then
      seen ← literalData moduleIndex seen called
    else
      let info ← getConstInfo called
      let harmless := #[``Int.instNegInt,``instOfNat,``instOfNatNat,
          ``Codec.Json].contains called ||
        ((← getEnv).getProjectionFnInfo? called).isSome ||
        match info with
        | .ctorInfo _ | .inductInfo _ | .recInfo _ | .thmInfo _ => true
        | _ => false
      unless harmless do throwError "literal {name} calls unlisted computation {called}"
  return seen

run_meta do
  let _ ← getConstInfo ``runFinished
  let some index := (← getEnv).getModuleIdxFor? ``subject
    | throwError "literal subject module missing"
  let mut literalNames : NameHashSet := {}
  for name in #[``subject,``evidence,``frameJson] do
    literalNames ← literalData index literalNames name
  unless literalNames.size == 49 do
    throwError "cubic literal closure changed: {literalNames.size}"
  logInfo m!"cubic frozen JSON closure: {literalNames.size} definitions"
  let roots := #[``nativeRoot_read,``subject_encoded,``subject_read,``reader_ok,``root_raw,``root_subject]
  for name in roots do
    let .thmInfo declaration ← getConstInfo name | throwError "checked root theorem missing"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "unexpected complete cubic reader axiom closure"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  let some quotedIndex := (← getEnv).getModuleIdxFor? ``nativeRoot
    | throwError "quoted root module missing"
  let mut checked : Nat := 0
  for name in dependencies.toArray do
    if (← getEnv).getModuleIdxFor? name == some quotedIndex then
      let declaration ← getConstInfo name
      match declaration with
      | .thmInfo declaration =>
        Hex.RCF.SelectedRootTests.KernelCheck.addChecked
          (← mkFreshUserName `__rootQuoteBody) declaration.type declaration.value
        checked := checked + 1
      | .defnInfo declaration =>
        -- Data is checked at an equality type; its own closure is independently audited.
        let statement ← mkEq declaration.value declaration.value
        Hex.RCF.SelectedRootTests.KernelCheck.addChecked
          (← mkFreshUserName `__rootQuoteData) statement (← mkEqRefl declaration.value)
      | _ => pure ()
  unless checked > 20 do throwError "actual quotation auxiliary bodies were not inspected"
  logInfo m!"actual cubic quotation bodies under kernel producer diagnostics: {checked}"
  for name in #[``Tower.contextCodec_self,``NumberField.decode_payload,
      ``TarskiCertificate.check_eq,``Replay.table_lookup,``dite_eq_right] do
    unless dependencies.contains name do throwError "cubic reader omitted actual proof dependency {name}"
  unless (← getReducibilityStatus ``Node.check) == .semireducible do
    throwError "temporary checker reducibility escaped: {repr (← getReducibilityStatus ``Node.check)}"
  unless (← getReducibilityStatus ``Array.mapM.map) == .irreducible do
    throwError "temporary core reducibility escaped"
  logInfo "fresh original-reader and six literal bindings checked; actual public replay/core laws present; complete standard-three axiom closure; reducibility restored"
end Hex.RCF.RootQuoteTests
