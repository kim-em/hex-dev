/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RootQuoteSource
import KernelReplay.AxiomClosure
import HexRCF.ProofEvidence
open Lean Meta Hex Hex.RealClosure Hex.SignDet
namespace Hex.RCF.RootQuoteTests
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

run_meta do
  let _ ← getConstInfo ``runFinished
  let roots := #[``nativeRoot_read,``subject_encoded,``subject_read,``reader_ok,``root_raw,``root_subject]
  for name in roots do
    let .thmInfo declaration ← getConstInfo name | throwError "checked root theorem missing"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "unexpected complete cubic reader axiom closure"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for name in #[``Tower.contextCodec_self,``BaseContext.Element.codec_lawful,
      ``TarskiCertificate.check_eq,``Replay.table_lookup,``dite_eq_right] do
    unless dependencies.contains name do throwError "cubic reader omitted actual proof dependency {name}"
  unless (← getReducibilityStatus ``Node.check) == .semireducible do
    throwError "temporary checker reducibility escaped: {repr (← getReducibilityStatus ``Node.check)}"
  unless (← getReducibilityStatus ``Array.mapM.map) == .irreducible do
    throwError "temporary core reducibility escaped"
  logInfo "fresh original-reader and six literal bindings checked; actual public replay/core laws present; complete standard-three axiom closure; reducibility restored"
end Hex.RCF.RootQuoteTests
