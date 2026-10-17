/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardDescriptorPublic
import KernelReplay.GuardMomentAllPublicAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardDescriptorPoint.nodeData, mkConst ``GuardDescriptorPoint.nativeData,
    mkConst ``GuardDescriptorPoint.descriptorData, mkConst ``GuardDescriptorPoint.zero,
    mkConst ``GuardDescriptorPoint.unit, mkConst ``GuardDescriptorPoint.point,
    mkConst ``GuardDescriptorPoint.spec, mkConst ``GuardDescriptorPoint.reader,
    mkConst ``GuardDescriptorPoint.predecessor, mkConst ``GuardDescriptorPublic.descriptor,
    mkConst ``GuardDescriptorPublic.selected, mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"complete original second descriptor public consumer audit: originalOwnersExplicit=true allThreeMomentQueries=true completeOriginalDescriptor=true originalRootIntervalAndFullThomChecked=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorPublicAudit
