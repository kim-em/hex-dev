/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootReplay
public import HexRealClosure.SignCodec
public import KernelReplay.Nested
public meta import KernelReplay.Nested
public meta import HexRealClosure.RootReplay
import all HexRealClosure.RootReplay
import all HexRealClosure.SignCodec
import all HexRealClosure.SignRequests
import all HexRealClosure.Algebraic
import all HexRealClosure.AlgebraicCodec
import all HexRealClosureMathlib.NestedSignsConformance
import all HexRealClosureMathlib.PackingConformance
import all HexRealClosureMathlib.CoefficientSignsConformance
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Value
import all HexSignDet.Dag
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Euclid.DivGcd
import all Init.Data.Array.Basic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.Root
open CoefficientSignsConformance PackingConformance Hex.SignDet
open scoped Hex

@[expose] def subject : Codec.Json :=
  SignRequests.binding (Element.codec ValueCodec.rat) ValueCodec.nat
    NestedSignsConformance.linearRaw

@[expose] def evidence : Codec.Json :=
  Codec.graph (Element.codec ValueCodec.rat) ValueCodec.nat
    ⟨#[⟨NestedSignsConformance.linearNode, none⟩,
      ⟨NestedSignsConformance.linearNode, none⟩], 0⟩

@[expose] def literals : List (SignFact context) :=
  PackingConformance.literalFacts ++
    [⟨DensePoly.C (1 : Rat), 1, by
      rw [Context.signPoly_const context _ (by decide +kernel), DensePoly.coeff_C]
      decide +kernel⟩,
     ⟨DensePoly.C (-1 : Rat), -1, by
      rw [Context.signPoly_const context _ (by decide +kernel), DensePoly.coeff_C]
      decide +kernel⟩]

/-- Reconstruct the root and prepared cache using supplied coefficient records
and arithmetic facts. The returned context has the original element carrier. -/
@[expose] def restored (facts : List (SignFact context))
    (subject evidence : Codec.Json) :
    Except String (Context (Element context) Nat Element.sign 8) := RootReplay.readContext (Element.signCodec ValueCodec.rat facts) ValueCodec.nat
    Element.sign 8 Element.isClean
    (Element.cachedOne reduction reduction_eq facts)
    (Element.cachedAdd reduction reduction_eq facts)
    (Element.cachedNeg reduction reduction_eq facts)
    (Element.cachedSub reduction reduction_eq facts)
    (Element.cachedMul reduction reduction_eq facts)
    (Element.cachedInv reduction reduction_eq facts)
    (Element.cachedDiv reduction reduction_eq facts)
    (Element.cachedNatCast reduction reduction_eq facts)
    (Element.cachedOne_eq reduction reduction_eq facts)
    (Element.cachedAdd_eq reduction reduction_eq facts)
    (Element.cachedNeg_eq reduction reduction_eq facts)
    (Element.cachedSub_eq reduction reduction_eq facts)
    (Element.cachedMul_eq reduction reduction_eq facts)
    (Element.cachedInv_eq reduction reduction_eq facts)
    (Element.cachedDiv_eq reduction reduction_eq facts)
    (Element.cachedNatCast_eq reduction reduction_eq facts)
    subject evidence

@[expose] def reconstructed (subject evidence : Codec.Json)
    (facts : List (SignFact context)) : Bool :=
  match restored facts subject evidence with
  | .error _ => false
  | .ok result => decide (SignRequests.binding (Element.codec ValueCodec.rat)
      ValueCodec.nat result.root.raw = subject) && !result.canReduce

@[expose] def accepts (subject evidence : Codec.Json)
    (facts : List (SignFact context)) : Bool := (restored facts subject evidence).isOk

meta section
open Lean Meta Elab Command

private def replace (j : Codec.Json) (path : List Nat) (expected value : Codec.Json) :
    Option Codec.Json := do
  match path with
  | [] => if j = expected then some value else none
  | i :: rest =>
    let values ← j.getArr?.toOption
    let old ← values[i]?
    let changed ← replace old rest expected value
    return Codec.Json.arr (values.set! i changed)

private unsafe def control : TermElabM Unit := do
  for name in #[``RootReplay.readDescriptor_subject, ``RootReplay.readContext_eq] do
    let .thmInfo declaration ← getConstInfo name | throwError "root law is not a theorem"
    let _ ← KernelReplay.auditProof (mkConst name) declaration.type
  logInfo "rootLaws=2AuditedTheorems"
  let initial := mkConst ``literals
  let mut rules : SimpTheorems := {}
  for name in #[``accepts, ``reconstructed, ``restored, ``RootReplay.readContext,
      ``RootReplay.readDescriptor, ``SignRequests.readRoot, ``Codec.readGraph,
      ``Codec.tuple, ``Element.signCodec, ``Dag.descriptor?, ``Dag.replay?,
      ``Dag.validate?, ``Replay.check, ``queryPoly, ``Sturm.check,
      ``SignedRemainderChain.check] do
    rules ← rules.addDeclToUnfold name
  for name in #[``Dag.step_eq, ``Node.check_eq, ``checkMoment_eq,
      ``TarskiCertificate.check_eq, ``Array.toList_range, ``Replay.table_lookup,
      ``Context.changeOps_root, ``Descriptor.changeOps_raw, ``Context.root_adjoin] do
    rules ← rules.addConst name
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  let simpContext ← Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let subjectData ← evalExpr Codec.Json (mkConst ``Codec.Json) (mkConst ``subject)
    (checkMeta := false)
  let evidenceData ← evalExpr Codec.Json (mkConst ``Codec.Json) (mkConst ``evidence)
    (checkMeta := false)
  let program := mkAppN (mkConst ``reconstructed)
    #[KernelReplay.jsonExpr subjectData, KernelReplay.jsonExpr evidenceData]
  let packets ← IO.mkRef ([] : List Generated.Packet)
  let register := fun fact => do
    ofExceptKernelException (← KernelReplay.registerFact fact)
  let collected ← KernelReplay.collect 32 program initial simpContext (fun needed => do
    let some packet ← Generated.produce needed | return none
    packets.modify (packet :: ·)
    let some fact ← Generated.readFact packet | throwError "root arithmetic child rejected"
    return some (← register fact))
  match collected.outcome with
  | .checked true _ axioms =>
    logInfo m!"rootReconstructed=kernelAccepted children={collected.requests.size} axioms={axioms}"
  | .missing application => throwError "root reconstruction still needs evidence: {application}"
  | _ => throwError "root reconstruction rejected complete evidence"
  unless collected.requests.size == 2 do throwError "unexpected root arithmetic child count"
  let expected ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([2 * Sturm.Fixtures.x, 2 * Sturm.Fixtures.x - 1] :
      List (DensePoly Rat)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let retained := collected.requests.toList.map fun needed =>
    mkApp (mkConst ``PackingConformance.reduction) needed.polynomial
  let actual ← mkListLit (← inferType retained.head!) retained
  KernelReplay.kernelCheck `__rootReplayKeys (← mkEq actual expected) (← mkEqRefl expected)
  let replayed ← KernelReplay.collect 32 program initial simpContext (fun needed => do
    let some fact ← Generated.readPackets (← packets.get) needed | return none
    return some (← register fact))
  unless replayed.requests.size == collected.requests.size do
    throwError "root packet replay changed requests"
  match replayed.outcome with
  | .checked true _ _ => logInfo "rootReconstructedPackets=kernelAccepted"
  | _ => throwError "root reconstruction packet replay failed"

  let empty ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (SignFact context)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let empty ← instantiateMVars empty
  let (rejected, _) ← KernelReplay.assemble
    (mkAppN (mkConst ``accepts)
      #[KernelReplay.jsonExpr subjectData, KernelReplay.jsonExpr evidenceData, empty]) simpContext
  match rejected with
  | .checked false _ _ => logInfo "rootMissingStoredFacts=kernelRejected"
  | _ => throwError "root decoder accepted absent stored coefficient evidence"
  let some stale := replace subjectData [0] (.of (8 : Nat)) (.of (9 : Nat))
    | throwError "stale binding mutation failed"
  let some copied := replace subjectData [4] (.arr #[]) (.of ([1] : List Nat))
    | throwError "derivative index mutation failed"
  let some copied := replace copied [5] (.arr #[]) (.of ([-1] : List Int))
    | throwError "derivative sign mutation failed"
  let some forged := replace evidenceData [2, 1, 0, 7, 0, 11]
    (.of (1 : Int)) (.of (2 : Int)) | throwError "unused count mutation failed"
  for (label, subject, graph) in [("staleContext", stale, evidenceData),
      ("copiedDerivatives", copied, evidenceData), ("unusedCount", subjectData, forged)] do
    let malformed := mkAppN (mkConst ``accepts)
      #[KernelReplay.jsonExpr subject, KernelReplay.jsonExpr graph]
    let outcome ← KernelReplay.collect 32 malformed initial simpContext (fun needed => do
      let some fact ← Generated.readPackets (← packets.get) needed | return none
      return some (← register fact))
    match outcome.outcome with
    | .checked false _ _ => logInfo m!"rootRejected={label}"
    | _ => throwError "root reader failed to reject {label}"

syntax (name := rootReplayProbe) "#root_replay_probe" : command
@[command_elab rootReplayProbe]
unsafe def elaborateProbe : CommandElab := fun _ => liftTermElabM control

end
end Hex.RealClosure.Algebraic.KernelReplay.Root
