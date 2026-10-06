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
import all HexSignDet.Codec.Bytes
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Value
import all HexSignDet.Dag
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Euclid.DivGcd
import all Init.Data.Array.Basic
import all Init.Data.Repr

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

-- These executable checks exercise the public byte-descriptor adapter.
-- The ordinary-kernel control below separately checks context reconstruction.
#guard (RootReplay.decodeDescriptor (Element.codec (context := context) ValueCodec.rat) ValueCodec.nat
  Element.sign 8 subject.writeBytes evidence.writeBytes).isOk
#guard match RootReplay.decodeDescriptor (Element.codec (context := context) ValueCodec.rat)
    ValueCodec.nat Element.sign 8 subject.writeBytes (evidence.writeBytes.extract 0 1) with
  | .error message => message == "truncated certificate syntax"
  | .ok _ => false
#guard Codec.checkBytes {} (subject.writeBytes.extract 0 (subject.writeBytes.size - 2)) =
  .error "truncated certificate syntax"

@[expose] def literals : List (SignFact context) :=
  PackingConformance.literalFacts ++
    [⟨DensePoly.C (1 : Rat), 1, by
      rw [Context.signPoly_const context _ (by decide +kernel), DensePoly.coeff_C]
      decide +kernel⟩,
     ⟨DensePoly.C (-1 : Rat), -1, by
      rw [Context.signPoly_const context _ (by decide +kernel), DensePoly.coeff_C]
      decide +kernel⟩]

/-- Reconstruct the root and prepared cache using supplied coefficient records
and arithmetic facts. The returned context has the original operations. -/
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

@[expose] def rejectsWith (message : String) (subject evidence : Codec.Json)
    (facts : List (SignFact context)) : Bool :=
  match restored facts subject evidence with
  | .error actual => decide (actual = message)
  | .ok _ => false

@[expose] def accepted (result : Except String Bool) : Bool :=
  match result with
  | .error _ => false
  | .ok value => value

/-- Reconstruct the context from both actual byte records using the supplied
predecessor facts and operations. Check its retained root and reduction policy. -/
@[expose] def acceptsBytes (limits : Codec.Limits) (subject evidence : ByteArray)
    (facts : List (SignFact context)) : Bool :=
  accepted (Codec.decodePair (fun raw graph => .ok (reconstructed raw graph facts))
    subject evidence limits)

meta section
open Lean Meta Elab Command

private def proveDecision (proposition : Expr) (context : Simp.Context) : MetaM Expr := do
  let (simplified, _) ← Meta.simp proposition context
  let equality ← simplified.getProof' proposition
  let dec ← synthInstance (mkApp (mkConst ``Decidable) simplified.expr)
  let decision ← mkEq (mkAppN (mkConst ``decide) #[simplified.expr, dec]) (mkConst ``Bool.true)
  let refl ← mkEqRefl (mkConst ``Bool.true)
  KernelReplay.kernelCheck `__rootByteDecision decision refl
  let proof := mkAppN (mkConst ``of_decide_eq_true) #[simplified.expr, dec, refl]
  let result ← mkAppM ``Eq.mpr #[equality, proof]
  let _ ← KernelReplay.auditProof result proposition
  KernelReplay.kernelCheck `__rootByteEquation proposition result
  return result

private def saveProof (stem : Name) (proof : Expr) (type? : Option Expr := none) :
    MetaM Name := do
  let type ← match type? with
    | some type => pure type
    | none => inferType proof
  let _ ← KernelReplay.auditProof proof type
  let name ← mkFreshUserName stem
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let env ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    (.thmDecl {name, levelParams := [], type, value := proof}) none (doCheck := true)
  setEnv env
  return name

private unsafe def control : TermElabM Unit := do
  for name in #[``RootReplay.readDescriptor_subject, ``RootReplay.readContext_eq,
      ``RootReplay.decodeDescriptor_write, ``RootReplay.decodeDescriptor_subject,
      ``Codec.decodePair_write, ``Codec.decodePair_ok, ``Codec.parse_write] do
    let .thmInfo declaration ← getConstInfo name | throwError "root law is not a theorem"
    let _ ← KernelReplay.auditProof (mkConst name) declaration.type
  logInfo "rootLaws=7AuditedTheorems"
  let initial := mkConst ``literals
  let mut rules : SimpTheorems := {}
  for name in #[``rejectsWith, ``reconstructed, ``restored, ``RootReplay.readContext,
      ``RootReplay.readDescriptor, ``SignRequests.readRoot, ``Codec.readDescriptor, ``Codec.readGraph,
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
  for needed in collected.requests do
    let originalContext := mkConst ``CoefficientSignsConformance.context
    KernelReplay.kernelCheck `__rootReplayContext (← mkEq needed.context originalContext)
      (← mkEqRefl originalContext)
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

  -- Prove the binding from actual byte constructors to the quoted JSON before
  -- using the shared parser theorem. Neither native encoding nor quotation
  -- is itself evidence of parsing or certificate acceptance.
  let mut byteRules := rules
  let mut lexicalRules : SimpTheorems := {}
  lexicalRules ← lexicalRules.addDeclToUnfold ``Codec.checkBytes
  lexicalRules ← lexicalRules.addConst ``Codec.forIn_data
  lexicalRules ← lexicalRules.addConst ``Array.forIn_toList (inv := true)
  let byteDecisionContext ← Simp.mkContext (simpTheorems := #[lexicalRules])
    (congrTheorems := ← getSimpCongrTheorems)
  let limits ← Term.withoutErrToSorry
    (Term.elabTerm (← `(({} : Codec.Limits))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let limits ← instantiateMVars limits
  let mut bytes : Array Expr := #[]
  let mut parserNames : Array Name := #[]
  for (label, data) in [("subject", subjectData), ("graph", evidenceData)] do
    let phaseStarted ← IO.monoNanosNow
    IO.eprintln s!"rootBytePhase={label} bytes={data.writeBytes.size} start"
    let quoted := KernelReplay.jsonExpr data
    let input := mkApp (mkConst ``ByteArray.mk) (toExpr data.writeBytes.data)
    let printed := mkApp (mkConst ``Codec.Json.Value.writeBytes) quoted
    let writerLaw ← mkAppM ``Codec.Json.Value.writeBytes_toList #[quoted]
    let writerType ← inferType writerLaw
    let rhs := writerType.getAppArgs[2]!
    let listComparison ← mkEq (toExpr data.writeBytes.data.toList) rhs
    let listProof ← proveDecision listComparison byteDecisionContext
    IO.eprintln s!"rootBytePhase={label} quoted nanos={(← IO.monoNanosNow) - phaseStarted}"
    let writerReverse ← mkAppM ``Eq.symm #[writerLaw]
    let listEquation ← mkAppM ``Eq.trans #[listProof, writerReverse]
    let inputData := mkProj ``ByteArray 0 input
    let printedData := mkProj ``ByteArray 0 printed
    let arrayEquation := mkAppN (mkConst ``Array.ext' [Level.zero])
      #[mkConst ``UInt8, inputData, printedData, listEquation]
    let inputProof := mkAppN (mkConst ``ByteArray.ext) #[input, printed, arrayEquation]
    KernelReplay.kernelCheck `__rootByteBinding (← mkEq input printed) inputProof
    let bound ← mkEq (mkAppN (mkConst ``Codec.checkBytes) #[limits, input])
      (mkAppN (mkConst ``Except.ok [Level.zero, Level.zero])
        #[mkConst ``String, mkConst ``Unit, mkConst ``Unit.unit])
    let literalBound ← proveDecision bound byteDecisionContext
    IO.eprintln s!"rootBytePhase={label} bounded nanos={(← IO.monoNanosNow) - phaseStarted}"
    let check := mkApp (mkConst ``Codec.checkBytes) limits
    let checkEquation ← mkAppM ``congrArg #[check, inputProof]
    let checkReverse ← mkAppM ``Eq.symm #[checkEquation]
    let boundProof ← mkAppM ``Eq.trans #[checkReverse, literalBound]
    let parseWritten ← mkAppM ``Codec.parse_write #[quoted, limits, boundProof]
    let parse := mkApp (mkConst ``Codec.parse) limits
    let inputEquation ← mkAppM ``congrArg #[parse, inputProof]
    let parseEquation ← mkAppM ``Eq.trans #[inputEquation, parseWritten]
    let parseName ← saveProof `__rootByteParse parseEquation
    parserNames := parserNames.push parseName
    IO.eprintln s!"rootBytePhase={label} registered nanos={(← IO.monoNanosNow) - phaseStarted}"
    bytes := bytes.push input
  let jsonType := mkConst ``Codec.Json
  let readerType ← mkArrow jsonType (← mkArrow jsonType
    (mkAppN (mkConst ``Except [Level.zero, Level.zero]) #[mkConst ``String, mkConst ``Bool]))
  let pairProof ← withLocalDeclD `reader readerType fun reader => do
    let proof ← mkAppM ``Codec.decodePair_ok
      #[reader, bytes[0]!, bytes[1]!, limits, KernelReplay.jsonExpr subjectData,
        KernelReplay.jsonExpr evidenceData, mkConst parserNames[0]!, mkConst parserNames[1]!]
    mkLambdaFVars #[reader] proof
  let pairConstants := pairProof.getUsedConstants
  unless parserNames.size == 2 && parserNames.all pairConstants.contains do
    throwError "the pair equation did not retain both checked parser theorems"
  let pairName ← saveProof `__rootBytePair pairProof
  let byteProgram := mkAppN (mkConst ``acceptsBytes) (#[limits] ++ bytes)
  IO.eprintln "rootByteFront=start"
  let (frontType, frontProof) ← withLocalDeclD `facts (← inferType initial) fun facts => do
    let rawType := mkConst ``Codec.Json
    let reader ← withLocalDeclD `raw rawType fun raw =>
      withLocalDeclD `graph rawType fun graph => do
        let checked := mkAppN (mkConst ``reconstructed) #[raw, graph, facts]
        let result := mkAppN (mkConst ``Except.ok [Level.zero, Level.zero])
          #[mkConst ``String, mkConst ``Bool, checked]
        mkLambdaFVars #[raw, graph] result
    let decoded := mkApp (mkConst pairName) reader
    let proof ← mkAppM ``congrArg #[mkConst ``accepted, decoded]
    let type ← mkForallFVars #[facts]
      (← mkEq (mkApp byteProgram facts) (mkApp program facts))
    let proof ← mkLambdaFVars #[facts] proof
    return (type, proof)
  unless frontProof.getUsedConstants.contains pairName do
    throwError "the byte frontend proof did not retain the checked pair theorem"
  let frontName ← saveProof `__rootByteFront frontProof (some frontType)
  let retainedFront := mkAppN (mkConst ``id [Level.zero]) #[frontType, mkConst frontName]
  byteRules ← byteRules.add (.stx `__rootBytesFront Syntax.missing) #[] retainedFront
    (post := false)
  let byteContext ← Simp.mkContext (simpTheorems := #[byteRules])
    (congrTheorems := ← getSimpCongrTheorems)
  logInfo "rootBytesFront=originalStructuredChecker"
  IO.eprintln "rootByteReplay=start"
  let checkedBytes ← KernelReplay.collect 32 byteProgram initial byteContext (fun needed => do
    let some fact ← Generated.readPackets (← packets.get) needed | return none
    return some (← register fact))
  unless checkedBytes.requests.size == collected.requests.size do
    throwError "actual byte replay changed the arithmetic child count"
  match checkedBytes.outcome with
  | .checked true _ _ => logInfo "rootBytes=kernelAccepted actualInputs=2"
  | _ => throwError "actual root bytes failed to replay the supplied packets"

  IO.eprintln "rootByteReplay=checked"
  let (finalByteReplay, byteStats) ← KernelReplay.assemble
    (mkApp byteProgram checkedBytes.facts) byteContext
  match finalByteReplay with
  | .checked true proof _ =>
    let constants := proof.getUsedConstants
    unless constants.contains frontName do
      throwError "the final byte proof did not retain the checked pair theorem"
  | _ => throwError "the final byte replay did not accept the retained facts"
  let used := byteStats.usedTheorems.toArray.map (·.key)
  unless used.contains `__rootBytesFront do
    throwError "the final byte replay did not use the checked frontend equation"
  -- The pair equation retains both parser theorems; the frontend retains that pair.
  logInfo "rootBytesBindings=2UsedParserEquations"
  IO.eprintln "rootByteReplay=bindingsChecked"
  let (missingByteChild, _) ← KernelReplay.assemble (mkApp byteProgram initial) byteContext
  match missingByteChild with
  | .missing _ => logInfo "rootBytesMissingChild=unproved"
  | _ => throwError "actual bytes replay did not stop at the missing arithmetic child"

  let empty ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (SignFact context)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let empty ← instantiateMVars empty
  let (missingStored, _) ← KernelReplay.assemble (mkApp byteProgram empty) byteContext
  match missingStored with
  | .checked false _ _ => logInfo "rootBytesMissingStoredFacts=kernelRejected"
  | _ => throwError "actual bytes accepted absent stored coefficient facts"
  let truncationRules ← lexicalRules.addDeclToUnfold ``Codec.parse
  let truncationContext ← Simp.mkContext (simpTheorems := #[rules, truncationRules])
    (congrTheorems := ← getSimpCongrTheorems)
  let truncatedData := subjectData.writeBytes.extract 0 (subjectData.writeBytes.size - 2)
  let truncated := mkApp (mkConst ``ByteArray.mk) (toExpr truncatedData.data)
  let (truncatedResult, _) ← KernelReplay.assemble
    (mkAppN (mkConst ``acceptsBytes) #[limits, truncated, bytes[1]!, initial]) truncationContext
  match truncatedResult with
  | .checked false _ _ => logInfo "rootBytesTruncated=kernelRejected"
  | _ => throwError "actual bytes reader failed to reject truncated syntax"
  let (rejected, _) ← KernelReplay.assemble
    (mkAppN (mkConst ``rejectsWith)
      #[toExpr "stored sign fact missing or mismatched", KernelReplay.jsonExpr subjectData,
        KernelReplay.jsonExpr evidenceData, empty]) simpContext
  match rejected with
  | .checked true _ _ => logInfo "rootMissingStoredFacts=kernelRejected"
  | _ => throwError "root decoder accepted absent stored coefficient evidence"
  let some stale := replace subjectData [0] (.of (8 : Nat)) (.of (9 : Nat))
    | throwError "stale binding mutation failed"
  let some copied := replace subjectData [4] (.arr #[]) (.of ([1] : List Nat))
    | throwError "derivative index mutation failed"
  let some copied := replace copied [5] (.arr #[]) (.of ([-1] : List Int))
    | throwError "derivative sign mutation failed"
  let some forged := replace evidenceData [2, 1, 0, 7, 0, 11]
    (.of (1 : Int)) (.of (2 : Int)) | throwError "unused count mutation failed"
  for (label, subject, graph) in [("parentLabelMismatch", stale, evidenceData),
      ("uncertifiedDerivative", copied, evidenceData), ("unusedCount", subjectData, forged)] do
    let malformed := mkAppN (mkConst ``rejectsWith)
      #[toExpr "root descriptor replay rejected", KernelReplay.jsonExpr subject, KernelReplay.jsonExpr graph]
    let outcome ← KernelReplay.collect 32 malformed initial simpContext (fun needed => do
      let some fact ← Generated.readPackets (← packets.get) needed | return none
      return some (← register fact))
    match outcome.outcome with
    | .checked true _ _ => logInfo m!"rootRejected={label}"
    | _ => throwError "root reader failed to reject {label}"

syntax (name := rootReplayProbe) "#root_replay_probe" : command
@[command_elab rootReplayProbe]
unsafe def elaborateProbe : CommandElab := fun _ => liftTermElabM control

end
end Hex.RealClosure.Algebraic.KernelReplay.Root
