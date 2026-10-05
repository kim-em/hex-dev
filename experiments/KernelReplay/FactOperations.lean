/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.FactOperations
public import KernelReplay.Nested
public meta import KernelReplay.Nested
public meta import HexRealClosure.FactOperations
import all HexRealClosure.Algebraic
import all HexRealClosure.FactOperations
import all HexRealClosureMathlib.NestedSignsConformance
import all HexRealClosureMathlib.PackingConformance
import all HexRealClosureMathlib.CoefficientSignsConformance
import all HexPoly.Euclid.DivGcd
import all HexPoly.Dense
import all HexSturm.Basic
import all Init.Data.Array.Basic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FactOperations
open CoefficientSignsConformance PackingConformance
open scoped Hex

/-- The next context keeps its nonmonic defining polynomial, so its packing
policy retains the operand polynomial literally. -/
theorem nextReduction_eq : (id : DensePoly (Element context) → DensePoly (Element context)) =
    NestedSignsConformance.next.reduce := by
  funext p
  symm
  apply Context.reduce_nonmonic
  simp only [NestedSignsConformance.next, Context.extend, Context.root_adjoin,
    NestedSignsConformance.root_raw, NestedSignsConformance.linearRaw,
    NestedSignsConformance.linearHead]
  have h := Element.cachedOne_eq PackingConformance.reduction
    PackingConformance.reduction_eq ([] : List (SignFact context))
  dsimp only [inferInstance] at h
  rw [← h]
  decide +kernel

@[expose] def upperLiteral : Element NestedSignsConformance.next :=
  Element.restore (DensePoly.C PackingConformance.literal) 1 (by
    have h := NestedSignsConformance.next.signPoly_const
      (DensePoly.C PackingConformance.literal) (by decide +kernel)
    simpa only [DensePoly.coeff_C, ↓reduceIte, PackingConformance.literal_sign] using h)
    (by decide +kernel)

/-- Addition in a second extension still uses supplied evidence in the first.
Neither the element carrier nor its immutable context depends on the fact list. -/
@[expose] def sum (facts : List (SignFact context)) : Bool :=
  let operation := Element.factAdd
    (Element.cachedAdd PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id nextReduction_eq ([] : List (SignFact NestedSignsConformance.next))
  decide ((operation.add upperLiteral upperLiteral).sign = 1)

/-- Exercise every operation through the same original second-extension
carrier, with all required predecessor polynomial operations supplied. -/
@[expose] def arithmetic (facts : List (SignFact context)) : Bool :=
  let one := Element.factOne
    (Element.cachedOne PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedOne_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id nextReduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let add := Element.factAdd
    (Element.cachedAdd PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id nextReduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let neg := Element.factNeg
    (Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id nextReduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let sub := Element.factSub
    (Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id nextReduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let mul := Element.factMul
    (Element.cachedAdd PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id nextReduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let inv := Element.factInv
    (Element.cachedOne PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedInv PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedDiv PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedOne_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedInv_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedDiv_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id nextReduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let div := Element.factDiv
    (Element.cachedOne PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedInv PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedDiv PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedOne_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedInv_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedDiv_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id nextReduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let natCast := Element.factNatCast
    (Element.cachedNatCast PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedNatCast_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id nextReduction_eq ([] : List (SignFact NestedSignsConformance.next))
  decide (one.one.sign = 1 ∧ (add.add upperLiteral upperLiteral).sign = 1 ∧
    (neg.neg upperLiteral).sign = -1 ∧ (sub.sub upperLiteral upperLiteral).sign = 0 ∧
    (mul.mul upperLiteral upperLiteral).sign = 1 ∧ (inv.inv upperLiteral).sign = 1 ∧
    (div.div upperLiteral upperLiteral).sign = 1 ∧ (natCast.natCast 3).sign = 1)

@[expose] def monicOne : Element context :=
  Element.restore (DensePoly.C (1 : Rat)) 1 (by
    rw [Context.signPoly_const context _ (by decide +kernel), DensePoly.coeff_C]
    decide +kernel)
    (by decide +kernel)

@[expose] def monicHalf : Element context :=
  Element.restore (DensePoly.C (-1 / 2 : Rat)) (-1) (by
    rw [Context.signPoly_const context _ (by decide +kernel), DensePoly.coeff_C]
    decide +kernel)
    (by decide +kernel)

@[expose] def monicHead : DensePoly (Element context) :=
  DensePoly.ofCoeffs #[monicHalf,
    monicOne]

@[expose] def monicChain : Hex.SignedRemainderChain (Element context) :=
  { NestedSignsConformance.linearChain with
    chain := #[monicHead, NestedSignsConformance.unitPoly]
    initial := ⟨monicOne, 0, monicOne⟩
    terminal := some (monicOne, monicHead) }

@[expose] def monicCount : Hex.TarskiCertificate (Element context) (Element context) Nat :=
  { NestedSignsConformance.linearCount with
    head := monicHead
    squarefree := monicChain
    remainders := monicChain }

@[expose] def monicNode : Hex.SignDet.Node (Element context) Nat :=
  { NestedSignsConformance.linearNode with head := monicHead, moments := #v[monicCount] }

@[expose] def monicRaw : Hex.SignDet.RawDescriptor (Element context) Nat :=
  { NestedSignsConformance.linearRaw with head := monicHead }

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem monicCached :
    letI := Element.cachedOne PackingConformance.reduction PackingConformance.reduction_eq
      NestedSignsConformance.facts
    letI := Element.cachedAdd PackingConformance.reduction PackingConformance.reduction_eq
      NestedSignsConformance.facts
    letI := Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq
      NestedSignsConformance.facts
    letI := Element.cachedMul PackingConformance.reduction PackingConformance.reduction_eq
      NestedSignsConformance.facts
    letI := Element.cachedNatCast PackingConformance.reduction PackingConformance.reduction_eq
      NestedSignsConformance.facts
    monicRaw.check Element.sign 8 (.leaf monicNode) = true := by
  simp only [monicRaw, monicNode, monicCount, monicChain, monicHead,
    NestedSignsConformance.linearRaw, NestedSignsConformance.linearNode,
    NestedSignsConformance.linearCount, NestedSignsConformance.linearChain]
  simp only [Hex.SignDet.RawDescriptor.check, Hex.SignDet.Replay.check,
    Hex.SignDet.Node.check_eq, Hex.SignDet.checkMoment_eq, Hex.SignDet.queryPoly,
    Hex.Sturm.check, Hex.TarskiCertificate.check_eq,
    Hex.SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

@[expose] def monicRoot : Hex.SignDet.Descriptor (Element context) Nat Element.sign 8 :=
  Hex.SignDet.Descriptor.ofChecked Element.sign 8 monicRaw (.leaf monicNode) (by
    have h := monicCached
    rw [Element.cachedOne_eq PackingConformance.reduction PackingConformance.reduction_eq
        NestedSignsConformance.facts,
      Element.cachedAdd_eq PackingConformance.reduction PackingConformance.reduction_eq
        NestedSignsConformance.facts,
      Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq
        NestedSignsConformance.facts,
      Element.cachedMul_eq PackingConformance.reduction PackingConformance.reduction_eq
        NestedSignsConformance.facts,
      Element.cachedNatCast_eq PackingConformance.reduction PackingConformance.reduction_eq
        NestedSignsConformance.facts] at h
    exact h)

@[expose] def monicContext := context.extend monicRoot

/-- Reduction of `literal * X` uses supplied predecessor arithmetic in the
monic division loop and retains the exact lower representative of one. -/
@[expose] def monicReduction (facts : List (SignFact context)) : Bool :=
  let reduced := Context.factReduce monicContext
    (Element.cachedOne PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedOne_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (DensePoly.ofCoeffs #[0, PackingConformance.literal])
  decide (reduced.size = 1 ∧ (reduced.coeff 0).polynomial = Sturm.Fixtures.x ∧
    (reduced.coeff 0).sign = 1)

@[expose] def upperFacts : List (SignFact NestedSignsConformance.next) :=
  [⟨NestedSignsConformance.nextQuery, 1, NestedSignsConformance.next_sign⟩]

/-- A nonconstant result also needs its own upper-context fact. Lower
coefficient operations alone cannot discharge that missing upper evidence. -/
@[expose] def nonconstant (facts : List (SignFact NestedSignsConformance.next)) : Bool :=
  let operation := Element.factAdd
    (Element.cachedAdd PackingConformance.reduction PackingConformance.reduction_eq [])
    (Element.cachedAdd_eq PackingConformance.reduction PackingConformance.reduction_eq [])
    id nextReduction_eq facts
  let result := operation.add NestedSignsConformance.nextLiteral 0
  decide (result.polynomial = NestedSignsConformance.nextQuery ∧ result.sign = 1)

meta section
open Lean Meta Elab Command

private unsafe def control : TermElabM Unit := do
  for name in #[``Context.factReduce_eq, ``Element.factOne_eq, ``Element.factAdd_eq, ``Element.factNeg_eq,
      ``Element.factSub_eq, ``Element.factMul_eq, ``Element.factInv_eq,
      ``Element.factDiv_eq, ``Element.factNatCast_eq] do
    let .thmInfo declaration ← getConstInfo name | throwError "operation law is not a theorem"
    let _ ← KernelReplay.auditProof (mkConst name) declaration.type
  logInfo "factOperationsLaws=9AuditedTheorems"
  let initial ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (SignFact context)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let initial ← instantiateMVars initial
  let simpContext ← Simp.mkContext (simpTheorems := #[{}])
    (congrTheorems := ← getSimpCongrTheorems)
  let program := mkConst ``sum
  let packets ← IO.mkRef ([] : List Generated.Packet)
  let register := fun fact => do
    ofExceptKernelException (← KernelReplay.registerFact fact)
  let collected ← KernelReplay.collect 2 program initial simpContext (fun needed => do
    let some packet ← Generated.produce needed | return none
    packets.modify (packet :: ·)
    let some fact ← Generated.readFact packet | throwError "lower packet rejected"
    return some (← register fact))
  unless collected.requests.size == 1 do throwError "unexpected predecessor request count"
  let some needed := collected.requests[0]? | throwError "missing predecessor request"
  let expected ← Term.withoutErrToSorry
    (Term.elabTerm (← `((4 * Sturm.Fixtures.x : DensePoly Rat))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  KernelReplay.kernelCheck `__factOperationsContext
    (← mkEq needed.context (mkConst ``CoefficientSignsConformance.context))
    (← mkEqRefl (mkConst ``CoefficientSignsConformance.context))
  KernelReplay.kernelCheck `__factOperationsKey
    (← mkEq (mkApp (mkConst ``PackingConformance.reduction) needed.polynomial) expected)
    (← mkEqRefl expected)
  match collected.outcome with
  | .checked true _ axioms =>
    logInfo m!"factOperations=kernelAccepted children=1 axioms={axioms}"
  | _ => throwError "supplied predecessor arithmetic failed"
  let replayed ← KernelReplay.collect 2 program initial simpContext (fun needed => do
    let some fact ← Generated.readPackets (← packets.get) needed | return none
    return some (← register fact))
  unless replayed.requests.size == 1 do throwError "unexpected replay request count"
  match replayed.outcome with
  | .checked true _ _ => logInfo "factOperationsPackets=kernelAccepted"
  | _ => throwError "predecessor packet replay failed"
  let (missing, _) ← KernelReplay.assemble (mkApp program initial) simpContext
  match missing with
  | .missing application =>
    let request ← KernelReplay.request application
    KernelReplay.kernelCheck `__factOperationsMissingContext
      (← mkEq request.context needed.context) (← mkEqRefl needed.context)
    logInfo "factOperationsMissing=lowerContext"
  | _ => throwError "predecessor sign search escaped supplied-fact arithmetic"
  let program := mkConst ``arithmetic
  packets.set []
  let collected ← KernelReplay.collect 32 program initial simpContext (fun needed => do
    let some packet ← Generated.produce needed | return none
    packets.modify (packet :: ·)
    let some fact ← Generated.readFact packet | throwError "arithmetic child rejected"
    return some (← register fact))
  match collected.outcome with
  | .checked true _ axioms =>
    logInfo m!"factArithmetic=kernelAccepted children={collected.requests.size} axioms={axioms}"
  | .missing application => throwError "arithmetic still needs evidence: {application}"
  | _ => throwError "supplied predecessor arithmetic rejected"
  let replayed ← KernelReplay.collect 32 program initial simpContext (fun needed => do
    let some fact ← Generated.readPackets (← packets.get) needed | return none
    return some (← register fact))
  unless replayed.requests.size == collected.requests.size do
    throwError "arithmetic replay changed child requests"
  match replayed.outcome with
  | .checked true _ _ => logInfo "factArithmeticPackets=kernelAccepted"
  | _ => throwError "arithmetic packet replay failed"
  let supplied ← packets.get
  unless supplied.length == 5 do throwError "unexpected arithmetic packet count"
  for omitted in supplied do
    let incomplete := supplied.filter (fun packet => packet.polynomial != omitted.polynomial)
    unless incomplete.length == 4 do throwError "omission removed the wrong packet count"
    let rejected ← KernelReplay.collect 32 program initial simpContext (fun needed => do
      let some fact ← Generated.readPackets incomplete needed | return none
      return some (← register fact))
    match rejected.outcome with
    | .missing application =>
      let request ← KernelReplay.request application
      KernelReplay.kernelCheck `__factArithmeticMissingContext
        (← mkEq request.context (mkConst ``CoefficientSignsConformance.context))
        (← mkEqRefl (mkConst ``CoefficientSignsConformance.context))
      let decoded ← mkAppM ``Hex.SignDet.Codec.readPoly
        #[mkConst ``Hex.SignDet.ValueCodec.rat, KernelReplay.jsonExpr omitted.polynomial]
      let decoded ← withTransparency .all (whnf decoded)
      unless decoded.getAppFn.isConstOf ``Except.ok do throwError "omitted key did not decode"
      let expected := decoded.getAppArgs.back!
      KernelReplay.kernelCheck `__factArithmeticMissingKey
        (← mkEq (mkApp (mkConst ``PackingConformance.reduction) request.polynomial) expected)
        (← mkEqRefl expected)
    | _ => throwError "arithmetic succeeded without a required child packet"
  logInfo "factArithmeticIncomplete=5MissingChildren"

  let program := mkConst ``monicReduction
  packets.set []
  let collected ← KernelReplay.collect 32 program initial simpContext (fun needed => do
    let some packet ← Generated.produce needed | return none
    packets.modify (packet :: ·)
    let some fact ← Generated.readFact packet | throwError "monic division child rejected"
    return some (← register fact))
  match collected.outcome with
  | .checked true _ _ =>
    logInfo m!"factMonic=kernelAccepted children={collected.requests.size}"
  | .missing application => throwError "monic division still needs evidence: {application}"
  | _ => throwError "supplied monic division rejected"
  unless collected.requests.size > 0 do throwError "monic division did not demand lower evidence"
  let replayed ← KernelReplay.collect 32 program initial simpContext (fun needed => do
    let some fact ← Generated.readPackets (← packets.get) needed | return none
    return some (← register fact))
  unless replayed.requests.size == collected.requests.size do
    throwError "monic division replay changed child requests"
  match replayed.outcome with
  | .checked true _ _ => logInfo "factMonicPackets=kernelAccepted"
  | _ => throwError "monic division packet replay failed"
  let (missing, _) ← KernelReplay.assemble (mkApp program initial) simpContext
  match missing with
  | .missing application =>
    let request ← KernelReplay.request application
    KernelReplay.kernelCheck `__factMonicMissingContext
      (← mkEq request.context (mkConst ``CoefficientSignsConformance.context))
      (← mkEqRefl (mkConst ``CoefficientSignsConformance.context))
    let some first := collected.requests[0]? | throwError "missing division child request"
    KernelReplay.kernelCheck `__factMonicMissingKey
      (← mkEq request.polynomial first.polynomial) (← mkEqRefl first.polynomial)
    logInfo "factMonicMissing=lowerContextAndKey"
  | _ => throwError "monic division escaped supplied-fact arithmetic"

  let complete := mkApp (mkConst ``nonconstant) (mkConst ``upperFacts)
  let (accepted, _) ← KernelReplay.assemble complete simpContext
  match accepted with
  | .checked true _ _ => logInfo "factNonconstant=kernelAccepted"
  | _ => throwError "nonconstant result rejected complete upper evidence"
  let empty ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (SignFact NestedSignsConformance.next)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let empty ← instantiateMVars empty
  let (missing, _) ← KernelReplay.assemble (mkApp (mkConst ``nonconstant) empty) simpContext
  match missing with
  | .missing application =>
    let request ← KernelReplay.request application
    KernelReplay.kernelCheck `__factNonconstantMissingContext
      (← mkEq request.context (mkConst ``NestedSignsConformance.next))
      (← mkEqRefl (mkConst ``NestedSignsConformance.next))
    KernelReplay.kernelCheck `__factNonconstantMissingKey
      (← mkEq request.polynomial (mkConst ``NestedSignsConformance.nextQuery))
      (← mkEqRefl (mkConst ``NestedSignsConformance.nextQuery))
    logInfo "factNonconstantMissing=upperContextAndKey"
  | _ => throwError "nonconstant result escaped supplied upper evidence"

syntax (name := factOperationsProbe) "#fact_operations_probe" : command
@[command_elab factOperationsProbe]
unsafe def elaborateProbe : CommandElab := fun _ => liftTermElabM control

end
end Hex.RealClosure.Algebraic.KernelReplay.FactOperations
