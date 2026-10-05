/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.Generated
public meta import KernelReplay.Generated
public import HexRealClosure.ContextOperations
import all HexRealClosure.Algebraic
import all HexRealClosureMathlib.NestedSignsConformance
import all HexRealClosure.ContextOperations
import all HexSignDet.Descriptor
import all HexSignDet.Codec
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexPoly.Euclid.DivGcd
import all Init.Data.Array.Basic

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.Nested
open Hex.SignDet
open CoefficientSignsConformance PackingConformance
open scoped Hex

@[expose] noncomputable def embedding : Element context → ℝ :=
  Element.denote (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) Generated.cast_sign

/-- Transport the existing upper context to equal supplied-fact operations. -/
@[expose] def cachedContext (facts : List (SignFact context)) :=
  letI := Element.cachedOne reduction reduction_eq facts
  letI := Element.cachedAdd reduction reduction_eq facts
  letI := Element.cachedNeg reduction reduction_eq facts
  letI := Element.cachedSub reduction reduction_eq facts
  letI := Element.cachedMul reduction reduction_eq facts
  letI := Element.cachedInv reduction reduction_eq facts
  letI := Element.cachedDiv reduction reduction_eq facts
  letI := Element.cachedNatCast reduction reduction_eq facts
  Context.changeOps Element.instOne Element.instAdd Element.instNeg Element.instSub
    Element.instMul Element.instInv Element.instDiv Element.instNatCast
    (Element.cachedOne_eq reduction reduction_eq facts).symm
    (Element.cachedAdd_eq reduction reduction_eq facts).symm
    (Element.cachedNeg_eq reduction reduction_eq facts).symm
    (Element.cachedSub_eq reduction reduction_eq facts).symm
    (Element.cachedMul_eq reduction reduction_eq facts).symm
    (Element.cachedInv_eq reduction reduction_eq facts).symm
    (Element.cachedDiv_eq reduction reduction_eq facts).symm
    (Element.cachedNatCast_eq reduction reduction_eq facts).symm
    Element.sign 8 NestedSignsConformance.next

/-- Check supplied upper evidence with shared lower facts, returning a fact
in the original context with its exact polynomial key. -/
@[expose, macro_inline] def readFacts? (facts : List (SignFact context))
    (inputs : List (DensePoly (Element context) × Int)) (graph : Dag (Element context) Nat) :
    Option (List (SignFact NestedSignsConformance.next)) :=
  letI := Element.cachedOne reduction reduction_eq facts
  letI := Element.cachedAdd reduction reduction_eq facts
  letI := Element.cachedNeg reduction reduction_eq facts
  letI := Element.cachedSub reduction reduction_eq facts
  letI := Element.cachedMul reduction reduction_eq facts
  letI := Element.cachedInv reduction reduction_eq facts
  letI := Element.cachedDiv reduction reduction_eq facts
  letI := Element.cachedNatCast reduction reduction_eq facts
  let current := cachedContext facts
  do
    let memo ← graph.validate? Element.sign 8 current.root.raw.head
      current.root.raw.lower current.root.raw.upper
    inputs.mapM fun (p, claimed) => do
      let fact ← current.readSignFact? embedding
        (Element.denote_eq_zero (fun q : Rat => (q : ℝ))
          (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
          (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
          (fun _ => by simp) Generated.cast_sign
          (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
        (by
          rw [Element.cachedOne_eq]
          exact Element.denote_one _ _ _ _ _ _ _ Generated.cast_sign
            (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
        (by
          rw [Element.cachedAdd_eq]
          exact Element.denote_add _ _ _ _ _ _ _ Generated.cast_sign
            (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
        (by
          rw [Element.cachedSub_eq]
          exact Element.denote_sub _ _ _ _ _ _ _ Generated.cast_sign
            (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
        (by
          rw [Element.cachedMul_eq]
          exact Element.denote_mul _ _ _ _ _ _ _ Generated.cast_sign
            (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
        (by
          rw [Element.cachedNatCast_eq]
          exact Element.denote_nat _ _ _ _ _ _ _ Generated.cast_sign
            (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
        (by
          exact Element.sign_spec _ _ _ _ _ _ _ Generated.cast_sign
            (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
        (by
          rw [Element.cachedNeg_eq]
          exact Element.denote_neg _ _ _ _ _ _ _ Generated.cast_sign
            (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
        (by
          rw [Element.cachedInv_eq]
          exact Element.denote_inv _ _ _ _ _ _ _ Generated.cast_sign
            (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _)
            (fun _ _ => Rat.cast_div _ _)) p claimed memo graph.root
      return @SignFact.mk _ _ _ _ Element.instOne Element.instAdd Element.instNeg
        Element.instSub Element.instMul Element.instInv Element.instDiv Element.instNatCast
        _ _ _ NestedSignsConformance.next fact.polynomial fact.sign (by
        have same := Context.changeOps_signPoly Element.instOne Element.instAdd
          Element.instNeg Element.instSub Element.instMul Element.instInv Element.instDiv
          Element.instNatCast
          (Element.cachedOne_eq reduction reduction_eq facts).symm
          (Element.cachedAdd_eq reduction reduction_eq facts).symm
          (Element.cachedNeg_eq reduction reduction_eq facts).symm
          (Element.cachedSub_eq reduction reduction_eq facts).symm
          (Element.cachedMul_eq reduction reduction_eq facts).symm
          (Element.cachedInv_eq reduction reduction_eq facts).symm
          (Element.cachedDiv_eq reduction reduction_eq facts).symm
          (Element.cachedNatCast_eq reduction reduction_eq facts).symm
          Element.sign 8 NestedSignsConformance.next
        exact (congrFun same fact.polynomial).symm.trans fact.checked)

@[expose] def selections (facts : List (SignFact context)) : Bool :=
  match readFacts? facts [(NestedSignsConformance.nextQuery, 1),
      (NestedSignsConformance.unitPoly, 1)] NestedSignsConformance.graph with
  | some [a, b] => decide (a.polynomial = NestedSignsConformance.nextQuery ∧
      b.polynomial = NestedSignsConformance.unitPoly ∧ a.sign = 1 ∧ b.sign = 1)
  | _ => false

@[expose] def wrongSign (facts : List (SignFact context)) : Bool :=
  (readFacts? facts [(NestedSignsConformance.nextQuery, -1)]
    NestedSignsConformance.graph).isSome

@[expose] def wrongContext (facts : List (SignFact context)) : Bool :=
  (readFacts? facts [(NestedSignsConformance.nextQuery, 1)]
    {NestedSignsConformance.graph with entries :=
      NestedSignsConformance.graph.entries.modify 0 (fun entry =>
        {entry with node := {entry.node with context := 9}})}).isSome

@[expose] def wrongQuery (facts : List (SignFact context)) : Bool :=
  (readFacts? facts [(DensePoly.ofCoeffs #[NestedSignsConformance.rational 2], 1)]
    NestedSignsConformance.graph).isSome

@[expose] def wrongCount (facts : List (SignFact context)) : Bool :=
  (readFacts? facts [(NestedSignsConformance.nextQuery, 1)]
    {NestedSignsConformance.graph with entries :=
      NestedSignsConformance.graph.entries.modify 0 (fun entry =>
        {entry with node := {NestedSignsConformance.linearNode with moments :=
          #v[{NestedSignsConformance.linearCount with lowerVariations := 0}]}})}).isSome

meta section
open Lean Meta Elab Command

private def rules : MetaM SimpTheorems := do
  let mut rules : SimpTheorems := {}
  for name in #[``selections, ``wrongSign, ``wrongContext, ``wrongQuery, ``wrongCount, ``readFacts?, ``cachedContext,
      ``NestedSignsConformance.next, ``Context.extend, ``Dag.validate?, ``Replay.check,
      ``queryPoly, ``Sturm.check, ``SignedRemainderChain.check] do
    rules ← rules.addDeclToUnfold name
  for name in #[``Context.changeOps_root, ``Descriptor.changeOps_raw,
      ``Context.root_adjoin, ``NestedSignsConformance.root_raw, ``Dag.step_eq, ``Node.check_eq, ``checkMoment_eq,
      ``TarskiCertificate.check_eq, ``Array.toList_range] do
    rules ← rules.addConst name
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  rules ← rules.addConst ``eq_self
  rules ← rules.addConst ``iff_self
  return rules

private unsafe def control : TermElabM Unit := do
  let initial ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (SignFact context)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let initial ← instantiateMVars initial
  let simpContext ← Simp.mkContext (simpTheorems := #[← rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let program := mkConst ``selections
  let registered ← IO.mkRef (#[] : Array Name)
  let register := fun fact => do
    let restored ← KernelReplay.registerFact fact
    unless restored.getAppFn.isConstOf ``SignFact.mk do
      throwError "registered fact was not a constructor"
    let proof := restored.getAppArgs.back!
    let .const name _ := proof | throwError "registered proof was not a constant"
    let .thmInfo _ ← getConstInfo name | throwError "registered proof was not a theorem"
    registered.modify (·.push name)
    return restored
  let packets ← IO.mkRef ([] : List Generated.Packet)
  let collected ← KernelReplay.collect 2 program initial simpContext (fun needed => do
    let some packet ← Generated.produce needed | return none
    packets.modify (packet :: ·)
    let some fact ← Generated.readFact packet | throwError "generated child certificate rejected"
    return some (← register fact))
  unless collected.requests.size == 2 do throwError "unexpected nested child count"
  let firstKey ← Term.withoutErrToSorry
    (Term.elabTerm (← `((2 * Sturm.Fixtures.x : DensePoly Rat))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let firstKey ← instantiateMVars firstKey
  for (needed, expected) in collected.requests.zip #[firstKey,
      mkConst ``NestedSignsConformance.endpointQuery] do
    let actualContext := mkConst ``CoefficientSignsConformance.context
    KernelReplay.kernelCheck `__kernelReplayNestedContext
      (← mkEq needed.context actualContext) (← mkEqRefl actualContext)
    let key := mkApp (mkConst ``reduction) needed.polynomial
    KernelReplay.kernelCheck `__kernelReplayNestedKey
      (← mkEq key expected) (← mkEqRefl expected)
  match collected.outcome with
  | .checked true proof axioms =>
    KernelReplay.kernelCheck `__kernelReplayNestedSelections
      (← mkEq (mkApp program collected.facts) (mkConst ``Bool.true)) proof
    logInfo m!"nestedSelections=kernelAccepted children={collected.requests.size} axioms={axioms}"
  | .missing application => throwError "nested selection still missing: {application}"
  | _ => throwError "nested selections rejected"
  let replayed ← KernelReplay.collect 2 program initial simpContext
    (fun needed => do
      let some fact ← Generated.readPackets (← packets.get) needed | return none
      return some (← register fact))
  match replayed.outcome with
  | .checked true _ _ => logInfo "nestedPacketReplay=kernelAccepted"
  | _ => throwError "nested packet replay failed"
  unless (← registered.get).size == 4 do throwError "unexpected registered proof count"
  logInfo "nestedChildProofs=theoremReferences"
  let (empty, _) ← KernelReplay.assemble (mkApp program initial) simpContext
  match empty with
  | .missing application =>
    let needed ← KernelReplay.request application
    KernelReplay.kernelCheck `__kernelReplayNestedMissingContext
      (← mkEq needed.context (mkConst ``CoefficientSignsConformance.context))
      (← mkEqRefl (mkConst ``CoefficientSignsConformance.context))
    logInfo "nestedMissingChild=unproved"
  | _ => throwError "nested replay ran without child evidence"
  for name in [``wrongSign, ``wrongContext, ``wrongQuery, ``wrongCount] do
    let (outcome, _) ← KernelReplay.assemble (mkApp (mkConst name) collected.facts) simpContext
    match outcome with
    | .checked false _ _ => logInfo m!"nestedRejected={name}"
    | _ => throwError "forged upper evidence was not rejected: {name}"
  let incomplete ← KernelReplay.collect 1 program initial simpContext
    (Generated.readPackets (← packets.get))
  unless incomplete.requests.size == 2 do throwError "unexpected incomplete request count"
  match incomplete.outcome with
  | .missing _ => logInfo "nestedIncompleteChildren=unproved"
  | _ => throwError "nested replay completed with incomplete child evidence"

  let honest ← mkAppM ``List.head? #[collected.facts]
  let honest ← withTransparency .all (whnf honest)
  let honest ← withTransparency .all (whnf honest.getAppArgs.back!)
  unless honest.getAppFn.isConstOf ``SignFact.mk do throwError "unexpected collected fact"
  let args := honest.getAppArgs
  let corrupt := mkAppN honest.getAppFn (args.set! (args.size - 2) (toExpr (-1 : Int)))
  let countRegistered := fun env => env.toKernelEnv.constants.fold
    (fun count name _ => if name.eraseMacroScopes == `__kernelReplaySign then count + 1 else count)
    (0 : Nat)
  let before := countRegistered (← getEnv)
  let rejected ← try
    let _ ← KernelReplay.registerFact corrupt
    pure false
  catch exception =>
    let message ← exception.toMessageData.toString
    if message.startsWith "(kernel) application type mismatch" then pure true else throw exception
  unless rejected do throwError "registered malformed sign proof"
  unless countRegistered (← getEnv) == before do
    throwError "rejected proof changed the registered declarations"
  logInfo "nestedMalformedProof=kernelRejected"
  let hole ← mkFreshExprMVar (← inferType honest)
  let rejected ← try
    let _ ← KernelReplay.registerFact hole
    pure false
  catch exception =>
    let message ← exception.toMessageData.toString
    if message.startsWith "incomplete fact" then pure true else throw exception
  unless rejected && countRegistered (← getEnv) == before do
    throwError "incomplete fact changed the registered declarations"
  logInfo "nestedIncompleteProof=rejected"

syntax (name := nestedProbe) "#nested_probe" : command
@[command_elab nestedProbe]
unsafe def elaborateNested : CommandElab := fun _ => liftTermElabM control

end

end Hex.RealClosure.Algebraic.KernelReplay.Nested
