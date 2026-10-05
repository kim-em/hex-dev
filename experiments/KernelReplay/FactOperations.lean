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
import all HexPoly.Euclid.DivGcd

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FactOperations
open CoefficientSignsConformance PackingConformance
open scoped Hex

/-- The next context keeps its nonmonic defining polynomial, so its packing
policy retains the operand polynomial literally. -/
theorem reduction_eq : (id : DensePoly (Element context) → DensePoly (Element context)) =
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

@[expose] def literal : Element NestedSignsConformance.next :=
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
    id reduction_eq ([] : List (SignFact NestedSignsConformance.next))
  decide ((operation.add literal literal).sign = 1)

/-- Exercise every operation through the same original second-extension
carrier, with all required predecessor polynomial operations supplied. -/
@[expose] def arithmetic (facts : List (SignFact context)) : Bool :=
  let one := Element.factOne
    (Element.cachedOne PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedOne_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id reduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let add := Element.factAdd
    (Element.cachedAdd PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id reduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let neg := Element.factNeg
    (Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id reduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let sub := Element.factSub
    (Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id reduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let mul := Element.factMul
    (Element.cachedAdd PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id reduction_eq ([] : List (SignFact NestedSignsConformance.next))
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
    id reduction_eq ([] : List (SignFact NestedSignsConformance.next))
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
    id reduction_eq ([] : List (SignFact NestedSignsConformance.next))
  let natCast := Element.factNatCast
    (Element.cachedNatCast PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedNatCast_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    id reduction_eq ([] : List (SignFact NestedSignsConformance.next))
  decide (one.one.sign = 1 ∧ (add.add literal literal).sign = 1 ∧
    (neg.neg literal).sign = -1 ∧ (sub.sub literal literal).sign = 0 ∧
    (mul.mul literal literal).sign = 1 ∧ (inv.inv literal).sign = 1 ∧
    (div.div literal literal).sign = 1 ∧ (natCast.natCast 3).sign = 1)

meta section
open Lean Meta Elab Command

private unsafe def control : TermElabM Unit := do
  for name in #[``Element.factOne_eq, ``Element.factAdd_eq, ``Element.factNeg_eq,
      ``Element.factSub_eq, ``Element.factMul_eq, ``Element.factInv_eq,
      ``Element.factDiv_eq, ``Element.factNatCast_eq] do
    let .thmInfo declaration ← getConstInfo name | throwError "operation law is not a theorem"
    let _ ← KernelReplay.auditProof (mkConst name) declaration.type
  logInfo "factOperationsLaws=8AuditedTheorems"
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
    let rejected ← KernelReplay.collect 32 program initial simpContext (fun needed => do
      let some fact ← Generated.readPackets incomplete needed | return none
      return some (← register fact))
    match rejected.outcome with
    | .missing application =>
      let request ← KernelReplay.request application
      KernelReplay.kernelCheck `__factArithmeticMissingContext
        (← mkEq request.context (mkConst ``CoefficientSignsConformance.context))
        (← mkEqRefl (mkConst ``CoefficientSignsConformance.context))
    | _ => throwError "arithmetic succeeded without a required child packet"
  logInfo "factArithmeticIncomplete=5MissingChildren"

syntax (name := factOperationsProbe) "#fact_operations_probe" : command
@[command_elab factOperationsProbe]
unsafe def elaborateProbe : CommandElab := fun _ => liftTermElabM control

end
end Hex.RealClosure.Algebraic.KernelReplay.FactOperations
