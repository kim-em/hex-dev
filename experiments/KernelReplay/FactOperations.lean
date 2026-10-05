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
import all HexSignDet.Descriptor
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

/-- Packing receives the supplied monic reduction and its exact equality
proof, retaining the reduced constant rather than the original linear input. -/
@[expose] def monicPacking (facts : List (SignFact context)) : Bool :=
  let reduce := Context.factReduce monicContext
    (Element.cachedOne PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedOne_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
  let equal := Context.factReduce_eq monicContext
    (Element.cachedOne PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedOne_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
  let result : Element monicContext := Element.pack reduce equal []
    (DensePoly.ofCoeffs #[0, PackingConformance.literal])
  decide (result.polynomial.size = 1 ∧
    (result.polynomial.coeff 0).polynomial = Sturm.Fixtures.x ∧ result.sign = 1)

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

/-- Two distinct native coefficient fields retain separate inventories. Reusing
an upper result does not demand another certificate. -/
@[expose] def multiple (lower : List (SignFact context))
    (upper : List (SignFact NestedSignsConformance.next)) : Bool :=
  Nested.selections lower && nonconstant upper && nonconstant upper

/-- A second root over Rat with the same context label 7. The supplied count
certificate selects the negative root of X² - 1 on `(-2, 0]`. -/
@[expose] def siblingRaw : SignDet.RawDescriptor Rat Nat :=
  {SignDet.Conformance.singletonRaw with lower := .finite (-2), upper := .finite 0}

@[expose] def siblingCount : TarskiCertificate Rat Rat Nat :=
  {Sturm.Fixtures.literal with
    upper := .finite 0
    upperSigns := #[-1, 0, 1]
    upperVariations := 1
    value := 1}

@[expose] def siblingNode : SignDet.Node Rat Nat :=
  {SignDet.Conformance.singletonNode with
    lower := .finite (-2)
    upper := .finite 0
    moments := #v[siblingCount]}

set_option maxRecDepth 32768 in
theorem sibling_checked : siblingRaw.check Sturm.orderSign 7 (.leaf siblingNode) = true := by
  simp only [SignDet.RawDescriptor.check, SignDet.Replay.check, SignDet.Node.check_eq,
    SignDet.checkMoment_eq, SignDet.queryPoly, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

@[expose] def siblingRoot : SignDet.Descriptor Rat Nat Sturm.orderSign 7 :=
  SignDet.Descriptor.ofTable siblingRaw (.leaf siblingNode)
    (SignDet.RawDescriptor.check_eq sibling_checked).1
    (SignDet.RawDescriptor.check_eq sibling_checked).2.1
    (SignDet.RawDescriptor.check_eq sibling_checked).2.2.1
    (SignDet.RawDescriptor.check_eq sibling_checked).2.2.2

@[expose] def siblingContext := Context.adjoin siblingRoot (fun _ => false)

theorem siblingReduction : (id : DensePoly Rat → DensePoly Rat) = siblingContext.reduce := by
  funext p
  symm
  apply Context.reduce_unclean
  simp only [siblingContext, Context.root_adjoin, Context.clean_adjoin,
    siblingRoot, SignDet.Descriptor.ofTable_raw, siblingRaw,
    SignDet.Conformance.singletonRaw]
  decide +kernel

@[expose] def siblingFirst : TarskiCertificate Rat Rat Nat :=
  {SignDet.Conformance.firstQuery with
    lower := .finite (-2)
    upper := .finite 0
    lowerSigns := #[1, 1]
    upperSigns := #[-1, 1]
    lowerVariations := 0
    upperVariations := 1
    value := -1}

@[expose] def siblingSquare : TarskiCertificate Rat Rat Nat :=
  {SignDet.Conformance.firstSquare with
    lower := .finite (-2)
    upper := .finite 0
    lowerSigns := #[1, -1, 1]
    upperSigns := #[-1, 0, 1]
    lowerVariations := 2
    upperVariations := 1
    value := 1}

@[expose] def siblingSigns : SignDet.Node Rat Nat :=
  {SignDet.Conformance.firstNode with
    lower := .finite (-2)
    upper := .finite 0
    system := {SignDet.Conformance.firstNode.system with
      counts := #v[1, 0, 0]
      values := #v[1, -1, 1]}
    moments := #v[siblingCount, siblingFirst, siblingSquare]}

set_option maxRecDepth 32768 in
theorem siblingSigns_checked :
    siblingRoot.checkSigns [2 * Sturm.Fixtures.x] #v[-1] (.leaf siblingSigns) = true := by
  simp only [siblingRoot, SignDet.Descriptor.ofTable_raw, SignDet.Descriptor.checkSigns,
    SignDet.RawDescriptor.checkSigns, SignDet.Replay.check, SignDet.Node.check_eq,
    SignDet.checkMoment_eq, SignDet.queryPoly, Sturm.check, TarskiCertificate.check_eq,
    SignedRemainderChain.check, ← Array.all_toList, Array.toList_range]
  decide +kernel

theorem sibling_sign : siblingContext.signPoly (2 * Sturm.Fixtures.x) = -1 := by
  have queryEq : siblingContext.queryPoly (2 * Sturm.Fixtures.x) = 2 * Sturm.Fixtures.x := by
    simp only [Context.queryPoly, Context.queryRemainder, siblingContext,
      Context.root_adjoin, siblingRoot, SignDet.Descriptor.ofTable_raw,
      siblingRaw, SignDet.Conformance.singletonRaw]
    decide +kernel
  let signs : SignDet.SelectedSigns siblingContext.root
      [siblingContext.queryPoly (2 * Sturm.Fixtures.x)] :=
    ⟨#v[-1], .leaf siblingSigns, by
      rw [queryEq]
      simpa only [siblingContext, Context.root_adjoin] using siblingSigns_checked⟩
  have h := siblingContext.signPoly_checked (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
    (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
    (fun _ => by simp) Generated.cast_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _)
    (2 * Sturm.Fixtures.x) signs
  simpa [SignDet.SelectedSigns.value, signs] using h

@[expose] def siblingFact : SignFact siblingContext :=
  ⟨2 * Sturm.Fixtures.x, -1, sibling_sign⟩

@[expose] def siblingLiteral : Element siblingContext :=
  Element.restore (2 * Sturm.Fixtures.x) (-1) sibling_sign (by decide +kernel)

@[expose] def siblings (_positive : List (SignFact context))
    (negative : List (SignFact siblingContext)) : Bool :=
  decide (((Element.cachedAdd id siblingReduction negative).add siblingLiteral 0).sign = -1)

@[expose] def nonBoolProgram (_positive : List (SignFact context))
    (_negative : List (SignFact siblingContext)) : Nat := 0

meta section
open Lean Meta Elab Command

/-- Read the supplied upper graph with the current lower inventory. No
certificate producer is called while checking this upper packet. -/
private def readUpper (needed : KernelReplay.Request) (lower : Expr)
    (simpContext : Simp.Context) : MetaM (Option Expr) := do
  let actualContext := mkConst ``NestedSignsConformance.next
  unless ← isDefEq needed.context actualContext do return none
  let expected := mkConst ``NestedSignsConformance.nextQuery
  KernelReplay.kernelCheck `__multiUpperKey
    (← mkEq needed.polynomial expected) (← mkEqRefl expected)
  let pair ← mkAppM ``Prod.mk #[expected, toExpr (1 : Int)]
  let inputs ← mkListLit (← inferType pair) [pair]
  let original ← mkAppM ``Nested.readFacts?
    #[lower, inputs, mkConst ``NestedSignsConformance.graph]
  let (simplified, _) ← Meta.simp original simpContext
  let equation ← simplified.getProof' original
  let _ ← KernelReplay.auditProof equation (← mkEq original simplified.expr)
  KernelReplay.kernelCheck `__multiUpperPacket (← mkEq original simplified.expr) equation
  let result ← withTransparency .all (whnf simplified.expr)
  if result.getAppFn.isConstOf ``Option.none then return none
  unless result.getAppFn.isConstOf ``Option.some do
    throwError "upper packet did not reduce to a checked result"
  let facts := result.getAppArgs.back!
  let first ← mkAppM ``List.head? #[facts]
  let first ← withTransparency .all (whnf first)
  unless first.getAppFn.isConstOf ``Option.some do
    throwError "upper packet returned no scalar fact"
  return some first.getAppArgs.back!


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
  unless collected.requests.size == 3 do throwError "unexpected monic division child count"
  let expectedKeys ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([2 * Sturm.Fixtures.x, -Sturm.Fixtures.x, Sturm.Fixtures.x] :
      List (DensePoly Rat)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let expectedKeys ← instantiateMVars expectedKeys
  let retained := collected.requests.toList.map fun needed =>
    mkApp (mkConst ``PackingConformance.reduction) needed.polynomial
  let actual ← mkListLit (← inferType retained.head!) retained
  KernelReplay.kernelCheck `__factMonicKeys (← mkEq actual expectedKeys)
    (← mkEqRefl expectedKeys)
  let replayed ← KernelReplay.collect 32 program initial simpContext (fun needed => do
    let some fact ← Generated.readPackets (← packets.get) needed | return none
    return some (← register fact))
  unless replayed.requests.size == collected.requests.size do
    throwError "monic division replay changed child requests"
  match replayed.outcome with
  | .checked true _ _ => logInfo "factMonicPackets=kernelAccepted"
  | _ => throwError "monic division packet replay failed"
  let supplied ← packets.get
  unless supplied.length == 3 do throwError "unexpected monic packet count"
  for omitted in supplied do
    let incomplete := supplied.filter (fun packet => packet.polynomial != omitted.polynomial)
    unless incomplete.length == 2 do throwError "monic omission removed the wrong packet count"
    let rejected ← KernelReplay.collect 32 program initial simpContext (fun needed => do
      let some fact ← Generated.readPackets incomplete needed | return none
      return some (← register fact))
    match rejected.outcome with
    | .missing application =>
      let request ← KernelReplay.request application
      KernelReplay.kernelCheck `__factMonicMissingContext
        (← mkEq request.context (mkConst ``CoefficientSignsConformance.context))
        (← mkEqRefl (mkConst ``CoefficientSignsConformance.context))
      let decoded ← mkAppM ``Hex.SignDet.Codec.readPoly
        #[mkConst ``Hex.SignDet.ValueCodec.rat, KernelReplay.jsonExpr omitted.polynomial]
      let decoded ← withTransparency .all (whnf decoded)
      unless decoded.getAppFn.isConstOf ``Except.ok do throwError "monic omitted key did not decode"
      let expected := decoded.getAppArgs.back!
      KernelReplay.kernelCheck `__factMonicMissingKey
        (← mkEq (mkApp (mkConst ``PackingConformance.reduction) request.polynomial) expected)
        (← mkEqRefl expected)
    | _ => throwError "monic division succeeded without a required packet"
  logInfo "factMonicMissing=3ExactLowerKeys"
  let packing ← KernelReplay.collect 32 (mkConst ``monicPacking) initial simpContext
    (fun needed => do
      let some fact ← Generated.readPackets supplied needed | return none
      return some (← register fact))
  unless packing.requests.size == 3 do throwError "monic packing changed division child requests"
  match packing.outcome with
  | .checked true _ _ => logInfo "factMonicPacking=kernelAcceptedReducedRemainder"
  | _ => throwError "monic packing rejected supplied division evidence"

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

  let multiContext ← Simp.mkContext (simpTheorems := #[← Nested.rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let inventories : Array KernelReplay.Inventory := #[⟨initial⟩, ⟨empty⟩]
  let multiProgram := mkConst ``multiple
  packets.set []
  let produced ← KernelReplay.collectMany 8 multiProgram inventories multiContext
    (fun needed current => do
      if ← isDefEq needed.context (mkConst ``CoefficientSignsConformance.context) then
        let some packet ← Generated.produce needed | return none
        packets.modify (packet :: ·)
        let some fact ← Generated.readFact packet | throwError "lower packet rejected"
        return some (← register fact)
      let some lower := current[0]? | throwError "missing lower inventory"
      let some fact ← readUpper needed lower.facts multiContext | return none
      return some (← register fact))
  match produced.outcome with
  | .checked true _ _ => logInfo m!"multiFields=kernelAccepted requests={produced.requests.size}"
  | .missing application => throwError "multi-field collection still needs {application}"
  | _ => throwError "multi-field collection rejected"
  unless produced.requests.size == 3 do throwError "unexpected multi-field request count"
  let replayed ← KernelReplay.collectMany 8 multiProgram inventories multiContext
    (fun needed current => do
      if ← isDefEq needed.context (mkConst ``CoefficientSignsConformance.context) then
        let some fact ← Generated.readPackets (← packets.get) needed | return none
        return some (← register fact)
      let some lower := current[0]? | throwError "missing lower inventory"
      let some fact ← readUpper needed lower.facts multiContext | return none
      return some (← register fact))
  match replayed.outcome with
  | .checked true _ _ => logInfo "multiFieldPackets=kernelAccepted"
  | _ => throwError "multi-field recorded replay failed"
  unless replayed.requests.size == 3 do throwError "multi-field sharing changed"
  let missingUpper ← KernelReplay.collectMany 8 multiProgram inventories multiContext
    (fun needed _ => do Generated.readPackets (← packets.get) needed)
  match missingUpper.outcome with
  | .missing application =>
    let needed ← KernelReplay.request application
    let actualContext := mkConst ``NestedSignsConformance.next
    KernelReplay.kernelCheck `__multiMissingContext
      (← mkEq needed.context actualContext) (← mkEqRefl actualContext)
    let key := mkConst ``NestedSignsConformance.nextQuery
    KernelReplay.kernelCheck `__multiMissingKey
      (← mkEq needed.polynomial key) (← mkEqRefl key)
    logInfo "multiFieldMissing=exactUpperRequest"
  | _ => throwError "multi-field replay succeeded without upper evidence"

  let wrongContext : Except Exception KernelReplay.Collections ← try
    let result ← KernelReplay.collectMany 1 multiProgram inventories multiContext
      (fun _ _ => do
        let first ← mkAppM ``List.head? #[mkConst ``upperFacts]
        let first ← withTransparency .all (whnf first)
        unless first.getAppFn.isConstOf ``Option.some do throwError "missing upper fixture"
        return some first.getAppArgs.back!)
    pure (.ok result)
  catch error => pure (.error error)
  match wrongContext with
  | .error error =>
    unless (← error.toMessageData.toString) ==
        "supplied fact belongs to a different coefficient context" do throw error
    logInfo "multiFieldWrongContext=rejected"
  | .ok _ => throwError "multi-field collector accepted a foreign fact"
  let unknownProgram ← Term.withoutErrToSorry (Term.elabTerm
    (← `((fun lower : List (SignFact context) => multiple lower []))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let unknownProgram ← instantiateMVars unknownProgram
  let unknown ← KernelReplay.collectMany 8 unknownProgram #[⟨initial⟩] multiContext
    (fun needed _ => do Generated.readPackets (← packets.get) needed)
  match unknown.outcome with
  | .missing application =>
    let needed ← KernelReplay.request application
    let expected := mkConst ``NestedSignsConformance.next
    KernelReplay.kernelCheck `__multiUnknownContext
      (← mkEq needed.context expected) (← mkEqRefl expected)
    logInfo "multiFieldUnknownContext=unproved"
  | _ => throwError "multi-field collector manufactured an absent inventory"


  let negative ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (SignFact siblingContext)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let negative ← instantiateMVars negative
  let positive := mkConst ``PackingConformance.facts
  let siblingsInitial : Array KernelReplay.Inventory := #[⟨positive⟩, ⟨negative⟩]
  let siblingsProgram := mkConst ``siblings
  let siblingCollected ← KernelReplay.collectMany 1 siblingsProgram siblingsInitial simpContext
    (fun needed _ => do
      let expected := mkConst ``siblingContext
      KernelReplay.kernelCheck `__siblingContext
        (← mkEq needed.context expected) (← mkEqRefl expected)
      let fact ← register (mkConst ``siblingFact)
      return some fact)
  unless siblingCollected.requests.size == 1 do
    throwError "same-carrier collection changed request count"
  let some retainedPositive := siblingCollected.inventories[0]?
    | throwError "missing positive-root inventory"
  let some retainedNegative := siblingCollected.inventories[1]?
    | throwError "missing negative-root inventory"
  KernelReplay.kernelCheck `__siblingPositiveInventory
    (← mkEq retainedPositive.facts positive) (← mkEqRefl positive)
  let expected ← mkAppM ``List.cons #[mkConst ``siblingFact, negative]
  KernelReplay.kernelCheck `__siblingNegativeInventory
    (← mkEq retainedNegative.facts expected) (← mkEqRefl expected)
  match siblingCollected.outcome with
  | .checked true _ _ => logInfo "multiSiblingFields=kernelAcceptedSameCarrier"
  | _ => throwError "same-carrier collection rejected the negative-root fact"
  let wrongSibling : Except Exception KernelReplay.Collections ← try
    let result ← KernelReplay.collectMany 1 siblingsProgram siblingsInitial simpContext
      (fun _ _ => do
        let first ← mkAppM ``List.head? #[positive]
        let first ← withTransparency .all (whnf first)
        unless first.getAppFn.isConstOf ``Option.some do throwError "missing positive fixture"
        return some first.getAppArgs.back!)
    pure (.ok result)
  catch error => pure (.error error)
  match wrongSibling with
  | .error error =>
    unless (← error.toMessageData.toString) ==
        "supplied fact belongs to a different coefficient context" do throw error
    logInfo "multiSiblingWrongRoot=rejected"
  | .ok _ => throwError "same-carrier collection accepted a different selected root"
  let nonBool := mkConst ``nonBoolProgram
  let malformed : Except Exception KernelReplay.Collections ← try
    let result ← KernelReplay.collectMany 1 nonBool siblingsInitial simpContext
      (fun _ _ => throwError "malformed program called the supplier")
    pure (.ok result)
  catch error => pure (.error error)
  match malformed with
  | .error error =>
    unless (← error.toMessageData.toString) ==
        "collection program must return Bool with these inventories" do throw error
    logInfo "multiNonBoolProgram=rejectedBeforeSupply"
  | .ok _ => throwError "collection accepted a non-Bool program"

syntax (name := factOperationsProbe) "#fact_operations_probe" : command
@[command_elab factOperationsProbe]
unsafe def elaborateProbe : CommandElab := fun _ => liftTermElabM control

end
end Hex.RealClosure.Algebraic.KernelReplay.FactOperations
