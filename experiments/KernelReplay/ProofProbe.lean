/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Elab.Command
public import Lean.Meta.Reduce
public import Lean.Meta.Tactic.Simp
public import Lean.Util.CollectAxioms
public meta import KernelReplay.Assemble
public import HexRealClosure.SignCodec
public import HexSignDet.Codec.FiniteGraph
import all HexSignDet.Codec
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Evidence
import all HexRealClosure.AlgebraicCodec
public import HexRealClosureMathlib.PackingConformance
public import HexRealClosureMathlib.NestedSignsConformance
import all HexRealClosure.Algebraic
import all HexPoly.Euclid.DivGcd

public section

namespace Hex.RealClosure.Algebraic.KernelReplayProofProbe
open Hex.SignDet CoefficientSignsConformance PackingConformance
open scoped Hex

@[expose] def complete : Bool :=
  decide (((Element.cachedAdd reduction reduction_eq facts).add small 0).sign = 1)

@[expose] def missing : Bool :=
  decide (((Element.cachedAdd reduction reduction_eq ([] : List (SignFact context))).add small 0).sign = 1)

@[expose] def falseClaim : Bool :=
  decide (((Element.cachedAdd reduction reduction_eq facts).add small 0).sign = -1)

@[expose] def completeGraph : Bool :=
  (Dag.validateCached? reduction reduction_eq NestedSignsConformance.facts 8
    NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
    NestedSignsConformance.linearRaw.upper NestedSignsConformance.graph).isSome

@[expose] def missingGraph : Bool :=
  (Dag.validateCached? reduction reduction_eq facts 8
    NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
    NestedSignsConformance.linearRaw.upper NestedSignsConformance.graph).isSome

@[expose] def collectionGraph (facts : List (SignFact context)) : Bool :=
  (Dag.validateCached? reduction reduction_eq facts 8
    NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
    NestedSignsConformance.linearRaw.upper NestedSignsConformance.graph).isSome

@[expose] def falseGraph : Bool :=
  let bad := {NestedSignsConformance.linearNode with system :=
    {NestedSignsConformance.linearNode.system with
      values := NestedSignsConformance.linearNode.system.values.map (· + 1)}}
  let entries := NestedSignsConformance.graph.entries.push ⟨bad, none⟩
  let graph := {NestedSignsConformance.graph with entries := entries}
  (Dag.validateCached? reduction reduction_eq NestedSignsConformance.facts 8
    NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
    NestedSignsConformance.linearRaw.upper graph).isSome

@[expose] def completeMemo : Bool :=
  decide ((Dag.validateCached? reduction reduction_eq NestedSignsConformance.facts 8
    NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
    NestedSignsConformance.linearRaw.upper NestedSignsConformance.graph).map
      (fun memo => memo.map (fun checked => checked.value.node)) =
    some #[NestedSignsConformance.linearNode, NestedSignsConformance.queryNode])

@[expose] def falseEndpointGraph (facts : List (SignFact context)) : Bool :=
  let upperSigns := NestedSignsConformance.linearCount.upperSigns.set! 0 (-1)
  let badCount := {NestedSignsConformance.linearCount with upperSigns := upperSigns}
  let badNode := {NestedSignsConformance.linearNode with moments := NestedSignsConformance.linearNode.moments.map (fun _ => badCount)}
  let entries := NestedSignsConformance.graph.entries.push ⟨badNode, none⟩
  let graph := {NestedSignsConformance.graph with entries := entries}
  (Dag.validateCached? reduction reduction_eq facts 8
    NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
    NestedSignsConformance.linearRaw.upper graph).isSome

@[expose] def literalFacts : List (SignFact context) :=
  PackingConformance.literalFacts ++
    [⟨DensePoly.C (0 : Rat), 0, context.signPoly_const _ (by decide +kernel)⟩,
     ⟨DensePoly.C (1 : Rat), 1, context.signPoly_const _ (by decide +kernel)⟩,
     ⟨DensePoly.C (-1 : Rat), -1, context.signPoly_const _ (by decide +kernel)⟩]

@[expose] def fullJsonFacts := literalFacts ++ NestedSignsConformance.facts
@[expose] def missingJsonFacts := literalFacts ++ PackingConformance.facts

@[expose] def graphJson : Codec.Json :=
  Codec.graph (Element.signCodec ValueCodec.rat fullJsonFacts) ValueCodec.nat
    NestedSignsConformance.graph

@[expose] def byteEqual (j : Codec.Json) : Bool := decide (j = graphJson)

@[expose] def readJson (facts : List (SignFact context)) (j : Codec.Json) : Bool :=
  (Codec.readGraph (Element.signCodec ValueCodec.rat facts) ValueCodec.nat 8
    NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
    NestedSignsConformance.linearRaw.upper j).isOk

/-- Decode the actual existing graph format using finite literal facts, then
apply the existing supplied-fact arithmetic checker to every entry. -/
@[expose] def checkJson (facts : List (SignFact context)) (j : Codec.Json) : Bool :=
  ((Codec.readGraph (Element.signCodec ValueCodec.rat facts) ValueCodec.nat 8
    NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
    NestedSignsConformance.linearRaw.upper j).toOption.bind fun graph =>
    Dag.validateCached? reduction reduction_eq facts 8
      NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
      NestedSignsConformance.linearRaw.upper graph).isSome

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
private theorem graph_read (facts : List (SignFact context))
    (keys : (Element.signKeys (Codec.Coefficients.graph NestedSignsConformance.graph)).all
      (fun p => facts.any (fun f => decide (f.polynomial = p))) = true) :
    Codec.readGraph (Element.signCodec ValueCodec.rat facts) ValueCodec.nat 8
      NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
      NestedSignsConformance.linearRaw.upper graphJson = .ok NestedSignsConformance.graph := by
  apply Codec.read_graph_covered (Element.signCodec ValueCodec.rat facts) ValueCodec.nat 8
    NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
    NestedSignsConformance.linearRaw.upper NestedSignsConformance.graph
  · apply Element.signCodec_covers
    · intro x _; exact ValueCodec.rat_lawful x
    · intro p hp
      obtain ⟨f, hf, he⟩ := List.any_eq_true.mp ((List.all_eq_true.mp keys) p hp)
      exact ⟨f, hf, of_decide_eq_true he⟩
  · intro x _; exact ValueCodec.nat_lawful x
  · decide +kernel
  · intro e he
    simp only [NestedSignsConformance.graph, Array.mem_def,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    all_goals
      constructor
      all_goals simp [NestedSignsConformance.linearNode, NestedSignsConformance.queryNode,
        Vector.toList, NestedSignsConformance.unitPoly, Conformance.singletonNode,
        Conformance.literalNode, Conformance.literalSystem, Conformance.selectedNode, System.positive]
      all_goals decide +kernel
  · intro e he
    simp only [NestedSignsConformance.graph, Array.mem_def,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    all_goals decide +kernel
  · intro i hi pair hp
    have bound : i < 2 := hi
    interval_cases i <;> simp [NestedSignsConformance.graph] at hp

set_option maxRecDepth 32768 in
theorem graph_read_full :
    Codec.readGraph (Element.signCodec ValueCodec.rat fullJsonFacts) ValueCodec.nat 8
      NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
      NestedSignsConformance.linearRaw.upper graphJson = .ok NestedSignsConformance.graph :=
  graph_read fullJsonFacts (by decide +kernel)

set_option maxRecDepth 32768 in
theorem graph_read_missing :
    Codec.readGraph (Element.signCodec ValueCodec.rat missingJsonFacts) ValueCodec.nat 8
      NestedSignsConformance.linearHead NestedSignsConformance.linearRaw.lower
      NestedSignsConformance.linearRaw.upper graphJson = .ok NestedSignsConformance.graph :=
  graph_read missingJsonFacts (by decide +kernel)

set_option maxRecDepth 32768 in
/-- This missing scalar fact reaches the opaque boundary, with a kernel proof. -/
theorem scalar_missing :
    ((Element.cachedAdd reduction reduction_eq ([] : List (SignFact context))).add small 0) =
      (Element.missing (small.polynomial + (0 : Element context).polynomial)).val := by
  change Element.pack reduction reduction_eq []
    (small.polynomial + (0 : Element context).polynomial) = _
  apply Element.pack_missing
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- The graph's finite upper endpoint needs this nonconstant coefficient fact. -/
theorem endpoint_missing :
    letI := Element.cachedAdd reduction reduction_eq facts
    letI := Element.cachedMul reduction reduction_eq facts
    NestedSignsConformance.rational (-1) + literal * NestedSignsConformance.rational 1 =
      (Element.missing NestedSignsConformance.endpointQuery).val := by
  let input := (NestedSignsConformance.rational (-1)).polynomial +
    ((Element.cachedMul reduction reduction_eq facts).mul literal (NestedSignsConformance.rational 1)).polynomial
  change Element.pack reduction reduction_eq facts input = _
  have hp : input = NestedSignsConformance.endpointQuery := by decide +kernel
  rw [← hp]
  apply Element.pack_missing
  · decide +kernel
  · decide +kernel

/--
info: 'Hex.RealClosure.Algebraic.KernelReplayProofProbe.scalar_missing' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms scalar_missing
/--
info: 'Hex.RealClosure.Algebraic.KernelReplayProofProbe.endpoint_missing' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms endpoint_missing

open Lean Meta Elab Command KernelReplay

meta section

/-- Regression terms must be closed before inspecting their reduction paths. -/
private def closedTerm (stx : Syntax) (typeName : Name) : TermElabM Expr := do
  let expression ← Term.withoutErrToSorry
    (Term.elabTermEnsuringType stx (mkConst typeName))
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasSorry || expression.hasMVar then throwError "incomplete regression input"
  return expression

private def probeRules : MetaM SimpTheorems := do
  let mut rules : SimpTheorems := {}
  for decl in #[``complete, ``missing, ``falseClaim, ``completeGraph, ``missingGraph, ``collectionGraph,
      ``falseGraph, ``falseEndpointGraph, ``completeMemo, ``byteEqual, ``readJson, ``checkJson,
      ``Dag.validateCached?, ``Hex.SignDet.Dag.changeOps, ``Hex.SignDet.Dag.validate?,
      ``Replay.check, ``queryPoly, ``Sturm.check, ``SignedRemainderChain.check] do
    rules ← rules.addDeclToUnfold decl
  for decl in #[``graph_read_full, ``graph_read_missing, ``Hex.SignDet.Dag.step_eq,
      ``Node.check_eq, ``checkMoment_eq, ``TarskiCertificate.check_eq,
      ``Array.toList_range] do
    rules ← rules.addConst decl
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  rules ← rules.addConst ``eq_self
  rules ← rules.addConst ``iff_self
  return rules

syntax "#proof_probe " term " expecting " str (" binding " term)? : command
elab_rules : command
| `(#proof_probe $term expecting $expected $[binding $literal]?) => do
  liftTermElabM do
    let expression ← Term.withoutErrToSorry (Term.elabTermEnsuringType term (mkConst ``Bool))
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasSorry || expression.hasMVar then throwError "incomplete input"
    let started ← IO.monoNanosNow
    let mut rules ← probeRules
    if let some literal := literal then
      let input ← Term.withoutErrToSorry (Term.elabTermEnsuringType literal (mkConst ``Codec.Json))
      Term.synthesizeSyntheticMVarsNoPostponing
      let input ← instantiateMVars input
      if input.hasSorry || input.hasMVar then throwError "incomplete binding input"
      let type ← mkEq input (mkConst ``graphJson)
      let decisionInstance ← synthInstance (mkApp (mkConst ``Decidable) type)
      let decision := mkAppN (mkConst ``decide) #[type, decisionInstance]
      let comparison ← mkEq decision (mkConst ``Bool.true)
      let refl ← mkEqRefl (mkConst ``Bool.true)
      let options := (← getOptions).setBool `debug.skipKernelTC false
      unless ← acceptKernel ((← getEnv).toKernelEnv.addDecl options
          (.thmDecl {
            name := `__kernelReplayBindingDecision
            levelParams := []
            type := comparison
            value := refl })) do
        throwError "literal input binding failed"
      let proof := mkAppN (mkConst ``of_decide_eq_true) #[type, decisionInstance, refl]
      let _ ← auditProof proof type
      kernelCheck `__kernelReplayBinding type proof
      rules ← rules.add (.stx `__inputBinding literal.raw) #[] proof
      logInfo "inputBinding=proved"
    let context ← Simp.mkContext (simpTheorems := #[rules])
      (congrTheorems := ← getSimpCongrTheorems)
    let (assembled, stats) ← KernelReplay.assemble expression context
    if literal.isSome then
      let used := stats.usedTheorems.toArray.map (·.key)
      unless used.contains `__inputBinding &&
          (used.contains ``graph_read_full || used.contains ``graph_read_missing) do
        throwError "binding or certified decoder rewrite was not used"
      logInfo "inputBinding=used decoderEquation=used"
    let outcome ← match assembled with
      | .checked value _ axioms => do
        logInfo m!"kernelAccepted=true axioms={axioms}"
        pure (if value then "true" else "false")
      | .missing redex => do
        logInfo m!"missingRedex={redex}"
        pure "unproved"
    logInfo m!"result={outcome} nanos={(← IO.monoNanosNow) - started}"
    unless outcome == expected.getString do throwError "unexpected result {outcome}"

/-- The inventory contains facts already proved before execution. Selection
collects those demanded by the actual two-entry checker, including Horner
intermediates absent from the stored-coefficient list. -/
private def supplyFrom (inventory : Expr) (needed : KernelReplay.Request) : MetaM (Option Expr) := do
  unless ← isDefEq needed.context (mkConst ``CoefficientSignsConformance.context) do
    return none
  let kept := mkApp (mkConst ``reduction) needed.polynomial
  let selected ← mkAppM ``SignFact.find #[inventory, kept]
  let selected ← withTransparency .all (whnf selected)
  if selected.getAppFn.isConstOf ``Option.none then return none
  unless selected.getAppFn.isConstOf ``Option.some do
    throwError "coefficient inventory lookup did not reduce"
  let selected := selected.getAppArgs.back!
  return some (← mkAppM ``SignFact.mk
    #[kept, ← mkAppM ``Subtype.val #[selected], ← mkAppM ``Subtype.property #[selected]])

private def rejectError (expectedPrefix : String) (action : MetaM Unit) : MetaM Unit := do
  let rejected ← try
    action
    pure false
  catch exception =>
    let message ← exception.toMessageData.toString
    if message.startsWith expectedPrefix then pure true else throw exception
  unless rejected do throwError "expected rejection with prefix {expectedPrefix}"

syntax "#collect_probe" : command
elab_rules : command
| `(#collect_probe) => liftTermElabM do
    let initial ← Term.withoutErrToSorry
      (Term.elabTerm (← `(([] : List (SignFact context)))) none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let initial ← instantiateMVars initial
    let context ← Simp.mkContext (simpTheorems := #[← probeRules])
      (congrTheorems := ← getSimpCongrTheorems)
    let program := mkConst ``collectionGraph
    let collected ← KernelReplay.collect 2 program initial context
      (supplyFrom (mkConst ``NestedSignsConformance.facts))
    unless collected.requests.size == 2 do
      throwError "unexpected number of demanded facts: {collected.requests.size}"
    let firstKey ← Term.withoutErrToSorry
      (Term.elabTerm (← `((2 * Sturm.Fixtures.x : DensePoly Rat))) none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let firstKey ← instantiateMVars firstKey
    for (needed, expected) in collected.requests.zip #[firstKey,
        mkConst ``NestedSignsConformance.endpointQuery] do
      let actualContext := mkConst ``CoefficientSignsConformance.context
      kernelCheck `__kernelReplayRequestContext (← mkEq needed.context actualContext)
        (← mkEqRefl actualContext)
      let key := mkApp (mkConst ``reduction) needed.polynomial
      kernelCheck `__kernelReplayRequestKey (← mkEq key expected) (← mkEqRefl expected)
    match collected.outcome with
    | .checked true proof axioms =>
      let type ← mkEq (mkApp program collected.facts) (mkConst ``Bool.true)
      kernelCheck `__kernelReplayCollectedGraph type proof
      logInfo m!"collected=2 kernelAccepted=true axioms={axioms}"
    | _ => throwError "complete inventory did not check the actual graph"
    let missing ← KernelReplay.collect 2 program initial context
      (supplyFrom (mkConst ``PackingConformance.facts))
    unless missing.requests.size == 2 do throwError "incomplete inventory request count changed"
    match missing.outcome with
    | .missing application =>
      let needed ← KernelReplay.request application
      let actualContext := mkConst ``CoefficientSignsConformance.context
      kernelCheck `__kernelReplayMissingContext (← mkEq needed.context actualContext)
        (← mkEqRefl actualContext)
      let key := mkApp (mkConst ``reduction) needed.polynomial
      let expected := mkConst ``NestedSignsConformance.endpointQuery
      kernelCheck `__kernelReplayMissingKey (← mkEq key expected) (← mkEqRefl expected)
      logInfo "incompleteInventory=missingEndpoint"
    | _ => throwError "incomplete inventory unexpectedly checked"
    let bounded ← KernelReplay.collect 0 program initial context
      (fun _ => throwError "supplier called after fuel exhaustion")
    unless bounded.requests.size == 1 do throwError "zero fuel request count changed"
    match bounded.outcome with
    | .missing _ => logInfo "zeroFuel=normalRejection"
    | _ => throwError "empty inventory unexpectedly checked"
    let literal ← mkAppM ``List.head? #[mkConst ``PackingConformance.literalFacts]
    let literal ← withTransparency .all (whnf literal)
    unless literal.getAppFn.isConstOf ``Option.some do
      throwError "missing literal fixture fact"
    let calls ← IO.mkRef (0 : Nat)
    let irrelevant ← KernelReplay.collect 2 program initial context (fun _ => do
      calls.modify (· + 1)
      pure (some literal.getAppArgs.back!))
    unless (← calls.get) == 2 do throwError "irrelevant supplier call count changed"
    unless irrelevant.requests.size == 3 do throwError "irrelevant supplier request count changed"
    match irrelevant.outcome with
    | .missing _ => logInfo "irrelevantSupplier=boundedRejection"
    | _ => throwError "irrelevant facts unexpectedly checked"
    let limited ← KernelReplay.collect 1 program initial context
      (supplyFrom (mkConst ``NestedSignsConformance.facts))
    unless limited.requests.size == 2 do throwError "one fuel request count changed"
    match limited.outcome with
    | .missing application =>
      let needed ← KernelReplay.request application
      let expected := mkConst ``NestedSignsConformance.endpointQuery
      kernelCheck `__kernelReplayFuelKey
        (← mkEq (mkApp (mkConst ``reduction) needed.polynomial) expected) (← mkEqRefl expected)
      logInfo "oneFuel=missingEndpoint"
    | _ => throwError "one fuel incorrectly completed two demands"
    let falseResult ← KernelReplay.collect 2 (mkConst ``falseEndpointGraph) initial context
      (supplyFrom (mkConst ``NestedSignsConformance.facts))
    match falseResult.outcome with
    | .checked false _ _ => logInfo "falseGraph=checkedFalse"
    | _ => throwError "false graph did not yield a checked false result"
    let inventory ← mkAppM ``List.reverse #[← mkAppM ``List.append
      #[mkConst ``NestedSignsConformance.facts, mkConst ``PackingConformance.literalFacts]]
    let reordered ← KernelReplay.collect 2 program initial context (supplyFrom inventory)
    match reordered.outcome with
    | .checked true _ _ =>
      let length ← mkAppM ``List.length #[reordered.facts]
      kernelCheck `__kernelReplayCollectedLength (← mkEq length (toExpr (2 : Nat)))
        (← mkEqRefl (toExpr (2 : Nat)))
      logInfo "extraReorderedInventory=twoFacts"
    | _ => throwError "extra reordered inventory did not complete"
    let honest ← mkAppM ``List.head? #[mkConst ``PackingConformance.facts]
    let honest ← withTransparency .all (whnf honest)
    let honest ← withTransparency .all (whnf honest.getAppArgs.back!)
    unless honest.getAppFn.isConstOf ``SignFact.mk do throwError "unexpected fact fixture"
    let args := honest.getAppArgs
    let corrupt := mkAppN honest.getAppFn (args.set! (args.size - 2) (toExpr (-1 : Int)))
    rejectError "(kernel) application type mismatch" do
      let _ ← KernelReplay.collect 1 program initial context (fun _ => pure (some corrupt))
    logInfo "malformedFact=kernelRejected"
    let hole ← mkFreshExprMVar (← inferType honest)
    rejectError "incomplete supplied fact" do
      let _ ← KernelReplay.collect 1 program initial context (fun _ => pure (some hole))
    logInfo "incompleteFact=rejected"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#collect_probe

/-- An unrelated opaque boundary must never be classified as missing evidence. -/
opaque otherStuck : Bool := true
opaque otherNat : Nat := 0

/- A primitive that recurses on its unrelated second operand must not blame
missing evidence in its first. This exercises the diagnostic's actual path. -/
#guard_msgs in
run_elab do
  let second ← closedTerm (← `(if missing then (1 : Nat) else 0)) ``Nat
  let expression := mkApp2 (mkConst ``Nat.add) second (mkConst ``otherNat)
  unless (← missingRedex expression).isNone do
    throwError "ambiguous primitive operands were reported as missing evidence"
  let positive := mkApp2 (mkConst ``Nat.add) (mkConst ``otherNat) second
  unless (← missingRedex positive).isSome do
    throwError "missing recursive operand was not reported"

/- A constructor in the first discriminant can still contain the obstruction.
Do not skip that field and attribute failure to a later missing sign. -/
#guard_msgs in
run_elab do
  let expression ← closedTerm (← `(match some otherStuck, missing with
    | some true, true => true
    | _, _ => false)) ``Bool
  unless (← missingRedex expression).isNone do
    throwError "blocked constructor field was reported as missing evidence"
  let positive ← closedTerm (← `(match some true, missing with
    | some true, true => true
    | _, _ => false)) ``Bool
  unless (← missingRedex positive).isSome do
    throwError "missing matcher operand was not reported"

/-- error: (kernel) deterministic timeout -/
#guard_msgs (error, drop info) in
run_elab do
  let _ ← acceptKernel (α := Unit) (.error .deterministicTimeout)

/-- error: unproved result without a demanded missing-fact boundary: otherStuck -/
#guard_msgs (error, drop info) in
#proof_probe otherStuck expecting "unproved"

/-- error: incomplete proof -/
#guard_msgs (error, drop info) in
run_elab do
  let value ← mkFreshExprMVar (mkConst ``Bool)
  let _ ← auditProof value (mkConst ``Bool)

/-- error: (kernel) deterministic timeout -/
#guard_msgs (error, drop info) in
run_elab do
  let type ← mkEq (mkConst ``completeGraph) (mkConst ``Bool.true)
  let proof ← mkEqRefl (mkConst ``Bool.true)
  withOptions (fun options => maxHeartbeats.set options 1) do
    kernelCheck `__kernelReplayTimeout type proof

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe complete expecting "true"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe missing expecting "unproved"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe falseClaim expecting "false"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe completeGraph expecting "true"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe missingGraph expecting "unproved"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe falseGraph expecting "false"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe completeMemo expecting "true"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe falseEndpointGraph NestedSignsConformance.facts expecting "false"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe falseEndpointGraph facts expecting "unproved"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe checkJson fullJsonFacts graphJson expecting "true"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#proof_probe checkJson missingJsonFacts graphJson expecting "unproved"

end Hex.RealClosure.Algebraic.KernelReplayProofProbe
