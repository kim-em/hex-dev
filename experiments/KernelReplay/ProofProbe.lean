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

open Lean Meta Elab Command

meta section

private def auditProof (proof type : Expr) : MetaM (Array Name) := do
  if proof.hasSorry || proof.hasMVar || type.hasSorry || type.hasMVar then
    throwError "incomplete proof"
  let mut axioms : Array Name := #[]
  for decl in (proof.getUsedConstants ++ type.getUsedConstants) do
    for axiomName in (← collectAxioms decl) do
      if !axioms.contains axiomName then axioms := axioms.push axiomName
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "unexpected axiom {axiomName} through {decl}"
  return axioms

private def kernelCheck (name : Name) (type proof : Expr) : MetaM Unit := do
  let options := (← getOptions).setBool `debug.skipKernelTC false
  ofExceptKernelException <| ((← getEnv).toKernelEnv.addDecl options
    (.thmDecl { name, levelParams := [], type, value := proof })).map (fun _ => ())

/-- Follow demanded projections and recursor scrutinees, never lambda bodies. -/
private partial def missingRedex (expression : Expr) : MetaM (Option Expr) :=
  withIncRecDepth do
    let expression ← withTransparency .all (whnf expression)
    if expression.getAppFn.isConstOf ``Element.missing then return some expression
    match expression with
    | .proj _ _ value => missingRedex value
    | .mdata _ value => missingRedex value
    | .app .. =>
      if let .const name _ := expression.getAppFn then
        let args := expression.getAppArgs
        if let .recInfo recursor ← getConstInfo name then
          if let some major := args[recursor.getMajorIdx]? then return ← missingRedex major
        if let some matcher ← getMatcherInfo? name then
          for index in matcher.getDiscrRange do
            if let some discr := args[index]? then
              let discr ← withTransparency .all (whnf discr)
              unless discr.isLit || (← isConstructorApp discr) do
                return ← missingRedex discr
        if #[``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pow,
            ``Nat.gcd, ``Nat.beq, ``Nat.ble].contains name then
          for arg in args do
            let arg ← withTransparency .all (whnf arg)
            unless arg.isLit || (← isConstructorApp arg) do
              return ← missingRedex arg
      return none
    | _ => return none

syntax "#proof_probe " term " expecting " str (" binding " term)? : command
elab_rules : command
| `(#proof_probe $term expecting $expected $[binding $literal]?) => do
  liftTermElabM do
    let expression ← Term.withoutErrToSorry (Term.elabTermEnsuringType term (mkConst ``Bool))
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasSorry || expression.hasMVar then throwError "incomplete input"
    let started ← IO.monoNanosNow
    let mut rules : SimpTheorems := {}
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
      match (← getEnv).toKernelEnv.addDecl options
          (.thmDecl {
            name := `__kernelReplayBindingDecision
            levelParams := []
            type := comparison
            value := refl }) with
      | .error (.declTypeMismatch _ _ _) => throwError "literal input binding failed"
      | .error exception => throwKernelException exception
      | .ok _ => pure ()
      let proof := mkAppN (mkConst ``of_decide_eq_true) #[type, decisionInstance, refl]
      let _ ← auditProof proof type
      kernelCheck `__kernelReplayBinding type proof
      rules ← rules.add (.stx `__inputBinding literal.raw) #[] proof
      logInfo "inputBinding=proved"
    for decl in #[``complete, ``missing, ``falseClaim, ``completeGraph, ``missingGraph,
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
    let context ← Simp.mkContext (simpTheorems := #[rules])
      (congrTheorems := ← getSimpCongrTheorems)
    let (simplified, stats) ← Meta.simp expression context
    if literal.isSome then
      let used := stats.usedTheorems.toArray.map (·.key)
      unless used.contains `__inputBinding &&
          (used.contains ``graph_read_full || used.contains ``graph_read_missing) do
        throwError "binding or certified decoder rewrite was not used"
      logInfo "inputBinding=used decoderEquation=used"
    let equation ← simplified.getProof' expression
    let equationType ← mkEq expression simplified.expr
    let _ ← auditProof equation equationType
    kernelCheck `__kernelReplaySimplification equationType equation
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let env := (← getEnv).toKernelEnv
    let mut outcome := "unproved"
    for candidate in [true, false] do
      let result := mkConst (if candidate then ``Bool.true else ``Bool.false)
      let proposition ← mkEq simplified.expr result
      let decisionInstance ← synthInstance (mkApp (mkConst ``Decidable) proposition)
      let decision := mkAppN (mkConst ``decide) #[proposition, decisionInstance]
      let comparisonType ← mkEq decision (mkConst ``Bool.true)
      let reflexivity ← mkEqRefl (mkConst ``Bool.true)
      let checked := env.addDecl options
        (.thmDecl {
          name := `__kernelReplayReduction
          levelParams := []
          type := comparisonType
          value := reflexivity })
      match checked with
      | .error (.declTypeMismatch _ _ _) => logInfo "kernelResult=typeMismatch"
      | .error exception => throwKernelException exception
      | .ok _ =>
        let resultProof := mkAppN (mkConst ``of_decide_eq_true)
          #[proposition, decisionInstance, reflexivity]
        let proof := mkAppN (mkConst ``Eq.trans [.succ .zero])
          #[mkConst ``Bool, expression, simplified.expr, result, equation, resultProof]
        let type ← mkEq expression result
        let axioms ← auditProof proof type
        kernelCheck `__kernelReplayProofProbe type proof
        logInfo m!"kernelAccepted=true axioms={axioms}"
        outcome := if candidate then "true" else "false"
        break
    if outcome == "unproved" then
      let some redex ← missingRedex simplified.expr
        | throwError "unproved result without a demanded missing-fact boundary: {simplified.expr}"
      logInfo m!"missingRedex={redex}"
    logInfo m!"result={outcome} nanos={(← IO.monoNanosNow) - started}"
    unless outcome == expected.getString do throwError "unexpected result {outcome}"

end

/-- An unrelated opaque boundary must never be classified as missing evidence. -/
opaque otherStuck : Bool := true

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
