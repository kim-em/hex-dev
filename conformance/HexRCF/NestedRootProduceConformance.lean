/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.RootReplay
import HexRCF.NestedRootLiterals
import HexRCF.SelectedRoot.RowCollect
import HexRCF.SelectedRoot.RowTools
import HexRCF.SelectedRoot.KernelCheck
import HexRCF.RealCoefficients.ScalarPacket
import HexRCF.ProofEvidence
open Hex Hex.RealClosure Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.SelectedRootTests.Data
open Lean Meta Elab Command
open Hex.RCF.RealCoefficients
namespace Hex.RCF.RealCoefficients.NestedRootProduceConformance

def polynomial (facts : List (Algebraic.SignFact native)) : parent.Poly :=
  DensePoly.ofList [@Neg.neg parent.Value (Algebraic.Element.cachedNeg reduction reduction_eq facts) alpha,
    @Zero.zero parent.Value (Tower.instZeroValue parent),
    @One.one parent.Value (Algebraic.Element.cachedOne reduction reduction_eq facts)]
def readAt (facts : List (Algebraic.SignFact native)) (head : parent.Poly)
    (lower upper : Endpoint parent.Value) (graph : Codec.Json) :=
  RootReplay.readWith (Algebraic.Element.signCodec base.codec facts) [] head lower upper
    (Algebraic.Element.cachedOne reduction reduction_eq facts)
    (Algebraic.Element.cachedAdd reduction reduction_eq facts)
    (Algebraic.Element.cachedSub reduction reduction_eq facts)
    (Algebraic.Element.cachedMul reduction reduction_eq facts)
    (Algebraic.Element.cachedNatCast reduction reduction_eq facts)
    (Algebraic.Element.cachedOne_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedAdd_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedSub_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedMul_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedNatCast_eq reduction reduction_eq facts)
    graph

def resultAt (facts : List (Algebraic.SignFact native)) :=
  readAt facts (polynomial facts)
    (.finite (@One.one parent.Value (Algebraic.Element.cachedOne reduction reduction_eq facts)))
    (.finite (@NatCast.natCast parent.Value
      (Algebraic.Element.cachedNatCast reduction reduction_eq facts) 2)) NestedRootLiterals.positive

def missingAt (facts : List (Algebraic.SignFact native)) :=
  readAt [] (polynomial facts)
    (.finite (@One.one parent.Value (Algebraic.Element.cachedOne reduction reduction_eq facts)))
    (.finite (@NatCast.natCast parent.Value
      (Algebraic.Element.cachedNatCast reduction reduction_eq facts) 2)) NestedRootLiterals.positive

def wrongHeadAt (facts : List (Algebraic.SignFact native)) :=
  readAt facts (DensePoly.ofList [alpha, @Zero.zero parent.Value (Tower.instZeroValue parent),
      @One.one parent.Value (Algebraic.Element.cachedOne reduction reduction_eq facts)])
    (.finite (@One.one parent.Value (Algebraic.Element.cachedOne reduction reduction_eq facts)))
    (.finite (@NatCast.natCast parent.Value
      (Algebraic.Element.cachedNatCast reduction reduction_eq facts) 2)) NestedRootLiterals.positive

def wrongEndpointAt (facts : List (Algebraic.SignFact native)) :=
  readAt facts (polynomial facts)
    (.finite (@One.one parent.Value (Algebraic.Element.cachedOne reduction reduction_eq facts)))
    (.finite (@NatCast.natCast parent.Value
      (Algebraic.Element.cachedNatCast reduction reduction_eq facts) 3)) NestedRootLiterals.positive

def lengthAt (facts : List (Algebraic.SignFact native)) : Option Nat :=
  (resultAt facts).toOption.map (fun result => result.roots.length)

def nestedHints (literal : Codec.Json) : List Codec.Json :=
  match Codec.readGraph parent.codec Tower.Signature.codec parent.signature
      (DensePoly.ofList [-alpha,0,1]) (.finite 1) (.finite 2) literal with
  | .error _ => []
  | .ok graph => (Codec.Coefficients.graph graph).map parent.codec.encode

meta section
private def producers : Array Name := #[``ScalarPacket.build, ``ScalarPacket.buildLiteral, ``Descriptor.buildRoots]
private unsafe def evalHintsUnsafe (literal : Codec.Json) : MetaM (List Codec.Json) :=
  pure (nestedHints literal)
@[implemented_by evalHintsUnsafe]
private opaque evalHints (literal : Codec.Json) : MetaM (List Codec.Json)

private unsafe def evalJsonUnsafe (expression : Expr) : MetaM (Option Codec.Json) := do
  evalExpr (Option Codec.Json) (← inferType expression) expression
@[implemented_by evalJsonUnsafe]
private opaque evalJson (expression : Expr) : MetaM (Option Codec.Json)

mutual
private partial def jsonExpr : Codec.Json → Expr
  | .null => mkConst ``Codec.Json.Value.null
  | .bool value => mkApp (mkConst ``Codec.Json.Value.bool) (toExpr value)
  | .number value => mkApp (mkConst ``Codec.Json.Value.number) (toExpr value)
  | .string value => mkApp (mkConst ``Codec.Json.Value.string) (toExpr value)
  | .array values => mkApp (mkConst ``Codec.Json.Value.array) (arrayExpr values)
  | .object fields => mkApp (mkConst ``Codec.Json.Value.object) (fieldsExpr fields)
private partial def arrayExpr : Codec.Json.Values → Expr
  | .nil => mkConst ``Codec.Json.Values.nil
  | .cons value rest => mkAppN (mkConst ``Codec.Json.Values.cons) #[jsonExpr value, arrayExpr rest]
private partial def fieldsExpr : Codec.Json.Fields → Expr
  | .nil => mkConst ``Codec.Json.Fields.nil
  | .cons key value rest => mkAppN (mkConst ``Codec.Json.Fields.cons)
      #[toExpr key, jsonExpr value, fieldsExpr rest]
end

private def restoreProposal (scope : Name) (packet : Codec.Json) : MetaM Expr := do
  let context := mkConst ``native
  let value ← mkAppM ``Tower.Context.codec #[mkConst ``base]
  let .ok fields := packet.getArr? | throwError "scalar producer returned malformed fields"
  unless fields.size == 3 do throwError "scalar producer returned wrong field count"
  let .ok claimed := Codec.Json.decode (α := Int) fields[1]! | throwError "invalid scalar sign"
  let args := #[mkConst ``rational, value, context, jsonExpr fields[0]!,
    toExpr claimed, jsonExpr fields[2]!]
  let read ← mkAppM ``ScalarPacket.read args
  let predicate ← mkAppM ``Option.isSome #[read]
  let proposition ← mkEq predicate (mkConst ``Bool.true)
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let reflexivity ← mkEqRefl (mkConst ``Bool.true)
  let proof := mkAppN (mkConst ``of_decide_eq_true)
    #[proposition, dictionary, reflexivity]
  let name ← mkFreshUserName (scope ++ `sectionScalarAccepted)
  let _ ← Algebraic.KernelReplay.auditProof proof proposition
  KernelCheck.addChecked name proposition proof producers
  return ← mkAppM ``ScalarPacket.restore (args.push (mkConst name))

private def supply (scope : Name) (seen : IO.Ref (ExprMap Unit))
    (needed : Algebraic.KernelReplay.Request)
    (_inventory : Array Algebraic.KernelReplay.Inventory) : MetaM (Option Expr) := do
  unless needed.kind == .coefficient do return none
  unless ← isDefEq needed.context (mkConst ``native) do return none
  let context := mkConst ``native
  let value ← mkAppM ``Tower.Context.codec #[mkConst ``base]
  let key := mkApp (mkConst ``reduction) needed.polynomial
  let encoded ← mkAppM ``Codec.poly #[value, key]
  let encoded ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (reduce encoded)
  if (← seen.get).contains encoded then
    throwError "repeated reduced scalar request after checked supply"
  seen.modify (fun keys => keys.insert encoded ())
  let producer ← mkAppM ``ScalarPacket.buildLiteral #[context, value, encoded]
  let some packet ← evalJson producer | throwError "scalar production failed"
  let .ok fields := packet.getArr? | throwError "scalar producer returned malformed fields"
  unless fields.size == 3 do throwError "scalar producer returned wrong field count"
  unless ← isDefEq (jsonExpr fields[0]!) encoded do
    throwError "scalar producer changed the requested key"
  return some (← restoreProposal scope packet)

private def seed (scope : Name) (coefficients : List Codec.Json) : MetaM Expr := do
  let type ← whnf (← inferType (mkConst ``RowCollect.facts))
  let mut facts ← mkListLit type.getAppArgs.back! []
  let mut count := 0
  let value ← mkAppM ``Tower.Context.codec #[mkConst ``base]
  for coefficient in coefficients.eraseDups do
    let .ok fields := coefficient.getArr? | throwError "malformed predecessor coefficient hint"
    if fields.isEmpty then continue
    unless fields.size == 2 do throwError "malformed algebraic predecessor hint"
    let producer ← mkAppM ``ScalarPacket.buildLiteral
      #[mkConst ``native, value, jsonExpr fields[0]!]
    let some packet ← evalJson producer | throwError "initial scalar production failed"
    let fact ← restoreProposal scope packet
    facts ← mkAppM ``List.cons #[fact, facts]
    count := count + 1
  logInfo m!"checked scalar seeds={count}; pre-supplied fixture facts=0"
  unless count == 5 do throwError "nested fixture scalar seed count changed"
  let name ← mkFreshUserName (scope ++ `sectionSeed)
  let type ← inferType facts
  let options ← getOptions
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type, value := facts, hints := .regular 0, safety := .safe }
  let env ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true)
  setEnv env
  compileDecl declaration (logErrors := true)
  return mkConst name


elab "#nested_root_control" : command => liftTermElabM do
  let some graphValue ← evalJson (mkAppN (mkConst ``Option.some [.zero])
      #[mkConst ``Codec.Json.Value, mkConst ``NestedRootLiterals.positive]) | throwError "missing frozen graph"
  let hints ← evalHints graphValue
  let initial ← seed `Hex.RCF.RealCoefficients.NestedRootProduceConformance hints
  let mut rules ← RowTools.rules
  for name in #[``resultAt, ``readAt, ``polynomial, ``RootReplay.readWith, ``RootReplay.read, ``RootReplay.fromTable,
      ``RootTable.readWith, ``RootTable.read, ``RootTable.extract, ``RootTable.changeOps,
      ``Descriptor.changeOps, ``Descriptor.ofChecked] do
    rules ← rules.addDeclToUnfold name
  let context ← Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let program ← withLocalDeclD `facts (← inferType initial) fun facts => do
    let result ← mkAppM ``resultAt #[facts]
    let predicate ← mkAppM ``Option.isSome #[← mkAppM ``Except.toOption #[result]]
    let equation ← mkEq predicate (mkConst ``Bool.true)
    let dictionary ← synthInstance (mkApp (mkConst ``Decidable) equation)
    mkLambdaFVars #[facts] (mkAppN (mkConst ``Decidable.decide) #[equation,dictionary])
  let seen ← IO.mkRef ({} : ExprMap Unit)
  let called ← IO.mkRef false
  let limited ← Algebraic.KernelReplay.collectMany 0 program #[⟨initial⟩] context
    (fun request inventories => do
      called.set true
      supply `Hex.RCF.RealCoefficients.NestedRootProduceConformance seen request inventories)
  match limited.outcome with
  | .missing _ => pure ()
  | _ => throwError "zero-budget nested replay did not expose a missing record"
  -- The missing outcome is the refusal check; zero fuel never invokes supply.
  unless limited.requests.size == 1 do throwError "zero-budget missing-request count changed"
  unless !(← called.get) do throwError "zero-budget replay called its supplier"
  unless (← seen.get).isEmpty do throwError "zero-budget replay called scalar production"
  let collected ← Algebraic.KernelReplay.collectMany 96 program #[⟨initial⟩] context
    (supply `Hex.RCF.RealCoefficients.NestedRootProduceConformance seen)
  let outcome := collected.outcome
  unless collected.requests.size == 3 do throwError "nested reached-record count changed"
  let some firstLimited := limited.requests[0]? | throwError "missing limited request"
  let some firstFull := collected.requests[0]? | throwError "missing full request"
  unless ← isDefEq firstLimited.polynomial firstFull.polynomial do
    throwError "zero-budget and full replay requested different first records"
  let some inventory := collected.inventories[0]? | throwError "missing scalar inventory"
  let result ← mkAppM ``resultAt #[inventory.facts]
  let proposition ← mkEq (← mkAppM ``Option.isSome #[← mkAppM ``Except.toOption #[result]])
    (mkConst ``Bool.true)
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let checkedFactsName := `Hex.RCF.RealCoefficients.NestedRootProduceConformance.checkedFacts
  let factsDeclaration := Declaration.defnDecl {
    name := checkedFactsName
    levelParams := []
    type := ← inferType inventory.facts
    value := inventory.facts
    hints := .regular 0
    safety := .safe }
  let checkedEnv ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats (← getOptions)).toUSize (maxRecDepth.get (← getOptions)).toUSize
    factsDeclaration none (doCheck := true)
  setEnv checkedEnv
  compileDecl factsDeclaration (logErrors := true)
  logInfo m!"nested root reached scalar requests={collected.requests.size}"
  match outcome with
  | .checked true proof _ =>
    let accepted := mkAppN (mkConst ``of_decide_eq_true) #[proposition,dictionary,proof]

    KernelCheck.addChecked `Hex.RCF.RealCoefficients.NestedRootProduceConformance.accepted proposition accepted
      (producers ++ #[``Descriptor.ofReplay?])
    let shape ← mkAppM ``lengthAt #[mkConst `Hex.RCF.RealCoefficients.NestedRootProduceConformance.checkedFacts]
    let expected ← mkAppM ``Option.some #[mkNatLit 1]
    let shapeType ← mkEq shape expected
    let shapeDictionary ← synthInstance (mkApp (mkConst ``Decidable) shapeType)
    let shapeDecision := mkAppN (mkConst ``Decidable.decide) #[shapeType,shapeDictionary]
    let mut shapeRules ← RowTools.rules
    for name in #[``lengthAt, ``resultAt, ``readAt, ``polynomial, ``RootReplay.readWith, ``RootReplay.read, ``RootReplay.fromTable,
        ``RootTable.readWith, ``RootTable.read, ``RootTable.extract, ``RootTable.changeOps,
        ``Descriptor.changeOps, ``Descriptor.ofChecked] do
      shapeRules ← shapeRules.addDeclToUnfold name
    let shapeContext ← Simp.mkContext (simpTheorems := #[shapeRules])
      (congrTheorems := ← getSimpCongrTheorems)
    let (shapeOutcome, _) ← Algebraic.KernelReplay.assemble shapeDecision shapeContext
    match shapeOutcome with
    | .checked true shapeProof _ =>
      let proof := mkAppN (mkConst ``of_decide_eq_true) #[shapeType,shapeDictionary,shapeProof]
      KernelCheck.addChecked `Hex.RCF.RealCoefficients.NestedRootProduceConformance.oneRoot shapeType proof (producers ++ #[``Descriptor.ofReplay?])
    | _ => throwError "nested output cardinality not checked"
  | .checked false .. => throwError "nested frozen graph rejected"
  | .missing request => throwError "nested frozen replay lacks {request}"
elab "#nested_rejection " name:ident " := " term:term : command => liftTermElabM do
  let proposition ← Term.elabTerm term (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let decision := mkAppN (mkConst ``Decidable.decide) #[proposition,dictionary]
  let mut rules ← RowTools.rules
  for law in #[``missingAt, ``wrongHeadAt, ``wrongEndpointAt, ``readAt, ``polynomial, ``RootReplay.readWith,
      ``RootReplay.fromTable, ``RootTable.readWith, ``RootTable.read,
      ``RootTable.extract, ``RootTable.changeOps, ``Descriptor.changeOps] do
    rules ← rules.addDeclToUnfold law
  let context ← Simp.mkContext (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)
  let (outcome, _) ← Algebraic.KernelReplay.assemble decision context
  match outcome with
  | .checked true proof _ =>
    let proof := mkAppN (mkConst ``of_decide_eq_true) #[proposition,dictionary,proof]
    KernelCheck.addChecked ((← getCurrNamespace) ++ name.getId) proposition proof
      (producers ++ #[``Descriptor.ofReplay?])
  | _ => throwError "nested rejection control did not check"

end
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 32768 in
#nested_root_control
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 32768 in
#nested_rejection missing_literals :=
  (missingAt checkedFacts).map (fun _ => ()) = .error Replay.Error.evidence
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 32768 in
#nested_rejection changed_head :=
  (wrongHeadAt checkedFacts).map (fun _ => ()) = .error Replay.Error.evidence
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 32768 in
#nested_rejection changed_endpoint :=
  (wrongEndpointAt checkedFacts).map (fun _ => ()) = .error Replay.Error.evidence
end Hex.RCF.RealCoefficients.NestedRootProduceConformance

namespace Hex.RCF.RealCoefficients.NestedRootProduceConformance
set_option maxRecDepth 32768 in
theorem checked : (resultAt checkedFacts).toOption.isSome = true := accepted
set_option maxRecDepth 32768 in
def reconstructed := (resultAt checkedFacts).toOption.get checked

def output : Hex.RCF.RealCoefficients.RootReplay.Result
    (polynomial checkedFacts)
    (.finite (@One.one parent.Value (Algebraic.Element.cachedOne reduction reduction_eq checkedFacts)))
    (.finite (@NatCast.natCast parent.Value
      (Algebraic.Element.cachedNatCast reduction reduction_eq checkedFacts) 2)) :=
  reconstructed

open HexPolyMathlib.Interpret HexRealRootsMathlib in
theorem root_sound (d : Descriptor parent.Value Tower.Signature parent.sign parent.signature)
    (member : d ∈ output.roots) :
    d.root original.value original.zero_iff original.one original.add original.sub original.mul
      original.nat original.sign ∈ Tarski.rootsIn
        (interpret original.value original.zero_iff (polynomial checkedFacts))
        (.finite (original.value (@One.one parent.Value
          (Algebraic.Element.cachedOne reduction reduction_eq checkedFacts))))
        (.finite (original.value (@NatCast.natCast parent.Value
          (Algebraic.Element.cachedNatCast reduction reduction_eq checkedFacts) 2))) :=
  output.root_spec original d member
#print axioms root_sound
end Hex.RCF.RealCoefficients.NestedRootProduceConformance
namespace Hex.RCF.RealCoefficients.NestedRootProduceConformance
private theorem result_some : (resultAt checkedFacts).toOption = some reconstructed :=
  (Option.some_get checked).symm
private theorem output_one : output.roots.length = 1 := by
  have h := oneRoot
  unfold lengthAt at h
  rw [result_some] at h
  exact Option.some.inj h
private theorem has_root : ∃ d, d ∈ output.roots := by
  cases h : output.roots with
  | nil =>
    have length := output_one
    simp [h] at length
  | cons d rest => exact ⟨d, by simp⟩
open HexPolyMathlib.Interpret in
private theorem interpreted : interpret original.value original.zero_iff (polynomial checkedFacts) =
    (Polynomial.X ^ 2 - Polynomial.C (Real.sqrt 2) : Polynomial ℝ) := by
  have negValue : original.value (@Neg.neg parent.Value
      (Algebraic.Element.cachedNeg reduction reduction_eq checkedFacts) alpha) = -Real.sqrt 2 := by
    erw [Algebraic.Element.cachedNeg_eq, original.neg, alpha_value]
  have oneValue : original.value (@One.one parent.Value
      (Algebraic.Element.cachedOne reduction reduction_eq checkedFacts)) = 1 := by
    erw [Algebraic.Element.cachedOne_eq, original.one]
  have zeroValue : original.value (@Zero.zero parent.Value (Tower.instZeroValue parent)) = 0 :=
    (original.zero_iff _).mpr rfl
  ext i
  rcases i with _ | _ | _ | i
  all_goals simp [polynomial, coeff_interpret, DensePoly.ofList, DensePoly.coeff_ofCoeffs,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, negValue, oneValue,
    zeroValue]

open HexPolyMathlib.Interpret HexRealRootsMathlib in
theorem source : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by
  obtain ⟨d, member⟩ := has_root
  let x := d.root original.value original.zero_iff original.one original.add original.sub original.mul
    original.nat original.sign
  have root := root_sound d member
  have valid := output.domain original
  have facts := (Tarski.mem_rootsIn_iff _ valid.1 _ _ x).mp root
  rw [interpreted] at facts
  have lower : original.value (@One.one parent.Value
      (Algebraic.Element.cachedOne reduction reduction_eq checkedFacts)) = 1 := by
    erw [Algebraic.Element.cachedOne_eq, original.one]
  have upper : original.value (@NatCast.natCast parent.Value
      (Algebraic.Element.cachedNatCast reduction reduction_eq checkedFacts) 2) = 2 := by
    have dictionary := Algebraic.Element.cachedNatCast_eq reduction reduction_eq checkedFacts
    have value := congrArg (fun naturalCast : NatCast parent.Value =>
      original.value (@NatCast.natCast parent.Value naturalCast 2)) dictionary
    exact value.trans (original.nat 2)
  refine ⟨x, ?_, ?_⟩
  · simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] using facts.1
  · have bounds := facts.2
    change original.value (@One.one parent.Value
      (Algebraic.Element.cachedOne reduction reduction_eq checkedFacts)) < x ∧
      x < original.value (@NatCast.natCast parent.Value
        (Algebraic.Element.cachedNatCast reduction reduction_eq checkedFacts) 2) at bounds
    rw [lower, upper] at bounds
    exact bounds
/-- info: 'Hex.RCF.RealCoefficients.NestedRootProduceConformance.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source
end Hex.RCF.RealCoefficients.NestedRootProduceConformance

open Lean Meta in
run_meta do
  for (name, law) in #[
      (``Hex.RCF.RealCoefficients.NestedRootProduceConformance.root_sound, ``Hex.RCF.RealCoefficients.RootReplay.Result.root_spec),
      (``Hex.RCF.RealCoefficients.NestedRootProduceConformance.source, ``Hex.RCF.RealCoefficients.RootReplay.Result.domain)] do
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
      throwError "nested source omitted replay interpretation {law}"
  for name in #[``Hex.RCF.RealCoefficients.NestedRootProduceConformance.root_sound, ``Hex.RCF.RealCoefficients.NestedRootProduceConformance.source] do
    for producer in #[``Hex.SignDet.Descriptor.buildRoots, ``Hex.SignDet.buildPrepared,
        ``Hex.RCF.RealCoefficients.ScalarPacket.build, ``Hex.RCF.RealCoefficients.ScalarPacket.buildLiteral] do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf producer) then
        throwError "nested source retained native production {producer}"

open Lean Meta in
run_meta do
  for name in #[``Hex.RCF.RealCoefficients.NestedRootProduceConformance.accepted,
      ``Hex.RCF.RealCoefficients.NestedRootProduceConformance.oneRoot,
      ``Hex.RCF.RealCoefficients.NestedRootProduceConformance.missing_literals,
      ``Hex.RCF.RealCoefficients.NestedRootProduceConformance.changed_head,
      ``Hex.RCF.RealCoefficients.NestedRootProduceConformance.changed_endpoint,
      ``Hex.RCF.RealCoefficients.NestedRootProduceConformance.root_sound,
      ``Hex.RCF.RealCoefficients.NestedRootProduceConformance.source,
      ``Hex.RCF.RealCoefficients.RootTable.extract_eq,
      ``Hex.RCF.RealCoefficients.RootTable.changeOps_self,
      ``Hex.RCF.RealCoefficients.RootTable.readWith_eq,
      ``Hex.RCF.RealCoefficients.RootReplay.readWith_eq] do
    let axioms ← collectAxioms name
    unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "nested root replay has an unapproved axiom"
    logInfo m!"{name}: {axioms}"
