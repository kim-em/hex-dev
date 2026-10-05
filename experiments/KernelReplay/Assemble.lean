/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Elab.Command
public import Lean.Meta.Reduce
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp.Main
public import Lean.Util.CollectAxioms
public import HexRealClosure.SignFacts

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta

/-- An actual checked Boolean equation, or the demanded missing-fact
application that prevented checking either Boolean value. -/
inductive Outcome where
  | checked (value : Bool) (proof : Expr) (axioms : Array Name)
  | missing (application : Expr)

/-- The original polynomial passed to missing packing, in its exact context.
Its retained key is obtained by the context's existing reduction policy. -/
structure Request where
  context : Expr
  polynomial : Expr

def request (application : Expr) : MetaM Request := do
  unless application.getAppFn.isConstOf ``Element.missing do
    throwError "expected a missing coefficient fact"
  let type ← inferType application
  unless type.getAppFn.isConstOf ``Subtype && type.getAppArgs.size == 2 do
    throwError "unexpected missing coefficient type"
  let element := type.getAppArgs[0]!
  unless element.getAppFn.isConstOf ``Element do
    throwError "unexpected algebraic element type"
  return ⟨element.getAppArgs.back!, application.getAppArgs.back!⟩

def auditProof (proof type : Expr) : MetaM (Array Name) := do
  if proof.hasSorry || proof.hasMVar || type.hasSorry || type.hasMVar then
    throwError "incomplete proof"
  let mut axioms : Array Name := #[]
  for decl in (proof.getUsedConstants ++ type.getUsedConstants) do
    for axiomName in (← collectAxioms decl) do
      if !axioms.contains axiomName then axioms := axioms.push axiomName
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "unexpected axiom {axiomName} through {decl}"
  return axioms

def kernelCheck (name : Name) (type proof : Expr) : MetaM Unit := do
  let options := (← getOptions).setBool `debug.skipKernelTC false
  ofExceptKernelException <| ((← getEnv).toKernelEnv.addDecl options
    (.thmDecl { name, levelParams := [], type, value := proof })).map (fun _ => ())

/-- Store a checked scalar-sign proof once as an ordinary theorem. Its fact
keeps transparent polynomial/sign data and an opaque proof reference, so later
checks do not inline the child certificate again. No native evaluation is used. -/
def registerFact (fact : Expr) : MetaM Expr := do
  if fact.hasSorry || fact.hasMVar || fact.hasFVar then
    throwError "incomplete fact"
  let factType ← inferType fact
  unless factType.getAppFn.isConstOf ``SignFact do
    throwError "expected a scalar sign fact"
  let context := factType.getAppArgs.back!
  let polynomial ← mkAppM ``SignFact.polynomial #[fact]
  let polynomial ← withTransparency .all (whnf polynomial)
  let claimed ← mkAppM ``SignFact.sign #[fact]
  let claimed ← withTransparency .all (whnf claimed)
  let proof ← mkAppM ``SignFact.checked #[fact]
  let type ← mkEq (← mkAppM ``Context.signPoly #[context, polynomial]) claimed
  let _ ← auditProof proof type
  let name ← mkFreshUserName `__kernelReplaySign
  let options ← getOptions
  let env ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    (.thmDecl { name, levelParams := [], type, value := proof }) none (doCheck := true)
  setEnv env
  let restored ← mkAppM ``SignFact.mk #[polynomial, claimed, mkConst name]
  let equationType ← mkEq restored restored
  let equation ← mkEqRefl restored
  let _ ← auditProof equation equationType
  kernelCheck `__kernelReplayRegisteredFact equationType equation
  return restored

/-- Only a declaration type mismatch permits trying the other Boolean value.
Timeouts and other kernel failures remain errors. -/
def acceptKernel {α : Type} (checked : Except Kernel.Exception α) : MetaM Bool :=
  match checked with
  | .ok _ => pure true
  | .error (.declTypeMismatch _ _ _) => pure false
  | .error exception => throwKernelException exception

/-- Follow demanded projections and recursor scrutinees, never lambda bodies.
The returned application retains its exact context and polynomial arguments. -/
partial def missingRedex (expression : Expr) : MetaM (Option Expr) :=
  withIncRecDepth do
    let expression ← withOptions (fun options => smartUnfolding.set options false) do
      withTransparency .all (whnf expression)
    if expression.getAppFn.isConstOf ``Element.missing then return some expression
    match expression with
    | .proj _ _ value => missingRedex value
    | .mdata _ value => missingRedex value
    | .app .. =>
      if let .proj .. := expression.getAppFn then return ← missingRedex expression.getAppFn
      if let .const name levels := expression.getAppFn then
        let args := expression.getAppArgs
        if let .recInfo recursor ← getConstInfo name then
          if let some major := args[recursor.getMajorIdx]? then return ← missingRedex major
        if let .defnInfo definition ← getConstInfo name then
          let body := definition.value.instantiateLevelParams definition.levelParams levels
          return ← missingRedex (body.beta args)
      return none
    | _ => return none

/-- Check the caller's actual expression with the ordinary kernel. Supplied
simplification equations are themselves audited and kernel checked. This
function uses no native coefficient evaluation. The caller must retain the
supplied-fact packing boundary to prevent sign production during reduction. -/
def assemble (expression : Expr) (context : Simp.Context) :
    MetaM (Outcome × Simp.Stats) := do
  if expression.hasSorry || expression.hasMVar || expression.hasFVar then
    throwError "incomplete input"
  let (simplified, stats) ← Meta.simp expression context
  let equation ← simplified.getProof' expression
  let equationType ← mkEq expression simplified.expr
  let _ ← auditProof equation equationType
  kernelCheck `__kernelReplaySimplification equationType equation
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let env := (← getEnv).toKernelEnv
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
    if ← acceptKernel checked then
      let resultProof := mkAppN (mkConst ``of_decide_eq_true)
        #[proposition, decisionInstance, reflexivity]
      let proof := mkAppN (mkConst ``Eq.trans [.succ .zero])
        #[mkConst ``Bool, expression, simplified.expr, result, equation, resultProof]
      let type ← mkEq expression result
      let axioms ← auditProof proof type
      kernelCheck `__kernelReplayProof type proof
      return (.checked candidate proof axioms, stats)
  let some redex ← missingRedex simplified.expr
    | throwError "unproved result without a demanded missing-fact boundary: {simplified.expr}"
  return (.missing redex, stats)

/-- Collection retains the actual finite fact list used in the final check.
Missing outcomes include the unresolved request; they establish no Boolean
result and make no completeness claim. -/
structure Collection where
  facts : Expr
  outcome : Outcome
  requests : Array Request

/-- Producer-side collection follows the demanded computations of the actual
checker. The supplier may produce evidence; `assemble` itself never does.
Each supplied fact is closed, audited and kernel checked before use. Fuel
bounds a faulty supplier that repeatedly supplies irrelevant facts. -/
def collect (fuel : Nat) (program initial : Expr) (context : Simp.Context)
    (supply : Request → MetaM (Option Expr)) : MetaM Collection := do
  if program.hasSorry || program.hasMVar || program.hasFVar ||
      initial.hasSorry || initial.hasMVar || initial.hasFVar then
    throwError "incomplete collection input"
  go fuel initial #[]
where
  go (remaining : Nat) (facts : Expr) (requests : Array Request) : MetaM Collection := do
    let (outcome, _) ← assemble (mkApp program facts) context
    match outcome with
    | .checked .. => return ⟨facts, outcome, requests⟩
    | .missing application =>
      let needed ← request application
      let requests := requests.push needed
      match remaining with
      | 0 => return ⟨facts, outcome, requests⟩
      | n + 1 =>
        let some fact ← supply needed | return ⟨facts, outcome, requests⟩
        if fact.hasSorry || fact.hasMVar || fact.hasFVar then
          throwError "incomplete supplied fact"
        let type ← mkEq fact fact
        let proof ← mkEqRefl fact
        let _ ← auditProof proof type
        kernelCheck `__kernelReplayCollectedFact type proof
        let facts ← mkAppM ``List.cons #[fact, facts]
        go n facts requests

end Hex.RealClosure.Algebraic.KernelReplay
