/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Elab.Command
public import Lean.Meta.Reduce
public meta import Lean.Meta.Reduce
public meta import Lean.Meta.Check
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp.Main
public import Lean.Util.CollectAxioms
public import HexRealClosure.Packing

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

/-- Store exact data bindings and a scalar-sign proof in one checked theorem.
The restored fact uses its semantic conjunct. Kernel failures are returned with
their actual exception constructor; callers must propagate resource errors.
The environment is committed only after the restored fact is also checked. -/
def registerFact (fact : Expr) : MetaM (Except Kernel.Exception Expr) := do
  if fact.hasSorry || fact.hasMVar || fact.hasFVar then
    throwError "incomplete fact"
  let factType ← inferType fact
  unless factType.getAppFn.isConstOf ``SignFact do
    throwError "expected a scalar sign fact"
  let context := factType.getAppArgs.back!
  let originalPolynomial ← mkAppM ``SignFact.polynomial #[fact]
  let polynomial ← withTransparency .all (reduce originalPolynomial)
  let originalSign ← mkAppM ``SignFact.sign #[fact]
  let claimed ← withTransparency .all (reduce originalSign)
  let semantic ← mkEq (← mkAppM ``Context.signPoly #[context, polynomial]) claimed
  let type ← mkAppM ``And #[← mkEq polynomial originalPolynomial,
    ← mkAppM ``And #[← mkEq claimed originalSign, semantic]]
  let proof ← mkAppM ``And.intro #[← mkEqRefl polynomial,
    ← mkAppM ``And.intro #[← mkEqRefl claimed, ← mkAppM ``SignFact.checked #[fact]]]
  let _ ← auditProof proof type
  let name ← mkFreshUserName `__kernelReplaySign
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let env ← match (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      (.thmDecl { name, levelParams := [], type, value := proof }) none (doCheck := true) with
    | .error exception => return .error exception
    | .ok env => pure env
  let restored : Except Kernel.Exception Expr ← withEnv env do
    -- Projections reuse the checked semantic conjunct without supplying
    -- proposition arguments that require the original data to reduce again.
    let semanticProof := Expr.proj ``And 1 (Expr.proj ``And 1 (mkConst name))
    let restored ← mkAppM ``SignFact.mk #[polynomial, claimed, semanticProof]
    let equationType ← mkEq restored restored
    let equation ← mkEqRefl restored
    let _ ← auditProof equation equationType
    match (← getEnv).toKernelEnv.addDecl options
        (.thmDecl {
          name := `__kernelReplayRegisteredFact
          levelParams := []
          type := equationType
          value := equation }) with
    | .error exception => return .error exception
    | .ok _ => return .ok restored
  match restored with
  | .error exception => return .error exception
  | .ok restored =>
    setEnv env
    return .ok restored

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
    if expression.getAppFn.isConstOf ``Element.missing then
      -- Authenticate a raw key only after its coefficient packings are known.
      -- An outer missing packing can otherwise conceal an unrecorded inverse
      -- inside its polynomial argument. Equality forces the finite literal key
      -- without following unused branches or lambda bodies.
      let polynomial := expression.getAppArgs.back!
      let equality ← mkEq polynomial polynomial
      let decisionInstance ← synthInstance (mkApp (mkConst ``Decidable) equality)
      let decision := mkAppN (mkConst ``decide) #[equality, decisionInstance]
      if let some prerequisite ← missingRedex decision then return some prerequisite
      return some expression
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

/-- One typed finite sign-fact or original-packing list. Different entries may have different coefficient
carriers; their expressions are never cast to a common mathematical carrier. -/
structure Inventory where
  facts : Expr

/-- Check closed fact data, including its semantic proof, with the ordinary
kernel before adding it to the appropriate typed inventory. -/
private def checkFact (fact : Expr) : MetaM Expr := do
  if fact.hasSorry || fact.hasMVar || fact.hasFVar then
    throwError "incomplete supplied fact"
  let type ← inferType fact
  unless type.getAppFn.isConstOf ``SignFact || type.getAppFn.isConstOf ``Packing do
    throwError "expected a scalar sign fact or packing record"
  let equation ← mkEq fact fact
  let proof ← mkEqRefl fact
  let _ ← auditProof proof equation
  kernelCheck `__kernelReplayInventoryFact equation proof
  return type

private def inventoryType (inventory : Inventory) : MetaM Expr := do
  let facts := inventory.facts
  if facts.hasSorry || facts.hasMVar || facts.hasFVar then
    throwError "incomplete fact inventory"
  let type ← withTransparency .all (whnf (← inferType facts))
  unless type.getAppFn.isConstOf ``List && type.getAppArgs.size == 1 do
    throwError "expected a typed fact list"
  let element := type.getAppArgs[0]!
  unless element.getAppFn.isConstOf ``SignFact || element.getAppFn.isConstOf ``Packing do
    throwError "expected a scalar sign fact or packing list"
  let equation ← mkEq facts facts
  let proof ← mkEqRefl facts
  let _ ← auditProof proof equation
  kernelCheck `__kernelReplayInventory equation proof
  return element

/-- Preserve the inventories actually used by a multi-field check. Each request
retains its exact context, even when another field has the same label. -/
structure Collections where
  inventories : Array Inventory
  outcome : Outcome
  requests : Array Request

/-- Collect demanded intermediate facts in several coefficient fields. The
program takes one typed list argument per inventory. The supplier may produce
certificates; replay instead supplies only recorded certificates. Every returned
fact is kernel checked and can enter only a list with its exact `SignFact` or
`Packing` type. Original-packing programs use `Element.replayPack` throughout
the recorded operations; the returned inventories retain initial records as
well as every collected raw request, including constant and zero packing.
Legacy scalar-sign programs still collect only their missing reduced keys.
Fuel bounds irrelevant evidence. This function does not reconstruct contexts. -/
def collectMany (fuel : Nat) (program : Expr) (initial : Array Inventory)
    (context : Simp.Context) (supply : Request → Array Inventory → MetaM (Option Expr)) :
    MetaM Collections := do
  if program.hasSorry || program.hasMVar || program.hasFVar then
    throwError "incomplete collection program"
  let mut types := #[]
  for inventory in initial do
    let type ← inventoryType inventory
    for previous in types do
      if ← isDefEq previous type then throwError "duplicate coefficient inventory"
    types := types.push type
  let expression := mkAppN program (initial.map Inventory.facts)
  check expression
  unless ← isDefEq (← inferType expression) (mkConst ``Bool) do
    throwError "collection program must return Bool with these inventories"
  go fuel initial types #[]
where
  go (remaining : Nat) (inventories : Array Inventory) (types : Array Expr)
      (requests : Array Request) : MetaM Collections := do
    let expression := mkAppN program (inventories.map Inventory.facts)
    let (outcome, _) ← assemble expression context
    match outcome with
    | .checked .. => return ⟨inventories, outcome, requests⟩
    | .missing application =>
      let needed ← request application
      let requests := requests.push needed
      let mut candidates : Array Nat := #[]
      for i in [:types.size] do
        let declared := types[i]!.getAppArgs.back!
        if declared == needed.context || (← isDefEq declared needed.context) then
          candidates := candidates.push i
      if candidates.isEmpty then return ⟨inventories, outcome, requests⟩
      match remaining with
      | 0 => return ⟨inventories, outcome, requests⟩
      | n + 1 =>
        let some fact ← supply needed inventories
          | return ⟨inventories, outcome, requests⟩
        let type ← checkFact fact
        let mut selected := none
        for i in candidates do
          if ← isDefEq type types[i]! then
            selected := some i
            break
        let some slot := selected
          | if ← isDefEq type.getAppArgs.back! needed.context then
              throwError "supplied fact belongs to a different inventory kind"
            else
              throwError "supplied fact belongs to a different coefficient context"
        let some inventory := inventories[slot]?
          | throwError "coefficient inventory index mismatch"
        let facts ← mkAppM ``List.cons #[fact, inventory.facts]
        go n (inventories.set! slot ⟨facts⟩) types requests

end Hex.RealClosure.Algebraic.KernelReplay
