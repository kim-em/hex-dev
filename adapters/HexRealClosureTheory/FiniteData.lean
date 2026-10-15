/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.PackingNext
public import HexRealClosureTheory.KernelReplay
public import Lean.Meta.Tactic.Constructor
public import Lean.Meta.Tactic.Intro
public meta import Lean.Meta.Tactic.Constructor
public meta import Lean.Meta.Tactic.Intro
public meta import Lean.Meta.Tactic.Simp.Main
public meta import Lean.Meta.Transform

public section
namespace Hex.RealClosure.Transport.Finite

/-- Assemble one bounded index range from its actual preceding range and last
index. The bound is retained in the generated ordinary proof. -/
theorem bounded {n : Nat} {p : (i : Nat) → i < n + 1 → Prop}
    (earlier : ∀ i (h : i < n), p i (Nat.lt_trans h (Nat.lt_succ_self n)))
    (last : ∀ h : n < n + 1, p n h) : ∀ i h, p i h := by
  intro i h
  by_cases before : i < n
  · exact earlier i before
  · have equal : i = n := by omega
    subst i
    exact last h

/-- The empty index range needs no arithmetic or inventory evidence. -/
theorem empty {p : (i : Nat) → i < 0 → Prop} : ∀ i h, p i h :=
  fun i h => (Nat.not_lt_zero i h).elim

/-- Traverse the literal finite node indices without enumerating an unrelated
type or replacing the node's stored bound. -/
theorem indices {n : Nat} {p : Fin (n + 1) → Prop}
    (first : p 0) (rest : ∀ i : Fin n, p i.succ) : ∀ i, p i :=
  Fin.forall_fin_succ.mpr ⟨first, rest⟩

/-- A node with no indices has no indexed obligations. -/
theorem noIndices {p : Fin 0 → Prop} : ∀ i, p i := fun i => i.elim0

/-- Empty literal lists have no membership obligations, including predicates
that use their membership proof. -/
theorem noMembers {α : Type u} {p : (a : α) → a ∈ ([] : List α) → Prop} :
    ∀ a h, p a h := by
  intro a h
  cases h

/-- Traverse one actual list member and its tail, retaining membership proofs
for dependent certificate indices. -/
theorem members {α : Type u} {first : α} {rest : List α}
    {p : (a : α) → a ∈ first :: rest → Prop}
    (head : ∀ h, p first h)
    (tail : ∀ a (h : a ∈ rest), p a (List.mem_cons_of_mem first h)) : ∀ a h, p a h := by
  intro a h
  rcases List.mem_cons.mp h with equal | member
  · subst a
    exact head h
  · exact tail a member

/-- Traverse the stored list of an array, retaining its original membership
guard even when the predicate depends on that guard. -/
theorem arrayMembers {α : Type u} {xs : Array α} {p : (a : α) → a ∈ xs → Prop}
    (data : ∀ a (h : a ∈ xs.toList), p a (Array.mem_toList_iff.mp h)) :
    ∀ a h, p a h :=
  fun a h => data a (Array.mem_toList_iff.mpr h)

/-- A stored optional pair contributes only its actual two coordinates. -/
theorem pair {α : Type u} {β : Type v} {p : α → β → Prop} {a : α} {b : β}
    (data : p a b) : ∀ x y, a = x ∧ b = y → p x y := by
  intro x y equal
  rcases equal with ⟨rfl, rfl⟩
  exact data

/-- A successful optional result contributes its actual stored value. Retain
the equality hypothesis for predicates whose certificate indices depend on it. -/
theorem option {α : Type u} {a : α} {p : (r : α) → some a = some r → Prop}
    (data : ∀ h, p a h) : ∀ r h, p r h := by
  intro r equal
  have same : a = r := Option.some.inj equal
  subst r
  exact data equal

/-- Retain both coordinates and the original equality guard of a stored
optional terminal pair. -/
theorem optionPair {α : Type u} {β : Type v} {a : α} {b : β}
    {p : (x : α) → (y : β) → some (a, b) = some (x, y) → Prop}
    (data : ∀ h, p a b h) : ∀ x y h, p x y h := by
  intro x y equal
  have same := Prod.mk.inj (Option.some.inj equal)
  rcases same with ⟨rfl, rfl⟩
  exact data equal

/-- An absent terminal contributes no pair or arithmetic obligation. -/
theorem noOptionPair {α : Type u} {β : Type v}
    {p : (x : α) → (y : β) → (none : Option (α × β)) = some (x, y) → Prop} :
    ∀ x y h, p x y h := by
  intro x y h
  cases h

end Hex.RealClosure.Transport.Finite

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- One leaf supplier provides only the exact reached operation, key or sign
guard requested by the structural traversal. Missing evidence is an error;
it cannot become a proof admission. -/
abbrev Supplier := Expr → MetaM (Option Expr)

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

private def diagnoseTypes (obtained required : Expr) : MetaM Unit := do
  if (← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE").isNone then return
  let left := obtained.getAppArgs
  let right := required.getAppArgs
  diagnostic s!"finite: supplied type {obtained.getAppFn.constName?}, expected {required.getAppFn.constName?}"
  let some name := required.getAppFn.constName? | return
  let mut signature := (← getConstInfo name).type
  for index in [:min left.size right.size] do
    let .forallE binder _ body _ := signature | return
    signature := body
    if left[index]! != right[index]! then
      diagnostic s!"finite: differing argument {index} {binder}, obtained head {left[index]!.getAppFn.constName?}, expected head {right[index]!.getAppFn.constName?}"

/-- A discovered obligation retains its local hypotheses and instances.
Consumers must enter this context before inspecting or supplying its terms. -/
structure Leaf where
  type : Expr
  context : LocalContext
  instances : LocalInstances

/-- Inspect a discovered obligation with exactly the hypotheses and instances
under which the structural traversal reached it. -/
def Leaf.withContext (leaf : Leaf) (action : MetaM α) : MetaM α :=
  withLCtx leaf.context leaf.instances action

private def normalizeFinite (type : Expr) : MetaM Expr :=
  Core.transform type (pre := fun expression => do
    if expression.isForall then return .continue
    let arguments := expression.getAppArgs
    if expression.getAppFn.isConstOf ``Eq && arguments.size == 3 &&
        arguments[0]!.getAppFn.isConstOf ``Option && !arguments[1]!.hasLooseBVars then
      let left ← withTransparency .all (whnf arguments[1]!)
      return .done (mkAppN expression.getAppFn (arguments.set! 1 left))
    if expression.getAppFn.isConstOf ``Membership.mem && arguments.size == 5 &&
        !arguments[3]!.hasLooseBVars then
      let collection ← withTransparency .all (whnf arguments[3]!)
      return .done (mkAppN expression.getAppFn (arguments.set! 3 collection))
    return .done expression)

private def simplify (goal : MVarId) : MetaM (Option MVarId) := do
  let mut rules : SimpTheorems := {}
  for name in #[``List.forall_mem_cons, ``List.forall_mem_nil,
      ``Option.some.injEq, ``Prod.mk.injEq, ``forall_eq, ``forall_eq',
      ``forall_and, ``and_true, ``true_and, ``Array.forall_mem_iff_forall_getElem] do
    rules ← rules.addConst name
  let context ← Simp.mkContext (simpTheorems := #[rules])
    (config := { decide := false }) (congrTheorems := ← getSimpCongrTheorems)
  -- Native data is inspected by the finite traversal and suppliers.
  -- Simplifying inside it can execute arithmetic before its original keys
  -- are collected. Restrict this pass to the logical obligations.
  -- Rewriting the predicate of a choice can change the selected witness.
  -- The finite laws refer to the original choice, so preserve it while
  -- simplifying the surrounding list and index obligations.
  let defaults := Simp.mkDefaultMethodsCore #[]
  let methods : Simp.Methods := { defaults with
    pre := fun expression => do
      if expression.getAppFn.isConstOf ``Classical.choose ||
          (!expression.hasLooseBVars && !(← isProp expression)) then
        return .done { expr := expression }
      defaults.pre expression
    dpre := fun expression => do
      if expression.getAppFn.isConstOf ``Classical.choose ||
          (!expression.hasLooseBVars && !(← isProp expression)) then return .done expression
      defaults.dpre expression }
  let target ← instantiateMVars (← goal.getType)
  let (result, _) ← withTransparency .all (Simp.main target context (methods := methods))
  if result.expr.isTrue then
    goal.assign (← match result.proof? with
      | some proof => mkOfEqTrue proof
      | none => pure (mkConst ``True.intro))
    return none
  applySimpResultToTarget goal target result

private def finiteRange? (type : Expr) : MetaM (Option Nat) := do
  let .forallE _ domain body _ := type | return none
  unless domain.isConstOf ``Nat do return none
  let .forallE _ bound _ _ := body | return none
  unless bound.getAppFn.isConstOf ``Nat.lt || bound.getAppFn.isConstOf ``LT.lt do return none
  let arguments := bound.getAppArgs
  if bound.getAppFn.isConstOf ``LT.lt then
    unless arguments.size == 4 && arguments[0]! == mkConst ``Nat do return none
    let standard ← withNewMCtxDepth do
      withTransparency .instances (isDefEq arguments[1]! (mkConst ``instLTNat))
    unless standard do return none
  else
    unless arguments.size == 2 do return none
  unless arguments[arguments.size - 2]! == .bvar 0 do return none
  if arguments.back!.hasLooseBVars then return none
  withTransparency .all do
    getNatValue? (← reduce arguments.back!)

/-- Construct finite replay data by following structures, actual list members
and literal bounded indices. Primitive arithmetic, lookup and sign obligations
are delegated to the supplier. This never interprets a whole algebraic field
and never proves a missing lookup by native evaluation. -/
private partial def traverse (goal : MVarId) (supply : Supplier)
    (missing : Option (Leaf → MetaM Unit))
    (terminal : Expr → MetaM Bool := fun _ => pure false) : MetaM Unit := goal.withContext do
  let original ← instantiateMVars (← goal.getType)
  diagnostic s!"finite: begin obligation {original.getAppFn.constName?}"
  let supplied ← supply original
  if let some proof := supplied then
    diagnostic s!"finite: begin supplied proof inference for {original.getAppFn.constName?}"
    let obtained ← inferType proof
    diagnoseTypes obtained original
    unless ← withTransparency .all (isDefEq obtained original) do
      throwError "finite-data supplier returned a proof of a different obligation"
    diagnostic "finite: supplied proof type checked"
    if proof.hasSorry then throwError "finite-data supplier returned an admission"
    goal.assign proof
    return
  -- Preserve operation and replay operands before reducing their predicates.
  -- Even weak-head normalization can execute coefficient work in a stopped
  -- obligation. Discovery contributes no proof for this original boundary.
  if ← terminal original then
    let some record := missing | throwError "finite discovery cannot construct a stopped premise"
    record ⟨original, ← getLCtx, ← getLocalInstances⟩
    return
  let type ← goal.getType'
  let supplied ← if original == type then pure none else supply type
  if let some proof := supplied then
    unless ← withTransparency .all (isDefEq (← inferType proof) original) do
      throwError "finite-data supplier returned a proof of a different obligation"
    if proof.hasSorry then throwError "finite-data supplier returned an admission"
    goal.assign proof
    return
  if original != type && (← terminal type) then
    let some record := missing | throwError "finite discovery cannot construct a stopped premise"
    record ⟨original, ← getLCtx, ← getLocalInstances⟩
    return
  if type.getAppFn.isConstOf ``Eq && type.getAppArgs[0]!.isConstOf ``Bool then
    if let some record := missing then
      record ⟨← instantiateMVars type, ← getLCtx, ← getLocalInstances⟩
      return
    throwError "missing finite replay evidence for {type}"
  if let .forallE _ domain _ _ := type then
    let domain ← whnf domain
    if domain.getAppFn.isConstOf ``Fin then
      let some count ← withTransparency .all (getNatValue? (← reduce domain.getAppArgs.back!))
        | throwError "finite replay index has a nonliteral bound"
      if count == 0 then
        let [] ← withTransparency .all
            (goal.apply (← mkConstWithFreshMVarLevels ``Transport.Finite.noIndices))
          | throwError "empty finite replay index did not close"
        return
      let predicate ← forallBoundedTelescope type (some 1) fun binders body =>
        mkLambdaFVars binders body
      let indexProof := mkApp2 (mkConst ``Transport.Finite.indices) (toExpr (count - 1)) predicate
      for child in ← withTransparency .all (goal.apply indexProof) do traverse child supply missing terminal
      return
  if let some count ← finiteRange? type then
    let predicate ← forallBoundedTelescope type (some 2) fun binders body => do
      unless binders.size == 2 do throwError "invalid finite index range"
      mkLambdaFVars binders body
    if count == 0 then
      let [] ← withTransparency .all
          (goal.apply (mkApp (mkConst ``Transport.Finite.empty) predicate))
        | throwError "empty finite-data range did not close"
      return
    let mut signature := (← getConstInfo ``Transport.Finite.bounded).type
    for expected in #[`n, `p, `earlier, `last, `i, `h] do
      let .forallE actual _ body _ := signature |
        throwError "bounded traversal changed its theorem arity"
      unless actual == expected do throwError "bounded traversal changed its theorem layout"
      signature := body
    unless signature == mkApp2 (.bvar 4) (.bvar 1) (.bvar 0) do
      throwError "bounded traversal changed its dependent conclusion"
    let rangeProof := mkApp2 (mkConst ``Transport.Finite.bounded) (toExpr (count - 1)) predicate
    -- Keep the original dependent predicate without rechecking its computed
    -- size during application. Discovery uses the standard Nat relation and
    -- its reduced bound; proof-producing callers kernel-check the conversion
    -- and both actual theorem premises before exposing a theorem.
    let .forallE firstName earlier following _ ← inferType rangeProof |
      throwError "bounded traversal lost its preceding range"
    unless firstName == `earlier do throwError "bounded traversal changed its preceding premise"
    let first ← mkFreshExprMVar earlier
    let .forallE lastName last _ _ := following.instantiate1 first |
      throwError "bounded traversal lost its last index"
    unless lastName == `last do throwError "bounded traversal changed its final premise"
    let second ← mkFreshExprMVar last
    goal.assign (mkApp2 rangeProof first second)
    for child in [first.mvarId!, second.mvarId!] do traverse child supply missing terminal
    return
  if let .forallE _ domain (.forallE _ member _ _) _ := type then
    if member.getAppFn.isConstOf ``Membership.mem && member.getAppArgs.size == 5 then
      let collection := member.getAppArgs[3]!
      unless collection.hasLooseBVars do
        if (← inferType collection).getAppFn.isConstOf ``Array then
          let predicate ← forallBoundedTelescope type (some 2) fun binders body =>
            mkLambdaFVars binders body
          let proof ← mkConstWithFreshMVarLevels ``Transport.Finite.arrayMembers
          for child in ← withTransparency .all
              (goal.apply (mkAppN proof #[domain, collection, predicate])) do
            traverse child supply missing terminal
          return
        let literal ← withTransparency .all (whnf collection)
        if literal.getAppFn.isConstOf ``List.nil || literal.getAppFn.isConstOf ``List.cons then
          let predicate ← forallBoundedTelescope type (some 2) fun binders body =>
            mkLambdaFVars binders body
          let proof ← mkConstWithFreshMVarLevels
            (if literal.getAppFn.isConstOf ``List.nil then ``Transport.Finite.noMembers
              else ``Transport.Finite.members)
          let proof := if literal.getAppFn.isConstOf ``List.nil then
              mkAppN proof #[domain, predicate]
            else mkAppN proof #[domain, literal.getAppArgs[1]!, literal.getAppArgs[2]!, predicate]
          for child in ← withTransparency .all (goal.apply proof) do traverse child supply missing terminal
          return
  let finite ← normalizeFinite type
  if finite != type then
    let changed ← withTransparency .all (goal.change finite)
    traverse changed supply missing terminal
    return
  if let .forallE _ domain (.forallE _ equal _ _) _ := type then
    if equal.getAppFn.isConstOf ``Eq && equal.getAppArgs.size == 3 then
      let left := equal.getAppArgs[1]!
      let right := equal.getAppArgs[2]!
      if left.getAppFn.isConstOf ``Option.some && !left.hasLooseBVars &&
          right.getAppFn.isConstOf ``Option.some && right.getAppArgs.back! == .bvar 0 then
        let predicate ← forallBoundedTelescope type (some 2) fun binders body =>
          mkLambdaFVars binders body
        let proof ← mkConstWithFreshMVarLevels ``Transport.Finite.option
        let proof := mkAppN proof #[domain, left.getAppArgs.back!, predicate]
        for child in ← withTransparency .all (goal.apply proof) do
          traverse child supply missing terminal
        return
  if let .forallE _ first (.forallE _ second (.forallE _ equal _ _) _) _ := type then
    if equal.getAppFn.isConstOf ``Eq && equal.getAppArgs.size == 3 then
      let left := equal.getAppArgs[1]!
      let right := equal.getAppArgs[2]!
      if equal.getAppArgs[0]!.getAppFn.isConstOf ``Option then
        diagnostic s!"finite: optional pair guard left {left.getAppFn.constName?}, right {right.getAppFn.constName?}"
      if left.getAppFn.isConstOf ``Option.none && right.getAppFn.isConstOf ``Option.some then
        let requested := right.getAppArgs.back!
        if requested.getAppFn.isConstOf ``Prod.mk &&
            requested.getAppArgs[2]! == .bvar 1 && requested.getAppArgs[3]! == .bvar 0 then
          let predicate ← forallBoundedTelescope type (some 3) fun binders body =>
            mkLambdaFVars binders body
          let proof ← mkConstWithFreshMVarLevels ``Transport.Finite.noOptionPair
          let [] ← withTransparency .all
              (goal.apply (mkAppN proof #[first, second, predicate]))
            | throwError "absent finite terminal pair did not close"
          return
      if left.getAppFn.isConstOf ``Option.some && !left.hasLooseBVars &&
          right.getAppFn.isConstOf ``Option.some then
        let stored ← withTransparency .all (whnf left.getAppArgs.back!)
        let requested := right.getAppArgs.back!
        if stored.getAppFn.isConstOf ``Prod.mk && requested.getAppFn.isConstOf ``Prod.mk &&
            requested.getAppArgs[2]! == .bvar 1 && requested.getAppArgs[3]! == .bvar 0 then
          let predicate ← forallBoundedTelescope type (some 3) fun binders body =>
            mkLambdaFVars binders body
          let proof ← mkConstWithFreshMVarLevels ``Transport.Finite.optionPair
          let proof := mkAppN proof #[first, second, stored.getAppArgs[2]!,
            stored.getAppArgs[3]!, predicate]
          for child in ← withTransparency .all (goal.apply proof) do
            traverse child supply missing terminal
          return
    if equal.getAppFn.isConstOf ``And && equal.getAppArgs.size == 2 then
      let left := equal.getAppArgs[0]!.getAppArgs
      let right := equal.getAppArgs[1]!.getAppArgs
      if equal.getAppArgs[0]!.getAppFn.isConstOf ``Eq && left.size == 3 &&
          equal.getAppArgs[1]!.getAppFn.isConstOf ``Eq && right.size == 3 &&
          left[2]! == .bvar 1 && right[2]! == .bvar 0 &&
          !left[1]!.hasLooseBVars && !right[1]!.hasLooseBVars then
        let predicate ← forallBoundedTelescope type (some 3) fun binders body =>
          mkLambdaFVars #[binders[0]!, binders[1]!] body
        let proof ← mkConstWithFreshMVarLevels ``Transport.Finite.pair
        let proof := mkAppN proof #[first, second, predicate, left[1]!, right[1]!]
        for child in ← withTransparency .all (goal.apply proof) do traverse child supply missing terminal
        return
  let name := type.getAppFn.constName?
  let expand := name.any fun name => #[``Packing.DerivativeData, ``Packing.ReplayData,
    ``Packing.PowerData, ``Packing.FoldData, ``Packing.ReductionData,
    ``Packing.PreparationData, ``Transport.PowerData].contains name
  let reduced ← if expand then withTransparency .all (whnf type) else whnf type
  unless ← withTransparency .all (isDefEq reduced type) do
    throwError "finite replay reduction changed its obligation"
  if reduced != type then
    let changed ← withTransparency .all (goal.change reduced)
    traverse changed supply missing terminal
    return
  if let .const name _ := reduced.getAppFn then
    if (getStructureInfo? (← getEnv) name).isSome || name == ``And || name == ``True then
      for child in ← goal.constructor do traverse child supply missing terminal
      return
  if let some simplified ← simplify goal then
    if simplified != goal || (← simplified.getType') != type then
      traverse simplified supply missing terminal
      return
  else return
  if let .forallE _ domain _ _ := reduced then
    if ← isProp domain then
      let (_, child) ← goal.intro1
      traverse child supply missing terminal
      return
  if let some record := missing then
    record ⟨← instantiateMVars type, ← getLCtx, ← getLocalInstances⟩
    return
  throwError "missing finite replay evidence for {type}"

/-- Solve every reached finite premise; no unresolved leaf is accepted. -/
def solve (goal : MVarId) (supply : Supplier) : MetaM Unit :=
  traverse goal supply none

/-- Discover the exact primitive obligations before choosing interpretations
or producing additional records. Discovery returns expressions only, never a
proof. The subsequent `buildClosed` must discharge every discovered leaf. -/
def leaves (type : Expr) (supply : Supplier) : MetaM (Array Leaf) := do
  let found ← IO.mkRef (#[] : Array Leaf)
  let goal ← mkFreshExprMVar type
  traverse goal.mvarId! supply (some (fun type => found.modify (·.push type)))
  found.get

/-- Discover finite premises up to the requested boundary. A stopped
premise retains its original expression and local hypotheses and contributes
no proof. This permits dependency lowering before any reader is chosen. -/
def frontier (type : Expr) (terminal : Expr → MetaM Bool)
    (supply : Supplier := fun _ => pure none) : MetaM (Array Leaf) := do
  let found ← IO.mkRef (#[] : Array Leaf)
  let goal ← mkFreshExprMVar type
  traverse goal.mvarId! supply (some (fun leaf => found.modify (·.push leaf))) terminal
  found.get

/-- Return a complete proof term. Callers retain the term and check its closed
declaration with `kernelCheck`; the supplier's native production is never a
proof rule. Resource failures and missing obligations propagate. -/
def build (type : Expr) (supply : Supplier) : MetaM Expr := do
  let goal ← mkFreshExprMVar type
  solve goal.mvarId! supply
  let proof ← instantiateMVars goal
  if proof.hasMVar || proof.hasSorry then throwError "incomplete finite replay data"
  let _ ← auditProof proof type
  return proof

/-- Close the ordinary-kernel boundary in this API itself. Open local proof
terms must first be abstracted by the caller; no declaration is installed from
an incomplete or admitted term. -/
def buildClosed (type : Expr) (supply : Supplier) : MetaM Expr := do
  let proof ← build type supply
  if proof.hasFVar || type.hasFVar then throwError "open finite replay declaration"
  kernelCheck `__finiteReplayData type proof
  return proof

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData

/-- info: 'Hex.RealClosure.Transport.Finite.bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.bounded

/-- info: 'Hex.RealClosure.Transport.Finite.empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.empty
