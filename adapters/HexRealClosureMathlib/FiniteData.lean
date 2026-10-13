/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.PackingNext
public import HexRealClosureMathlib.KernelReplay
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

/-- A stored optional pair contributes only its actual two coordinates. -/
theorem pair {α : Type u} {β : Type v} {p : α → β → Prop} {a : α} {b : β}
    (data : p a b) : ∀ x y, a = x ∧ b = y → p x y := by
  intro x y equal
  rcases equal with ⟨rfl, rfl⟩
  exact data

end Hex.RealClosure.Transport.Finite

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- One leaf supplier provides only the exact reached operation, key or sign
guard requested by the structural traversal. Missing evidence is an error;
it cannot become a proof admission. -/
abbrev Supplier := Expr → MetaM (Option Expr)

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
  return (← withTransparency .all (simpTarget goal context)).1

private def finiteRange? (type : Expr) : MetaM (Option Nat) := do
  let .forallE _ domain body _ := type | return none
  unless domain.isConstOf ``Nat do return none
  let .forallE _ bound _ _ := body | return none
  unless bound.getAppFn.isConstOf ``Nat.lt || bound.getAppFn.isConstOf ``LT.lt do return none
  let arguments := bound.getAppArgs
  unless arguments.size ≥ 2 && arguments[arguments.size - 2]! == .bvar 0 do return none
  withTransparency .all do
    getNatValue? (← reduce arguments.back!)

/-- Construct finite replay data by following structures, actual list members
and literal bounded indices. Primitive arithmetic, lookup and sign obligations
are delegated to the supplier. This never interprets a whole algebraic field
and never proves a missing lookup by native evaluation. -/
private partial def traverse (goal : MVarId) (supply : Supplier)
    (missing : Option (Leaf → MetaM Unit)) : MetaM Unit := goal.withContext do
  let type ← goal.getType'
  if let some proof ← supply type then
    unless ← isDefEq (← inferType proof) type do
      throwError "finite-data supplier returned a proof of a different obligation"
    if proof.hasSorry then throwError "finite-data supplier returned an admission"
    goal.assign proof
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
      for child in ← withTransparency .all (goal.apply indexProof) do traverse child supply missing
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
    let rangeProof := mkApp2 (mkConst ``Transport.Finite.bounded) (toExpr (count - 1)) predicate
    let children ← withTransparency .all (goal.apply rangeProof)
    for child in children do traverse child supply missing
    return
  if let .forallE _ domain (.forallE _ member _ _) _ := type then
    if member.getAppFn.isConstOf ``Membership.mem && member.getAppArgs.size == 5 then
      let collection := member.getAppArgs[3]!
      unless collection.hasLooseBVars do
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
          for child in ← withTransparency .all (goal.apply proof) do traverse child supply missing
          return
  let finite ← normalizeFinite type
  if finite != type then
    let changed ← withTransparency .all (goal.change finite)
    traverse changed supply missing
    return
  if let .forallE _ first (.forallE _ second (.forallE _ equal _ _) _) _ := type then
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
        for child in ← withTransparency .all (goal.apply proof) do traverse child supply missing
        return
  let name := type.getAppFn.constName?
  let expand := name.any fun name => #[``Packing.DerivativeData, ``Packing.ReplayData,
    ``Packing.PowerData, ``Packing.FoldData, ``Packing.ReductionData,
    ``Packing.PreparationData].contains name
  let reduced ← if expand then withTransparency .all (whnf type) else whnf type
  unless ← withTransparency .all (isDefEq reduced type) do
    throwError "finite replay reduction changed its obligation"
  if reduced != type then
    let changed ← withTransparency .all (goal.change reduced)
    traverse changed supply missing
    return
  if let .const name _ := reduced.getAppFn then
    if (getStructureInfo? (← getEnv) name).isSome || name == ``And || name == ``True then
      for child in ← goal.constructor do traverse child supply missing
      return
  if let some simplified ← simplify goal then
    if simplified != goal || (← simplified.getType') != type then
      traverse simplified supply missing
      return
  else return
  if let .forallE _ domain _ _ := reduced then
    if ← isProp domain then
      let (_, child) ← goal.intro1
      traverse child supply missing
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
