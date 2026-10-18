/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Tactic

public section

open Lean Meta
namespace Hex.RCF.AdmissionTests
opaque hidden : Nat := 13
inductive Link where
  | nil
  | cons (tail : Link)
private meta def reference (expression : Expr) : MetaM Bool := do
  let expression ← instantiateMVars expression
  if expression.hasExprMVar then return false
  for name in expression.getUsedConstants do
    for axiomName in ← collectAxioms name do
      unless [``propext,``Classical.choice,``Quot.sound].contains axiomName do return false
  return true
run_meta do
  withoutModifyingEnv do
    let mut previous := mkConst ``hidden
    let mut expressions := #[previous,mkConst ``Link,mkConst ``Link.rec,
      mkConst ``Quot.mk [.zero],mkConst ``Classical.choice [.zero],
      mkConst ``sorryAx [.zero],mkConst ``sorryAx [.succ .zero]]
    for i in [:64] do
      let value ← mkAppM ``Nat.add #[previous,previous]
      let name := mkPrivateName (← getEnv) (← mkFreshUserName `diamond)
      previous ← mkAuxDefinition name (mkConst ``Nat) value (compile := false)
      if i % 8 == 0 then expressions := expressions.push previous
    expressions := expressions.push (← mkAppM ``Nat.add #[previous,previous])
    let value ← mkAppM ``Nat.add #[previous,mkNatLit 1]
    let left ← mkAuxDefinition (mkPrivateName (← getEnv) (← mkFreshUserName `left))
      (mkConst ``Nat) value (compile := false)
    let right ← mkAuxDefinition (mkPrivateName (← getEnv) (← mkFreshUserName `right))
      (mkConst ``Nat) value (compile := false)
    expressions := expressions.push (← mkAppM ``Nat.add #[left,right])
    expressions := expressions.push (← mkFreshExprMVar (mkConst ``True))
    let forbidden := mkConst ``sorryAx [.zero]
    expressions := expressions.push (mkApp (mkLambda `unused .default (← inferType forbidden)
      (mkConst ``True.intro)) forbidden)
    for expression in expressions do
      let expected ← reference expression
      let actual ← try
        Hex.RCF.checkAxioms `forestProbe expression
        pure true
      catch _ => pure false
      unless expected == actual do
        throwError "forest and authoritative admission policies disagree: {expression}"
    logInfo m!"forest/reference agree on {expressions.size} imported/local/opaque/inductive/shared/forbidden/unresolved cases"
-- Reuse an identical declaration name across rolled-back environments. A
-- previous successful check must not mask a later forbidden dependency, and
-- a failed check must not poison a later valid declaration with that name.
run_meta do
  let reused := Name.mkSimple "__rcfForestEnvironmentProbe"
  for forbidden in #[false,true,false] do
    let saved ← saveState
    try
        let value ← if forbidden then mkSorry (mkConst ``Nat) false else pure (mkNatLit 3)
        let root ← mkAuxDefinition reused (mkConst ``Nat) value (compile := false)
        let shared ← mkAppM ``Nat.add #[root,root]
        let expected ← reference shared
        let actual ← try
          Hex.RCF.checkAxioms `forestEnvironment shared
          pure true
        catch _ => pure false
        unless expected == !forbidden && actual == expected do
          throwError "admission retained results across an environment rollback"
    finally
      saved.restore
  logInfo "forest admission follows all three rolled-back environments"
end Hex.RCF.AdmissionTests
