/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Tactic

public section

/-!
# Optional coefficient handler regressions

Synthetic handlers exercise the base boundary without importing the real-closure
family or claiming real-coefficient search. The only successful handler proves
reflexivity. IO references record calls and identify metavariables to corrupt;
they deliberately survive MetaM backtracking so the assertions observe it.
-/

namespace Hex.RCF.HandlerTests

open Lean Meta Elab Tactic

meta section

register_option rcf.testMode : Nat := {
  defValue := 0
  descr := "synthetic RCF handler test case"
}

end

meta initialize calls : IO.Ref (Array Nat) ← IO.mkRef #[]
meta initialize probes : IO.Ref (Array MVarId) ← IO.mkRef #[]

unsafe def unsafeIdentity (n : Nat) : Nat := n

private meta def record (n : Nat) : MetaM Unit := do
  calls.modify (·.push n)

private meta def corrupt : MetaM Unit := do
  for id in ← probes.get do
    id.assign (mkNatLit 37)

meta def assertRestored : MetaM Unit := do
  for id in ← probes.get do
    if ← id.isAssigned then throwError "handler state leaked"

-- Deliberately register in reverse order. Import/attribute order must not
-- determine which solver gets the first attempt.
@[rcf_handler] meta def zLast : Handler := fun _ => do
  record 3
  assertRestored
  if rcf.testMode.get (← getOptions) != 8 then
    throwError "terminal result incorrectly tried another handler"
  return .declined

@[rcf_handler] meta def bResult : Handler := fun target => do
  record 2
  assertRestored
  corrupt
  match rcf.testMode.get (← getOptions) with
  | 0 =>
      -- A successful handler may use fresh metavariables internally.
      let proof ← forallTelescope target fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "expected equality"
        mkLambdaFVars xs (← mkEqRefl lhs)
      let candidate ← mkFreshExprMVar target
      let proof ← mkAuxTheorem target proof (cache := false)
      candidate.mvarId!.assign proof
      return .proved candidate
  | 1 => return .proved (mkConst ``True.intro)
  | 2 => return .proved (← mkFreshExprMVar target)
  | 3 => return .failed "checked false verdict"
  | 4 => return .failed "coefficient budget exhausted"
  | 5 => return .failed "literal replay rejected"
  | 6 => throwError "unexpected handler exception"
  | 7 =>
      Core.throwMaxHeartbeat `rcf `maxHeartbeats 1000
      return .declined
  | 8 => return .declined
  | 9 =>
      let proof ← forallTelescope target fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "expected equality"
        mkLambdaFVars xs (← mkEqRefl lhs)
      -- inferType alone would accept this application: its result type is
      -- correct, but its argument does not have the claimed False type.
      return .proved (mkApp (mkLambda `h .default (mkConst ``False) proof)
        (mkConst ``True.intro))
  | 10 =>
      for id in ← getMVars target do id.assign (mkConst ``Real.pi)
      let proof ← forallTelescope (← instantiateMVars target) fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "expected equality"
        mkLambdaFVars xs (← mkEqRefl lhs)
      return .proved proof
  | 11 => return .proved (← mkSorry target false)
  | 12 =>
      -- Exercise existential and bounded goals through actual tactic quotation.
      let candidate ← mkFreshExprMVar target
      let goals ← Lean.Elab.runTactic' candidate.mvarId!
        (← `(tactic| first | exact ⟨0, rfl⟩ | exact fun _ _ => rfl))
      unless goals.isEmpty do throwError "synthetic handler left goals"
      return .proved candidate
  | 13 =>
      let candidate ← mkFreshExprMVar target
      let goals ← Lean.Elab.runTactic' candidate.mvarId!
        (← `(tactic| intro x; simp_all only))
      unless goals.isEmpty do throwError "alias handler left goals"
      return .proved candidate
  | 14 =>
      -- Hide the rejected candidate behind an auxiliary theorem to exercise
      -- the transitive dependency walk and failed-environment rollback.
      return .proved (← mkAuxTheorem target (← mkSorry target false) (cache := false))
  | 15 =>
      let proof ← forallTelescope target fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "expected equality"
        mkLambdaFVars xs (← mkEqRefl lhs)
      -- An unused argument still contributes its axiom dependency, even
      -- though beta reduction would erase it from the candidate proof.
      let forbidden := mkConst ``sorryAx [.zero]
      return .proved (mkApp (mkLambda `unused .default (← inferType forbidden) proof) forbidden)
  | 16 | 21 =>
      let proof ← forallTelescope target fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "expected equality"
        mkLambdaFVars xs (← mkEqRefl lhs)
      -- The result type agrees immediately. Validating its unused argument
      -- requires reducing a recursor, and must obey the kernel's depth limit.
      let nat := mkConst ``Nat
      let motive := mkLambda `n .default nat nat
      let step := mkLambda `n .default nat (mkLambda `a .default nat (mkBVar 0))
      let reduced := mkAppN (mkConst ``Nat.rec [.succ .zero])
        #[motive, mkNatLit 0, step, mkNatLit 10000]
      let argumentType ← mkEq reduced (mkNatLit 0)
      let candidate := mkApp (mkLambda `unused .default argumentType proof)
        (← mkEqRefl (mkNatLit 0))
      if rcf.testMode.get (← getOptions) == 21 then
        -- The base must also force checking of the handler's own lemmas.
        return .proved (← withOptions (Elab.async.set · false) <|
          mkAuxTheorem target candidate (zetaDelta := true) (cache := false))
      return .proved candidate
  | 17 =>
      -- A free variable created inside the handler cannot escape its scope.
      withLocalDeclD `escaped target fun escaped => return .proved escaped
  | 18 =>
      let some hypothesis := (← getLCtx).findFromUserName? `assigned
        | throwError "missing assigned hypothesis"
      return .proved hypothesis.toExpr
  | 19 =>
      let proof ← forallTelescope target fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "expected equality"
        mkLambdaFVars xs (← mkEqRefl lhs)
      withLocalDeclD `escaped (mkConst ``True) fun escaped =>
        return .proved (mkApp (mkLambda `unused .default (mkConst ``True) proof) escaped)
  | 20 =>
      let proof ← forallTelescope target fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "expected equality"
        mkLambdaFVars xs (← mkEqRefl lhs)
      return .proved (mkApp (mkLambda `unused .default
        (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) proof) (mkConst ``unsafeIdentity))
  | 22 =>
      let proof ← forallTelescope target fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "expected equality"
        mkLambdaFVars xs (← mkEqRefl lhs)
      let some localDef := (← getLCtx).findFromUserName? `unsafeAlias
        | throwError "missing unsafe alias"
      return .proved (mkApp (mkLambda `unused .default localDef.type proof) localDef.toExpr)
  | 23 =>
      let proof ← forallTelescope target fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "expected equality"
        mkLambdaFVars xs (← mkEqRefl lhs)
      return .proved proof
  | _ => throwError "unknown test case"

@[rcf_handler] meta def aDecline : Handler := fun _ => do
  record 1
  corrupt
  return .declined

/-- A closed coefficient whose rational recognizer exhausts its resources. -/
noncomputable opaque budgetCoefficient : ℝ := Real.pi

@[norm_num budgetCoefficient] meta def budgetNormalizer : Mathlib.Meta.NormNum.NormNumExt where
  eval _ := do
    Core.throwMaxHeartbeat `rcf `maxHeartbeats 1000
    failure

end Hex.RCF.HandlerTests
