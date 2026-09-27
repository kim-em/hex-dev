/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Bird.Evaluator

open Lean Meta Qq Mathlib.Tactic.Ring Mathlib.Tactic.Determinant

/-! Direct checks of relation indexing, expansion reuse and entry-zero pruning. -/

run_meta do
  withLocalDeclD `a q(Rat) fun a =>
    withLocalDeclD `b q(Rat) fun b => do
      have a : Q(Rat) := a
      have b : Q(Rat) := b
      let c ← Common.mkCache q(inferInstance : CommSemiring Rat)
      let audit : Mathlib.Tactic.AtomM Unit := do
        let value ← HexPolyDetMathlib.Bird.Scalar.eval rcℕ (ringCompute c) c q($a + $b)
        let state ← IO.mkRef ({} : HexPolyDetMathlib.Bird.Relations.State)
        let _ ← HexPolyDetMathlib.Bird.Relations.index 100 state value.val
        let first ← state.get
        let _ ← HexPolyDetMathlib.Bird.Relations.index 100 state value.val
        let second ← state.get
        unless first.work > 0 && first.work == second.work && first.sums.size > 0 do
          throwError "relation sum tails were not cached and reused"
        let _ ← HexPolyDetMathlib.Bird.Relations.factors state 64 q($a * $b)
        unless ((← state.get).factors.get? (q($a * $b), false, 64)).isSome do
          throwError "relation factor signature was not cached"
        let limited ← IO.mkRef ({} : HexPolyDetMathlib.Bird.Relations.State)
        let rejected ← try
          let _ ← HexPolyDetMathlib.Bird.Relations.index 1 limited value.val
          pure false
        catch e => pure (if let .internal id _ := e then
          id == HexPolyDetMathlib.Bird.Relations.budgetException else false)
        unless rejected do throwError "relation work limit did not reject distinct tails"
      audit.run .reducible

run_meta do
  withLocalDeclD `a q(Rat) fun a =>
    withLocalDeclD `b q(Rat) fun b =>
      withLocalDeclD `u q(Rat) fun u =>
        withLocalDeclD `v q(Rat) fun v => do
          have a : Q(Rat) := a
          have b : Q(Rat) := b
          have u : Q(Rat) := u
          have v : Q(Rat) := v
          let reified ← reifyBirdDet q(BirdDet.birdDet 2
            (#[$a*$a/$u, $a*$b/$u, $b*$a/$v, $b*$b/$v]))
          let cα ← Common.mkCache (commSemiringOfCommRing reified.rα)
          let ctx := { reified.ctx with cα, rc := ringCompute cα }
          let state ← IO.mkRef ({} : HexPolyDetMathlib.Bird.Relations.State)
          let cache ← IO.mkRef ({} : Std.HashMap Expr (Cert reified.rα))
          let result ← (HexPolyDetMathlib.Bird.Recurrence.certBirdDet
            (HexPolyDetMathlib.Bird.Relations.normalize 100 state cache)).run' {} |>.run ctx |>.run .reducible
          unless result.isZero && (← state.get).rewrites > 0 && !(← cache.get).isEmpty do
            throwError "colliding quotient products failed to cache a relation proof"
          let reified ← reifyBirdDet q(BirdDet.birdDet 2
            (#[$a/$u*($b/$v)-$a/$v*($b/$u), 0, $a, $b]))
          let cα ← Common.mkCache (commSemiringOfCommRing reified.rα)
          let ctx := { reified.ctx with cα, rc := ringCompute cα }
          let state ← IO.mkRef ({} : HexPolyDetMathlib.Bird.Relations.State)
          let cache ← IO.mkRef ({} : Std.HashMap Expr (Cert reified.rα))
          let audit : CertM reified.rα Unit := do
            let _ ← HexPolyDetMathlib.Bird.Recurrence.coeffEntry 0 0
              (HexPolyDetMathlib.Bird.Relations.normalize 100 state cache)
            let some entry := (← get).entryCache[(0, 0)]?
              | throwError "normalized entry was not cached"
            unless entry.isZero do throwError "relation-proved zero was not cached"
          audit.run' {} |>.run ctx |>.run .reducible

run_meta do
  withLocalDeclD `a q(Rat) fun a =>
    withLocalDeclD `b q(Rat) fun b =>
      withLocalDeclD `u q(Rat) fun u =>
        withLocalDeclD `v q(Rat) fun v => do
          have a : Q(Rat) := a
          have b : Q(Rat) := b
          have u : Q(Rat) := u
          have v : Q(Rat) := v
          let reified ← reifyBirdDet q(BirdDet.birdDet 1 (#[(0 : Rat)]))
          have _rα : Q(CommRing Rat) := reified.rα
          let cα ← Common.mkCache (commSemiringOfCommRing reified.rα)
          let ctx := { reified.ctx with cα, rc := ringCompute cα }
          let state ← IO.mkRef ({} : HexPolyDetMathlib.Bird.Relations.State)
          let cache ← IO.mkRef ({} : Std.HashMap Expr (Cert reified.rα))
          let audit : CertM reified.rα Unit := do
            let context ← read
            have leftExpr : Q(Rat) := q(($a/$u)*($b/$v))
            let left ← toCert <$> HexPolyDetMathlib.Bird.Scalar.eval rcℕ
              context.rc context.cα leftExpr
            unless (← HexPolyDetMathlib.Bird.Relations.independent state) do
              throwError "independent prefix was not recognized"
            let basisBefore := (← state.get).basisSize
            have rightExpr : Q(Rat) := q(($a*$b)/($u*$v))
            let right ← toCert <$> HexPolyDetMathlib.Bird.Scalar.eval rcℕ
              context.rc context.cα rightExpr
            let atoms := (← getThe Mathlib.Tactic.AtomM.State).atoms.size
            unless atoms > basisBefore do throwError "target did not grow the atom table"
            let (alignedLeft, alignedRight) ←
              HexPolyDetMathlib.Bird.Relations.align 100 state cache left right
            unless (← state.get).basisSize == atoms && (← state.get).rewrites > 0 &&
                !(← cache.get).isEmpty && alignedLeft.val.eq rcℕ context.rc alignedRight.val do
              throwError "target growth did not invalidate the factor test and align values"
          audit.run' {} |>.run ctx |>.run .reducible

run_meta do
  let now ← IO.getNumHeartbeats
  withTheReader Core.Context (fun ctx => {ctx with initHeartbeats := now, maxHeartbeats := 100000}) do
    HexPolyDetMathlib.Bird.withBudget 2000000 do
      let effective := (← readThe Core.Context).maxHeartbeats
      unless effective > 0 && effective <= 100000 do
        throwError "symbolic ceiling increased the outer heartbeat allowance"

run_meta do
  withLocalDeclD `a q(Rat) fun a =>
    withLocalDeclD `b q(Rat) fun b =>
      withLocalDeclD `c q(Rat) fun c => do
        have a : Q(Rat) := a
        have b : Q(Rat) := b
        have c : Q(Rat) := c
        let cache ← Common.mkCache q(inferInstance : CommSemiring Rat)
        let term : Q(Rat) := q(($a + $b)^8 / $c)
        let check : Mathlib.Tactic.AtomM Unit := do
          let _ ← HexPolyDetMathlib.Bird.Scalar.eval rcℕ (ringCompute cache) cache term
          let state ← getThe Mathlib.Tactic.AtomM.State
          unless state.atoms.size == 1 && state.atoms[0]! == term do
            throwError "compact quotient introduced interior atoms"
        check.run .reducible
        let inverse : Q(Rat) := q((($a + $b)^8)⁻¹)
        let rollback : Mathlib.Tactic.AtomM Unit := do
          let _ ← HexPolyDetMathlib.Bird.Scalar.eval rcℕ (ringCompute cache) cache inverse
          let state ← getThe Mathlib.Tactic.AtomM.State
          if state.atoms.contains a || state.atoms.contains b then
            throwError "refused inverse speculation leaked interior atoms"
        rollback.run .reducible

run_meta do
  withLocalDeclD `x q(Rat) fun x => do
    have x : Q(Rat) := x
    let A : Q(Matrix (Fin 2) (Fin 2) Rat) := q(!![$x, 1; 1, $x])
    let heartbeat ← HexPolyDetMathlib.Bird.compute {maxHeartbeats := 0} A
    let relation ← HexPolyDetMathlib.Bird.compute {maxRelationWork := 0} A
    match heartbeat, relation with
    | .declined a, .declined b =>
      unless (← a.toString) == "symbolic heartbeat budget exhausted (0/0) before evaluation" &&
          (← b.toString) == "relation work budget exhausted (0/0) before evaluation" do
        throwError "symbolic zero-budget diagnostics changed"
    | _, _ => throwError "zero symbolic limits did not decline"
    let hole : Q(Rat) ← mkFreshExprMVar q(Rat)
    let unresolved : Q(Matrix (Fin 2) (Fin 2) Rat) := q(!![$hole, 1; 1, $x])
    match ← HexPolyDetMathlib.Bird.compute {} unresolved with
    | .notApplicable _ => pure ()
    | _ => throwError "symbolic input metavariable was guessed"
  let natural : Q(Matrix (Fin 2) (Fin 2) Nat) := q(!![1, 2; 3, 4])
  match ← HexPolyDetMathlib.Bird.compute {} natural with
  | .notApplicable _ => pure ()
  | _ => throwError "carrier without CommRing was not declined"
