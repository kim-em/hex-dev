/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.SineProofConformance
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Tactic-frontend canary for arbitrary-function interval search

`interval_sine` runs the opaque live planner at elaboration time, then emits
the already transparent, kernel-checked proof chain for that accepted trace.
It is deliberately narrow: automatic quotation of an arbitrary returned trace
is the next experiment.  The canary establishes that compiled planning can be
kept outside the trusted proof while an ordinary tactic closes the caller's
goal.
-/

namespace Hex.IntervalMathlib.SineTacticConformance

open Lean Elab Tactic Meta
open SineSignConformance SineProofConformance

/-- Find two local hypotheses accepted by the emitted sine theorem and build
an application whose inferred target is definitionally the caller's goal. -/
private meta def proveSine (target : Expr) : MetaM Expr := do
  unless transported?.isSome do
    throwError "interval_sine: compiled interval search failed"
  let context <- getLCtx
  for first in context do
    unless first.isImplementationDetail do
      for second in context do
        unless second.isImplementationDetail do
          try
            let proof <- mkAppM ``emittedSineTheorem
              #[mkFVar first.fvarId, mkFVar second.fvarId]
            if <- isDefEq (← inferType proof) target then
              return proof
          catch _ => pure ()
  throwError
    "interval_sine: expected hypotheses matching `0 ≤ x` and `x ≤ 1` and goal `Real.sin (-x) ≤ 0`"

/-- Run the real-sine interval planner and emit its kernel-checked proof. -/
syntax (name := intervalSineTac) "interval_sine" : tactic

@[tactic intervalSineTac] meta def evalIntervalSine : Tactic := fun stx => do
  match stx with
  | `(tactic| interval_sine) =>
      let goal <- getMainGoal
      goal.withContext do
        let target <- instantiateMVars (← goal.getType)
        let proof <- proveSine target
        goal.assign proof
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

example {x : ℝ} (upper : x ≤ 1) (lower : 0 ≤ x) : Real.sin (-x) ≤ 0 := by
  interval_sine

example {x : ℝ} (_upper : x ≤ 1) (_lower : 0 ≤ x) : True := by
  fail_if_success interval_sine
  trivial

end Hex.IntervalMathlib.SineTacticConformance
