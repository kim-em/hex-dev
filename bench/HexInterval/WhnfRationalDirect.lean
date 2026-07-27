/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import Lean
public import HexInterval.Experiment.Rational

public section

/-! Downstream `Lean.Kernel.whnf` canary for exposed rational replay. -/

open Lean Meta
open Hex.Interval.Experiment.Rational

run_meta do
  let lhs := mkApp (mkConst ``directFold) (mkNatLit 433)
  let rhs := mkApp2 (mkConst ``Rat.divInt) (mkIntLit 1) (mkIntLit 1)
  let proposition ← mkEq lhs rhs
  let decision ← mkDecide proposition
  let start ← IO.monoNanosNow
  match Lean.Kernel.whnf (← getEnv) {} decision with
  | .ok result =>
      let stop ← IO.monoNanosNow
      logInfo m!"__HEX_WHNF_NANOS__={stop - start}"
      unless result.isConstOf ``Bool.true do
        throwError "exposed rational replay did not kernel-reduce to true; stuck at {result}"
  | .error _ =>
      let stop ← IO.monoNanosNow
      logInfo m!"__HEX_WHNF_NANOS__={stop - start}"
      throwError "exposed rational replay failed during kernel reduction"
