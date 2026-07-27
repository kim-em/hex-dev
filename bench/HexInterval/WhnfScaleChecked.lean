/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import Lean
public import HexInterval.Experiment.Scale

public section

/-!
# Forced kernel reduction for centered scaling workloads

Each line reports only the `Lean.Kernel.whnf` call for
`decide (workload.accepts = true)`. Optional workload builders are reduced to
their outer `some` before timing and cause the module build to fail if a
committed ladder point is invalid.
-/

open Lean Meta
open Hex.Interval.Experiment.Scale

/-- Extract a statically generated workload without silently substituting a
fallback if its builder rejects the requested ladder point. -/
private meta def requireSome (family : String) (size : Nat)
    (candidate : Expr) : MetaM Expr := do
  match Lean.Kernel.whnf (← getEnv) {} candidate with
  | .ok result =>
      if result.getAppFn.isConstOf ``Option.some then
        let args := result.getAppArgs
        if h : 1 < args.size then
          return args[1]
        else
          throwError "{family} size {size} reduced to malformed Option.some: {result}"
      else
        throwError "{family} size {size} is not a valid scaling workload: {result}"
  | .error _ =>
      throwError "{family} size {size} failed while constructing its scaling workload"

/-- Reduce a total workload builder to its outer constructor before timing. -/
private meta def requireWorkload (family : String) (size : Nat)
    (candidate : Expr) : MetaM Expr := do
  match Lean.Kernel.whnf (← getEnv) {} candidate with
  | .ok result =>
      unless result.getAppFn.isConstOf ``Workload.mk do
        throwError "{family} size {size} did not reduce to a workload: {result}"
      return result
  | .error _ =>
      throwError "{family} size {size} failed while constructing its scaling workload"

/-- Time ordinary kernel reduction of one workload's acceptance decision and
emit a stable, machine-readable result line. -/
private meta def timeAccept (family : String) (size : Nat)
    (workload : Expr) : MetaM Unit := do
  let accepted := mkApp (mkConst ``Workload.accepts) workload
  let proposition ← mkEq accepted (mkConst ``Bool.true)
  let decision ← mkDecide proposition
  let start ← IO.monoNanosNow
  match Lean.Kernel.whnf (← getEnv) {} decision with
  | .ok result =>
      let stop ← IO.monoNanosNow
      logInfo m!"__HEX_SCALE_WHNF__ family={family} size={size} nanos={stop - start}"
      unless result.isConstOf ``Bool.true do
        throwError
          "{family} size {size} did not kernel-reduce to true; stuck at {result}"
  | .error _ =>
      let stop ← IO.monoNanosNow
      logInfo m!"__HEX_SCALE_WHNF__ family={family} size={size} nanos={stop - start}"
      throwError "{family} size {size} failed during kernel reduction"

/-- Construct one optional workload and time its acceptance reduction. -/
private meta def timeOptional (family : String) (builder : Name)
    (size : Nat) : MetaM Unit := do
  let candidate := mkApp (mkConst builder) (mkNatLit size)
  let workload ← requireWorkload family size (← requireSome family size candidate)
  timeAccept family size workload

/-- Construct one total workload and time its acceptance reduction. -/
private meta def timeTotal (family : String) (builder : Name)
    (size : Nat) : MetaM Unit := do
  let candidate := mkApp (mkConst builder) (mkNatLit size)
  let workload ← requireWorkload family size candidate
  timeAccept family size workload

run_meta do
  for size in [9, 20, 50, 100, 500, 2000] do
    timeOptional "dead" ``deadNodes? size
  for size in [1, 11, 41, 91, 491] do
    timeOptional "adjacent" ``adjacent? size
  for size in [1, 11, 41, 91, 491] do
    timeOptional "far" ``far? size
  for size in [0, 10, 40, 90, 490] do
    timeTotal "sourcePad" ``sourcePad size
