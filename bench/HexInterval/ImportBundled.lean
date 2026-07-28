/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.ReplayBundled

public section

/-! Incremental-import canary for the bundled replay proof. -/

example : Hex.Interval.Experiment.replayBundledWork 433 = 5801550 :=
  Hex.Interval.Experiment.replayBundled433
