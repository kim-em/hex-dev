/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.ReplayChecked

public section

/-! Incremental-import canary for the externally checked replay proof. -/

example : Hex.Interval.Experiment.replayCheckedWork 433 = 5801550 :=
  Hex.Interval.Experiment.replayChecked433
