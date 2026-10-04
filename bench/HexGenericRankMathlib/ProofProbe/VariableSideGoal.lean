/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib
public import Mathlib.Algebra.Field.ZMod

public section


open Matrix

theorem result (x : ℚ) (h : True → x ≠ 0) : (!![x]).rank = 1 := by
  rank
  guard_target = x ≠ 0
  exact h trivial

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
