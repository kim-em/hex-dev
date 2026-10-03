/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFnMathlib

public section

namespace RealClosureConsumer

open Hex Hex.OrderedFn.Infinitesimal
open scoped Hex.OrderedFn.Infinitesimal

attribute [local instance 2000] Field.toGrindField

/-- The ordinary companion umbrella exposes order at successive infinitesimal
levels. This consumes the general law rather than a named constant provider. -/
theorem successive_order (n : Nat) :
    (0 : RationalFn (RationalFn Rat)) < RationalFn.X ∧
      (RationalFn.X : RationalFn (RationalFn Rat)) <
        RationalFn.C ((RationalFn.X : RationalFn Rat) ^ n) :=
  ⟨X_pos, X_lt_pow n⟩

/-- info: 'RealClosureConsumer.successive_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms successive_order

end RealClosureConsumer
