/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Matrix
public import Std.Do
meta import Std.Tactic.Do

public section

namespace Hex.Groebner.Matrix

set_option linter.deprecated.syntax false in
open Std.Do in
private theorem zeros_spec (size : Nat) :
    Std.Do.Triple (m := Id) (zeros size) ⌜True⌝
      (PostCond.noThrow fun bytes => ⌜bytes.size = size⌝) := by
  unfold zeros
  dsimp only [Id.run]
  mvcgen invariants
  · ⟨fun ⟨cursor,bytes⟩ => ⌜bytes.size = cursor.prefix.length⌝,ExceptConds.false⟩
  all_goals simp_all

/-- The portable workspace initializer allocates exactly the requested logical
number of bytes, including the empty buffer. -/
@[simp] theorem zeros_size (size : Nat) : (zeros size).size = size :=
  (zeros_spec size) True.intro

/-- info: 'Hex.Groebner.Matrix.zeros_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zeros_size

end Hex.Groebner.Matrix
