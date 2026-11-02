/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.NativeGather
public import Std.Do
meta import Std.Tactic.Do

public section

namespace Hex.Groebner.Native.Gather

set_option maxHeartbeats 1000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem size_spec (modulus : UInt64) (initial : State)
    (stop quantum entriesLimit bytesLimit workLimit : Nat) (factor : UInt64) :
    Std.Do.Triple (m := Id)
      (portable modulus initial stop quantum entriesLimit bytesLimit workLimit factor)
      ⌜True⌝ (PostCond.noThrow fun out => ⌜out.state.dense.size = initial.dense.size⌝) := by
  unfold portable
  dsimp only [Id.run]
  mvcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun out _ => ⌜out.state.dense.size = initial.dense.size⌝)
      (onContinue := fun _ out => ⌜out.state.dense.size = initial.dense.size⌝)
  all_goals simp_all

/-- Gathering preserves the dense buffer's length on completion, suspension
and every rejected prefix; only values and sparse output buffers change. -/
theorem dense_size (modulus : UInt64) (initial : State)
    (stop quantum entriesLimit bytesLimit workLimit : Nat) (factor : UInt64) :
    (portable modulus initial stop quantum entriesLimit bytesLimit workLimit factor).state.dense.size =
      initial.dense.size :=
  (size_spec modulus initial stop quantum entriesLimit bytesLimit workLimit factor) True.intro

/-- info: 'Hex.Groebner.Native.Gather.dense_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dense_size

end Hex.Groebner.Native.Gather
