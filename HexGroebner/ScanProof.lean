/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.NativeScan
public import Std.Do
meta import Std.Tactic.Do

public section

namespace Hex.Groebner.Native.Scan

set_option maxHeartbeats 1000000 in
-- The pinned vcgen does not infer this pure Id program; mvcgen supports it.
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem events_spec (modulus : UInt64) (slots : ByteArray)
    (pivots : Array Native.Scan.Pivot) (initial : Native.Scan.State)
    (quantum workLimit traceLimit : Nat) :
    Std.Do.Triple (m := Id)
      (Native.Scan.portable modulus slots pivots initial quantum workLimit traceLimit false)
      ⌜True⌝ (PostCond.noThrow fun out => ⌜out.events = #[]⌝) := by
  unfold Native.Scan.portable
  dsimp only [Id.run]
  mvcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun r _ => ⌜r.events = #[]⌝)
      (onContinue := fun _ out => ⌜out.events = #[]⌝)
  all_goals simp_all

theorem untraced_events (modulus : UInt64) (slots : ByteArray)
    (pivots : Array Native.Scan.Pivot) (initial : Native.Scan.State)
    (quantum workLimit traceLimit : Nat) :
    (Native.Scan.portable modulus slots pivots initial quantum workLimit traceLimit false).events = #[] := by
  exact (events_spec modulus slots pivots initial quantum workLimit traceLimit) True.intro


end Hex.Groebner.Native.Scan
