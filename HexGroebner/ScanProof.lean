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
  unfold Native.Scan.portable Native.Scan.portableWith
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


set_option maxHeartbeats 1000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem bounds_spec (modulus : UInt64) (slots : ByteArray)
    (pivots : Array Native.Scan.Pivot) (initial : Native.Scan.State)
    (quantum workLimit traceLimit : Nat) (provenance : Bool)
    (hlast : initial.last < max 1 (initial.dense.size / Native.width modulus.toNat))
    (hleading : initial.leading ≤ initial.dense.size / Native.width modulus.toNat) :
    Std.Do.Triple (m := Id)
      (Native.Scan.portable modulus slots pivots initial quantum workLimit traceLimit provenance)
      ⌜True⌝ (PostCond.noThrow fun out =>
        ⌜out.state.dense.size = initial.dense.size ∧
          out.state.last < max 1 (initial.dense.size / Native.width modulus.toNat) ∧
          out.state.leading ≤ initial.dense.size / Native.width modulus.toNat⌝) := by
  unfold Native.Scan.portable Native.Scan.portableWith
  dsimp only [Id.run]
  mvcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun out _ => ⌜out.state.dense.size = initial.dense.size ∧
        out.state.last < max 1 (initial.dense.size / Native.width modulus.toNat) ∧
        out.state.leading ≤ initial.dense.size / Native.width modulus.toNat⌝)
      (onContinue := fun _ out => ⌜out.state.dense.size = initial.dense.size ∧
        out.state.last < max 1 (initial.dense.size / Native.width modulus.toNat) ∧
        out.state.leading ≤ initial.dense.size / Native.width modulus.toNat⌝)
  all_goals simp_all [Native.size_write, Nat.max_lt]
  all_goals first | omega | (split <;> simp_all <;> omega)

/-- Scanning preserves its dense geometry and column bounds, even on errors.
A zero-column workspace has the conventional inactive last index zero. -/
theorem bounds (modulus : UInt64) (slots : ByteArray)
    (pivots : Array Native.Scan.Pivot) (initial : Native.Scan.State)
    (quantum workLimit traceLimit : Nat) (provenance : Bool)
    (hlast : initial.last < max 1 (initial.dense.size / Native.width modulus.toNat))
    (hleading : initial.leading ≤ initial.dense.size / Native.width modulus.toNat) :
    let out := Native.Scan.portable modulus slots pivots initial quantum workLimit traceLimit provenance
    out.state.dense.size = initial.dense.size ∧
      out.state.last < max 1 (initial.dense.size / Native.width modulus.toNat) ∧
      out.state.leading ≤ initial.dense.size / Native.width modulus.toNat :=
  (bounds_spec modulus slots pivots initial quantum workLimit traceLimit provenance hlast hleading) True.intro


/-- Every non-malformed scan result has bounded geometry, without requiring
an external validity witness for its initial state. -/
theorem bounds_of_status (modulus : UInt64) (slots : ByteArray)
    (pivots : Array Native.Scan.Pivot) (initial : Native.Scan.State)
    (quantum workLimit traceLimit : Nat) (provenance : Bool)
    (hstatus : (portable modulus slots pivots initial quantum workLimit traceLimit provenance).status ≠ 4) :
    let out := portable modulus slots pivots initial quantum workLimit traceLimit provenance
    out.state.dense.size = initial.dense.size ∧
      out.state.last < max 1 (initial.dense.size / Native.width modulus.toNat) ∧
      out.state.leading ≤ initial.dense.size / Native.width modulus.toNat := by
  by_cases hlast : initial.last < max 1 (initial.dense.size / Native.width modulus.toNat)
  · by_cases hleading : initial.leading ≤ initial.dense.size / Native.width modulus.toNat
    · exact bounds modulus slots pivots initial quantum workLimit traceLimit provenance hlast hleading
    · have bad : initial.dense.size / Native.width modulus.toNat < initial.leading := by omega
      simp [portable,portableWith,bad] at hstatus
  · by_cases hzero : initial.dense.size / Native.width modulus.toNat = 0
    · have bad : initial.last ≠ 0 := by omega
      simp [portable,portableWith,hzero,bad] at hstatus
    · have bad : initial.dense.size / Native.width modulus.toNat ≤ initial.last := by omega
      simp [portable,portableWith,hzero,bad] at hstatus


/-- info: 'Hex.Groebner.Native.size_write' depends on axioms: [propext] -/
#guard_msgs in #print axioms Native.size_write

/-- info: 'Hex.Groebner.Native.Scan.bounds_of_status' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bounds_of_status


end Hex.Groebner.Native.Scan
