/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.Elimination
public import HexGroebner.Elimination
public import HexGroebner.ScanProof
public import Std.Do
meta import Std.Tactic.Do

public section

namespace Hex.Groebner.Native.Scan

/-- Untraced scans ignore the trace allowance in every field, including
errors, suspended states, charged work and completed reduction counters. -/
theorem untraced_limit (modulus : UInt64) (slots : ByteArray) (pivots : Array Pivot)
    (initial : State) (quantum workLimit trace₁ trace₂ : Nat) :
    portable modulus slots pivots initial quantum workLimit trace₁ false =
      portable modulus slots pivots initial quantum workLimit trace₂ false := by rfl

set_option maxHeartbeats 1000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem trace_status_spec (modulus : UInt64) (slots : ByteArray) (pivots : Array Pivot)
    (initial : State) (quantum workLimit traceLimit : Nat) :
    Std.Do.Triple (m := Id) (portable modulus slots pivots initial quantum workLimit traceLimit false)
      ⌜True⌝ (PostCond.noThrow fun out => ⌜out.status ≠ 3 ∧ out.traceNodes = 0⌝) := by
  unfold portable
  dsimp only [Id.run]
  mvcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun out _ => ⌜out.status ≠ 3 ∧ out.traceNodes = 0⌝)
      (onContinue := fun _ out => ⌜out.status ≠ 3 ∧ out.traceNodes = 0⌝)
  all_goals simp_all

/-- A scan without provenance never consumes trace nodes or exhausts them. -/
theorem untraced_status (modulus : UInt64) (slots : ByteArray) (pivots : Array Pivot)
    (initial : State) (quantum workLimit traceLimit : Nat) :
    let out := portable modulus slots pivots initial quantum workLimit traceLimit false
    out.status ≠ 3 ∧ out.traceNodes = 0 :=
  (trace_status_spec modulus slots pivots initial quantum workLimit traceLimit) True.intro

end Hex.Groebner.Native.Scan

namespace Hex.Groebner

open Matrix

/-- Disabling provenance preserves the trace and carries no derivation node. -/
private theorem record_untraced (limits : MatrixLimits) (trace : Array RowOp) (op : RowOp) :
    record limits false trace op = pure (trace,none) := by rfl

set_option maxHeartbeats 1000000 in
set_option linter.deprecated.syntax false in
open Std.Do in
private theorem scan_trace_spec (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (slots : ByteArray) (pivots : Array Pivot) (nativePivots : Array Native.Scan.Pivot)
    (first : Nat) (scan : Scan) :
    Std.Do.Triple (m := Matrix.Work) (ps := .except MatrixError (.arg MatrixStats .pure))
      (nativeScan field limits columns slots pivots nativePivots first scan false)
      (fun (_ : MatrixStats) => ⌜True⌝)
      (fun out (_ : MatrixStats) => ⌜out.trace = scan.trace ∧ out.node = scan.node⌝,
        fun _ (_ : MatrixStats) => ⌜True⌝,PUnit.unit) := by
  unfold nativeScan Matrix.work Matrix.charge
  simp only [Native.Scan.transition,Native.Scan.untraced_events]
  mvcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun out _ (_ : MatrixStats) => ⌜out.trace = scan.trace ∧ out.node = scan.node⌝)
      (onContinue := fun _ out (_ : MatrixStats) => ⌜out.2.1 = scan.trace ∧ out.2.2 = scan.node⌝)
      (onExcept := (fun _ (_ : MatrixStats) => ⌜True⌝,PUnit.unit))
  · (fun ⟨_,out⟩ (_ : MatrixStats) => ⌜out.1 = scan.trace ∧ out.2 = scan.node⌝,
      fun _ (_ : MatrixStats) => ⌜True⌝,PUnit.unit)
  all_goals simp_all [takeDense]
  all_goals grind [List.nil_eq_append_iff]

/-- info: 'Hex.Groebner.Native.Scan.untraced_limit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Native.Scan.untraced_limit
/-- info: 'Hex.Groebner.Native.Scan.untraced_status' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Native.Scan.untraced_status

end Hex.Groebner
