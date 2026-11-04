/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexGroebner.Elimination
import all HexGroebner.EliminationKernel
public import HexGroebner.Elimination
public import HexGroebner.EliminationProof

public section

namespace Hex.Groebner.Elimination

/-- The optimized untraced route has exactly the deterministic reference result. -/
theorem run_spec (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :
    run field limits columns reducers targets false sugars true independent =
      reference field limits columns reducers targets sugars independent := by
  unfold run attempt
  simp only [MatrixState.finish_reference]
  change (match attemptPortable field limits columns reducers targets sugars independent with
    | some result => result
    | none => if columns ≤ 65536 ∧ reducers.size+targets.size ≤ 65536 then
        reference field limits columns reducers targets sugars independent
      else reference field limits columns reducers targets sugars independent) = _
  simp only [ite_self]
  have h := attemptPortable_spec field limits columns reducers targets sugars independent
  cases hx : attemptPortable field limits columns reducers targets sugars independent with
  | none => rfl
  | some result => simpa only [hx, Option.getD_some] using h

/-- info: 'Hex.Groebner.Elimination.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_spec


end Hex.Groebner.Elimination
