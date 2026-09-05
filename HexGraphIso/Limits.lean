/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Iso

public section

/-!
Replay limits and the bounded permutation check.

The public canonical-form operations live in `HexGraphIso.Ops`,
backed by the certificate-checked nauty-semantic canonicalization.
This module keeps the replay limit structure and the bounded
permutation check that the tactic layer shares with them.
-/

namespace Hex.GraphIso

variable {n k : Nat}

/-- Limits on certificate and permutation replay. -/
structure ReplayLimits where
  /-- The largest number of checker steps performed before exhaustion. One
  step is charged for each proof-rule record, vertex or permutation entry
  inspected, and dense adjacency word inspected. -/
  maxKernelSteps : Nat := 5000000
deriving DecidableEq

/-- The step charge of one permutation check: each vertex colour and each
vertex pair inspected. -/
@[expose] def checkCost (n : Nat) : Nat :=
  n + n * n

/-- Bounded isomorphism check. `none` is replay exhaustion. -/
@[expose] def checkIso? (replay : ReplayLimits) (G H : Colored n k)
    (p : Perm n) : Option Bool :=
  if checkCost n ≤ replay.maxKernelSteps then some (checkIso G H p) else none

theorem checkIso?_some {replay : ReplayLimits} {G H : Colored n k}
    {p : Perm n} {b : Bool} (h : checkIso? replay G H p = some b) :
    b = true ↔ IsIso G H p := by
  rw [checkIso?] at h
  split at h
  · rw [← Option.some.inj h]
    exact checkIso_iff G H p
  · simp at h

end Hex.GraphIso
