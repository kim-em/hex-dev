/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Reference

public section

/-!
Resource limits and the bounded permutation check.

The public canonical-form operations live in `HexGraphIso.Ops`,
backed by the certificate-checked nauty-semantic canonicalization;
this module keeps the limit structures and the replay-bounded
permutation check they and the tactic layer share.
-/

namespace Hex.GraphIso

variable {n k : Nat}

/-! # Bounded operations -/

/-- Limits on canonical search. `maxNodes` counts every refined partition
visited, including the root; `maxCertNodes` counts every proof-rule record
emitted. -/
structure SearchLimits where
  /-- The largest number of search nodes visited before exhaustion. -/
  maxNodes : Nat := 100000
  /-- The largest number of certificate records emitted before
  exhaustion. -/
  maxCertNodes : Nat := 100000
deriving DecidableEq

/-- Limits on certificate and permutation replay. -/
structure ReplayLimits where
  /-- The largest number of checker steps performed before exhaustion. One
  step is charged for each proof-rule record, vertex or permutation entry
  inspected, and dense adjacency word inspected. -/
  maxCheckerSteps : Nat := 5000000
deriving DecidableEq

/-- The node charge of the conservative pre-check: one node per
enumerated candidate labelling. -/
@[expose] def searchCost (n : Nat) : Nat :=
  n ^ n

/-- The step charge of one permutation check: each vertex colour and each
vertex pair inspected. -/
@[expose] def checkCost (n : Nat) : Nat :=
  n + n * n

/-- Bounded isomorphism check. `none` is replay exhaustion. -/
@[expose] def checkIso? (replay : ReplayLimits) (G H : Colored n k)
    (p : Perm n) : Option Bool :=
  if checkCost n ≤ replay.maxCheckerSteps then some (checkIso G H p) else none

theorem checkIso?_some {replay : ReplayLimits} {G H : Colored n k}
    {p : Perm n} {b : Bool} (h : checkIso? replay G H p = some b) :
    b = true ↔ IsIso G H p := by
  rw [checkIso?] at h
  split at h
  · rw [← Option.some.inj h]
    exact checkIso_iff G H p
  · simp at h

end Hex.GraphIso
