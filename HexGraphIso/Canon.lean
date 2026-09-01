/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Reference

public section

/-!
Public canonical-form operations.

`canonicalize` is total: it returns the canonical form together with the
label producing it. `findIso` composes the two canonical labels into a
forward transporter when the canonical forms agree. The bounded surface
separates search limits from replay limits and returns `none` on
exhaustion; exhaustion is never evidence of non-isomorphism.

The operations are currently backed by the reference implementation. The
first release requires switching this backing to the nauty-compatible
individualization-refinement implementation without changing any theorem
stated here; until then the resource accounting below charges the
reference enumeration.
-/

namespace Hex.GraphIso

variable {n k : Nat}

/-- Compute the canonical form of a coloured graph together with the label
producing it. Total; worst-case cost is factorial. -/
@[expose] def canonicalize (G : Colored n k) : CanonResult n k :=
  Reference.canonicalize G

/-- The canonical form of a coloured graph. -/
@[expose] def canon (G : Colored n k) : Colored n k :=
  (canonicalize G).form

/-- The label producing the canonical form. -/
@[expose] def label (G : Colored n k) : Label n :=
  (canonicalize G).label

/-- Relabelling by the canonical label produces the canonical form. -/
theorem relabel_label (G : Colored n k) : G.relabel (label G) = canon G :=
  Reference.relabel_label G

/-- The canonical form has contiguous colour cells in their original
order. -/
theorem colorSorted_canon (G : Colored n k) : ColorSorted (canon G) :=
  Reference.colorSorted_canon G

/-- Every coloured graph is isomorphic to its canonical form. -/
theorem canon_iso (G : Colored n k) : Isomorphic G (canon G) :=
  Reference.canon_iso G

/-- Isomorphic coloured graphs have equal canonical forms. -/
theorem canon_invariant {G H : Colored n k} (h : Isomorphic G H) :
    canon G = canon H :=
  Reference.canon_invariant h

/-- Two coloured graphs are isomorphic exactly when their canonical forms
are equal. The biconditional compares canonical coloured graphs, not the
labels: label arrays refer to different input vertex names and generally
differ for isomorphic inputs. -/
theorem iso_iff_canon_eq (G : Colored n k) (H : Colored n k) :
    Isomorphic G H ↔ canon G = canon H :=
  Reference.iso_iff_canon_eq G H

/-! # Isomorphism search -/

/-- Find one isomorphism from `G` to `H` when one exists: the forward
transporter through the two canonical forms, the canonical label of `H`
composed with the inverse of the canonical label of `G` (in forward
permutation convention). -/
@[expose] def findIso (G H : Colored n k) : Option (Perm n) :=
  if canon G = canon H then
    some (((label H).toPerm.inv).comp ((label G).toPerm))
  else
    none

/-- Boolean isomorphism decision. -/
@[expose] def isIso (G H : Colored n k) : Bool :=
  (findIso G H).isSome

theorem findIso_sound {G H : Colored n k} {p : Perm n}
    (h : findIso G H = some p) : IsIso G H p := by
  rw [findIso] at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    have h1 : IsIso G (canon G) (label G).toPerm := by
      rw [← relabel_label G]
      exact isIso_relabel ..
    have h2 : IsIso H (canon G) (label H).toPerm := by
      rw [hc, ← relabel_label H]
      exact isIso_relabel ..
    exact h1.trans h2.symm
  · simp at h

theorem findIso_isSome_iff (G H : Colored n k) :
    (findIso G H).isSome = true ↔ Isomorphic G H := by
  rw [findIso]
  split
  · simpa using (iso_iff_canon_eq G H).mpr (by assumption)
  · rename_i hc
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun h => hc ((iso_iff_canon_eq G H).mp h)

theorem isIso_eq_true_iff (G H : Colored n k) :
    isIso G H = true ↔ Isomorphic G H :=
  findIso_isSome_iff G H

theorem isIso_eq_false_iff (G H : Colored n k) :
    isIso G H = false ↔ ¬Isomorphic G H := by
  rw [← isIso_eq_true_iff]
  rcases h : isIso G H <;> simp

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

/-- The node charge of the current (reference) search backing: one node per
enumerated candidate labelling. -/
@[expose] def searchCost (n : Nat) : Nat :=
  n ^ n

/-- The step charge of one permutation check: each vertex colour and each
vertex pair inspected. -/
@[expose] def checkCost (n : Nat) : Nat :=
  n + n * n

/-- Bounded isomorphism search. Outer `none` is exhaustion; `some none` is
a completed non-isomorphism result; `some (some p)` is a found
transporter. Exhaustion is not evidence of non-isomorphism. -/
@[expose] def findIso? (search : SearchLimits) (G H : Colored n k) :
    Option (Option (Perm n)) :=
  if searchCost n ≤ search.maxNodes then some (findIso G H) else none

/-- Bounded isomorphism check. `none` is replay exhaustion. -/
@[expose] def checkIso? (replay : ReplayLimits) (G H : Colored n k)
    (p : Perm n) : Option Bool :=
  if checkCost n ≤ replay.maxCheckerSteps then some (checkIso G H p) else none

/-- Bounded canonicalization. `none` is exhaustion. -/
@[expose] def canon? (search : SearchLimits) (replay : ReplayLimits)
    (G : Colored n k) : Option (CanonResult n k) :=
  if searchCost n ≤ search.maxNodes then some (canonicalize G) else none

namespace FindIso

theorem some_sound (search : SearchLimits) (G H : Colored n k) (p : Perm n)
    (h : findIso? search G H = some (some p)) : IsIso G H p := by
  rw [findIso?] at h
  split at h
  · exact findIso_sound (Option.some.inj h)
  · simp at h

theorem none_sound (search : SearchLimits) (G H : Colored n k)
    (h : findIso? search G H = some none) : ¬Isomorphic G H := by
  rw [findIso?] at h
  split at h
  · intro hiso
    have := (findIso_isSome_iff G H).mpr hiso
    rw [Option.some.inj h] at this
    simp at this
  · simp at h

end FindIso

theorem checkIso?_some {replay : ReplayLimits} {G H : Colored n k}
    {p : Perm n} {b : Bool} (h : checkIso? replay G H p = some b) :
    b = true ↔ IsIso G H p := by
  rw [checkIso?] at h
  split at h
  · rw [← Option.some.inj h]
    exact checkIso_iff G H p
  · simp at h

theorem canon?_eq_some {search : SearchLimits} {replay : ReplayLimits}
    {G : Colored n k} {result : CanonResult n k}
    (h : canon? search replay G = some result) :
    result.form = canon G ∧ G.relabel result.label = result.form := by
  rw [canon?] at h
  split at h
  · rw [← Option.some.inj h]
    exact ⟨rfl, relabel_label G⟩
  · simp at h

end Hex.GraphIso
