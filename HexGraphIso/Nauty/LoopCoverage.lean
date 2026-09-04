/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert

public section

/-!
Transitive coverage for a mutable child sweep.

The nauty loops shrink their target set while they run.  A child removed
by an orbit or stored-automorphism filter need not repeat an already
visited child: it may repeat a survivor of the newly filtered set.  The
invariant here records exactly that alternative and composes it across
successive filters.  Once the live set is empty, every original child is
covered.
-/

namespace Hex.GraphIso.Nauty

/-- Every member of `all` is either covered already or has the same key as
a member of `live`.  Predicates are used for the three sets because the
search represents them in different ways at different points of a loop. -/
@[expose] def ChildCover (key : Nat → Key)
    (all done live : Nat → Prop) : Prop :=
  ∀ x, all x → done x ∨ ∃ y, live y ∧ key x = key y

/-- Initially every child can witness itself in the live set. -/
theorem ChildCover.init (key : Nat → Key) (all : Nat → Prop) :
    ChildCover key all (fun _ => False) all := by
  intro x hx
  exact Or.inr ⟨x, hx, rfl⟩

/-- One sweep step composes coverage transitively.

The step may cover an old survivor directly, or replace it by a
key-equivalent new survivor.  This single rule handles ordinary visits,
orbit skips, and both target-set filters. -/
theorem ChildCover.step {key : Nat → Key}
    {all done live done' live' : Nat → Prop}
    (h : ChildCover key all done live)
    (hs : ∀ x, live x →
      (∀ z, key z = key x → done' z) ∨
        ∃ y, live' y ∧ key x = key y)
    (hd : ∀ x, done x → done' x) :
    ChildCover key all done' live' := by
  intro x hx
  rcases h x hx with hxd | ⟨y, hyl, hxy⟩
  · exact Or.inl (hd x hxd)
  · rcases hs y hyl with hyd | ⟨z, hzl, hyz⟩
    · exact Or.inl (hyd x hxy)
    · exact Or.inr ⟨z, hzl, hxy.trans hyz⟩

/-- Enlarging the covered set preserves coverage. -/
theorem ChildCover.monoDone {key : Nat → Key}
    {all done live done' : Nat → Prop}
    (h : ChildCover key all done live)
    (hd : ∀ x, done x → done' x) :
    ChildCover key all done' live :=
  h.step (fun x hx => Or.inr ⟨x, hx, rfl⟩) hd

/-- Filtering the live set preserves coverage when every removed survivor
repeats a survivor of the new set. -/
theorem ChildCover.filter {key : Nat → Key}
    {all done live live' : Nat → Prop}
    (h : ChildCover key all done live)
    (hs : ∀ x, live x → ∃ y, live' y ∧ key x = key y) :
    ChildCover key all done live' :=
  h.step (fun x hx => Or.inr (hs x hx)) (fun _ hx => hx)

/-- When no live survivor remains, every original child is covered. -/
theorem ChildCover.finish {key : Nat → Key}
    {all done live : Nat → Prop}
    (h : ChildCover key all done live)
    (hempty : ∀ x, ¬ live x) :
    ∀ x, all x → done x := by
  intro x hx
  rcases h x hx with hxd | ⟨y, hyl, _⟩
  · exact hxd
  · exact absurd hyl (hempty y)

/-- Coverage transfers a common upper bound from covered children to all
original children. -/
theorem ChildCover.bound {key : Nat → Key}
    {all done live : Nat → Prop} {b : Key}
    (h : ChildCover key all done live)
    (hempty : ∀ x, ¬ live x)
    (hle : ∀ x, done x → keyLe (key x) b) :
    ∀ x, all x → keyLe (key x) b := by
  intro x hx
  exact hle x (h.finish hempty x hx)

end Hex.GraphIso.Nauty
