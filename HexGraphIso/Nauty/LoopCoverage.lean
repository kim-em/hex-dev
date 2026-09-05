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
a no-larger member of `live`.  The decreasing rank lets successive
automorphism filters compose even when a new carrier lands outside the
already-filtered set. -/
@[expose] def ChildCover (key : Nat → Key n) (rank : Nat → Nat)
    (all done live : Nat → Prop) : Prop :=
  ∀ x, all x → done x ∨
    ∃ y, live y ∧ key x = key y ∧ rank y ≤ rank x

/-- Initially every child can witness itself in the live set. -/
theorem ChildCover.init (key : Nat → Key n) (rank : Nat → Nat)
    (all : Nat → Prop) :
    ChildCover key rank all (fun _ => False) all := by
  intro x hx
  exact Or.inr ⟨x, hx, rfl, Nat.le_refl _⟩

/-- One sweep step composes coverage transitively. -/
theorem ChildCover.step {key : Nat → Key n} {rank : Nat → Nat}
    {all done live done' live' : Nat → Prop}
    (h : ChildCover key rank all done live)
    (hs : ∀ x, live x →
      (∀ z, key z = key x → done' z) ∨
        ∃ y, live' y ∧ key x = key y ∧ rank y ≤ rank x)
    (hd : ∀ x, done x → done' x) :
    ChildCover key rank all done' live' := by
  intro x hx
  rcases h x hx with hxd | ⟨y, hyl, hxy, hyr⟩
  · exact Or.inl (hd x hxd)
  · rcases hs y hyl with hyd | ⟨z, hzl, hyz, hzr⟩
    · exact Or.inl (hyd x hxy)
    · exact Or.inr ⟨z, hzl, hxy.trans hyz, Nat.le_trans hzr hyr⟩

/-- Enlarging the covered set preserves coverage. -/
theorem ChildCover.monoDone {key : Nat → Key n} {rank : Nat → Nat}
    {all done live done' : Nat → Prop}
    (h : ChildCover key rank all done live)
    (hd : ∀ x, done x → done' x) :
    ChildCover key rank all done' live :=
  h.step (fun x hx => Or.inr ⟨x, hx, rfl, Nat.le_refl _⟩) hd

/-- Filtering the live set preserves coverage when every removed survivor
repeats a no-larger survivor of the new set. -/
theorem ChildCover.filter {key : Nat → Key n} {rank : Nat → Nat}
    {all done live live' : Nat → Prop}
    (h : ChildCover key rank all done live)
    (hs : ∀ x, live x →
      ∃ y, live' y ∧ key x = key y ∧ rank y ≤ rank x) :
    ChildCover key rank all done live' :=
  h.step (fun x hx => Or.inr (hs x hx)) (fun _ hx => hx)

/-- Resolving one filtered survivor may revisit the old coverage relation.
Strict rank descent at every newly removed live vertex makes this process
well founded. -/
theorem ChildCover.resolve {key : Nat → Key n} {rank : Nat → Nat}
    {all done live live' : Nat → Prop}
    (h : ChildCover key rank all done live)
    (hdone : ∀ x y, key x = key y → done y → done x)
    (hstep : ∀ x, live x → live' x ∨
      ∃ y, all y ∧ key x = key y ∧ rank y < rank x) :
    ∀ x, live x → done x ∨
      ∃ y, live' y ∧ key x = key y ∧ rank y ≤ rank x
  | x, hx => by
    rcases hstep x hx with hxl | ⟨y, hya, hxy, hyr⟩
    · exact Or.inr ⟨x, hxl, rfl, Nat.le_refl _⟩
    · rcases h y hya with hyd | ⟨z, hzl, hyz, hzr⟩
      · exact Or.inl (hdone x y hxy hyd)
      · have hzx : rank z < rank x := Nat.lt_of_le_of_lt hzr hyr
        rcases ChildCover.resolve h hdone hstep z hzl with hzd |
            ⟨w, hwl, hzw, hwr⟩
        · exact Or.inl (hdone x z (hxy.trans hyz) hzd)
        · exact Or.inr ⟨w, hwl, (hxy.trans hyz).trans hzw,
            Nat.le_trans hwr (Nat.le_of_lt hzx)⟩
  termination_by x => rank x

/-- A descending filter preserves ranked coverage even when a carrier
lands outside the old live set. -/
theorem ChildCover.filterDesc {key : Nat → Key n} {rank : Nat → Nat}
    {all done live live' : Nat → Prop}
    (h : ChildCover key rank all done live)
    (hdone : ∀ x y, key x = key y → done y → done x)
    (hstep : ∀ x, live x → live' x ∨
      ∃ y, all y ∧ key x = key y ∧ rank y < rank x) :
    ChildCover key rank all done live' := by
  intro x hx
  rcases h x hx with hxd | ⟨y, hyl, hxy, hyr⟩
  · exact Or.inl hxd
  · rcases ChildCover.resolve h hdone hstep y hyl with hyd |
        ⟨z, hzl, hyz, hzr⟩
    · exact Or.inl (hdone x y hxy hyd)
    · exact Or.inr ⟨z, hzl, hxy.trans hyz, Nat.le_trans hzr hyr⟩

/-- When no live survivor remains, every original child is covered. -/
theorem ChildCover.finish {key : Nat → Key n} {rank : Nat → Nat}
    {all done live : Nat → Prop}
    (h : ChildCover key rank all done live)
    (hempty : ∀ x, ¬ live x) :
    ∀ x, all x → done x := by
  intro x hx
  rcases h x hx with hxd | ⟨y, hyl, _, _⟩
  · exact hxd
  · exact absurd hyl (hempty y)

/-- Coverage transfers a common upper bound from covered children to all
original children. -/
theorem ChildCover.bound {key : Nat → Key n} {rank : Nat → Nat}
    {all done live : Nat → Prop} {b : Key n}
    (h : ChildCover key rank all done live)
    (hempty : ∀ x, ¬ live x)
    (hle : ∀ x, done x → keyLe (key x) b) :
    ∀ x, all x → keyLe (key x) b := by
  intro x hx
  exact hle x (h.finish hempty x hx)

/-- Coverage transfers a common upper bound when both absorbed children
and the surviving live representatives lie below it.  This is the form
used by a frozen comparison unwind: the existing ledger handles the
visited prefix, while the frozen code verdict handles the abandoned
suffix. -/
theorem ChildCover.boundLive {key : Nat → Key n} {rank : Nat → Nat}
    {all done live : Nat → Prop} {b : Key n}
    (h : ChildCover key rank all done live)
    (hdone : ∀ x, done x → keyLe (key x) b)
    (hlive : ∀ x, live x → keyLe (key x) b) :
    ∀ x, all x → keyLe (key x) b := by
  intro x hx
  rcases h x hx with hxd | ⟨y, hyl, hxy, -⟩
  · exact hdone x hxd
  · rw [hxy]
    exact hlive y hyl

end Hex.GraphIso.Nauty
