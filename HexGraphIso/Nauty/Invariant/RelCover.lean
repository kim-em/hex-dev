/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert.Cert

public section

namespace Hex.GraphIso.Nauty

universe u

variable {α : Sort u}

/-- Each original child is resolved or is related to a no-larger live
child. The relation may retain a permutation witness rather than only
equality of the children's values. -/
@[expose] def RelCover (R : α → α → Prop) (rank : α → Nat)
    (all done live : α → Prop) : Prop :=
  ∀ x, all x → done x ∨ ∃ y, live y ∧ R x y ∧ rank y ≤ rank x

namespace RelCover

variable {R : α → α → Prop} {rank : α → Nat}
    {all done live done' live' : α → Prop}

theorem init (hrefl : ∀ x, R x x) (all : α → Prop) :
    RelCover R rank all (fun _ => False) all :=
  fun x hx => Or.inr ⟨x, hx, hrefl x, Nat.le_refl _⟩

/-- Compose the witnesses through one change of the live set. -/
theorem step (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (h : RelCover R rank all done live)
    (hs : ∀ x, live x → (∀ z, R z x → done' z) ∨
      ∃ y, live' y ∧ R x y ∧ rank y ≤ rank x)
    (hd : ∀ x, done x → done' x) : RelCover R rank all done' live' := by
  intro x hx
  rcases h x hx with hxd | ⟨y, hyl, hxy, hyr⟩
  · exact Or.inl (hd x hxd)
  · rcases hs y hyl with hyd | ⟨z, hzl, hyz, hzr⟩
    · exact Or.inl (hyd x hxy)
    · exact Or.inr ⟨z, hzl, htrans hxy hyz, Nat.le_trans hzr hyr⟩

/-- Resolve a removed child by strict rank descent, including when the
carrier lands outside the set retained by an earlier filter. -/
theorem resolve (hrefl : ∀ x, R x x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (h : RelCover R rank all done live)
    (hdone : ∀ x y, R x y → done y → done x)
    (hstep : ∀ x, live x → live' x ∨
      ∃ y, all y ∧ R x y ∧ rank y < rank x) :
    ∀ x, live x → done x ∨ ∃ y, live' y ∧ R x y ∧ rank y ≤ rank x
  | x, hx => by
    rcases hstep x hx with hxl | ⟨y, hya, hxy, hyr⟩
    · exact Or.inr ⟨x, hxl, hrefl x, Nat.le_refl _⟩
    · rcases h y hya with hyd | ⟨z, hzl, hyz, hzr⟩
      · exact Or.inl (hdone x y hxy hyd)
      · have hzx : rank z < rank x := Nat.lt_of_le_of_lt hzr hyr
        rcases resolve hrefl htrans h hdone hstep z hzl with hzd | ⟨w, hwl, hzw, hwr⟩
        · exact Or.inl (hdone x z (htrans hxy hyz) hzd)
        · exact Or.inr ⟨w, hwl, htrans (htrans hxy hyz) hzw,
            Nat.le_trans hwr (Nat.le_of_lt hzx)⟩
  termination_by x => rank x

/-- Apply a descending filter while retaining the relational witnesses. -/
theorem filterDesc (hrefl : ∀ x, R x x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (h : RelCover R rank all done live)
    (hdone : ∀ x y, R x y → done y → done x)
    (hstep : ∀ x, live x → live' x ∨
      ∃ y, all y ∧ R x y ∧ rank y < rank x) :
    RelCover R rank all done live' := by
  intro x hx
  rcases h x hx with hxd | ⟨y, hyl, hxy, hyr⟩
  · exact Or.inl hxd
  · rcases resolve hrefl htrans h hdone hstep y hyl with hyd | ⟨z, hzl, hyz, hzr⟩
    · exact Or.inl (hdone x y hxy hyd)
    · exact Or.inr ⟨z, hzl, htrans hxy hyz, Nat.le_trans hzr hyr⟩

/-- Once the live suffix is empty, every original child is resolved. -/
theorem finish (h : RelCover R rank all done live) (hempty : ∀ x, ¬ live x) :
    ∀ x, all x → done x := by
  intro x hx
  rcases h x hx with hxd | ⟨y, hyl, _, _⟩
  · exact hxd
  · exact (hempty y hyl).elim

end RelCover

end Hex.GraphIso.Nauty
