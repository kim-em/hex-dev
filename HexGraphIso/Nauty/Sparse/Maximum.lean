/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Coverage
import all HexGraphIso.Nauty.Sparse.Coverage
import all HexGraphIso.Nauty.Sparse.ReturnCodes

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The native maximum of a subtree bound and an optional incoming key. -/
@[expose] def incMax (before : Option (Key n)) (bound : Key n) : Key n :=
  match before with
  | none => bound
  | some key => Key.max key bound

theorem le_incMax (before : Option (Key n)) (bound : Key n) : Key.Le bound (incMax before bound) := by
  cases before with
  | none => exact Key.le_refl _
  | some key => exact Key.le_max_right _ _

theorem incMax_mono (before : Option (Key n)) {a b : Key n} (h : Key.Le a b) :
    Key.Le (incMax before a) (incMax before b) := by
  cases before with
  | none => exact h
  | some key => exact Key.max_le (Key.le_max_left _ _) (Key.le_trans h (Key.le_max_right _ _))

theorem Grows.incMax (before : Option (Key n)) (bound : Key n) :
    Grows before (Option.some (incMax before bound)) := by
  intro key hkey
  subst before
  exact ⟨_, rfl, Key.le_max_left _ _⟩

theorem Covers.incMax (before : Option (Key n)) (bound : Key n) :
    Covers bound (some (incMax before bound)) := ⟨_, rfl, le_incMax before bound⟩

/-- A fragment preserves its incoming key and only installs native keys
bounded by the incoming incumbent and the frozen complete subtree. -/
structure Bounded (bound : Key n) (before after : Option (Key n)) : Prop where
  upper : ∀ key, after = some key → Key.Le key (incMax before bound)
  grows : Grows before after

namespace Bounded

theorem refl (bound : Key n) (before : Option (Key n)) : Bounded bound before before := by
  refine ⟨?_, Grows.refl _⟩
  intro key hkey
  rw [hkey]
  exact Key.le_max_left _ _

theorem of_eq {bound : Key n} {before after : Option (Key n)}
    (h : after = some (incMax before bound)) : Bounded bound before after := by
  subst after
  refine ⟨?_, Grows.incMax _ _⟩
  intro key hkey
  cases hkey
  exact Key.le_refl _

theorem mono {a b : Key n} {before after : Option (Key n)}
    (h : Bounded a before after) (hab : Key.Le a b) : Bounded b before after :=
  ⟨fun key hkey => Key.le_trans (h.upper key hkey) (incMax_mono before hab), h.grows⟩

/-- A child may be bounded by the incoming incumbent as well as the
parent subtree. This is needed for dominated, hinted target choices. -/
theorem absorb {child parent : Key n} {before after : Option (Key n)}
    (h : Bounded child before after) (hc : Key.Le child (incMax before parent)) :
    Bounded parent before after := by
  refine ⟨?_, h.grows⟩
  intro key hk
  have hu := h.upper key hk
  cases before with
  | none => exact Key.le_trans hu hc
  | some old => exact Key.le_trans hu (Key.max_le (Key.le_max_left _ _) hc)

theorem trans {bound : Key n} {before middle after : Option (Key n)}
    (h₁ : Bounded bound before middle) (h₂ : Bounded bound middle after) :
    Bounded bound before after := by
  refine ⟨?_, h₁.grows.trans h₂.grows⟩
  intro key hkey
  have hu := h₂.upper key hkey
  cases hm : middle with
  | none =>
    rw [hm, incMax] at hu
    exact Key.le_trans hu (le_incMax before bound)
  | some mid =>
    rw [hm, incMax] at hu
    exact Key.le_trans hu (Key.max_le (h₁.upper mid hm) (le_incMax before bound))

/-- Coverage of the frozen bound and the upper invariant determine the
exact native maximum, including calls made before the first incumbent. -/
theorem exact {bound : Key n} {before after : Option (Key n)}
    (h : Bounded bound before after) (hc : Covers bound after) :
    after = some (incMax before bound) := by
  obtain ⟨key, hkey, hbound⟩ := hc
  have hu := h.upper key hkey
  have hl : Key.Le (incMax before bound) key := by
    cases hb : before with
    | none => exact hbound
    | some old =>
      obtain ⟨out, hout, hle⟩ := h.grows old hb
      have he := Option.some.inj (hout.symm.trans hkey)
      subst out
      exact Key.max_le hle hbound
  exact hkey.trans (congrArg some (Key.le_antisymm hu hl))

end Bounded

/-- A completed exit covers its frozen subtree. A return to an earlier
ancestor carries the witness for that ancestor; fuel exhaustion asserts
neither kind of coverage and is excluded by production totality. -/
@[expose] def ExitCover (bound : Key n) (best : Option (Key n)) (stop : Nat)
    (witness : Nat → Option (Key n) → Prop) : Generic.Exit → Prop
  | .done => Covers bound best
  | .unwind target _ => target ≤ stop ∧
      (if target = stop then Covers bound best else witness target best)
  | .fuel => True

/-- Native upper bounds and the coverage appropriate to the actual exit. -/
structure MaxResult (bound : Key n) (before after : Option (Key n)) (stop : Nat)
    (witness : Nat → Option (Key n) → Prop) (exit : Generic.Exit) : Prop where
  bounded : Bounded bound before after
  coverage : ExitCover bound after stop witness exit

namespace MaxResult

theorem done {bound : Key n} {before after : Option (Key n)}
    {stop : Nat} {witness : Nat → Option (Key n) → Prop}
    (h : MaxResult bound before after stop witness .done) :
    after = some (incMax before bound) := h.bounded.exact h.coverage

theorem received {bound : Key n} {before after : Option (Key n)}
    {stop : Nat} {witness : Nat → Option (Key n) → Prop} {short : Bool}
    (h : MaxResult bound before after stop witness (.unwind stop short)) :
    after = some (incMax before bound) := by
  apply h.bounded.exact
  simpa only [ExitCover, ↓reduceIte] using h.coverage.2

theorem finish {bound : Key n} {before after : Option (Key n)}
    {stop parent : Nat} {witness : Nat → Option (Key n) → Prop}
    (h : MaxResult bound before after stop witness .done) :
    MaxResult bound before after parent witness (.unwind parent false) :=
  ⟨h.bounded, Nat.le_refl _, by simpa only [ExitCover, ↓reduceIte] using h.coverage⟩

theorem ascend {bound : Key n} {before after : Option (Key n)}
    {level target : Nat} {short : Bool} {witness : Nat → Option (Key n) → Prop}
    (h : MaxResult bound before after level witness (.unwind target short))
    (ht : target < level) (hresolve : witness (level - 1) after → Covers bound after) :
    MaxResult bound before after (level - 1) witness (.unwind target short) := by
  have hw : witness target after := by
    simpa only [ite_eq_right (by omega : target ≠ level)] using h.coverage.2
  refine ⟨h.bounded, by omega, ?_⟩
  split
  · rename_i he
    exact hresolve (he ▸ hw)
  · exact hw

/-- At the root, production's no-exhaustion theorem rules out the only
exit without coverage; there is no earlier ancestor witness to discharge. -/
theorem root {bound : Key n} {before after : Option (Key n)}
    {witness : Nat → Option (Key n) → Prop} {exit : Generic.Exit}
    (h : MaxResult bound before after 0 witness exit) (hfuel : exit ≠ .fuel) :
    after = some (incMax before bound) := by
  cases exit with
  | done => exact h.done
  | unwind target short =>
    have ht : target = 0 := Nat.eq_zero_of_le_zero h.coverage.1
    subst target
    exact h.received
  | fuel => exact (hfuel rfl).elim

end MaxResult
end Hex.GraphIso.Nauty.Sparse
