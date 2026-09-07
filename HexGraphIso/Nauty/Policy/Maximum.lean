/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Sound
public import HexGraphIso.Nauty.Invariant.Coverage

public section

/-!
Incumbent bounds for searches with nonlocal returns. The incumbent is
optional until the first leaf and may be a ghost value while executable
code storage is being overwritten. None of these definitions reads the
policy state.

A return below the receiving level transports coverage of a frozen
ancestor child. At that ancestor, the coverage becomes a lower bound;
together with the accumulated upper bound it yields the exact maximum.
-/

namespace Hex.GraphIso.Nauty.Generic

variable {n : Nat}

/-- An installed incumbent can only increase. -/
@[expose] def Grows (before after : Option (Key n)) : Prop :=
  ∀ b, before = some b → ∃ a, after = some a ∧ keyLe b a

/-- A key is bounded by an installed incumbent. -/
@[expose] def Covers (bound : Key n) (best : Option (Key n)) : Prop :=
  ∃ b, best = some b ∧ keyLe bound b

/-- A fragment only installs keys bounded by its incoming incumbent and
its fixed subtree bound, and preserves any incoming incumbent. -/
structure Bounded (bound : Key n) (before after : Option (Key n)) : Prop where
  /-- Every installed output has the fixed upper bound. -/
  upper : ∀ b, after = some b → keyLe b (incMax before bound)
  /-- Previously installed keys are retained or improved. -/
  grows : Grows before after

/-- Taking a maximum preserves either upper bound. -/
theorem max_le {a b c : Key n} (ha : keyLe a c) (hb : keyLe b c) :
    keyLe (keyMax a b) c := by
  rcases keyMax_mem a b with h | h <;> rwa [h]

/-- Folding a key into an optional incumbent bounds that key. -/
theorem le_incMax (best : Option (Key n)) (bound : Key n) :
    keyLe bound (incMax best bound) := by
  cases best with
  | none => exact keyLe_refl _
  | some b => exact keyLe_iff.mpr (keyMax_not_lt_right b bound)

/-- Increasing the subtree bound increases its incumbent maximum. -/
theorem incMax_mono (best : Option (Key n)) {a b : Key n}
    (h : keyLe a b) : keyLe (incMax best a) (incMax best b) := by
  cases best with
  | none => exact h
  | some c =>
    exact max_le (keyLe_iff.mpr (keyMax_not_lt_left c b))
      (keyLe_trans h (le_incMax (some c) b))

/-- Leaving the incumbent unchanged preserves it. -/
theorem Grows.refl (best : Option (Key n)) : Grows best best := by
  intro b hb
  exact ⟨b, hb, keyLe_refl _⟩

/-- Incumbent growth composes across consecutive fragments. -/
theorem Grows.trans {a b c : Option (Key n)} (hab : Grows a b)
    (hbc : Grows b c) : Grows a c := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hab x hx
  obtain ⟨z, hz, hyz⟩ := hbc y hy
  exact ⟨z, hz, keyLe_trans hxy hyz⟩

/-- Installing an incumbent maximum preserves the old incumbent. -/
theorem Grows.incMax (best : Option (Key n)) (bound : Key n) :
    Grows best (some (incMax best bound)) := by
  intro b hb
  subst best
  exact ⟨_, rfl, keyLe_iff.mpr (keyMax_not_lt_left b bound)⟩

/-- Coverage survives subsequent incumbent growth. -/
theorem Covers.grow {bound : Key n} {before after : Option (Key n)}
    (h : Covers bound before) (hg : Grows before after) : Covers bound after := by
  obtain ⟨b, hb, hbound⟩ := h
  obtain ⟨a, ha, hba⟩ := hg b hb
  exact ⟨a, ha, keyLe_trans hbound hba⟩

/-- A covered upper bound covers any smaller key. -/
theorem Covers.mono {a b : Key n} {best : Option (Key n)}
    (h : Covers b best) (hab : keyLe a b) : Covers a best := by
  obtain ⟨c, hc, hbc⟩ := h
  exact ⟨c, hc, keyLe_trans hab hbc⟩

/-- An exact incumbent maximum covers the folded subtree. -/
theorem Covers.incMax (best : Option (Key n)) (bound : Key n) :
    Covers bound (some (incMax best bound)) :=
  ⟨_, rfl, le_incMax best bound⟩

/-- A fragment that changes nothing satisfies any fixed bound. -/
theorem Bounded.refl (bound : Key n) (best : Option (Key n)) :
    Bounded bound best best := by
  refine ⟨?_, Grows.refl best⟩
  intro b hb
  rw [hb]
  exact keyLe_iff.mpr (keyMax_not_lt_left b bound)

/-- An exact maximum satisfies both fragment bounds. -/
theorem Bounded.of_eq {bound : Key n} {before after : Option (Key n)}
    (h : after = some (incMax before bound)) : Bounded bound before after := by
  subst after
  refine ⟨?_, Grows.incMax before bound⟩
  intro b hb
  cases hb
  exact keyLe_refl _

/-- A child fragment also satisfies every larger parent bound. -/
theorem Bounded.mono {a b : Key n} {before after : Option (Key n)}
    (h : Bounded a before after) (hab : keyLe a b) : Bounded b before after :=
  ⟨fun c hc => keyLe_trans (h.upper c hc) (incMax_mono before hab), h.grows⟩

/-- Fragments with the same frozen bound compose. -/
theorem Bounded.trans {bound : Key n} {before middle after : Option (Key n)}
    (h₁ : Bounded bound before middle) (h₂ : Bounded bound middle after) :
    Bounded bound before after := by
  refine ⟨?_, h₁.grows.trans h₂.grows⟩
  intro b hb
  have hu := h₂.upper b hb
  cases hm : middle with
  | none =>
    rw [hm, incMax] at hu
    exact keyLe_trans hu (le_incMax before bound)
  | some m =>
    rw [hm, incMax] at hu
    exact keyLe_trans hu (max_le (h₁.upper m hm) (le_incMax before bound))

/-- Coverage and fragment bounds determine the exact maximum. -/
theorem Bounded.exact {bound : Key n} {before after : Option (Key n)}
    (h : Bounded bound before after) (hc : Covers bound after) :
    after = some (incMax before bound) := by
  obtain ⟨b, hb, hbound⟩ := hc
  have hu := h.upper b hb
  have hl : keyLe (incMax before bound) b := by
    cases hi : before with
    | none => exact hbound
    | some a =>
      obtain ⟨c, hc, hac⟩ := h.grows a hi
      have he := Option.some.inj (hc.symm.trans hb)
      subst c
      exact max_le hac hbound
  exact hb.trans (congrArg some (keyLe_antisym hu hl))

/-- Ranked child coverage composes with an installed incumbent. -/
theorem ChildCover.covers {key : Nat → Key n} {rank : Nat → Nat}
    {all live : Nat → Prop} {best : Option (Key n)}
    (h : ChildCover key rank all (fun x => Covers (key x) best) live)
    (hlive : ∀ x, live x → Covers (key x) best) :
    ∀ x, all x → Covers (key x) best := by
  intro x hx
  rcases h x hx with hd | ⟨y, hy, he, _⟩
  · exact hd
  · rw [he]
    exact hlive y hy

/-- Coverage carried by an exit. A smaller target refers to the frozen
ancestor child named by `witness`; the receiving level supplies ordinary
coverage. Fuel exhaustion makes no coverage assertion. -/
@[expose] def ExitCover (bound : Key n) (best : Option (Key n)) (stop : Nat)
    (witness : Nat → Option (Key n) → Prop) : Exit → Prop
  | .done => Covers bound best
  | .unwind target _ => target ≤ stop ∧
      (if target = stop then Covers bound best else witness target best)
  | .fuel => True

/-- Bounds and the coverage appropriate to a nonlocal exit. -/
structure Result (bound : Key n) (before after : Option (Key n)) (stop : Nat)
    (witness : Nat → Option (Key n) → Prop) (exit : Exit) : Prop where
  /-- The incumbent stays within this fragment's bound. -/
  bounded : Bounded bound before after
  /-- The exit either completes coverage or transports an ancestor witness. -/
  coverage : ExitCover bound after stop witness exit

/-- A complete sweep computes its fixed incumbent maximum. -/
theorem Result.done {bound : Key n} {before after : Option (Key n)}
    {stop : Nat} {witness : Nat → Option (Key n) → Prop}
    (h : Result bound before after stop witness .done) :
    after = some (incMax before bound) := h.bounded.exact h.coverage

/-- A return to the receiving level computes its fixed incumbent maximum. -/
theorem Result.received {bound : Key n} {before after : Option (Key n)}
    {stop : Nat} {witness : Nat → Option (Key n) → Prop} {short : Bool}
    (h : Result bound before after stop witness (.unwind stop short)) :
    after = some (incMax before bound) := by
  apply h.bounded.exact
  simpa only [ExitCover, ↓reduceIte] using h.coverage.2

/-- A completed child sweep becomes ordinary node completion at its
parent. No ancestor witness is needed for this exit. -/
theorem Result.finish {bound : Key n} {before after : Option (Key n)}
    {stop parent : Nat} {witness : Nat → Option (Key n) → Prop}
    (h : Result bound before after stop witness .done) :
    Result bound before after parent witness (.unwind parent false) := by
  refine ⟨h.bounded, Nat.le_refl _, ?_⟩
  simpa only [ExitCover, ↓reduceIte] using h.coverage

/-- Transport an early sweep return through its node. When the target
is the node's parent, its frozen-child witness supplies node coverage. -/
theorem Result.ascend {bound : Key n} {before after : Option (Key n)}
    {level target : Nat} {short : Bool}
    {witness : Nat → Option (Key n) → Prop}
    (h : Result bound before after level witness (.unwind target short))
    (ht : target < level)
    (hresolve : witness (level - 1) after → Covers bound after) :
    Result bound before after (level - 1) witness (.unwind target short) := by
  have hw : witness target after := by
    simpa only [ite_eq_right (by omega : target ≠ level)] using h.coverage.2
  refine ⟨h.bounded, by omega, ?_⟩
  split
  · rename_i he
    exact hresolve (he ▸ hw)
  · exact hw

/-- The root has no earlier ancestor, so every non-exhausted return is
an exact maximum. -/
theorem Result.root {bound : Key n} {before after : Option (Key n)}
    {witness : Nat → Option (Key n) → Prop} {exit : Exit}
    (h : Result bound before after 0 witness exit) (hfuel : exit ≠ .fuel) :
    after = some (incMax before bound) := by
  cases exit with
  | done => exact h.done
  | unwind target short =>
    have ht : target = 0 := Nat.eq_zero_of_le_zero h.coverage.1
    subst target
    exact h.received
  | fuel => exact (hfuel rfl).elim

end Hex.GraphIso.Nauty.Generic
