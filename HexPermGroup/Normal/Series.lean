/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.DerivedCheck
public import HexPermGroup.Group.Trivial

public section

namespace Hex.PermGroup

theorem SameGroup.derived {G H : Group n} (h : SameGroup G H) : SameGroup G.derived H.derived := by
  have hG : G.IsSubgroup H := fun p hp => (h p).mp hp
  have hH : H.IsSubgroup G := fun p hp => (h p).mpr hp
  exact fun p => ⟨hG.derived p, hH.derived p⟩

namespace Group

/-- The mathematical sequence underlying the terminating derived-series
algorithm. Individual terms retain the original permutation degree. -/
@[expose] def derivedAt (G : Group n) : Nat → Group n
  | 0 => G
  | k + 1 => (G.derivedAt k).derived

theorem derivedAt_succ (G : Group n) (k : Nat) : G.derivedAt (k + 1) = G.derived.derivedAt k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Group.derived ih

theorem derivedAt_inside (G : Group n) (k : Nat) : (G.derivedAt k).IsSubgroup G := by
  induction k with
  | zero => exact fun _ hp => hp
  | succ k ih => exact fun p hp => ih p ((G.derivedAt k).derived_inside p hp)

/-- Solvability means that a term of the derived series is trivial. -/
@[expose] def IsSolvable (G : Group n) : Prop := ∃ k, (G.derivedAt k).order = 1

theorem solvable_of_trivial (G : Group n) (h : G.order = 1) : G.IsSolvable := ⟨0, h⟩

theorem solvable_derived (G : Group n) : G.IsSolvable ↔ G.derived.IsSolvable := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      have hi := G.derived_inside.order_le
      have hp := G.derived.order_pos
      exact ⟨0, by change G.order = 1 at hk; change G.derived.order = 1; omega⟩
    | succ k => exact ⟨k, by rwa [derivedAt_succ] at hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rwa [derivedAt_succ]⟩

end Group

theorem SameGroup.derivedAt {G H : Group n} (h : SameGroup G H) (k : Nat) :
    SameGroup (G.derivedAt k) (H.derivedAt k) := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.derived

theorem SameGroup.solvable {G H : Group n} (h : SameGroup G H) : G.IsSolvable ↔ H.IsSolvable := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (h.derivedAt k).order_eq ▸ hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (h.derivedAt k).order_eq.symm ▸ hk⟩

namespace Group

/-- A nontrivial perfect group remains unchanged throughout its derived series. -/
theorem not_solvable_of_perfect (G : Group n) (h : SameGroup G.derived G) (hn : G.order ≠ 1) :
    ¬G.IsSolvable := by
  have he (k : Nat) : SameGroup (G.derivedAt k) G := by
    induction k with
    | zero => exact fun _ => Iff.rfl
    | succ k ih => exact fun p => (ih.derived p).trans (h p)
  rintro ⟨k, hk⟩
  exact hn ((he k).order_eq ▸ hk)

end Group

end Hex.PermGroup
