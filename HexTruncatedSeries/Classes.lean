/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Ring

public section

/-!
Precision-local algebraic capabilities used by truncated-series algorithms.

`UnitOps` separates executable unit detection from the witness-taking core
algorithms.  `NatInverses R m` records only the finitely many integer inverses
required at a particular precision, so low-precision `exp` and `log` remain
available over rings such as `Int`.
-/

namespace Hex.TSeries

universe u

attribute [local instance] Lean.Grind.Semiring.natCast

/-- An executable partial inverse operation on a coefficient ring. -/
class UnitOps (R : Type u) where
  /-- Return a multiplicative inverse when one is available. -/
  inv? : R → Option R

/-- Soundness and completeness of executable unit detection. -/
class LawfulUnitOps (R : Type u) [Lean.Grind.CommRing R] [UnitOps R] : Prop where
  /-- A returned inverse is a right inverse. -/
  inv?_eq : ∀ (a u : R), UnitOps.inv? a = some u → a * u = 1
  /-- Every element admitting a right inverse is detected. -/
  inv?_isSome : ∀ (a : R), (∃ u : R, a * u = 1) → (UnitOps.inv? a).isSome

/-- Inverses of the natural numbers `1` through `m` in `R`. -/
class NatInverses (R : Type u) [Lean.Grind.CommRing R] (m : Nat) where
  /-- A total lookup whose values are constrained on `1, ..., m`. -/
  invNat : Nat → R
  /-- The lookup inverts every required natural number. -/
  invNat_eq : ∀ k : Nat, 1 ≤ k → k ≤ m → (k : R) * invNat k = 1

namespace NatInverses

/-- Restrict a family of natural inverses to a smaller precision.  This is a
definition rather than an instance to avoid instance-search loops. -/
@[instance_reducible]
def mono {R : Type u} [Lean.Grind.CommRing R] {m m' : Nat}
    [NatInverses R m] (h : m' ≤ m) : NatInverses R m' where
  invNat := NatInverses.invNat (R := R) (m := m)
  invNat_eq k hk hk' :=
    NatInverses.invNat_eq (R := R) (m := m) k hk (Nat.le_trans hk' h)

/-- Any two lawful choices of the inverse of a required natural agree. -/
theorem invNat_unique {R : Type u} [Lean.Grind.CommRing R] {m : Nat}
    (a b : NatInverses R m) (k : Nat) (hk : 1 ≤ k) (hkm : k ≤ m) :
    a.invNat k = b.invNat k := by
  have ha := a.invNat_eq k hk hkm
  have hb := b.invNat_eq k hk hkm
  calc
    a.invNat k = 1 * a.invNat k := by grind
    _ = ((k : R) * b.invNat k) * a.invNat k := by rw [hb]
    _ = ((k : R) * a.invNat k) * b.invNat k := by grind
    _ = 1 * b.invNat k := by rw [ha]
    _ = b.invNat k := by grind

end NatInverses

/-- No natural inverses are required at bound zero. -/
instance (priority := 1100) [Lean.Grind.CommRing R] : NatInverses R 0 where
  invNat := fun _ => 0
  invNat_eq := by omega

/-- A subtraction from zero still requests no inverses.  Keeping this
syntactic instance is necessary across module boundaries, where instance
matching need not unfold `Nat.sub` before comparing the index. -/
instance (priority := 1200) [Lean.Grind.CommRing R] (k : Nat) :
    NatInverses R (0 - k) where
  invNat := fun _ => 0
  invNat_eq := by omega

/-- A self-difference still requests no inverses.  This makes the
precision-one spelling `NatInverses R (1 - 1)` resolve without relying on
kernel reduction of subtraction during typeclass search. -/
instance (priority := 1200) [Lean.Grind.CommRing R] (k : Nat) :
    NatInverses R (k - k) where
  invNat := fun _ => 0
  invNat_eq := by omega

/-- The precision-two algorithm spelling requests `NatInverses R (2 - 1)`.
Keep that syntactic form available across module boundaries rather than relying
on typeclass search to reduce the subtraction to one. -/
instance (priority := 1200) [Lean.Grind.CommRing R] :
    NatInverses R (2 - 1) where
  invNat := fun _ => 1
  invNat_eq := by
    intro k hk hk'
    have : k = 1 := by omega
    subst k
    rw [Lean.Grind.Semiring.natCast_one, Lean.Grind.Semiring.one_mul]

/-- At bound one, the only required inverse is `1`. -/
instance (priority := 1100) [Lean.Grind.CommRing R] : NatInverses R 1 where
  invNat := fun _ => 1
  invNat_eq := by
    intro k hk hk'
    have : k = 1 := by omega
    subst k
    rw [Lean.Grind.Semiring.natCast_one, Lean.Grind.Semiring.one_mul]

/-- Rational numbers have an executable inverse exactly away from zero. -/
instance : UnitOps Rat where
  inv? a := if a = 0 then none else some a⁻¹

/-- Rational unit detection is sound and complete. -/
instance : LawfulUnitOps Rat where
  inv?_eq := by
    intro a u h
    change (if a = 0 then none else some a⁻¹) = some u at h
    by_cases ha : a = 0
    · simp [ha] at h
    · simp [ha] at h
      cases h
      exact Rat.mul_inv_cancel a ha
  inv?_isSome := by
    intro a h
    change (if a = 0 then none else some a⁻¹).isSome
    by_cases ha : a = 0
    · rcases h with ⟨u, hu⟩
      subst a
      simp only [Rat.zero_mul] at hu
      exact absurd hu (by decide)
    · simp [ha]

/-- The only integer units are `1` and `-1`. -/
instance : UnitOps Int where
  inv? a := if a = 1 then some 1 else if a = -1 then some (-1) else none

/-- Integer unit detection is sound and complete. -/
instance : LawfulUnitOps Int where
  inv?_eq := by
    intro a u h
    change (if a = 1 then some 1 else if a = -1 then some (-1) else none) = some u at h
    by_cases ha : a = 1
    · simp [ha] at h
      subst a
      cases h
      decide
    · by_cases ha' : a = -1
      · simp [ha'] at h
        subst a
        cases h
        decide
      · simp [ha, ha'] at h
  inv?_isSome := by
    intro a h
    rcases h with ⟨u, hu⟩
    have ha : a = 1 ∨ a = -1 := by
      by_cases hnonneg : 0 ≤ a
      · exact .inl (Int.eq_one_of_mul_eq_one_right hnonneg hu)
      · right
        have hneg : 0 ≤ -a := by omega
        have hmul : (-a) * (-u) = 1 := by
          rw [Int.neg_mul_neg]
          exact hu
        have := Int.eq_one_of_mul_eq_one_right hneg hmul
        omega
    change (if a = 1 then some 1 else if a = -1 then some (-1) else none).isSome
    rcases ha with rfl | rfl <;> decide

/-- Rational numbers contain inverses of every positive natural number. -/
instance (priority := 900) (m : Nat) : NatInverses Rat m where
  invNat k := if k = 0 then 0 else (k : Rat)⁻¹
  invNat_eq := by
    intro k hk _
    rw [ite_eq_right (by omega)]
    exact Rat.mul_inv_cancel _ (by simp; omega)

end Hex.TSeries
