/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Field.Roots

public section

/-!
Bundled `Lean.Grind` structure for the packed quotient `GF2nPoly`.

The laws are proved in `HexGF2.Field.Poly` and `HexGF2.Field.Roots`; this file
packages them so `grind` can use them. `hex-gfq-field` carries the same bundle
for the generic quotient field, and until now the packed representation had
none, so a goal that `grind` closed over `FiniteField` had to be done by hand
over `GF2nPoly`.
-/

namespace Hex

namespace GF2nPoly

variable {f : GF2Poly} {hirr : GF2Poly.Irreducible f}

/-- Natural literals step by one, which in characteristic two alternates. -/
@[simp, grind =] theorem natCast_succ (k : Nat) :
    (natCast (k + 1) : GF2nPoly f hirr) = natCast k + 1 := by
  unfold natCast
  by_cases hk : k % 2 = 0
  · rw [ite_eq_left hk, ite_eq_right (by omega)]
    show (one : GF2nPoly f hirr) = zero + 1
    rw [show (zero : GF2nPoly f hirr) = 0 from rfl, zero_add]
    rfl
  · rw [ite_eq_right hk, ite_eq_left (by omega)]
    show (zero : GF2nPoly f hirr) = one + 1
    rw [show (one : GF2nPoly f hirr) = 1 from rfl,
      show (zero : GF2nPoly f hirr) = 0 from rfl, add_self]

/-- Scalar multiplication by a natural is multiplication by its cast, since both
depend only on parity. -/
@[simp, grind =] theorem nsmul_eq_natCast_mul (k : Nat) (a : GF2nPoly f hirr) :
    k • a = (natCast k : GF2nPoly f hirr) * a := by
  show nsmul k a = natCast k * a
  unfold nsmul natCast
  by_cases hk : k % 2 = 0
  · rw [ite_eq_left hk, ite_eq_left hk]
    show (0 : GF2nPoly f hirr) = 0 * a
    rw [zero_mul]
  · rw [ite_eq_right hk, ite_eq_right hk]
    show a = one * a
    rw [show (one : GF2nPoly f hirr) = 1 from rfl, one_mul]

/-- The zeroth power is one, through the linear reference. -/
@[simp, grind =] theorem pow_zero (a : GF2nPoly f hirr) : a ^ 0 = 1 := by
  rw [Internal.pow_eq_linearPow, Internal.linearPow_zero]

/-- Each successor power multiplies by one more factor, through the linear
reference: the executable power is square-and-multiply, so this is not
definitional. -/
@[simp, grind =] theorem pow_succ (a : GF2nPoly f hirr) (n : Nat) :
    a ^ (n + 1) = a ^ n * a := by
  rw [Internal.pow_eq_linearPow, Internal.pow_eq_linearPow, Internal.linearPow_succ]

/-- Negation is the identity in characteristic two. -/
@[simp, grind =] theorem neg_eq_self (a : GF2nPoly f hirr) : -a = a :=
  eq_of_val_eq (neg_val a)

/-- Additive inverses cancel, which in characteristic two is `add_self`. -/
@[simp, grind =] theorem neg_add_cancel (a : GF2nPoly f hirr) : -a + a = 0 := by
  rw [neg_eq_self, add_self]

/-- Subtraction is addition of the negation, which here is addition. -/
@[simp, grind =] theorem sub_eq_add_neg (a b : GF2nPoly f hirr) :
    a - b = a + -b := by
  rw [neg_eq_self]
  exact eq_of_val_eq ((sub_val a b).trans (add_val a b).symm)

/-- Additive and multiplicative structure for the packed quotient field. -/
instance : Lean.Grind.Semiring (GF2nPoly f hirr) where
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul := one_mul
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  pow_zero := pow_zero
  pow_succ := pow_succ
  ofNat_succ := natCast_succ
  nsmul_eq_natCast_mul := nsmul_eq_natCast_mul

/-- Integer scalar multiplication negates with its scalar, which in
characteristic two is trivial on both sides. -/
@[grind =] theorem neg_zsmul (i : Int) (a : GF2nPoly f hirr) :
    (-i) • a = -(i • a) := by
  show zsmul (-i) a = -(zsmul i a)
  unfold zsmul
  rw [Int.natAbs_neg]
  by_cases hk : i.natAbs % 2 = 0
  · rw [ite_eq_left hk]; exact (neg_eq_self 0).symm
  · rw [ite_eq_right hk]; exact (neg_eq_self a).symm

/-- Integer casts negate trivially, since negation is the identity. -/
@[grind =] theorem intCast_neg (i : Int) :
    ((-i : Int) : GF2nPoly f hirr) = -((i : Int) : GF2nPoly f hirr) := by
  show intCast (-i) = -(intCast i)
  unfold intCast
  rw [Int.natAbs_neg, neg_eq_self]

/-- Additive inverses for the packed quotient. -/
instance : Lean.Grind.Ring (GF2nPoly f hirr) where
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg
  neg_zsmul := neg_zsmul
  intCast_neg := intCast_neg

/-- Multiplication is commutative, inherited from the packed polynomial ring. -/
instance : Lean.Grind.CommRing (GF2nPoly f hirr) where
  mul_comm := mul_comm

/-! # Field structure needs a nonconstant modulus

The three instances above hold for every `f` the type admits. The field laws do
not, and the reason is worth stating: `GF2Poly.Irreducible f` asks that `f` be
nonzero and admit no factorization into two positive-degree parts, which the
constant `1` satisfies. `GF2nPoly 1 _` is then the trivial ring, where every
residue is `0` and `0 = 1`, so both `zero_ne_one` and characteristic two fail.

`hex-gfq-field` avoids this by carrying `hf : 0 < f.degree` as a separate type
parameter beside the irreducibility proof. `GF2nPoly` does not, so the field
laws are supplied as definitions taking that hypothesis rather than as
instances. A caller with a genuine modulus has the hypothesis to hand: every
committed `PackedGF2Entry` carries `degree_pos`.
-/

/-- The zeroth integer power is one. -/
@[simp, grind =] theorem zpow_zero (a : GF2nPoly f hirr) :
    a ^ (0 : Int) = 1 := pow_zero a

/-- Successor integer powers multiply by one more factor. -/
@[grind =] theorem zpow_succ (a : GF2nPoly f hirr) (n : Nat) :
    a ^ ((n : Int) + 1) = a ^ (n : Int) * a := pow_succ a n

/-- Zero and one are distinct when the modulus is nonconstant. -/
theorem zero_ne_one_of_degree_pos (hdeg : 0 < f.degree) :
    (0 : GF2nPoly f hirr) ≠ 1 := by
  intro h
  have hval := congrArg GF2nPoly.val h
  rw [zero_val, one_val, GF2Poly.mod_eq_self_of_reduced 1 f
    (Or.inr (by rw [GF2Poly.degree_one]; exact hdeg))] at hval
  exact absurd hval (by decide)

/-- One is its own inverse. -/
theorem inv_one_of_degree_pos (hdeg : 0 < f.degree) :
    (1 : GF2nPoly f hirr)⁻¹ = 1 := by
  have h := mul_inv_cancel (1 : GF2nPoly f hirr)
    (fun hc => zero_ne_one_of_degree_pos (f := f) (hirr := hirr) hdeg hc.symm)
  rw [one_mul] at h
  exact h

/-- A nonzero element has a nonzero inverse. -/
theorem inv_ne_zero_of_degree_pos (hdeg : 0 < f.degree)
    {a : GF2nPoly f hirr} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro hc
  have h := mul_inv_cancel a ha
  rw [hc, mul_zero] at h
  exact zero_ne_one_of_degree_pos (f := f) (hirr := hirr) hdeg h

/-- Inversion is an involution, by cancelling through the defining identity. -/
theorem inv_inv_of_degree_pos (hdeg : 0 < f.degree) (a : GF2nPoly f hirr) :
    (a⁻¹)⁻¹ = a := by
  by_cases ha : a = 0
  · subst ha; rw [inv_zero, inv_zero]
  · calc (a⁻¹)⁻¹
        = 1 * (a⁻¹)⁻¹ := by rw [one_mul]
      _ = (a * a⁻¹) * (a⁻¹)⁻¹ := by rw [mul_inv_cancel a ha]
      _ = a * (a⁻¹ * (a⁻¹)⁻¹) := by rw [mul_assoc]
      _ = a * 1 := by
            rw [mul_inv_cancel a⁻¹ (inv_ne_zero_of_degree_pos hdeg ha)]
      _ = a := by rw [mul_one]

/-- Negating an integer exponent inverts the power. -/
theorem zpow_neg_of_degree_pos (hdeg : 0 < f.degree)
    (a : GF2nPoly f hirr) (n : Int) : a ^ (-n) = (a ^ n)⁻¹ := by
  cases n with
  | ofNat k =>
      cases k with
      | zero =>
          show zpow a 0 = (zpow a 0)⁻¹
          show (a ^ (0 : Nat)) = (a ^ (0 : Nat))⁻¹
          rw [pow_zero, inv_one_of_degree_pos hdeg]
      | succ k => rfl
  | negSucc k =>
      show zpow a (Int.ofNat (k + 1)) = (zpow a (Int.negSucc k))⁻¹
      show a ^ (k + 1) = ((a ^ (k + 1))⁻¹)⁻¹
      rw [inv_inv_of_degree_pos hdeg]

/-- Field laws for the packed quotient, given a nonconstant irreducible modulus.

Not an instance: see the note above on why irreducibility alone is not enough. -/
@[instance_reducible] def fieldOfDegreePos (hdeg : 0 < f.degree) : Lean.Grind.Field (GF2nPoly f hirr) where
  div_eq_mul_inv := div_eq_mul_inv
  zero_ne_one := zero_ne_one_of_degree_pos hdeg
  inv_zero := inv_zero
  mul_inv_cancel := fun {a} ha => mul_inv_cancel a ha
  zpow_zero := zpow_zero
  zpow_succ := zpow_succ
  zpow_neg := zpow_neg_of_degree_pos hdeg

/-- Characteristic two, given a nonconstant irreducible modulus. -/
theorem isCharPOfDegreePos (hdeg : 0 < f.degree) :
    Lean.Grind.IsCharP (GF2nPoly f hirr) 2 where
  ofNat_ext_iff {x y} := by
    show (natCast x : GF2nPoly f hirr) = natCast y ↔ x % 2 = y % 2
    unfold natCast
    have hne : (zero : GF2nPoly f hirr) ≠ one := by
      show (0 : GF2nPoly f hirr) ≠ 1
      exact zero_ne_one_of_degree_pos hdeg
    constructor
    · intro h
      by_cases hx : x % 2 = 0 <;> by_cases hy : y % 2 = 0
      · omega
      · rw [ite_eq_left hx, ite_eq_right hy] at h; exact absurd h hne
      · rw [ite_eq_right hx, ite_eq_left hy] at h; exact absurd h.symm hne
      · omega
    · intro h
      by_cases hx : x % 2 = 0
      · rw [ite_eq_left hx, ite_eq_left (by omega)]
      · rw [ite_eq_right hx, ite_eq_right (by omega)]

end GF2nPoly

end Hex
