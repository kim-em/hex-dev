/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Field.Poly

public section

/-!
The bare arithmetic laws for the packed single-word `GF2n` representation.

The proofs compare a canonical word with the corresponding `GF2nPoly`
quotient element. This keeps the computational library independent of Mathlib;
the companion `hex-gf2-mathlib` package can assemble these theorems into its
algebraic hierarchy without changing any executable operation.
-/

namespace Hex
namespace GF2n

variable {n : Nat} {irr : UInt64}
variable {hn : 0 < n} {hn64 : n < 64}
variable {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}

/-- The arbitrary-degree quotient element represented by a single-word field
element. Used only to transfer laws between the two executable packed models. -/
private def toPoly (a : GF2n n irr hn hn64 hirr) :
    GF2nPoly (GF2Poly.ofUInt64Monic irr n) hirr :=
  GF2nPoly.reducePoly (GF2Poly.ofUInt64 a.val)

/-- Reading back a packed polynomial reduction gives the corresponding
polynomial remainder. -/
private theorem ofUInt64_packedReduce_val
    (hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)) (p : GF2Poly) :
    GF2Poly.ofUInt64
      (GF2Poly.canonicalWordLT n hn64
        (GF2Poly.packedReduceWord n irr p)) =
      p % GF2Poly.ofUInt64Monic irr n := by
  have hcanonical :
      GF2Poly.canonicalWordLT n hn64
          (GF2Poly.packedReduceWord n irr p) =
        GF2Poly.packedReduceWord n irr p := by
    apply UInt64.toNat_inj.mp
    simp [GF2Poly.canonicalWordLT,
      Nat.mod_eq_of_lt (GF2Poly.packedReduceWord_toNat_lt hn64 _)]
  rw [hcanonical]
  apply GF2Poly.ofUInt64_packedReduceWord_eq_of_degree_lt hn64
  have hred :=
    GF2Poly.mod_degree_lt p (GF2Poly.ofUInt64Monic irr n) hirr.1
  rw [GF2Poly.degree_ofUInt64Monic_of_lt_64 irr hn64] at hred
  exact hred

/-- Reading back a reduced word gives its polynomial remainder modulo the
packed field modulus. -/
private theorem ofUInt64_reduce_val (w : UInt64) :
    GF2Poly.ofUInt64
        (reduce (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) w).val =
      GF2Poly.ofUInt64 w % GF2Poly.ofUInt64Monic irr n := by
  exact ofUInt64_packedReduce_val (hn64 := hn64) hirr (GF2Poly.ofUInt64 w)

/-- Reading back a reduced wide carry-less product gives its polynomial
remainder modulo the packed field modulus. -/
private theorem ofUInt64_reduceWide_val (hi lo : UInt64) :
    GF2Poly.ofUInt64
        (reduceWide (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr)
          hi lo).val =
      GF2Poly.ofWords #[lo, hi] % GF2Poly.ofUInt64Monic irr n := by
  exact ofUInt64_packedReduce_val (hn64 := hn64) hirr (GF2Poly.ofWords #[lo, hi])

/-- A canonical single-word representative unpacks to a polynomial reduced
below the extension degree. -/
private theorem val_reduced (a : GF2n n irr hn hn64 hirr) :
    (GF2Poly.ofUInt64 a.val).IsZero ∨ (GF2Poly.ofUInt64 a.val).degree < n := by
  by_cases hzero : (GF2Poly.ofUInt64 a.val).isZero = true
  · exact Or.inl hzero
  · right
    have hzeroFalse : (GF2Poly.ofUInt64 a.val).isZero = false := by
      cases h : (GF2Poly.ofUInt64 a.val).isZero <;> simp [h] at hzero ⊢
    obtain ⟨d, hd⟩ := GF2Poly.degree?_isSome_of_isZero_false hzeroFalse
    rw [GF2Poly.degree_eq_of_degree?_eq_some hd]
    by_cases hdn : d < n
    · exact hdn
    · have hnd : n ≤ d := Nat.le_of_not_gt hdn
      have htrue := GF2Poly.coeff_eq_true_of_degree?_eq_some hd
      have hfalse : (GF2Poly.ofUInt64 a.val).coeff d = false := by
        by_cases hd64 : d < 64
        · rw [GF2Poly.coeff_ofUInt64_eq_testBit a.val hd64]
          exact Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le a.val_lt (Nat.pow_le_pow_right (by decide) hnd))
        · exact GF2Poly.coeff_ofUInt64_eq_false_of_ge_64 a.val
            (Nat.le_of_not_lt hd64)
      rw [htrue] at hfalse
      exact Bool.noConfusion hfalse

/-- A canonical representative is unchanged by polynomial reduction. -/
private theorem val_mod_eq (a : GF2n n irr hn hn64 hirr) :
    GF2Poly.ofUInt64 a.val % GF2Poly.ofUInt64Monic irr n =
      GF2Poly.ofUInt64 a.val := by
  apply GF2Poly.mod_eq_self_of_reduced
  rw [GF2Poly.degree_ofUInt64Monic_of_lt_64 irr hn64]
  exact val_reduced a

/-- The comparison with `GF2nPoly` is injective. -/
private theorem toPoly_injective :
    Function.Injective (toPoly (n := n) (irr := irr) (hn := hn) (hn64 := hn64)
      (hirr := hirr)) := by
  intro a b h
  have hval := congrArg GF2nPoly.val h
  simp only [toPoly, GF2nPoly.reducePoly_val_eq_mod, val_mod_eq] at hval
  have hab := GF2Poly.ofUInt64_injective hval
  cases a
  cases b
  simp at hab
  subst hab
  rfl

/-- The comparison preserves addition. -/
private theorem toPoly_add (a b : GF2n n irr hn hn64 hirr) :
    toPoly (a + b) = toPoly a + toPoly b := by
  unfold toPoly
  change GF2nPoly.reducePoly (GF2Poly.ofUInt64 (a + b).val) =
    GF2nPoly.reducePoly
      ((GF2nPoly.reducePoly (GF2Poly.ofUInt64 a.val)).val +
        (GF2nPoly.reducePoly (GF2Poly.ofUInt64 b.val)).val)
  rw [← GF2nPoly.reducePoly_add_eq]
  change GF2nPoly.reducePoly (GF2Poly.ofUInt64 (reduce (a.val ^^^ b.val)).val) = _
  rw [ofUInt64_reduce_val, ← GF2Poly.ofUInt64_xor, GF2nPoly.reducePoly_mod_eq]

/-- The comparison preserves multiplication. -/
private theorem toPoly_mul (a b : GF2n n irr hn hn64 hirr) :
    toPoly (a * b) = toPoly a * toPoly b := by
  unfold toPoly
  change GF2nPoly.reducePoly (GF2Poly.ofUInt64 (a * b).val) =
    GF2nPoly.reducePoly
      ((GF2nPoly.reducePoly (GF2Poly.ofUInt64 a.val)).val *
        (GF2nPoly.reducePoly (GF2Poly.ofUInt64 b.val)).val)
  rw [← GF2nPoly.reducePoly_mul_eq]
  change GF2nPoly.reducePoly
      (GF2Poly.ofUInt64 (reduceWide (clmul a.val b.val).fst (clmul a.val b.val).snd).val) = _
  rw [ofUInt64_reduceWide_val, GF2Poly.ofUInt64_mul_ofUInt64,
    GF2nPoly.reducePoly_mod_eq]

/-- The comparison preserves zero. -/
private theorem toPoly_zero :
    toPoly (0 : GF2n n irr hn hn64 hirr) = 0 := by
  unfold toPoly
  change GF2nPoly.reducePoly (GF2Poly.ofUInt64 0) = 0
  rw [GF2Poly.ofUInt64_zero, GF2nPoly.reducePoly_zero]
  rfl

/-- The comparison preserves one. -/
private theorem toPoly_one :
    toPoly (1 : GF2n n irr hn hn64 hirr) = 1 := by
  unfold toPoly
  change GF2nPoly.reducePoly (GF2Poly.ofUInt64 (reduce 1).val) = 1
  rw [ofUInt64_reduce_val, GF2nPoly.reducePoly_mod_eq]
  rfl

/-! # Bare ring laws -/

/-- Addition is commutative on the packed single-word field. -/
theorem add_comm (a b : GF2n n irr hn hn64 hirr) : a + b = b + a := by
  apply toPoly_injective
  rw [toPoly_add, toPoly_add, GF2nPoly.add_comm]

/-- Addition is associative on the packed single-word field. -/
theorem add_assoc (a b c : GF2n n irr hn hn64 hirr) :
    (a + b) + c = a + (b + c) := by
  apply toPoly_injective
  rw [toPoly_add, toPoly_add, toPoly_add, toPoly_add, GF2nPoly.add_assoc]

/-- The additive identity is a left identity. -/
@[simp, grind =] theorem zero_add (a : GF2n n irr hn hn64 hirr) : 0 + a = a := by
  apply toPoly_injective
  rw [toPoly_add, toPoly_zero, GF2nPoly.zero_add]

/-- The additive identity is a right identity. -/
@[simp, grind =] theorem add_zero (a : GF2n n irr hn hn64 hirr) : a + 0 = a := by
  rw [add_comm, zero_add]

/-- Every element is its own additive inverse in characteristic two. -/
@[simp, grind =] theorem add_self (a : GF2n n irr hn hn64 hirr) : a + a = 0 := by
  apply toPoly_injective
  rw [toPoly_add, toPoly_zero, GF2nPoly.add_self]

/-- Negation cancels addition. -/
@[simp, grind =] theorem neg_add_cancel (a : GF2n n irr hn hn64 hirr) : -a + a = 0 := by
  change a + a = 0
  exact add_self a

/-- Multiplication is commutative on the packed single-word field. -/
theorem mul_comm (a b : GF2n n irr hn hn64 hirr) : a * b = b * a := by
  apply toPoly_injective
  rw [toPoly_mul, toPoly_mul, GF2nPoly.mul_comm]

/-- Multiplication is associative on the packed single-word field. -/
theorem mul_assoc (a b c : GF2n n irr hn hn64 hirr) :
    (a * b) * c = a * (b * c) := by
  apply toPoly_injective
  rw [toPoly_mul, toPoly_mul, toPoly_mul, toPoly_mul, GF2nPoly.mul_assoc]

/-- The multiplicative identity is a left identity. -/
@[simp, grind =] theorem one_mul (a : GF2n n irr hn hn64 hirr) : 1 * a = a := by
  apply toPoly_injective
  rw [toPoly_mul, toPoly_one, GF2nPoly.one_mul]

/-- The multiplicative identity is a right identity. -/
@[simp, grind =] theorem mul_one (a : GF2n n irr hn hn64 hirr) : a * 1 = a := by
  rw [mul_comm, one_mul]

/-- Zero annihilates multiplication on the left. -/
@[simp, grind =] theorem zero_mul (a : GF2n n irr hn hn64 hirr) : 0 * a = 0 := by
  apply toPoly_injective
  rw [toPoly_mul, toPoly_zero, GF2nPoly.zero_mul]

/-- Zero annihilates multiplication on the right. -/
@[simp, grind =] theorem mul_zero (a : GF2n n irr hn hn64 hirr) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

/-- Multiplication distributes over addition on the left. -/
theorem left_distrib (a b c : GF2n n irr hn hn64 hirr) :
    a * (b + c) = a * b + a * c := by
  apply toPoly_injective
  rw [toPoly_mul, toPoly_add, toPoly_add, toPoly_mul, toPoly_mul,
    GF2nPoly.left_distrib]

/-- Multiplication distributes over addition on the right. -/
theorem right_distrib (a b c : GF2n n irr hn hn64 hirr) :
    (a + b) * c = a * c + b * c := by
  rw [mul_comm (a + b) c, left_distrib, mul_comm c a, mul_comm c b]

/-- The packed identity is nonzero for every accepted single-word modulus. -/
theorem one_ne_zero : (1 : GF2n n irr hn hn64 hirr) ≠ 0 := by
  intro h
  have hpoly := congrArg (toPoly (n := n) (irr := irr) (hn := hn) (hn64 := hn64)
    (hirr := hirr)) h
  rw [toPoly_one, toPoly_zero] at hpoly
  exact GF2nPoly.one_ne_zero
    (by simpa using (show 0 < (GF2Poly.ofUInt64Monic irr n).degree by
      rw [GF2Poly.degree_ofUInt64Monic_of_lt_64 irr hn64]
      exact hn)) hpoly

end GF2n
end Hex
