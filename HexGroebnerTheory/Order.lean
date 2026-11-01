/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyTheory.Equiv
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Order.Std
public import Mathlib.Algebra.Group.TransferInstance

@[expose] public section

/-! Transport every lawful Hex monomial comparator through the existing exponent
and polynomial correspondences. The synonym carries the selected comparison;
its additive structure is transported from finitely supported exponent functions.
Leading monomials and coefficients therefore have their existing polynomial
meaning in Mathlib's order-dependent APIs. -/

open Hex
namespace HexGroebnerTheory
noncomputable section
variable {n : Nat} (cmp : Mono n → Mono n → Ordering) [IsMonomialOrder cmp]

/-- Exponent vectors carrying one explicit monomial order. -/
def OrderSyn (_cmp : Mono n → Mono n → Ordering) := Mono n

/-- The existing exponent equivalence on the ordered synonym. -/
def synEquiv : OrderSyn cmp ≃ (Fin n →₀ Nat) := HexMvPolyTheory.monoEquiv

instance : AddCommMonoid (OrderSyn cmp) := (synEquiv cmp).addCommMonoid
instance : Ord (OrderSyn cmp) := ⟨cmp⟩
instance : Std.TransOrd (OrderSyn cmp) := inferInstanceAs (Std.TransCmp cmp)
instance : Std.LawfulEqOrd (OrderSyn cmp) := inferInstanceAs (Std.LawfulEqCmp cmp)
instance : LinearOrder (OrderSyn cmp) := LinearOrder.ofStd _

omit [IsMonomialOrder cmp] in
private theorem add_eq_mul (a b : OrderSyn cmp) :
    a + b = Mono.mul a b := by
  apply (synEquiv cmp).injective
  calc
    (synEquiv cmp) (a + b) = (synEquiv cmp) a + (synEquiv cmp) b :=
      (synEquiv cmp).addEquiv.map_add a b
    _ = (synEquiv cmp) (Mono.mul a b) := (HexMvPolyTheory.monoEquiv_mul a b).symm

instance : IsOrderedAddMonoid (OrderSyn cmp) where
  add_le_add_left a b hab c := by
    rw [← Std.isLE_compare]
    change (cmp (a + c) (b + c)).isLE
    erw [add_eq_mul, add_eq_mul, ← IsMonomialOrder.mul_mono (cmp := cmp) a b c]
    exact Std.isLE_compare.mpr hab

instance : WellFoundedLT (OrderSyn cmp) := by
  let h : WellFounded (fun a b : OrderSyn cmp => cmp a b = .lt) := IsMonomialOrder.wf
  exact h.mono fun _ _ hab => Std.compare_eq_lt.mpr hab

omit [IsMonomialOrder cmp] in
private theorem zero_eq : (0 : OrderSyn cmp) = Mono.zero := by
  apply (synEquiv cmp).injective
  calc
    (synEquiv cmp) 0 = 0 := (synEquiv cmp).addEquiv.map_zero
    _ = (synEquiv cmp) Mono.zero := HexMvPolyTheory.monoEquiv_zero.symm

instance : OrderBot (OrderSyn cmp) where
  bot := 0
  bot_le a := by
    rw [← Std.isLE_compare]
    change (cmp (0 : OrderSyn cmp) a).isLE
    erw [zero_eq]
    have h := IsMonomialOrder.zero_le (cmp := cmp) a
    cases hc : cmp Mono.zero a <;> simp_all

/-- Transport any lawful Hex monomial order through the existing exponent equivalence. -/
def toMonomialOrder : MonomialOrder (Fin n) where
  syn := OrderSyn cmp
  toSyn := (synEquiv cmp).addEquiv.symm
  toSyn_monotone := by
    intro a b hab
    obtain ⟨c, rfl⟩ := exists_add_of_le hab
    rw [map_add]
    exact le_add_of_nonneg_right (show (0 : OrderSyn cmp) ≤ _ from bot_le)

/-- Converting a Hex exponent vector into the ordered synonym recovers it. -/
@[simp] theorem toSyn_mono (a : Mono n) :
    (toMonomialOrder cmp).toSyn (HexMvPolyTheory.monoEquiv a) = (a : OrderSyn cmp) := by
  change (synEquiv cmp).symm ((synEquiv cmp) a) = a
  exact (synEquiv cmp).symm_apply_apply a

/-- Strict comparison agrees exactly with the transported Mathlib order. -/
theorem compare_lt (a b : Mono n) :
    cmp a b = .lt ↔
      (toMonomialOrder cmp).toSyn (HexMvPolyTheory.monoEquiv a) <
        (toMonomialOrder cmp).toSyn (HexMvPolyTheory.monoEquiv b) := by
  rw [toSyn_mono, toSyn_mono]
  exact Std.compare_eq_lt (α := OrderSyn cmp)

/-- Non-strict comparison agrees with the transported order. -/
theorem compare_le (a b : Mono n) :
    (cmp a b).isLE ↔
      (toMonomialOrder cmp).toSyn (HexMvPolyTheory.monoEquiv a) ≤
        (toMonomialOrder cmp).toSyn (HexMvPolyTheory.monoEquiv b) := by
  rw [toSyn_mono, toSyn_mono]
  exact Std.isLE_compare (α := OrderSyn cmp)

omit [IsMonomialOrder cmp] in
/-- Exact monomial divisibility is pointwise order on exponent functions. -/
theorem divides_iff (a b : Mono n) :
    Mono.dvd a b = true ↔ HexMvPolyTheory.monoEquiv a ≤ HexMvPolyTheory.monoEquiv b := by
  simp only [Mono.dvd_eq_true_iff, Finsupp.le_def, HexMvPolyTheory.monoEquiv_apply]

omit [IsMonomialOrder cmp] in
/-- Monomial least common multiples become pointwise suprema. -/
theorem lcm_eq (a b : Mono n) :
    HexMvPolyTheory.monoEquiv (Mono.lcm a b) =
      HexMvPolyTheory.monoEquiv a ⊔ HexMvPolyTheory.monoEquiv b := by
  ext i
  simp only [HexMvPolyTheory.monoEquiv_apply, Mono.getElem_lcm, Finsupp.sup_apply]

open scoped HexMvPolyTheory
variable {R : Type*} [CommSemiring R] [DecidableEq R]

/-- A nonzero Hex leading monomial is exactly Mathlib's ordered degree. -/
theorem leading_degree {p : Hex.MvPoly n R cmp} {m : Mono n} {c : R}
    (h : p.leadingTerm = some (m, c)) :
    (toMonomialOrder cmp).degree (HexMvPolyTheory.toMvPolynomial p) =
      HexMvPolyTheory.monoEquiv m := by
  apply (toMonomialOrder cmp).toSyn.injective
  apply le_antisymm
  · apply MonomialOrder.degree_le_iff.mpr
    intro d hd
    obtain ⟨k, rfl⟩ := HexMvPolyTheory.monoEquiv.surjective d
    apply (compare_le cmp k m).mp
    apply Hex.MvPoly.le_leadingTerm h k
    have hc := MvPolynomial.mem_support_iff.mp hd
    rw [HexMvPolyTheory.coeff_toMvPolynomial] at hc
    exact (Hex.MvPoly.mem_monomials_iff k p).mpr hc
  · apply MonomialOrder.le_degree
    rw [MvPolynomial.mem_support_iff, HexMvPolyTheory.coeff_toMvPolynomial]
    have hc := (Hex.MvPoly.leadingTerm_eq_some_iff p m c).mp h |>.1
    rw [Hex.MvPoly.coeff_eq_of_leadingTerm h]
    intro hz
    exact p.coeff?_ne_zero m (hc.trans (congrArg some hz))

/-- Leading coefficients agree under the existing polynomial conversion. -/
theorem leading_coefficient {p : Hex.MvPoly n R cmp} {m : Mono n} {c : R}
    (h : p.leadingTerm = some (m, c)) :
    (toMonomialOrder cmp).leadingCoeff (HexMvPolyTheory.toMvPolynomial p) = c := by
  rw [MonomialOrder.leadingCoeff, leading_degree cmp h,
    HexMvPolyTheory.coeff_toMvPolynomial, Hex.MvPoly.coeff_eq_of_leadingTerm h]

end
end HexGroebnerTheory
