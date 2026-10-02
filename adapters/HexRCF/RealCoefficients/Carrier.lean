/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Specialize
public import HexPolyMathlib.Interpret

public section

/-! The atom product before squarefree preparation. -/

namespace Hex.RCF.RealCoefficients.Specialize

open Hex.RealFormula HexPolyMathlib.Interpret

local instance : CommRing (DensePoly RealAlgebraicNumber) := HexPolyMathlib.denseCommRing

theorem toReal_eq_zero (a : RealAlgebraicNumber) :
    a.toReal = 0 ↔ a = 0 := by
  rw [← RealAlgebraicNumber.zero_toReal]
  exact RealAlgebraicNumber.toReal_injective.eq_iff

/-- The ring-hom evaluation used for specialization is the same evaluation
used by Sturm's real interpretation. -/
theorem evaluate_interpret (x : ℝ) (p : DensePoly RealAlgebraicNumber) :
    evaluate x p =
      (interpret RealAlgebraicNumber.toReal toReal_eq_zero p).eval x := by
  have hmap : interpret RealAlgebraicNumber.toReal toReal_eq_zero p =
      (HexPolyMathlib.toPolynomial p).map RealAlgebraicNumber.toRealHom := by
    ext i
    simp [RealAlgebraicNumber.toRealHom]
  rw [hmap, Polynomial.eval_map]
  simp [evaluate]

/-- The product omits identically zero atoms, whose signs are already known.
The empty product is one. Repeated factors remain: this is input to a later
checked squarefree preparation, not itself an isolation head. -/
@[expose] def product (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) : DensePoly RealAlgebraicNumber :=
  ((formula.polys.map (polynomial values)).filter (fun p => !p.isZero)).prod

private theorem evaluate_prod_zero (x : ℝ)
    (ps : List (DensePoly RealAlgebraicNumber)) (p : DensePoly RealAlgebraicNumber)
    (hp : p ∈ ps) (hz : evaluate x p = 0) : evaluate x ps.prod = 0 := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      rw [List.prod_cons, map_mul]
      rcases hp with rfl | hp
      · simp [hz]
      · simp [ih hp]

/- An atom is either identically zero or its real roots are roots of the
product. In particular, filtering zero atoms cannot lose a root. -/
private theorem atom_root (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (p : Hex.RealFormula.Poly (n + 1))
    (hp : p ∈ formula.polys) :
    polynomial values p = 0 ∨
      (∀ x, evaluate x (polynomial values p) = 0 →
        evaluate x (product values formula) = 0) := by
  let q := polynomial values p
  by_cases hq : q.isZero = true
  · left
    exact (DensePoly.size_eq_zero_iff q).mp
      ((DensePoly.isZero_eq_true_iff q).mp hq)
  · right
    intro x hx
    apply evaluate_prod_zero x _ q
    · apply List.mem_filter.mpr
      refine ⟨List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
      simp [hq]
    · exact hx

/-- The root coverage required by the checked open-cell formula theorem follows
from the actual specialized product, including an identically zero atom. -/
theorem atom_roots (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (p : Hex.RealFormula.Poly (n + 1))
    (hp : p ∈ formula.polys) :
    interpret RealAlgebraicNumber.toReal toReal_eq_zero (polynomial values p) = 0 ∨
      (∀ x, (interpret RealAlgebraicNumber.toReal toReal_eq_zero
          (polynomial values p)).IsRoot x →
        (interpret RealAlgebraicNumber.toReal toReal_eq_zero
          (product values formula)).IsRoot x) := by
  rcases atom_root values formula p hp with hzero | hroot
  · exact Or.inl ((interpret_eq_zero RealAlgebraicNumber.toReal toReal_eq_zero _).mpr hzero)
  · right
    intro x hx
    simp only [Polynomial.IsRoot] at hx ⊢
    rw [← evaluate_interpret x] at hx ⊢
    exact hroot x hx

/-- A specialized atom has exactly the value of its source polynomial under
the chosen real embeddings of all fixed coefficients. -/
theorem atom_eval (values : Fin n → RealAlgebraicNumber)
    (p : Hex.RealFormula.Poly (n + 1)) (x : ℝ) :
    (interpret RealAlgebraicNumber.toReal toReal_eq_zero
      (polynomial values p)).eval x =
      p.eval (Hex.RealFormula.append (fun i => (values i).toReal) x) := by
  rw [← evaluate_interpret]
  exact polynomial_eval values p x

private theorem interpret_product
    (ps : List (DensePoly RealAlgebraicNumber)) :
    interpret RealAlgebraicNumber.toReal toReal_eq_zero ps.prod =
      (ps.map (interpret RealAlgebraicNumber.toReal toReal_eq_zero)).prod := by
  induction ps with
  | nil =>
      simp [interpret_one, RealAlgebraicNumber.one_toReal]
  | cons p ps ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons,
        interpret_mul RealAlgebraicNumber.toReal toReal_eq_zero
          RealAlgebraicNumber.add_toReal RealAlgebraicNumber.mul_toReal, ih]

/-- The product of all nonzero specialized atoms cannot vanish identically. -/
theorem product_ne_zero (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) : product values formula ≠ 0 := by
  let ps := (formula.polys.map (polynomial values)).filter (fun p => !p.isZero)
  have hfactor : ∀ p ∈ ps,
      interpret RealAlgebraicNumber.toReal toReal_eq_zero p ≠ 0 := by
    intro p hp hzero
    have hnonzero : p.isZero = false := by
      have h := (List.mem_filter.mp hp).2
      cases hzeroBool : p.isZero <;> simp_all
    have hpzero := (interpret_eq_zero RealAlgebraicNumber.toReal toReal_eq_zero p).mp hzero
    subst p
    have hz : (0 : DensePoly RealAlgebraicNumber).isZero = true := by decide
    exact Bool.false_ne_true (hnonzero.symm.trans hz)
  intro hzero
  have hproduct : (ps.map (interpret RealAlgebraicNumber.toReal toReal_eq_zero)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hmem
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hmem
    exact hfactor p hp heq
  apply hproduct
  rw [← interpret_product]
  exact (interpret_eq_zero RealAlgebraicNumber.toReal toReal_eq_zero _).mpr hzero

end Hex.RCF.RealCoefficients.Specialize
