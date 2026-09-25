/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldSpecialize
public import HexPolyMathlib.Interpret

public section

/-! Root coverage for the compiled product of fixed-field atoms. -/

namespace Hex.RCF.RealCoefficients.FieldCarrier

open Hex.RealFormula HexPolyMathlib.Interpret

variable {p : ZPoly} {root : SimpleRoot p} [ZPoly.CheckedIrreducible p]

/-- The product uses only ordinary reduced-coordinate operations. A zero atom
is omitted because its sign is already identically zero. -/
@[expose] def product (values : Fin n → PolyQuot p root)
    (formula : QF (n + 1)) : DensePoly (PolyQuot p root) :=
  ((formula.polys.map (FieldSpecialize.literalPolynomial values)).filter
    (fun q => !q.isZero)).foldr (· * ·) 1

noncomputable local instance : Field (PolyQuot p root) := Hex.PolyQuot.field p root
noncomputable local instance : CommRing (DensePoly (PolyQuot p root)) :=
  HexPolyMathlib.denseCommRing

noncomputable local instance : IsDomain (DensePoly (PolyQuot p root)) :=
  MulEquiv.isDomain (Polynomial (PolyQuot p root))
    (HexPolyMathlib.equiv (R := PolyQuot p root)).toMulEquiv

omit [ZPoly.CheckedIrreducible p] in
private theorem product_eq (values : Fin n → PolyQuot p root)
    (formula : QF (n + 1)) :
    product values formula =
      ((formula.polys.map (FieldSpecialize.literalPolynomial values)).filter
        (fun q => !q.isZero)).prod := by
  rfl

/-- Specialization's real evaluator is the same interpretation used by the
shared Sturm–Tarski soundness theorems. -/
theorem evaluate_interpret (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (x : ℝ) (q : DensePoly (PolyQuot p root)) :
    FieldSpecialize.evaluate (FieldSpecialize.realHom rep hrep hr) x q =
      (interpret (Field.value rep) (Field.value_eq_zero rep hrep hr) q).eval x := by
  have hmap : interpret (Field.value rep) (Field.value_eq_zero rep hrep hr) q =
      (HexPolyMathlib.toPolynomial q).map
        (FieldSpecialize.realHom rep hrep hr) := by
    ext i
    simp [FieldSpecialize.realHom]
  rw [hmap, Polynomial.eval_map]
  rfl

/-- A compiled field atom has the value of its source polynomial. -/
theorem atom_eval (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (values : Fin n → PolyQuot p root)
    (q : RealFormula.Poly (n + 1)) (x : ℝ) :
    (interpret (Field.value rep) (Field.value_eq_zero rep hrep hr)
      (FieldSpecialize.literalPolynomial values q)).eval x =
      q.eval (append (fun j => Field.value rep (values j)) x) := by
  rw [← evaluate_interpret rep hrep hr x]
  exact FieldSpecialize.literalPolynomial_real rep hrep hr values q x

private theorem evaluate_prod_zero (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (x : ℝ) (ps : List (DensePoly (PolyQuot p root)))
    (q : DensePoly (PolyQuot p root)) (hq : q ∈ ps)
    (hz : FieldSpecialize.evaluate (FieldSpecialize.realHom rep hrep hr) x q = 0) :
    FieldSpecialize.evaluate (FieldSpecialize.realHom rep hrep hr) x ps.prod = 0 := by
  induction ps with
  | nil => simp at hq
  | cons first rest ih =>
      simp only [List.mem_cons] at hq
      rw [List.prod_cons, map_mul]
      rcases hq with rfl | hq
      · simp [hz]
      · simp [ih hq]

private theorem atom_root (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (values : Fin n → PolyQuot p root) (formula : QF (n + 1))
    (atom : RealFormula.Poly (n + 1)) (hatom : atom ∈ formula.polys) :
    FieldSpecialize.literalPolynomial values atom = 0 ∨
      (∀ x,
        FieldSpecialize.evaluate (FieldSpecialize.realHom rep hrep hr) x
          (FieldSpecialize.literalPolynomial values atom) = 0 →
        FieldSpecialize.evaluate (FieldSpecialize.realHom rep hrep hr) x
          (product values formula) = 0) := by
  let q := FieldSpecialize.literalPolynomial values atom
  by_cases hq : q.isZero = true
  · left
    exact (DensePoly.size_eq_zero_iff q).mp
      ((DensePoly.isZero_eq_true_iff q).mp hq)
  · right
    intro x hx
    rw [product_eq]
    apply evaluate_prod_zero rep hrep hr x _ q
    · apply List.mem_filter.mpr
      refine ⟨List.mem_map.mpr ⟨atom, hatom, rfl⟩, ?_⟩
      simp [hq]
    · exact hx

/-- Every nonzero source atom root remains in the compiled product. -/
theorem atom_roots (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (values : Fin n → PolyQuot p root) (formula : QF (n + 1))
    (atom : RealFormula.Poly (n + 1)) (hatom : atom ∈ formula.polys) :
    interpret (Field.value rep) (Field.value_eq_zero rep hrep hr)
      (FieldSpecialize.literalPolynomial values atom) = 0 ∨
      (∀ x, (interpret (Field.value rep) (Field.value_eq_zero rep hrep hr)
          (FieldSpecialize.literalPolynomial values atom)).IsRoot x →
        (interpret (Field.value rep) (Field.value_eq_zero rep hrep hr)
          (product values formula)).IsRoot x) := by
  rcases atom_root rep hrep hr values formula atom hatom with hz | hroot
  · exact Or.inl ((interpret_eq_zero (Field.value rep)
        (Field.value_eq_zero rep hrep hr) _).mpr hz)
  · right
    intro x hx
    simp only [Polynomial.IsRoot] at hx ⊢
    rw [← evaluate_interpret rep hrep hr x] at hx ⊢
    exact hroot x hx

/-- Omitting identically zero atoms leaves a nonzero product, including when
the formula has no atoms. -/
theorem product_ne_zero (values : Fin n → PolyQuot p root)
    (formula : QF (n + 1)) :
    product values formula ≠ 0 := by
  rw [product_eq]
  apply List.prod_ne_zero
  intro hq
  have htest := (List.mem_filter.mp hq).2
  simp at htest
  have hz : (0 : DensePoly (PolyQuot p root)).isZero = true := rfl
  exact Bool.false_ne_true (htest.symm.trans hz)

end Hex.RCF.RealCoefficients.FieldCarrier
