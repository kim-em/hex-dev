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

private theorem interpret_product (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (ps : List (DensePoly (PolyQuot p root))) :
    interpret (Field.value rep) (Field.value_eq_zero rep hrep hr) ps.prod =
      (ps.map (interpret (Field.value rep)
        (Field.value_eq_zero rep hrep hr))).prod := by
  induction ps with
  | nil =>
      simp [interpret_one, Field.value_one rep hrep hr]
  | cons q qs ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons,
        interpret_mul (Field.value rep) (Field.value_eq_zero rep hrep hr)
          (Field.value_add rep hrep hr) (Field.value_mul rep hrep hr), ih]

/-- Omitting identically zero atoms leaves a nonzero product, including when
the formula has no atoms. -/
theorem product_ne_zero (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (values : Fin n → PolyQuot p root) (formula : QF (n + 1)) :
    product values formula ≠ 0 := by
  let ps := (formula.polys.map (FieldSpecialize.literalPolynomial values)).filter
    (fun q => !q.isZero)
  have hfactor : ∀ q ∈ ps,
      interpret (Field.value rep) (Field.value_eq_zero rep hrep hr) q ≠ 0 := by
    intro q hq hzero
    have hnonzero : q.isZero = false := by
      have h := (List.mem_filter.mp hq).2
      cases hzeroBool : q.isZero <;> simp_all
    have hqzero := (interpret_eq_zero (Field.value rep)
      (Field.value_eq_zero rep hrep hr) q).mp hzero
    subst q
    have hz : (0 : DensePoly (PolyQuot p root)).isZero = true := rfl
    exact Bool.false_ne_true (hnonzero.symm.trans hz)
  intro hzero
  have hproduct :
      (ps.map (interpret (Field.value rep)
        (Field.value_eq_zero rep hrep hr))).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hmem
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hmem
    exact hfactor q hq heq
  apply hproduct
  rw [← interpret_product rep hrep hr]
  exact (interpret_eq_zero (Field.value rep)
    (Field.value_eq_zero rep hrep hr) _).mpr (by simpa only [product_eq] using hzero)

end Hex.RCF.RealCoefficients.FieldCarrier
