/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Field
public import HexRealFormulaMathlib.Semantics
public import HexPolyMathlib.GrindTransport
public import HexPolyMathlib.PolynomialEquivalence

public section

/-! Interpret shared polynomial syntax in a fixed real coefficient ring. -/

namespace Hex.RCF.RealCoefficients.FieldSpecialize

open Hex.RealFormula
open scoped HexMvPolyMathlib

attribute [local instance 2500] Semiring.toGrindSemiring

variable {D : Type u} [CommRing D] [DecidableEq D]

local instance : CommRing (DensePoly D) := HexPolyMathlib.denseCommRing

/-- Substitute fixed coefficients while retaining the last coordinate as the
polynomial variable. -/
@[expose] def coordinate (values : Fin n → D) (i : Fin (n + 1)) : DensePoly D :=
  if h : i.val < n then DensePoly.C (values ⟨i.val, h⟩)
  else DensePoly.monomial 1 1

/-- Evaluate the shared syntax in the existing executable dense-polynomial ring. -/
@[expose] def polynomial (values : Fin n → D)
    (p : RealFormula.Poly (n + 1)) : DensePoly D :=
  MvPoly.eval₂ (Int.castRingHom (DensePoly D)) (coordinate values) p

/-- Interpret a specialized polynomial at a real argument. -/
@[expose] noncomputable def evaluate (f : D →+* ℝ) (x : ℝ) : DensePoly D →+* ℝ :=
  (Polynomial.eval₂RingHom f x).comp HexPolyMathlib.equiv.toRingHom

theorem evaluate_coordinate (f : D →+* ℝ) (values : Fin n → D)
    (x : ℝ) (i : Fin (n + 1)) :
    evaluate f x (coordinate values i) = append (fun j => f (values j)) x i := by
  simp only [coordinate, append]
  split <;> simp [evaluate, HexPolyMathlib.toPolynomial_C,
    HexPolyMathlib.toPolynomial_monomial]

/-- Executable specialization has exactly the value of the source polynomial. -/
theorem polynomial_eval (f : D →+* ℝ) (values : Fin n → D)
    (p : RealFormula.Poly (n + 1)) (x : ℝ) :
    evaluate f x (polynomial values p) =
      p.eval (append (fun j => f (values j)) x) := by
  unfold polynomial RealFormula.Poly.eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial,
    ← HexMvPolyMathlib.eval₂_toMvPolynomial]
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (evaluate f x).comp (Int.castRingHom (DensePoly D)) =
      Int.castRingHom ℝ := by ext; simp
  rw [hc]
  congr 1
  funext i
  exact evaluate_coordinate f values x i

variable {p : ZPoly} {root : SimpleRoot p} [ZPoly.CheckedIrreducible p]

/-- Compile substitution using only the fixed field's ordinary total
coefficient operations. No proof-bearing field instance is evaluated. -/
@[expose] def literalCoordinate (values : Fin n → PolyQuot p root)
    (i : Fin (n + 1)) : DensePoly (PolyQuot p root) :=
  if h : i.val < n then DensePoly.C (values ⟨i.val, h⟩)
  else DensePoly.monomial 1 1

@[expose] def literalPolynomial (values : Fin n → PolyQuot p root)
    (q : RealFormula.Poly (n + 1)) : DensePoly (PolyQuot p root) :=
  q.foldTerms (fun acc m (c : Int) =>
    acc + DensePoly.C (Int.cast c : PolyQuot p root) *
      Mono.prod (literalCoordinate values) m) 0

noncomputable local instance : Field (PolyQuot p root) := Hex.PolyQuot.field p root

/-- Rational sample points retain their ordinary real value. -/
theorem value_ofRat (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0) (q : Rat) :
    Field.value rep (PolyQuot.ofRat q : PolyQuot p root) = (q : ℝ) := by
  apply Complex.ofReal_injective
  rw [Field.value_complex rep hrep hr]
  change PolyQuot.toComplex (q • (1 : PolyQuot p root)) rep hrep = _
  rw [PolyQuot.map_smul, PolyQuot.map_one, mul_one]
  norm_cast

theorem literalPolynomial_eq (values : Fin n → PolyQuot p root)
    (q : RealFormula.Poly (n + 1)) :
    literalPolynomial values q = polynomial values q := by
  unfold literalPolynomial polynomial MvPoly.eval₂
  congr 1
  funext acc m c
  have hcoord : literalCoordinate values = coordinate values := rfl
  rw [hcoord]
  have hcast : DensePoly.C (Int.cast c : PolyQuot p root) =
      (Int.cast c : DensePoly (PolyQuot p root)) := by
    apply HexPolyMathlib.equiv.injective
    simp
  rw [hcast]
  rfl

/-- The selected fixed-field interpretation as a ring map. Its operation
proofs come from the existing coordinate-field embedding. -/
@[expose] noncomputable def realHom (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0) :
    PolyQuot p root →+* ℝ where
  toFun := Field.value rep
  map_zero' := Field.value_zero rep hrep hr
  map_one' := Field.value_one rep hrep hr
  map_add' := Field.value_add rep hrep hr
  map_mul' := Field.value_mul rep hrep hr

/-- A source formula with literal field coefficients evaluates at precisely
the real embedding named by the selected root. -/
theorem polynomial_real (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (values : Fin n → PolyQuot p root)
    (q : RealFormula.Poly (n + 1)) (x : ℝ) :
    evaluate (realHom rep hrep hr) x (polynomial values q) =
      q.eval (append (fun j => Field.value rep (values j)) x) := by
  exact polynomial_eval (realHom rep hrep hr) values q x

/-- The compiled substitution has the same source interpretation. -/
theorem literalPolynomial_real (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (hr : rep.root.im = 0)
    (values : Fin n → PolyQuot p root)
    (q : RealFormula.Poly (n + 1)) (x : ℝ) :
    evaluate (realHom rep hrep hr) x (literalPolynomial values q) =
      q.eval (append (fun j => Field.value rep (values j)) x) := by
  rw [literalPolynomial_eq]
  exact polynomial_real rep hrep hr values q x

end Hex.RCF.RealCoefficients.FieldSpecialize
