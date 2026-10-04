/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SpecializeFractionRing

public section

namespace Hex.RealClosure

attribute [local instance 2000] Field.toGrindField

variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

/-- A coefficient interpretation on a subring. Certificate transfer requires
membership only for the actual finite coefficient inventory it uses. -/
structure CoefficientMap (F G : Type) [Field F] [Field G] where
  domain : Subring F
  value : domain →+* G

namespace CoefficientMap

variable (interpretation : CoefficientMap F G)

/-- Read the interpreted coefficient. Zero is the total fallback outside the
domain; preservation theorems require membership for their actual operands. -/
noncomputable def map (coefficient : F) : G := by
  classical
  exact if member : coefficient ∈ interpretation.domain then
    interpretation.value ⟨coefficient, member⟩ else 0

theorem map_mem (coefficient : F) (member : coefficient ∈ interpretation.domain) :
    interpretation.map coefficient = interpretation.value ⟨coefficient, member⟩ := by
  simp only [map, dite_eq_left member]

theorem map_zero : interpretation.map 0 = 0 := by
  rw [map_mem _ _ interpretation.domain.zero_mem]
  exact interpretation.value.map_zero

theorem map_one : interpretation.map 1 = 1 := by
  rw [map_mem _ _ interpretation.domain.one_mem]
  exact interpretation.value.map_one

theorem map_add {first second : F} (left : first ∈ interpretation.domain)
    (right : second ∈ interpretation.domain) :
    interpretation.map (first + second) = interpretation.map first + interpretation.map second := by
  rw [map_mem _ _ (interpretation.domain.add_mem left right), map_mem _ _ left, map_mem _ _ right]
  exact interpretation.value.map_add ⟨first, left⟩ ⟨second, right⟩

theorem map_mul {first second : F} (left : first ∈ interpretation.domain)
    (right : second ∈ interpretation.domain) :
    interpretation.map (first * second) = interpretation.map first * interpretation.map second := by
  rw [map_mem _ _ (interpretation.domain.mul_mem left right), map_mem _ _ left, map_mem _ _ right]
  exact interpretation.value.map_mul ⟨first, left⟩ ⟨second, right⟩

theorem map_neg {coefficient : F} (member : coefficient ∈ interpretation.domain) :
    interpretation.map (-coefficient) = -interpretation.map coefficient := by
  rw [map_mem _ _ (interpretation.domain.neg_mem member), map_mem _ _ member]
  exact interpretation.value.map_neg ⟨coefficient, member⟩

/-- Substitute the actual stored array and retain native normalization. -/
noncomputable def polynomial (p : Hex.DensePoly F) : Hex.DensePoly G :=
  Hex.DensePoly.ofCoeffs (p.toArray.map interpretation.map)

/-- Implicit zero coefficients are also preserved by the total reader. -/
theorem polynomial_coeff (p : Hex.DensePoly F) (i : Nat) :
    (interpretation.polynomial p).coeff i = interpretation.map (p.coeff i) := by
  rw [polynomial, Hex.DensePoly.coeff_ofCoeffs]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases read : p.toArray[i]? with
  | none =>
    have zero : p.coeff i = 0 := by
      rw [← Hex.DensePoly.toArray_getD, Array.getD_eq_getD_getElem?, read]
      rfl
    simp only [Option.map_none, Option.getD_none, zero, map_zero]
    rfl
  | some coefficient =>
    have original : p.coeff i = coefficient := by
      rw [← Hex.DensePoly.toArray_getD, Array.getD_eq_getD_getElem?, read]
      rfl
    simp only [Option.map_some, Option.getD_some, original]

/-- The finite stored coefficient guards lift the entire actual polynomial
into the interpretation's subring. -/
theorem polynomial_lift (p : Hex.DensePoly F)
    (guards : ∀ i < p.size, p.coeff i ∈ interpretation.domain) :
    ∃ q : Polynomial interpretation.domain,
      q.map interpretation.domain.subtype = HexPolyMathlib.toPolynomial p := by
  classical
  apply Polynomial.mem_lifts _ |>.mp
  apply Polynomial.lifts_iff_coeff_lifts _ |>.mpr
  intro i
  refine ⟨⟨(HexPolyMathlib.toPolynomial p).coeff i, ?_⟩, rfl⟩
  rw [HexPolyMathlib.coeff_toPolynomial]
  by_cases stored : i < p.size
  · exact guards i stored
  · rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt stored)]
    exact interpretation.domain.zero_mem

/-- Mapping a regular lift is the same native coefficient substitution,
independently of the lift's membership proofs. -/
theorem polynomial_map (p : Hex.DensePoly F) (q : Polynomial interpretation.domain)
    (lift : q.map interpretation.domain.subtype = HexPolyMathlib.toPolynomial p) :
    HexPolyMathlib.toPolynomial (interpretation.polynomial p) = q.map interpretation.value := by
  classical
  ext i
  rw [HexPolyMathlib.coeff_toPolynomial, polynomial_coeff, Polynomial.coeff_map]
  have coefficient := congrArg (fun p => p.coeff i) lift
  simp only [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial] at coefficient
  change (q.coeff i).val = p.coeff i at coefficient
  rw [← coefficient, map_mem _ _ (q.coeff i).property]

/-- Only the finitely stored zero tests are needed to preserve and reflect
the zero polynomial. -/
theorem polynomial_zero (p : Hex.DensePoly F)
    (reflects : ∀ i < p.size, interpretation.map (p.coeff i) = 0 ↔ p.coeff i = 0) :
    interpretation.polynomial p = 0 ↔ p = 0 := by
  constructor
  · intro zero
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [Hex.DensePoly.coeff_zero]
    by_cases stored : i < p.size
    · apply (reflects i stored).mp
      rw [← polynomial_coeff, zero, Hex.DensePoly.coeff_zero]
    · exact Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt stored)
  · intro zero
    subst p
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [polynomial_coeff, Hex.DensePoly.coeff_zero, map_zero, Hex.DensePoly.coeff_zero]

/-- The head degree is retained when its actual finite zero pattern is
retained. No zero reflection outside those coefficients is assumed. -/
theorem polynomial_degree (p : Hex.DensePoly F)
    (reflects : ∀ i < p.size, interpretation.map (p.coeff i) = 0 ↔ p.coeff i = 0) :
    (interpretation.polynomial p).natDegree = p.natDegree := by
  by_cases zero : p = 0
  · rw [zero, (polynomial_zero interpretation 0 (by simp [map_zero])).mpr rfl,
      Hex.DensePoly.natDegree_zero]
    rfl
  · have positive : 0 < p.size := Nat.pos_of_ne_zero
      (fun empty => zero ((Hex.DensePoly.size_eq_zero_iff p).mp empty))
    rw [← HexPolyMathlib.natDegree_toPolynomial, Hex.DensePoly.natDegree_eq_size_sub_one]
    apply le_antisymm
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro i high
      rw [HexPolyMathlib.coeff_toPolynomial, polynomial_coeff,
        Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)]
      change interpretation.map (0 : F) = 0
      exact map_zero interpretation
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [HexPolyMathlib.coeff_toPolynomial, polynomial_coeff]
      exact (reflects (p.size - 1) (by omega)).not.mpr
        (Hex.DensePoly.coeff_last_ne_zero_of_pos_size p positive)

/-- The actual leading coefficient is the interpretation of the source
leading coefficient under the finite zero-pattern guard. -/
theorem polynomial_leading (p : Hex.DensePoly F)
    (reflects : ∀ i < p.size, interpretation.map (p.coeff i) = 0 ↔ p.coeff i = 0) :
    (interpretation.polynomial p).leadingCoeff = interpretation.map p.leadingCoeff := by
  have leading : p.coeff p.natDegree = p.leadingCoeff := by
    rw [← HexPolyMathlib.coeff_toPolynomial, ← HexPolyMathlib.natDegree_toPolynomial,
      ← Polynomial.leadingCoeff, HexPolyMathlib.leadingCoeff_toPolynomial]
  rw [← HexPolyMathlib.leadingCoeff_toPolynomial, Polynomial.leadingCoeff,
    HexPolyMathlib.natDegree_toPolynomial, HexPolyMathlib.coeff_toPolynomial,
    polynomial_degree interpretation p reflects, polynomial_coeff, leading]

/-- Actual polynomial addition specializes using only regularity of the
finitely stored input coefficients. Intermediate sums need no extra guards. -/
theorem polynomial_add (p q : Hex.DensePoly F)
    (left : ∀ i < p.size, p.coeff i ∈ interpretation.domain)
    (right : ∀ i < q.size, q.coeff i ∈ interpretation.domain) :
    interpretation.polynomial (p + q) = interpretation.polynomial p + interpretation.polynomial q := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift interpretation p left
  obtain ⟨Q, hq⟩ := polynomial_lift interpretation q right
  have lift : (P + Q).map interpretation.domain.subtype = HexPolyMathlib.toPolynomial (p + q) := by
    rw [Polynomial.map_add, hp, hq, HexPolyMathlib.toPolynomial_add]
  apply (HexPolyMathlib.equiv (R := G)).injective
  change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
  rw [polynomial_map interpretation (p + q) (P + Q) lift, HexPolyMathlib.toPolynomial_add,
    polynomial_map interpretation p P hp, polynomial_map interpretation q Q hq, Polynomial.map_add]

/-- Actual schoolbook polynomial multiplication specializes on the regular
input coefficients. Closure of the regular ring handles every accumulation. -/
theorem polynomial_mul (p q : Hex.DensePoly F)
    (left : ∀ i < p.size, p.coeff i ∈ interpretation.domain)
    (right : ∀ i < q.size, q.coeff i ∈ interpretation.domain) :
    interpretation.polynomial (p * q) = interpretation.polynomial p * interpretation.polynomial q := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift interpretation p left
  obtain ⟨Q, hq⟩ := polynomial_lift interpretation q right
  have lift : (P * Q).map interpretation.domain.subtype = HexPolyMathlib.toPolynomial (p * q) := by
    rw [Polynomial.map_mul, hp, hq, HexPolyMathlib.toPolynomial_mul]
  apply (HexPolyMathlib.equiv (R := G)).injective
  change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
  rw [polynomial_map interpretation (p * q) (P * Q) lift, HexPolyMathlib.toPolynomial_mul,
    polynomial_map interpretation p P hp, polynomial_map interpretation q Q hq, Polynomial.map_mul]

/-- Actual polynomial subtraction specializes under the two input coefficient
families' denominator guards. -/
theorem polynomial_sub (p q : Hex.DensePoly F)
    (left : ∀ i < p.size, p.coeff i ∈ interpretation.domain)
    (right : ∀ i < q.size, q.coeff i ∈ interpretation.domain) :
    interpretation.polynomial (p - q) = interpretation.polynomial p - interpretation.polynomial q := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift interpretation p left
  obtain ⟨Q, hq⟩ := polynomial_lift interpretation q right
  have lift : (P - Q).map interpretation.domain.subtype = HexPolyMathlib.toPolynomial (p - q) := by
    rw [Polynomial.map_sub, hp, hq, HexPolyMathlib.toPolynomial_sub]
  apply (HexPolyMathlib.equiv (R := G)).injective
  change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
  rw [polynomial_map interpretation (p - q) (P - Q) lift, HexPolyMathlib.toPolynomial_sub,
    polynomial_map interpretation p P hp, polynomial_map interpretation q Q hq, Polynomial.map_sub]

/-- Native differentiation specializes with the original coefficient guards;
natural casts and multiplication are preserved by regular evaluation. -/
theorem polynomial_derivative (p : Hex.DensePoly F)
    (guards : ∀ i < p.size, p.coeff i ∈ interpretation.domain) :
    interpretation.polynomial p.derivative = (interpretation.polynomial p).derivative := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift interpretation p guards
  have lift : P.derivative.map interpretation.domain.subtype =
      HexPolyMathlib.toPolynomial p.derivative := by
    rw [← Polynomial.derivative_map, hp, HexPolyMathlib.toPolynomial_derivative]
  apply (HexPolyMathlib.equiv (R := G)).injective
  change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
  rw [polynomial_map interpretation p.derivative P.derivative lift,
    HexPolyMathlib.toPolynomial_derivative, polynomial_map interpretation p P hp,
    Polynomial.derivative_map]

/-- Scaling specializes using only the scalar and stored coefficient guards. -/
theorem polynomial_scale (p : Hex.DensePoly F) (c : F)
    (scalar : c ∈ interpretation.domain)
    (guards : ∀ i < p.size, p.coeff i ∈ interpretation.domain) :
    interpretation.polynomial (Hex.DensePoly.scale c p) =
      Hex.DensePoly.scale (interpretation.map c) (interpretation.polynomial p) := by
  classical
  rw [map_mem _ _ scalar]
  obtain ⟨P, hp⟩ := polynomial_lift interpretation p guards
  have lift : (Polynomial.C (⟨c, scalar⟩ : interpretation.domain) * P).map
      interpretation.domain.subtype = HexPolyMathlib.toPolynomial (Hex.DensePoly.scale c p) := by
    rw [Polynomial.map_mul, Polynomial.map_C, hp, HexPolyMathlib.toPolynomial_scale]
    rfl
  apply (HexPolyMathlib.equiv (R := G)).injective
  change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
  rw [polynomial_map interpretation (Hex.DensePoly.scale c p) _ lift,
    HexPolyMathlib.toPolynomial_scale, polynomial_map interpretation p P hp,
    Polynomial.map_mul, Polynomial.map_C]

/-- Horner evaluation at a finite endpoint specializes using only regularity
of that endpoint and the original polynomial coefficients. -/
theorem polynomial_eval (p : Hex.DensePoly F) (x : F)
    (point : x ∈ interpretation.domain)
    (guards : ∀ i < p.size, p.coeff i ∈ interpretation.domain) :
    interpretation.map (p.eval x) = (interpretation.polynomial p).eval (interpretation.map x) := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift interpretation p guards
  have value : (P.eval (⟨x, point⟩ : interpretation.domain)).val = p.eval x := by
    have h := Polynomial.eval_map_apply (p := P) (f := interpretation.domain.subtype)
      (⟨x, point⟩ : interpretation.domain)
    rw [hp] at h
    change (HexPolyMathlib.toPolynomial p).eval x = (P.eval ⟨x, point⟩).val at h
    rw [HexPolyMathlib.eval_toPolynomial] at h
    exact h.symm
  rw [← value, map_mem _ _ (P.eval ⟨x, point⟩).property]
  change interpretation.value (P.eval ⟨x, point⟩) = _
  rw [← Polynomial.eval_map_apply]
  rw [← polynomial_map interpretation p P hp, HexPolyMathlib.eval_toPolynomial]
  rw [map_mem _ _ point]

end CoefficientMap
end Hex.RealClosure
