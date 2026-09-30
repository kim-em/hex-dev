/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SpecializePolynomial
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Polynomial.Lifts

public section

namespace Hex.RealClosure.Specialize

attribute [local instance 2000] Field.toGrindField

variable {F : Type} [Field F] [DecidableEq F]

/-- The canonical denominator remains nonzero after the prescribed coefficient
embedding and ordinary parameter substitution. -/
@[expose] def Regular (embedding : F →+* ℝ) (t : ℝ) (fraction : Hex.RationalFn F) : Prop :=
  ((HexPolyMathlib.toPolynomial fraction.den).map embedding).eval t ≠ 0

private theorem regular_of_represents (embedding : F →+* ℝ) (t : ℝ)
    {fraction : Hex.RationalFn F} {num den : Hex.DensePoly F}
    (represents : Hex.RationalFn.Represents fraction num den)
    (nonzero : ((HexPolyMathlib.toPolynomial den).map embedding).eval t ≠ 0) :
    Regular embedding t fraction := by
  rcases represents.den_dvd with ⟨q, equation⟩
  intro zero
  apply nonzero
  have equation := congrArg (fun p : Hex.DensePoly F =>
    ((HexPolyMathlib.toPolynomial p).map embedding).eval t) equation
  rw [HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul, Polynomial.eval_mul,
    zero, zero_mul] at equation
  exact equation

/-- Canonical addition preserves regularity of its two operands. -/
theorem regular_add (embedding : F →+* ℝ) (t : ℝ) {first second : Hex.RationalFn F}
    (left : Regular embedding t first) (right : Regular embedding t second) :
    Regular embedding t (first + second) := by
  apply regular_of_represents embedding t (Hex.RationalFn.add_spec first second)
  rw [HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul, Polynomial.eval_mul]
  exact mul_ne_zero left right

/-- Canonical multiplication preserves regularity of its two operands. -/
theorem regular_mul (embedding : F →+* ℝ) (t : ℝ) {first second : Hex.RationalFn F}
    (left : Regular embedding t first) (right : Regular embedding t second) :
    Regular embedding t (first * second) := by
  apply regular_of_represents embedding t (Hex.RationalFn.mul_spec first second)
  rw [HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul, Polynomial.eval_mul]
  exact mul_ne_zero left right

/-- Negation retains the actual stored denominator. -/
theorem regular_neg (embedding : F →+* ℝ) (t : ℝ) (fraction : Hex.RationalFn F) :
    Regular embedding t (-fraction) ↔ Regular embedding t fraction := Iff.rfl

/-- Fractions regular at a prescribed parameter form a ring. This ring can
contain a nonzero fraction whose numerator vanishes at that parameter. -/
@[expose] noncomputable def regularRing (embedding : F →+* ℝ) (t : ℝ) :
    Subring (Hex.RationalFn F) where
  carrier := Regular embedding t
  zero_mem' := by
    change ((HexPolyMathlib.toPolynomial (1 : Hex.DensePoly F)).map embedding).eval t ≠ 0
    rw [HexPolyMathlib.toPolynomial_one, Polynomial.map_one, Polynomial.eval_one]
    exact one_ne_zero
  one_mem' := by
    change ((HexPolyMathlib.toPolynomial (1 : Hex.DensePoly F)).map embedding).eval t ≠ 0
    rw [HexPolyMathlib.toPolynomial_one, Polynomial.map_one, Polynomial.eval_one]
    exact one_ne_zero
  add_mem' := regular_add embedding t
  mul_mem' := regular_mul embedding t
  neg_mem' := fun h => h

/-- Evaluation is a ring homomorphism on the ring of regular native fractions.
The regular ring need not be a field, and evaluation need not reflect zero. -/
@[expose] noncomputable def evaluation (embedding : F →+* ℝ) (t : ℝ) :
    regularRing embedding t →+* ℝ where
  toFun := fun fraction => evalMapped embedding fraction t
  map_zero' := evalMapped_zero embedding t
  map_one' := evalMapped_one embedding t
  map_add' := fun first second => evalMapped_add embedding first second t first.property second.property
  map_mul' := fun first second => evalMapped_mul embedding first second t first.property second.property

/-- Regularity of the stored coefficients lifts this actual native polynomial
to the regular coefficient ring at the prescribed parameter. -/
theorem polynomial_lift (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F))
    (guards : ∀ i < p.size, Regular embedding t (p.coeff i)) :
    ∃ q : Polynomial (regularRing embedding t),
      q.map (regularRing embedding t).subtype = HexPolyMathlib.toPolynomial p := by
  classical
  apply Polynomial.mem_lifts _ |>.mp
  apply Polynomial.lifts_iff_coeff_lifts _ |>.mpr
  intro i
  refine ⟨⟨(HexPolyMathlib.toPolynomial p).coeff i, ?_⟩, rfl⟩
  rw [HexPolyMathlib.coeff_toPolynomial]
  by_cases hi : i < p.size
  · exact guards i hi
  · rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hi)]
    exact (regularRing embedding t).zero_mem

/-- Evaluation of any regular-ring lift is the actual coefficient substitution.
The result is independent of the chosen lift. -/
theorem polynomial_map (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (q : Polynomial (regularRing embedding t))
    (lift : q.map (regularRing embedding t).subtype = HexPolyMathlib.toPolynomial p) :
    HexPolyMathlib.toPolynomial (polynomial embedding p t) = q.map (evaluation embedding t) := by
  classical
  ext i
  rw [HexPolyMathlib.coeff_toPolynomial, polynomial_coeff, Polynomial.coeff_map]
  have coefficient := congrArg (fun p => Polynomial.coeff p i) lift
  simp only [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial] at coefficient
  change (q.coeff i).val = p.coeff i at coefficient
  change evalMapped embedding (p.coeff i) t = evalMapped embedding (q.coeff i).val t
  rw [coefficient]

/-- Actual polynomial addition specializes using only regularity of the
finitely stored input coefficients. Intermediate sums need no extra guards. -/
theorem polynomial_add (embedding : F →+* ℝ) (t : ℝ)
    (p q : Hex.DensePoly (Hex.RationalFn F))
    (left : ∀ i < p.size, Regular embedding t (p.coeff i))
    (right : ∀ i < q.size, Regular embedding t (q.coeff i)) :
    polynomial embedding (p + q) t = polynomial embedding p t + polynomial embedding q t := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift embedding t p left
  obtain ⟨Q, hq⟩ := polynomial_lift embedding t q right
  have lift : (P + Q).map (regularRing embedding t).subtype = HexPolyMathlib.toPolynomial (p + q) := by
    rw [Polynomial.map_add, hp, hq, HexPolyMathlib.toPolynomial_add]
  apply (HexPolyMathlib.equiv (R := ℝ)).injective
  change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
  rw [polynomial_map embedding t (p + q) (P + Q) lift, HexPolyMathlib.toPolynomial_add,
    polynomial_map embedding t p P hp, polynomial_map embedding t q Q hq, Polynomial.map_add]

/-- Actual schoolbook polynomial multiplication specializes on the regular
input coefficients. Closure of the regular ring handles every accumulation. -/
theorem polynomial_mul (embedding : F →+* ℝ) (t : ℝ)
    (p q : Hex.DensePoly (Hex.RationalFn F))
    (left : ∀ i < p.size, Regular embedding t (p.coeff i))
    (right : ∀ i < q.size, Regular embedding t (q.coeff i)) :
    polynomial embedding (p * q) t = polynomial embedding p t * polynomial embedding q t := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift embedding t p left
  obtain ⟨Q, hq⟩ := polynomial_lift embedding t q right
  have lift : (P * Q).map (regularRing embedding t).subtype = HexPolyMathlib.toPolynomial (p * q) := by
    rw [Polynomial.map_mul, hp, hq, HexPolyMathlib.toPolynomial_mul]
  apply (HexPolyMathlib.equiv (R := ℝ)).injective
  change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
  rw [polynomial_map embedding t (p * q) (P * Q) lift, HexPolyMathlib.toPolynomial_mul,
    polynomial_map embedding t p P hp, polynomial_map embedding t q Q hq, Polynomial.map_mul]

/-- Actual polynomial subtraction specializes under the two input coefficient
families' denominator guards. -/
theorem polynomial_sub (embedding : F →+* ℝ) (t : ℝ)
    (p q : Hex.DensePoly (Hex.RationalFn F))
    (left : ∀ i < p.size, Regular embedding t (p.coeff i))
    (right : ∀ i < q.size, Regular embedding t (q.coeff i)) :
    polynomial embedding (p - q) t = polynomial embedding p t - polynomial embedding q t := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift embedding t p left
  obtain ⟨Q, hq⟩ := polynomial_lift embedding t q right
  have lift : (P - Q).map (regularRing embedding t).subtype = HexPolyMathlib.toPolynomial (p - q) := by
    rw [Polynomial.map_sub, hp, hq, HexPolyMathlib.toPolynomial_sub]
  apply (HexPolyMathlib.equiv (R := ℝ)).injective
  change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
  rw [polynomial_map embedding t (p - q) (P - Q) lift, HexPolyMathlib.toPolynomial_sub,
    polynomial_map embedding t p P hp, polynomial_map embedding t q Q hq, Polynomial.map_sub]

/-- Native differentiation specializes with the original coefficient guards;
natural casts and multiplication are preserved by regular evaluation. -/
theorem polynomial_derivative (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F))
    (guards : ∀ i < p.size, Regular embedding t (p.coeff i)) :
    polynomial embedding p.derivative t = (polynomial embedding p t).derivative := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift embedding t p guards
  have lift : P.derivative.map (regularRing embedding t).subtype =
      HexPolyMathlib.toPolynomial p.derivative := by
    rw [← Polynomial.derivative_map, hp, HexPolyMathlib.toPolynomial_derivative]
  apply (HexPolyMathlib.equiv (R := ℝ)).injective
  change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
  rw [polynomial_map embedding t p.derivative P.derivative lift,
    HexPolyMathlib.toPolynomial_derivative, polynomial_map embedding t p P hp,
    Polynomial.derivative_map]

/-- Scaling specializes using only the scalar and stored coefficient guards. -/
theorem polynomial_scale (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (c : Hex.RationalFn F)
    (scalar : Regular embedding t c)
    (guards : ∀ i < p.size, Regular embedding t (p.coeff i)) :
    polynomial embedding (Hex.DensePoly.scale c p) t =
      Hex.DensePoly.scale (evalMapped embedding c t) (polynomial embedding p t) := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift embedding t p guards
  have lift : (Polynomial.C (⟨c, scalar⟩ : regularRing embedding t) * P).map
      (regularRing embedding t).subtype = HexPolyMathlib.toPolynomial (Hex.DensePoly.scale c p) := by
    rw [Polynomial.map_mul, Polynomial.map_C, hp, HexPolyMathlib.toPolynomial_scale]
    rfl
  apply (HexPolyMathlib.equiv (R := ℝ)).injective
  change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
  rw [polynomial_map embedding t (Hex.DensePoly.scale c p) _ lift,
    HexPolyMathlib.toPolynomial_scale, polynomial_map embedding t p P hp,
    Polynomial.map_mul, Polynomial.map_C]
  rfl

/-- Horner evaluation at a finite endpoint specializes using only regularity
of that endpoint and the original polynomial coefficients. -/
theorem polynomial_eval (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (x : Hex.RationalFn F)
    (point : Regular embedding t x)
    (guards : ∀ i < p.size, Regular embedding t (p.coeff i)) :
    evalMapped embedding (p.eval x) t = (polynomial embedding p t).eval (evalMapped embedding x t) := by
  classical
  obtain ⟨P, hp⟩ := polynomial_lift embedding t p guards
  have value : (P.eval (⟨x, point⟩ : regularRing embedding t)).val = p.eval x := by
    have h := Polynomial.eval_map_apply (p := P) (f := (regularRing embedding t).subtype)
      (⟨x, point⟩ : regularRing embedding t)
    rw [hp] at h
    change (HexPolyMathlib.toPolynomial p).eval x = (P.eval ⟨x, point⟩).val at h
    rw [HexPolyMathlib.eval_toPolynomial] at h
    exact h.symm
  rw [← value]
  change evaluation embedding t (P.eval ⟨x, point⟩) = _
  rw [← Polynomial.eval_map_apply]
  rw [← polynomial_map embedding t p P hp, HexPolyMathlib.eval_toPolynomial]
  rfl

/-- info: 'Hex.RealClosure.Specialize.polynomial_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_lift

/-- info: 'Hex.RealClosure.Specialize.polynomial_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_map

/-- info: 'Hex.RealClosure.Specialize.regular_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.regular_add

/-- info: 'Hex.RealClosure.Specialize.regular_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.regular_mul

/-- info: 'Hex.RealClosure.Specialize.regular_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.regular_neg

/-- info: 'Hex.RealClosure.Specialize.regularRing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.regularRing

/-- info: 'Hex.RealClosure.Specialize.evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evaluation

/-- info: 'Hex.RealClosure.Specialize.polynomial_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_add

/-- info: 'Hex.RealClosure.Specialize.polynomial_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_mul

/-- info: 'Hex.RealClosure.Specialize.polynomial_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_sub

/-- info: 'Hex.RealClosure.Specialize.polynomial_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_derivative

/-- info: 'Hex.RealClosure.Specialize.polynomial_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_scale

/-- info: 'Hex.RealClosure.Specialize.polynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_eval

end Hex.RealClosure.Specialize
