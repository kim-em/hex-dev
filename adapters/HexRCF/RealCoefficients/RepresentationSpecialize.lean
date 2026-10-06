/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealFormulaTheory.Semantics
public import HexPolyTheory.Interpret

public section
namespace Hex.RCF.RealCoefficients.RepresentationSpecialize
open Hex Hex.RealFormula

attribute [local instance 2500] Semiring.toGrindSemiring

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Mul E] [Neg E] [NatCast E]

/-- Integer coefficients use only the representation's actual casts and negation. -/
@[expose] def scalar : Int → E
  | .ofNat n => (n : E)
  | .negSucc n => -((n + 1 : Nat) : E)

/-- Evaluate only the coefficient coordinates with their actual arithmetic. -/
@[expose] def coefficient (values : Fin n → E) (m : Mono (n + 1)) (c : Int) : E :=
  let product := (List.finRange n).foldl (fun acc i =>
    if m[i.castSucc] = 0 then acc else acc * Mono.powBySq (values i) m[i.castSucc]) 1
  if c = 1 then product else scalar c * product

/-- Group terms by their bound-variable exponent through dense coefficient addition.
Coefficient powers and products are evaluated in `E`, without polynomial products
or a ring or field instance on stored expressions. -/
@[expose] def polynomial (values : Fin n → E) (q : RealFormula.Poly (n + 1)) : DensePoly E :=
  q.termsList.foldl (fun acc term =>
    acc + DensePoly.monomial term.1[Fin.last n] (coefficient values term.1 term.2)) 0

/-- Retain every original atom, including zero, repeated and domain-guard atoms. -/
@[expose] def prepare (values : Fin n → E) (formula : RealFormula.QF (n + 1)) :
    List (DensePoly E) := formula.polys.map (polynomial values)

variable (f : E → ℝ) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hn : ∀ n : Nat, f (n : E) = (n : ℝ)) (hneg : ∀ a, f (-a) = -f a)

@[expose] noncomputable def evaluate (x : ℝ) (p : DensePoly E) : ℝ :=
  (HexPolyTheory.Interpret.interpret f hz p).eval x

omit [One E] [Add E] [Mul E] [Neg E] [NatCast E] in
private theorem evaluate_zero (x : ℝ) : evaluate f hz x (0 : DensePoly E) = 0 := by
  simp [evaluate]

include ha in
omit [One E] [Mul E] [Neg E] [NatCast E] in
private theorem evaluate_add (x : ℝ) (a b : DensePoly E) :
    evaluate f hz x (a + b) = evaluate f hz x a + evaluate f hz x b := by
  simp only [evaluate, HexPolyTheory.Interpret.interpret_add f hz ha, Polynomial.eval_add]

omit [One E] [Add E] [Mul E] [Neg E] [NatCast E] in
private theorem evaluate_monomial (x : ℝ) (k : Nat) (c : E) :
    evaluate f hz x (DensePoly.monomial k c) = f c * x ^ k := by
  have interpreted : HexPolyTheory.Interpret.interpret f hz (DensePoly.monomial k c) =
      Polynomial.monomial k (f c) := by
    ext i
    simp only [HexPolyTheory.Interpret.coeff_interpret, DensePoly.coeff_monomial,
      Polynomial.coeff_monomial]
    by_cases at_degree : i = k
    · subst i
      simp only [ite_true]
    · simp only [ite_eq_right at_degree, ite_eq_right (Ne.symm at_degree)]
      exact (hz (0 : E)).mpr rfl
  simp only [evaluate, interpreted, Polynomial.eval_monomial]

include hn hneg in
omit [Zero E] [DecidableEq E] [One E] [Add E] [Mul E] in
private theorem scalar_value (c : Int) : f (scalar c) = (c : ℝ) := by
  cases c <;> simp [scalar, hn, hneg]

include h1 hm in
omit [Zero E] [DecidableEq E] [Add E] [Neg E] [NatCast E] in
private theorem power_value (a : E) (k : Nat) :
    f (Mono.powBySq a k) = Mono.powBySq (f a) k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simp only [Mono.powBySq, h1]
    | succ k =>
      have smaller : (k + 1) / 2 < k + 1 := Nat.div_lt_self (Nat.succ_pos k) (by decide)
      rw [Mono.powBySq, Mono.powBySq]
      split <;> simp only [hm, ih _ smaller]

include h1 hm hn hneg in
omit [Zero E] [DecidableEq E] [Add E] in
private theorem coefficient_value (values : Fin n → E) (x : ℝ)
    (m : Mono (n + 1)) (c : Int) :
    f (coefficient values m c) * x ^ m[Fin.last n] =
      (c : ℝ) * Mono.prod (append (fun j => f (values j)) x) m := by
  have fold (indices : List (Fin n)) (acc : E) :
      f (indices.foldl (fun acc i =>
        if m[i.castSucc] = 0 then acc else acc * Mono.powBySq (values i) m[i.castSucc]) acc) =
      indices.foldl (fun acc i => acc * Mono.powBySq (f (values i)) m[i.castSucc]) (f acc) := by
    induction indices generalizing acc with
    | nil => rfl
    | cons i rest ih =>
      by_cases unused : m[i.castSucc] = 0
      · simp only [List.foldl_cons, unused, ite_true, Mono.powBySq, mul_one, ih]
      · simp only [List.foldl_cons, unused, ite_false, ih, hm, power_value f h1 hm]
  have scalar_product : ∀ a : E,
      f (if c = 1 then a else scalar c * a) = (c : ℝ) * f a := by
    intro a
    by_cases unit : c = 1
    · subst c
      simp only [ite_true, Int.cast_one, one_mul]
    · simp only [ite_eq_right unit, hm, scalar_value f hn hneg]
  simp only [coefficient, scalar_product, fold, h1]
  simp only [Mono.prod, List.finRange_succ_last, List.foldl_append, List.foldl_map,
    List.foldl_cons, List.foldl_nil]
  simp only [append, Fin.val_castSucc, Fin.isLt, dite_true, Fin.val_last,
    Nat.lt_irrefl, dite_false, Mono.powBySq_eq_pow]
  exact mul_assoc _ _ _

include h1 ha hm hn hneg in
/-- All-valuation specialization at the fixed authenticated representation map.
Only zero reflection and preservation of actual operations are needed. -/
theorem polynomial_eval (values : Fin n → E) (q : RealFormula.Poly (n + 1)) (x : ℝ) :
    evaluate f hz x (polynomial values q) = q.eval (append (fun j => f (values j)) x) := by
  have fold (terms : List (Mono (n + 1) × Int)) (acc : DensePoly E) :
      evaluate f hz x (terms.foldl (fun acc term =>
        acc + DensePoly.monomial term.1[Fin.last n] (coefficient values term.1 term.2)) acc) =
      terms.foldl (fun acc term => acc + (term.2 : ℝ) *
        Mono.prod (append (fun j => f (values j)) x) term.1) (evaluate f hz x acc) := by
    induction terms generalizing acc with
    | nil => rfl
    | cons term rest ih =>
      simp only [List.foldl_cons, ih, evaluate_add f hz ha, evaluate_monomial,
        coefficient_value f h1 hm hn hneg]
  simpa only [polynomial, RealFormula.Poly.eval, MvPoly.eval₂, MvPoly.foldTerms,
    Std.ExtTreeMap.foldl_eq_foldl_toList, MvPoly.termsList, evaluate_zero f hz,
    Int.coe_castRingHom] using
      fold q.termsList 0

/-- Degree is preserved even when different stored nonzero values coincide. -/
theorem degree (values : Fin n → E) (q : RealFormula.Poly (n + 1)) :
    (HexPolyTheory.Interpret.interpret f hz (polynomial values q)).natDegree =
      (polynomial values q).natDegree := HexPolyTheory.Interpret.natDegree_interpret f hz _

/-- The leading coefficient is interpreted at the same fixed representation map. -/
theorem leading (values : Fin n → E) (q : RealFormula.Poly (n + 1)) :
    (HexPolyTheory.Interpret.interpret f hz (polynomial values q)).leadingCoeff =
      f (polynomial values q).leadingCoeff :=
  HexPolyTheory.Interpret.leadingCoeff_interpret f hz _

include h1 ha hm hn hneg in
/-- Every prepared atom has its original value; guards are not stripped. -/
theorem prepare_eval (values : Fin n → E) (formula : RealFormula.QF (n + 1)) (x : ℝ) :
    (prepare values formula).map (evaluate f hz x) =
      formula.polys.map (fun q => q.eval (append (fun j => f (values j)) x)) := by
  unfold prepare
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  exact polynomial_eval f hz h1 ha hm hn hneg values q x

/-- Semantic degrees retain zero atoms and cancellations in the full traversal. -/
theorem prepare_degrees (values : Fin n → E) (formula : RealFormula.QF (n + 1)) :
    (prepare values formula).map (fun q =>
      (HexPolyTheory.Interpret.interpret f hz q).natDegree) =
      (prepare values formula).map DensePoly.natDegree := by
  unfold prepare
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  exact degree f hz values q

end Hex.RCF.RealCoefficients.RepresentationSpecialize
