/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RepresentationSpecialize

public section
namespace Hex.RCF.RealCoefficients.RepresentationCarrier
open Hex Hex.RealFormula HexPolyMathlib.Interpret
variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Mul E]

/-- Product before squarefree preparation; zero atoms are omitted. -/
@[expose] def product (ps : List (DensePoly E)) : DensePoly E :=
  (ps.filter (fun p => !p.isZero)).foldr (· * ·) 1

variable {K : Type v} [Field K] [DecidableEq K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a+b) = f a+f b)
variable (hm : ∀ a b, f (a*b) = f a*f b)

include h1 ha hm in
private theorem fold_interpret (ps : List (DensePoly E)) :
    interpret f hz (ps.foldr (· * ·) 1) = (ps.map (interpret f hz)).prod := by
  induction ps with
  | nil => exact interpret_one f hz h1
  | cons p ps ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons,
      interpret_mul f hz ha hm, ih]

include f hz h1 ha hm in
theorem product_ne_zero (ps : List (DensePoly E)) : product ps ≠ 0 := by
  have nonzero : ((ps.filter (fun p => !p.isZero)).map (interpret f hz)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro member
    obtain ⟨p, hp, zero⟩ := List.mem_map.mp member
    have literal := (interpret_eq_zero f hz p).mp zero
    subst p
    have impossible : (0 : DensePoly E).isZero = false := by
      simpa using (List.mem_filter.mp hp).2
    exact Bool.false_ne_true (impossible.symm.trans rfl)
  intro zero
  apply nonzero
  rw [← fold_interpret f hz h1 ha hm]
  exact (interpret_eq_zero f hz _).mpr zero

include h1 ha hm in
theorem atom_roots (ps : List (DensePoly E)) (p : DensePoly E) (member : p ∈ ps) :
    interpret f hz p = 0 ∨ ∀ x, (interpret f hz p).IsRoot x →
      (interpret f hz (product ps)).IsRoot x := by
  by_cases zero : p = 0
  · exact Or.inl ((interpret_eq_zero f hz p).mpr zero)
  · right
    have retained : p ∈ ps.filter (fun p => !p.isZero) := by
      apply List.mem_filter.mpr
      refine ⟨member, ?_⟩
      have test : p.isZero ≠ true := by
        intro h
        exact zero ((DensePoly.size_eq_zero_iff p).mp ((DensePoly.isZero_eq_true_iff p).mp h))
      simpa using test
    intro x root
    change (interpret f hz (product ps)).eval x = 0
    rw [product, fold_interpret f hz h1 ha hm]
    have factor : interpret f hz p ∈ (ps.filter (fun p => !p.isZero)).map (interpret f hz) :=
      List.mem_map.mpr ⟨p, retained, rfl⟩
    generalize (ps.filter (fun p => !p.isZero)).map (interpret f hz) = qs at *
    induction qs with
    | nil => simp at factor
    | cons q qs ih =>
      rw [List.prod_cons, Polynomial.eval_mul]
      rcases List.mem_cons.mp factor with rfl | rest
      · simp only [Polynomial.IsRoot] at root
        rw [root, zero_mul]
      · rw [ih rest, mul_zero]
end Hex.RCF.RealCoefficients.RepresentationCarrier
