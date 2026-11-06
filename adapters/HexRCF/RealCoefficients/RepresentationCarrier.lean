/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RepresentationSpecialize
public import HexRCF.RealCoefficients.CellCheck
public import HexRealClosureTheory.TransportPower

public section
namespace Hex.RCF.RealCoefficients.RepresentationCarrier
open Hex Hex.RealFormula HexPolyTheory.Interpret
variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Mul E]

/-- Omitting structurally zero factors preserves root coverage even when the
interpretation is noninjective. A retained factor that maps to zero makes
the product zero; callers must separately check any required degree guards. -/
theorem atom_roots_transport (f : E → ℝ) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (ha : ∀ a b, f (a + b) = f a + f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (ps : List (DensePoly E)) (p : DensePoly E) (member : p ∈ ps) :
    interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Hex.RealClosure.Transport.polynomial f p) = 0 ∨
      ∀ x, (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Hex.RealClosure.Transport.polynomial f p)).IsRoot x →
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Hex.RealClosure.Transport.polynomial f (product ps))).IsRoot x := by
  let mapped (q : DensePoly E) := interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
    (Hex.RealClosure.Transport.polynomial f q)
  have zero : mapped 0 = 0 := by
    ext i
    simp only [mapped, coeff_interpret, Hex.RealClosure.Transport.polynomial_coeff f h0,
      DensePoly.coeff_zero, Polynomial.coeff_zero, h0]
  have unit : mapped 1 = 1 := by
    dsimp only [mapped]
    rw [Hex.RealClosure.Transport.polynomial_one f h0 h1]
    exact interpret_one (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
  have mul (a b : DensePoly E) : mapped (a * b) = mapped a * mapped b := by
    dsimp only [mapped]
    rw [Hex.RealClosure.Transport.Ring.polynomial_mul f h0 a b
      (fun _ _ _ _ => hm _ _) (fun _ _ _ _ => ha _ _)]
    exact interpret_mul (fun x : ℝ => x) (fun _ => Iff.rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) _ _
  have fold (qs : List (DensePoly E)) :
      mapped (qs.foldr (· * ·) 1) = (qs.map mapped).prod := by
    induction qs with
    | nil => exact unit
    | cons q qs ih => simp only [List.foldr_cons, List.map_cons, List.prod_cons, mul, ih]
  by_cases empty : p.isZero = true
  · have literal : p = 0 :=
      (DensePoly.size_eq_zero_iff _).mp ((DensePoly.isZero_eq_true_iff _).mp empty)
    exact Or.inl (literal ▸ zero)
  · right
    intro x root
    have retained : mapped p ∈ (ps.filter (fun p => !p.isZero)).map mapped := by
      apply List.mem_map.mpr
      exact ⟨p, List.mem_filter.mpr ⟨member, by simpa using empty⟩, rfl⟩
    change (mapped (product ps)).eval x = 0
    rw [product, fold]
    generalize (ps.filter (fun p => !p.isZero)).map mapped = qs at *
    induction qs with
    | nil => simp at retained
    | cons q qs ih =>
      rw [List.prod_cons, Polynomial.eval_mul]
      rcases List.mem_cons.mp retained with rfl | rest
      · simp only [Polynomial.IsRoot] at root
        rw [root, zero_mul]
      · rw [ih rest, mul_zero]

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
