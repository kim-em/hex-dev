/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import HexBasic.Fold
public import HexMvPolyMathlib.Aeval
public import HexMvPolyMathlib.Recursive

public section

/-!
Correspondence lemmas for the public semantic operations of `Hex.MvPoly`:
support and degree, direct and Horner evaluation, differentiation,
homogeneous components, substitution and partial evaluation, renaming, and
the recursive view.

Storage-order queries such as `leadingTerm` and representation filters such as
`restrictBy` intentionally remain characterized by their core coefficient
laws: Mathlib's `MvPolynomial` has no corresponding explicit monomial-order
parameter or polynomial-valued filtering operation.
-/

namespace HexMvPolyMathlib

open scoped BigOperators
open scoped HexMvPolyMathlib

open Hex
open Hex.MvPoly

universe u

variable {n k : Nat} {R : Type u}
  {cmp : Mono n → Mono n → Ordering}
  {targetCmp : Mono k → Mono k → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Std.TransCmp targetCmp] [Std.LawfulEqCmp targetCmp]

noncomputable section

/-- The Mathlib support is exactly the image of the executable canonical
support. -/
@[simp] theorem support_toMvPolynomial [CommSemiring R] [DecidableEq R]
    (p : MvPoly n R cmp) :
    (toMvPolynomial p).support =
      p.monomials.toFinset.map monoEquiv.toEmbedding := by
  ext d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp [MvPolynomial.mem_support_iff]

/-- Folding by maximum agrees with the supremum over the corresponding
finite set. -/
private theorem foldl_max_eq_sup {α : Type*} [DecidableEq α]
    (xs : List α) (f : α → Nat) (init : Nat) :
    xs.foldl (fun acc x => max acc (f x)) init =
      max init (xs.toFinset.sup f) := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp [Nat.max_left_comm, Nat.max_comm]

/-- Executable per-variable degree agrees with Mathlib's `degreeOf`. -/
@[simp] theorem degreeOf_toMvPolynomial
    [CommSemiring R] [DecidableEq R]
    (i : Fin n) (p : MvPoly n R cmp) :
    degreeOf i p = MvPolynomial.degreeOf i (toMvPolynomial p) := by
  rw [degreeOf_eq]
  unfold foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  rw [← List.foldl_map]
  change
    (p.termsList.map fun t => Mono.degreeOf i t.1).foldl max 0 =
      MvPolynomial.degreeOf i (toMvPolynomial p)
  have hmap :
      p.termsList.map (fun t => Mono.degreeOf i t.1) =
        p.monomials.map (Mono.degreeOf i) := by
    simp [monomials, Function.comp_def]
  rw [hmap]
  change
    (p.monomials.map (Mono.degreeOf i)).foldl max 0 =
      MvPolynomial.degreeOf i (toMvPolynomial p)
  rw [List.foldl_map]
  rw [foldl_max_eq_sup]
  simp only [Nat.zero_max]
  rw [MvPolynomial.degreeOf_eq_sup, support_toMvPolynomial]
  simp only [Finset.sup_map]
  apply Finset.sup_congr rfl
  intro m _
  change m[i] = monoEquiv m i
  exact (monoEquiv_apply m i).symm

/-- Each executable coordinate degree is Mathlib's corresponding
per-variable degree. -/
@[simp] theorem get_degrees_eq_degreeOf
    [CommSemiring R] [DecidableEq R]
    (i : Fin n) (p : MvPoly n R cmp) :
    p.degrees[i] = MvPolynomial.degreeOf i (toMvPolynomial p) := by
  rw [getElem_degrees, degreeOf_toMvPolynomial]

/-- The executable variable list contains exactly the variables of nonzero
Mathlib degree. -/
@[simp] theorem mem_vars_iff_degreeOf
    [CommSemiring R] [DecidableEq R]
    (i : Fin n) (p : MvPoly n R cmp) :
    i ∈ p.vars ↔ MvPolynomial.degreeOf i (toMvPolynomial p) ≠ 0 := by
  rw [mem_vars_iff, degreeOf_toMvPolynomial]

/-- Total exponent in an executable monomial is the corresponding Finsupp
sum. -/
theorem monoDegree_eq_sum (m : Mono n) :
    Mono.degree m = (monoEquiv m).sum fun _ e => e := by
  unfold Mono.degree
  rw [← List.foldl_map, ← List.sum_eq_foldl,
    ← List.sum_toFinset _ (List.nodup_finRange n),
    List.toFinset_finRange]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp

/-- Executable total degree agrees with Mathlib's `totalDegree`. -/
@[simp] theorem totalDegree_toMvPolynomial
    [CommSemiring R] [DecidableEq R]
    (p : MvPoly n R cmp) :
    totalDegree p = MvPolynomial.totalDegree (toMvPolynomial p) := by
  rw [totalDegree_eq]
  unfold foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  rw [← List.foldl_map]
  change
    (p.termsList.map fun t => Mono.degree t.1).foldl max 0 =
      MvPolynomial.totalDegree (toMvPolynomial p)
  have hmap :
      p.termsList.map (fun t => Mono.degree t.1) =
        p.monomials.map Mono.degree := by
    simp [monomials, Function.comp_def]
  rw [hmap, List.foldl_map, foldl_max_eq_sup]
  simp only [Nat.zero_max]
  unfold MvPolynomial.totalDegree
  rw [support_toMvPolynomial]
  simp only [Finset.sup_map]
  apply Finset.sup_congr rfl
  intro m _
  exact monoDegree_eq_sum m

/-- Fixed-order Horner evaluation has the same Mathlib interpretation as
direct algebra-hom evaluation. -/
theorem evalHorner_eq_aeval
    [CommSemiring R] [DecidableEq R]
    (x : Fin n → R) (p : MvPoly n R cmp) :
    evalHorner x p = MvPolynomial.aeval x (toMvPolynomial p) := by
  rw [evalHorner_eq, ← aeval_eq_eval, aeval_apply]

/-- Increasing one executable exponent corresponds to adding the Mathlib
single-variable exponent. -/
@[simp] theorem monoEquiv_succAt (i : Fin n) (m : Mono n) :
    monoEquiv (Mono.succAt i m) =
      monoEquiv m + Finsupp.single i 1 := by
  simp [Mono.succAt]

/-- Executable formal differentiation agrees with Mathlib's partial
derivative. -/
@[simp] theorem toMvPolynomial_derivative
    [CommSemiring R] [DecidableEq R]
    (i : Fin n) (p : MvPoly n R cmp) :
    toMvPolynomial (derivative i p) =
      MvPolynomial.pderiv i (toMvPolynomial p) := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  rw [coeff_toMvPolynomial, coeff_derivative,
    MvPolynomial.coeff_pderiv, ← monoEquiv_succAt,
    coeff_toMvPolynomial]
  simp [Mono.degreeOf, _root_.mul_comm]

/-- Executable homogeneous projection agrees with Mathlib's homogeneous
component. -/
@[simp] theorem toMvPolynomial_homogeneousComponent
    [CommSemiring R] [DecidableEq R]
    (d : Nat) (p : MvPoly n R cmp) :
    toMvPolynomial (homogeneousComponent d p) =
      MvPolynomial.homogeneousComponent d (toMvPolynomial p) := by
  apply MvPolynomial.ext
  intro exponent
  rcases monoEquiv.surjective exponent with ⟨m, rfl⟩
  rw [coeff_toMvPolynomial, coeff_homogeneousComponent,
    MvPolynomial.coeff_homogeneousComponent, coeff_toMvPolynomial]
  congr 2
  rw [Finsupp.degree_eq_sum]
  rw [monoDegree_eq_sum, Finsupp.sum_fintype _ _ (fun _ => rfl)]

/-- Executable substitution is its algebra-hom evaluation specialization. -/
theorem subst_eq_aeval [CommSemiring R] [DecidableEq R]
    (g : Fin n → MvPoly k R targetCmp) (p : MvPoly n R cmp) :
    subst g p = aeval g p := by
  rw [aeval_eq_eval₂]
  unfold subst Hex.MvPoly.bind eval₂
  simp [algebraMap_apply]

/-- Executable substitution agrees with Mathlib's variable bind. -/
@[simp] theorem toMvPolynomial_subst
    [CommSemiring R] [DecidableEq R]
    (g : Fin n → MvPoly k R targetCmp) (p : MvPoly n R cmp) :
    toMvPolynomial (subst g p) =
      MvPolynomial.bind₁ (fun i => toMvPolynomial (g i))
        (toMvPolynomial p) := by
  rw [subst_eq_aeval]
  rw [← algEquiv_apply (cmp := targetCmp) (aeval g p)]
  rw [aeval_apply]
  change
    (algEquiv (cmp := targetCmp)).toAlgHom
        (MvPolynomial.aeval g (toMvPolynomial p)) =
      MvPolynomial.bind₁ (fun i => toMvPolynomial (g i))
        (toMvPolynomial p)
  rw [MvPolynomial.comp_aeval_apply]
  simp

/-- Executable partial evaluation agrees with binding assigned variables to
constants and leaving the other variables unchanged. -/
@[simp] theorem toMvPolynomial_partialEval
    [CommSemiring R] [DecidableEq R]
    (s : Fin n → Option R) (p : MvPoly n R cmp) :
    toMvPolynomial (partialEval s p) =
      MvPolynomial.bind₁
        (fun i =>
          match s i with
          | some x => MvPolynomial.C x
          | none => MvPolynomial.X i)
        (toMvPolynomial p) := by
  rw [partialEval_eq_subst, toMvPolynomial_subst]
  congr 2
  funext i
  cases s i <;> simp

/-- The compatibility spelling `bind₁` has the same Mathlib correspondence
as substitution. -/
@[simp] theorem toMvPolynomial_bind₁
    [CommSemiring R] [DecidableEq R]
    (g : Fin n → MvPoly k R targetCmp) (p : MvPoly n R cmp) :
    toMvPolynomial (bind₁ g p) =
      MvPolynomial.bind₁ (fun i => toMvPolynomial (g i))
        (toMvPolynomial p) := by
  change toMvPolynomial (subst g p) = _
  exact toMvPolynomial_subst g p

/-- Changing the executable storage order does not change the corresponding
Mathlib polynomial. -/
@[simp] theorem toMvPolynomial_reorder
    [CommSemiring R] [DecidableEq R]
    (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly n R cmp) :
    toMvPolynomial (reorder cmp' p) = toMvPolynomial p := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp [coeff_reorder]

/-- Executable variable renaming agrees with Mathlib's `rename`. -/
@[simp] theorem toMvPolynomial_rename
    [CommSemiring R] [DecidableEq R]
    (f : Fin n → Fin k) (p : MvPoly n R cmp) :
    toMvPolynomial (rename targetCmp f p) =
      MvPolynomial.rename f (toMvPolynomial p) := by
  rw [rename_eq_subst, toMvPolynomial_subst]
  simp only [toMvPolynomial_X]
  rw [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval_eq_bind₁]
  rfl

section Recursive

variable {cmpSucc : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmpBase : Mono n → Mono n → Ordering}
  [Std.TransCmp cmpSucc] [Std.LawfulEqCmp cmpSucc]
  [Std.TransCmp cmpBase] [Std.LawfulEqCmp cmpBase]

/-- The inverse executable recursive view agrees with the inverse Mathlib
`finSuccEquiv`. -/
@[simp] theorem toMvPolynomial_ofUnivariate
    [CommSemiring R] [DecidableEq R]
    (q : DensePoly (MvPoly n R cmpBase)) :
    toMvPolynomial
        (ofUnivariate (cmp := cmpSucc) 0 cmpBase q) =
      (MvPolynomial.finSuccEquiv R n).symm
        (recursiveMap (cmp' := cmpBase) q) := by
  apply (MvPolynomial.finSuccEquiv R n).injective
  rw [(MvPolynomial.finSuccEquiv R n).apply_symm_apply]
  rw [← recursiveMap_toUnivariate
    (R := R) (cmp := cmpSucc) (cmp' := cmpBase)]
  rw [toUnivariate_ofUnivariate]

end Recursive

end

end HexMvPolyMathlib
