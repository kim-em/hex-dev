/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Squarefree

@[expose] public section
set_option backward.proofsInPublic true

/-!
Checked product decompositions for multivariate integer polynomials.

This layer deliberately says nothing about irreducibility.  Its checker
replays the product identity and the canonical-form side conditions which
make multiplicities meaningful.
-/

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

/-- One nonconstant entry in a product decomposition. -/
structure Factor (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  factor : MvPoly n Int cmp
  multiplicity : Nat

/-- An integer scalar and a list of polynomial powers. -/
structure Decomp (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  content : Int
  factors : List (Factor n cmp)

namespace Decomp

variable {n : Nat} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Reconstruct the polynomial represented by a decomposition. -/
@[reducible] def product (D : Decomp n cmp) : MvPoly n Int cmp :=
  D.factors.foldl
    (fun acc entry => acc * entry.factor ^ entry.multiplicity)
    (C D.content)

end Decomp

variable {n : Nat} {cmp : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp]

/-- The local canonical-form conditions for one decomposition entry. -/
@[reducible] def checkFactor (entry : Factor n cmp) : Bool :=
  decide (0 < entry.multiplicity) &&
    decide (entry.factor.vars ≠ []) &&
    (polyNormalize entry.factor == entry.factor) &&
    decide (MvPoly.content entry.factor = 1)

/-- Boolean pairwise distinctness, kept structural for kernel replay. -/
@[reducible] def distinctFactors : List (Factor n cmp) → Bool
  | [] => true
  | entry :: entries =>
      entries.all (fun other => decide (entry.factor ≠ other.factor)) &&
        distinctFactors entries

/-- Replay all five decomposition conditions from the SPEC. -/
@[reducible] def checkDecomp (f : MvPoly n Int cmp)
    (D : Decomp n cmp) : Bool :=
  (D.product == f) &&
    D.factors.all checkFactor &&
    distinctFactors D.factors

/-- The semantic product and nonconstant-positive-multiplicity payload of a
checked decomposition.  Normalization and distinctness are checker-side
canonicity conditions rather than part of this minimal witness. -/
def IsDecompOf (f : MvPoly n Int cmp) (D : Decomp n cmp) : Prop :=
  D.product = f ∧
    ∀ entry ∈ D.factors,
      0 < entry.multiplicity ∧ ¬ MvPoly.IsConst entry.factor

/-- Accepted decomposition data tied to the subject checked by its caller. -/
structure CheckedDecomp (f : MvPoly n Int cmp) where
  raw : Decomp n cmp
  valid : checkDecomp f raw = true

/-- Executable replay implies the semantic decomposition payload. -/
theorem checkDecomp_sound {f : MvPoly n Int cmp} {D : Decomp n cmp}
    (h : checkDecomp f D = true) : IsDecompOf f D := by
  simp only [checkDecomp, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at h
  refine ⟨h.1.1, ?_⟩
  intro entry hentry
  have hfactor := h.1.2 entry hentry
  simp only [decide_eq_true_eq] at hfactor
  exact ⟨hfactor.1.1.1, hfactor.1.1.2⟩

/-! # Structural answers

These are the complete no-search cases used before the EEZ driver: zero,
constants, and a single monomial.  A general polynomial with scalar or
monomial content still needs a residual factorization and is handled by the
driver rather than hidden behind a partial division here.
-/

/-- Each nonzero variable power is a canonical decomposition entry. -/
private theorem checkFactor_X (i : Fin n) {e : Nat} (he : e ≠ 0) :
    checkFactor (⟨X i, e⟩ : Factor n cmp) = true := by
  have hvars : (X i : MvPoly n Int cmp).vars ≠ [] := by
    intro hnil
    have hi : i ∈ (X i : MvPoly n Int cmp).vars := by
      rw [mem_vars_iff]
      change degreeOf i
        (monomial (Mono.unit i) (1 : Int) : MvPoly n Int cmp) ≠ 0
      rw [degreeOf_monomial]
      rw [ite_eq_right (by decide)]
      rw [Mono.getElem_unit]
      simp
    rw [hnil] at hi
    contradiction
  have hlead : (X i : MvPoly n Int cmp).leadingTerm =
      some (Mono.unit i, 1) := by
    exact leadingTerm_monomial (by decide)
  have hnorm : polyNormalize (X i : MvPoly n Int cmp) = X i := by
    rw [polyNormalize, polyNormUnit, hlead]
    change X i * (1 : MvPoly n Int cmp) = X i
    exact MvPoly.mul_one _
  have hcontent : content (X i : MvPoly n Int cmp) = 1 := by
    unfold content scalarContent
    change ((match
      (monomial (Mono.unit i) (1 : Int) : MvPoly n Int cmp).termsList with
      | [] => (0 : Int)
      | (_, c) :: terms =>
          normalize (terms.foldl (fun g term => GcdOps.gcd g term.2) c)) :
        Int) = (1 : Int)
    rw [termsList_monomial]
    simp [normalize]
    rfl
  simp only [checkFactor, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  exact ⟨⟨⟨Nat.pos_iff_ne_zero.mpr he, hvars⟩, hnorm⟩, hcontent⟩

/-- The variable factors of a monomial, in increasing variable order. -/
def monomialFactors (m : Mono n) : List (Factor n cmp) :=
  (List.finRange n).filterMap fun i =>
    let exponent := Mono.degreeOf i m
    if exponent = 0 then none else some ⟨X i, exponent⟩

/-- Canonical decomposition of one coefficient-monomial pair. -/
def monomialDecomp (coefficient : Int) (m : Mono n) : Decomp n cmp :=
  ⟨coefficient, monomialFactors m⟩

/-- Filtering zero exponents does not change the variable-power product. -/
private theorem fold_monomialFactors (m : Mono n)
    (initial : MvPoly n Int cmp) :
    (monomialFactors m).foldl
        (fun acc entry => acc * entry.factor ^ entry.multiplicity) initial =
      (List.finRange n).foldl
        (fun acc i => acc * X i ^ m[i]) initial := by
  unfold monomialFactors
  generalize hxs : List.finRange n = xs
  clear hxs
  induction xs generalizing initial with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.filterMap_cons, List.foldl_cons]
      by_cases he : Mono.degreeOf i m = 0
      ·
        simp only [ite_eq_left he]
        rw [show m[i] = 0 from he]
        rw [Lean.Grind.Semiring.pow_zero, MvPoly.mul_one]
        exact ih initial
      ·
        simp only [ite_eq_right he, List.foldl_cons]
        exact ih (initial * X i ^ m[i])

/-- A fold of variable powers is the corresponding monomial polynomial. -/
private theorem fold_variablePowers (m : Mono n) :
    ∀ (xs : List (Fin n)) (a : Mono n) (c : Int),
      xs.foldl (fun acc i => acc * X i ^ m[i])
          (monomial a c : MvPoly n Int cmp) =
        (monomial
          (xs.foldl
            (fun acc i => Mono.mul acc (Mono.scale m[i] (Mono.unit i))) a)
          c : MvPoly n Int cmp)
  | [], _, _ => rfl
  | i :: xs, a, c => by
      simp only [List.foldl_cons]
      have hpower : (X i : MvPoly n Int cmp) ^ m[i] =
          monomial (Mono.scale m[i] (Mono.unit i)) 1 := by
        rw [← Mono.powBySq_eq_pow, X, powBySq_monomial,
          Mono.powBySq_eq_pow]
        rw [Lean.Grind.Semiring.one_pow]
      rw [hpower, monomial_mul_monomial]
      simpa using fold_variablePowers m xs
        (Mono.mul a (Mono.scale m[i] (Mono.unit i))) c

/-- The canonical monomial decomposition reconstructs its one-term input. -/
private theorem monomialDecomp_product (coefficient : Int) (m : Mono n) :
    (monomialDecomp (cmp := cmp) coefficient m).product =
      monomial m coefficient := by
  unfold Decomp.product monomialDecomp
  change (monomialFactors m).foldl
      (fun acc entry => acc * entry.factor ^ entry.multiplicity)
      (C coefficient : MvPoly n Int cmp) =
    (monomial m coefficient : MvPoly n Int cmp)
  rw [fold_monomialFactors]
  change (List.finRange n).foldl (fun acc i => acc * X i ^ m[i])
      (monomial Mono.zero coefficient) = monomial m coefficient
  rw [fold_variablePowers (cmp := cmp), Mono.mul_units]

/-- Every emitted variable power satisfies the local factor checker. -/
private theorem monomialFactors_all (m : Mono n) :
    (monomialFactors (cmp := cmp) m).all checkFactor = true := by
  rw [List.all_eq_true]
  intro entry hentry
  unfold monomialFactors at hentry
  rcases List.mem_filterMap.mp hentry with ⟨i, _, hi⟩
  dsimp only at hi
  by_cases he : Mono.degreeOf i m = 0
  · rw [ite_eq_left he] at hi
    contradiction
  · rw [ite_eq_right he] at hi
    simp only [Option.some.injEq] at hi
    subst entry
    exact checkFactor_X i he

/-- Distinct variables denote distinct one-term polynomials. -/
private theorem X_injective : Function.Injective
    (fun i : Fin n => (X i : MvPoly n Int cmp)) := by
  intro i j h
  change (monomial (Mono.unit i) 1 : MvPoly n Int cmp) =
    monomial (Mono.unit j) 1 at h
  have hterms := congrArg MvPoly.termsList h
  rw [termsList_monomial, termsList_monomial] at hterms
  have hunit : Mono.unit i = Mono.unit j := by
    simpa using hterms
  by_cases hij : i = j
  · exact hij
  · have hget := congrArg (fun m : Mono n => m[i]) hunit
    rw [Mono.getElem_unit, Mono.getElem_unit] at hget
    rw [ite_eq_left rfl, ite_eq_right hij] at hget
    omega

/-- Filtering a duplicate-free index list preserves distinct variable keys. -/
private theorem factorList_pairwise (m : Mono n) :
    ∀ {xs : List (Fin n)}, xs.Nodup →
      (xs.filterMap fun i =>
        let exponent := Mono.degreeOf i m
        if exponent = 0 then none else some (⟨X i, exponent⟩ : Factor n cmp)
      ).Pairwise fun left right => left.factor ≠ right.factor
  | [], _ => .nil
  | i :: xs, hnodup => by
      rw [List.nodup_cons] at hnodup
      simp only [List.filterMap_cons]
      by_cases he : Mono.degreeOf i m = 0
      · rw [ite_eq_left he]
        exact factorList_pairwise m hnodup.2
      · rw [ite_eq_right he]
        apply List.Pairwise.cons
        · intro entry hentry
          rcases List.mem_filterMap.mp hentry with ⟨j, hj, hout⟩
          by_cases hjzero : Mono.degreeOf j m = 0
          · rw [ite_eq_left hjzero] at hout
            contradiction
          · rw [ite_eq_right hjzero] at hout
            simp only [Option.some.injEq] at hout
            subst entry
            intro hfactor
            apply hnodup.1
            exact X_injective hfactor ▸ hj
        · exact factorList_pairwise m hnodup.2

/-- Pairwise-distinct factor keys pass the structural Boolean replay. -/
private theorem distinctFactors_of_pairwise :
    ∀ {factors : List (Factor n cmp)},
      factors.Pairwise (fun left right => left.factor ≠ right.factor) →
      distinctFactors factors = true
  | [], _ => rfl
  | _ :: _, .cons head tail => by
      simp only [distinctFactors, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq]
      exact ⟨head, distinctFactors_of_pairwise tail⟩

/-- The increasing variable-factor list passes distinctness replay. -/
private theorem monomialFactors_distinct (m : Mono n) :
    distinctFactors (monomialFactors (cmp := cmp) m) = true := by
  apply distinctFactors_of_pairwise
  exact factorList_pairwise m (List.nodup_finRange n)

/-- Every canonical monomial decomposition passes full replay. -/
private theorem monomialDecomp_checks (coefficient : Int) (m : Mono n) :
    checkDecomp (monomial m coefficient : MvPoly n Int cmp)
      (monomialDecomp coefficient m) = true := by
  simp only [checkDecomp, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨monomialDecomp_product coefficient m, monomialFactors_all m⟩,
    monomialFactors_distinct m⟩

/-- Recognize the no-search structural cases. -/
def structural? (f : MvPoly n Int cmp) : Option (Decomp n cmp) :=
  match f.termsList with
  | [] => some ⟨0, []⟩
  | [(m, coefficient)] => some (monomialDecomp coefficient m)
  | _ => none

/-- Every structural answer passes the decomposition checker. -/
theorem structural_checks {f : MvPoly n Int cmp} {D : Decomp n cmp}
    (h : structural? f = some D) : checkDecomp f D = true := by
  unfold structural? at h
  cases hterms : f.termsList with
  | nil =>
      simp only [hterms, Option.some.injEq] at h
      subst D
      have hf : f = 0 := by
        apply termsList_inj
        rw [hterms]
        rfl
      subst f
      rfl
  | cons head tail =>
      cases tail with
      | nil =>
          rcases head with ⟨m, coefficient⟩
          simp only [hterms, Option.some.injEq] at h
          subst D
          have hmem : (m, coefficient) ∈ f.termsList := by
            rw [hterms]
            exact List.mem_cons_self
          unfold MvPoly.termsList at hmem
          have hget :=
            Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
          have hc : coefficient ≠ 0 := by
            intro hc
            subst coefficient
            exact f.nonzeroInternal m hget
          have hf : f = monomial m coefficient := by
            apply termsList_inj
            rw [hterms, termsList_monomial, ite_eq_right hc]
          subst f
          exact monomialDecomp_checks coefficient m
      | cons second rest =>
          simp only [hterms] at h
          contradiction

end Hex.MvFactor
