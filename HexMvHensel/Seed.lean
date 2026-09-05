/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexBasic.Fold
public import HexMvHensel.Diophantine

@[expose] public section

/-!
Input data and leading-coefficient preparation for multivariate Hensel
lifting.  `Setup` remains in `Uni`; this module extends that stable object
with the full checked input contract.
-/

namespace Hex.MvHensel

open Hex
open Hex.MvPoly

/-- The starting data for one multivariate lift. -/
structure Input (n : Nat)
    (cmp : Mono (n + 1) → Mono (n + 1) → Ordering)
    (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp] [IsMonomialOrder cmp'] where
  /-- Selected main variable, evaluation point, prime, and exponent. -/
  setup : Setup n
  /-- Multivariate polynomial whose factors are to be lifted. -/
  target : MvPoly (n + 1) Int cmp
  /-- Univariate factors of the target at the evaluation point. -/
  images : List ZPoly
  /-- Prescribed leading coefficients for the lifted factors. -/
  leading : List (MvPoly n Int cmp')
  /-- Univariate partial-fraction witnesses for the image factors. -/
  witness : List ZPoly

/-- Failures retain the distinction between malformed input, an unsuitable
point or prime, and failure to reconstruct at the available modulus. -/
inductive Failure where
  /-- Tuple arities, degrees, or setup parameters are malformed. -/
  | arity
  /-- Evaluation lowers the target's main-variable degree. -/
  | degreeDrop
  /-- The univariate images do not multiply to the evaluated target. -/
  | imageProduct
  /-- The prescribed leading coefficients do not multiply correctly. -/
  | leadingProduct
  /-- A leading coefficient has the wrong image at the selected point. -/
  | leadingImage (j : Nat)
  /-- The working prime divides an image leading coefficient. -/
  | primeDividesLc (j : Nat)
  /-- The univariate images are not pairwise coprime modulo the prime. -/
  | notCoprime
  /-- A partial-fraction witness exceeds its permitted degree. -/
  | witnessDegree (j : Nat)
  /-- Integer reconstruction failed at the reported modulus. -/
  | reconstruct (modulus : Nat)
  deriving BEq, DecidableEq, Repr

/-- Retry policy for reconstruction failures. -/
structure Config where
  doublings : Nat
  deriving BEq, DecidableEq, Repr

namespace Config

/-- Six exponent doublings after the initial attempt. -/
def default : Config := { doublings := 6 }

end Config

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp] [IsMonomialOrder cmp']

/-- Ordered product of multivariate polynomials. -/
def mvProduct {k : Nat} {order : Mono k → Mono k → Ordering}
    [IsMonomialOrder order] (fs : List (MvPoly k Int order)) :
    MvPoly k Int order :=
  fs.foldl (· * ·) 1

/-- Replace the coefficient at the main-variable degree of `p` by `L`. -/
def setLc (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (L : MvPoly n Int cmp') (p : MvPoly (n + 1) Int cmp) :
    MvPoly (n + 1) Int cmp :=
  let q := MvPoly.toUnivariate i cmp' p
  let degree := MvPoly.degreeOf i p
  let size := max q.size (degree + 1)
  let coefficients := Array.ofFn (n := size) fun k =>
    if k.val = degree then L else q.coeff k.val
  MvPoly.ofUnivariate (cmp := cmp) i cmp'
    (DensePoly.ofCoeffs coefficients)

/-- Embed a univariate image and replace its leading coefficient by `L`. -/
def seed (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (L : MvPoly n Int cmp') (F : ZPoly) :
    MvPoly (n + 1) Int cmp :=
  if F.size = 0 then 0
  else
    let coefficients := Array.ofFn (n := F.size) fun k =>
      if k.val + 1 = F.size then L else MvPoly.C (F.coeff k.val)
    MvPoly.ofUnivariate (cmp := cmp) i cmp'
      (DensePoly.ofCoeffs coefficients)

/-- Keep only variables whose indices are below `count`; this is evaluation
of every later variable at zero without changing the arity. -/
def prefixVars {k : Nat} {order : Mono k → Mono k → Ordering}
    [IsMonomialOrder order] (count : Nat) (p : MvPoly k Int order) :
    MvPoly k Int order :=
  p.restrictBy fun m =>
    decide (∀ j : Fin k, count ≤ j.val → Mono.degreeOf j m = 0)

/-- Keep the main variable and the first `count` remaining variables, setting
all later remaining variables to zero. -/
def prefixNonMain (i : Fin (n + 1)) (count : Nat)
    (p : MvPoly (n + 1) Int cmp) : MvPoly (n + 1) Int cmp :=
  p.restrictBy fun m =>
    decide (∀ j : Fin n, count ≤ j.val →
      Mono.degreeOf (remainingVar i j) m = 0)

private theorem arrayOfFn_getD {R : Type} [Zero R] {size : Nat}
    (f : Fin size → R) (k : Nat) :
    (Array.ofFn f).getD k 0 = if h : k < size then f ⟨k, h⟩ else 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases h : k < size
  · rw [dite_eq_left h, dite_eq_left h]
    rfl
  · rw [dite_eq_right h, dite_eq_right h]
    rfl

private theorem arrayMap_getD {R S : Type} [Zero R] [Zero S]
    (f : R → S) (hzero : f 0 = 0) (a : Array R) (k : Nat) :
    (a.map f).getD k 0 = f (a.getD k 0) := by
  rw [Array.getD_eq_getD_getElem?]
  rw [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_map]
  cases h : a[k]? <;> simp [hzero]

/-- Coefficients of an image are evaluations of recursive coefficients. -/
private theorem imageAt_coeff (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (a : Fin n → Int) (p : MvPoly (n + 1) Int cmp) (k : Nat) :
    (imageAt i cmp' a p).coeff k =
      MvPoly.evalHorner a ((MvPoly.toUnivariate i cmp' p).coeff k) := by
  unfold imageAt
  rw [DensePoly.coeff_ofCoeffs]
  have hzero : MvPoly.evalHorner a (0 : MvPoly n Int cmp') = 0 := by
    rw [MvPoly.evalHorner_eq, MvPoly.eval_eq]
    rfl
  calc
    _ = MvPoly.evalHorner a
        ((MvPoly.toUnivariate i cmp' p).toArray.getD k 0) :=
      arrayMap_getD (fun c => MvPoly.evalHorner a c) hzero _ _
    _ = _ := congrArg (MvPoly.evalHorner a)
      (DensePoly.toArray_getD (MvPoly.toUnivariate i cmp' p) k)

private theorem prod_zero (a : Fin n → Int) :
    Mono.prod a (Mono.zero : Mono n) = 1 := by
  unfold Mono.prod
  generalize List.finRange n = indices
  induction indices with
  | nil => rfl
  | cons j indices ih =>
      simp only [List.foldl_cons]
      rw [show (Mono.zero : Mono n)[j] = 0 by
        simp [Mono.zero], Mono.powBySq]
      simpa using ih

/-- A generated dense polynomial with nonzero last coefficient retains the
full generated size. -/
private theorem size_ofFn_last {R : Type} [Zero R] [DecidableEq R]
    {size : Nat} (hsize : 0 < size) (f : Fin size → R)
    (hlast : f ⟨size - 1, by omega⟩ ≠ Zero.zero) :
    (DensePoly.ofCoeffs (Array.ofFn f)).size = size := by
  let p := DensePoly.ofCoeffs (Array.ofFn f)
  change p.size = size
  have hindex : size - 1 < size := by omega
  have hcoeff : p.coeff (size - 1) = f ⟨size - 1, hindex⟩ := by
    unfold p
    rw [DensePoly.coeff_ofCoeffs]
    exact (arrayOfFn_getD f (size - 1)).trans (by
      rw [dite_eq_left hindex])
  have hupper : p.size ≤ size := by
    exact Nat.le_trans (DensePoly.size_ofCoeffs_le _) (by simp)
  have hlower : size ≤ p.size := by
    by_cases h : size ≤ p.size
    · exact h
    · exfalso
      have hle : p.size ≤ size - 1 := by omega
      have hzero := DensePoly.coeff_eq_zero_of_size_le p hle
      apply hlast
      exact hcoeff.symm.trans hzero
  exact Nat.le_antisymm hupper hlower

/-- A nonzero last generated coefficient survives dense normalization as the
leading coefficient. -/
private theorem leadingCoeff_ofFn_last {R : Type} [Zero R] [DecidableEq R]
    {size : Nat} (hsize : 0 < size) (f : Fin size → R)
    (hlast : f ⟨size - 1, by omega⟩ ≠ Zero.zero) :
    (DensePoly.ofCoeffs (Array.ofFn f)).leadingCoeff =
      f ⟨size - 1, by omega⟩ := by
  let p := DensePoly.ofCoeffs (Array.ofFn f)
  have hpSize : p.size = size := size_ofFn_last hsize f hlast
  have hindex : size - 1 < size := by omega
  have hcoeff : p.coeff (size - 1) = f ⟨size - 1, hindex⟩ := by
    unfold p
    rw [DensePoly.coeff_ofCoeffs]
    exact (arrayOfFn_getD f (size - 1)).trans (by
      rw [dite_eq_left hindex])
  change p.leadingCoeff = f ⟨size - 1, by omega⟩
  rw [DensePoly.leadingCoeff_eq_coeff_last p (by omega), hpSize, hcoeff]

/-- Reassembly preserves the degree in the reinserted variable. -/
private theorem degreeOf_ofUnivariate (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (q : DensePoly (MvPoly n Int cmp')) :
    MvPoly.degreeOf i (MvPoly.ofUnivariate (cmp := cmp) i cmp' q) =
      q.degree?.getD 0 := by
  let p := MvPoly.ofUnivariate (cmp := cmp) i cmp' q
  by_cases hqzero : q.size = 0
  · have hq : q = 0 := (DensePoly.size_eq_zero_iff q).mp hqzero
    subst q
    simp [MvPoly.ofUnivariate]
  · have hqpos : 0 < q.size := Nat.pos_of_ne_zero hqzero
    have hdegree : q.degree?.getD 0 = q.size - 1 := by
      rw [DensePoly.degree?_eq_some_of_pos_size q hqpos]
      rfl
    rw [hdegree]
    apply Nat.le_antisymm
    · rw [MvPoly.degreeOf_eq]
      unfold MvPoly.foldTerms
      rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
      change p.termsList.foldl
        (fun d term => max d (Mono.degreeOf i term.1)) 0 ≤ q.size - 1
      have hterm : ∀ term ∈ p.termsList,
          Mono.degreeOf i term.1 ≤ q.size - 1 := by
        intro term hmem
        have hcoeff := MvPoly.coeff_eq_of_mem_terms p hmem
        have hnonzero : term.2 ≠ 0 := by
          intro hzero
          have hmono : term.1 ∈ p.monomials := by
            unfold MvPoly.monomials
            exact List.mem_map.mpr ⟨term, hmem, rfl⟩
          exact ((MvPoly.mem_monomials_iff term.1 p).mp hmono)
            (hcoeff.trans hzero)
        have hview := MvPoly.ofUnivariate_coeff (cmp := cmp) i q
          (Mono.degreeOf i term.1) (MvPoly.removeVar i term.1)
        rw [MvPoly.insertVar_removeVar] at hview
        have hqcoeff : MvPoly.coeff (MvPoly.removeVar i term.1)
            (q.coeff (Mono.degreeOf i term.1)) ≠ 0 := by
          intro hzero
          apply hnonzero
          rw [← hcoeff, hview, hzero]
        have hlt : Mono.degreeOf i term.1 < q.size := by
          by_cases hlt : Mono.degreeOf i term.1 < q.size
          · exact hlt
          · have hzero := DensePoly.coeff_eq_zero_of_size_le q
              (Nat.le_of_not_gt hlt)
            rw [hzero] at hqcoeff
            exact False.elim (hqcoeff (MvPoly.coeff_zero _))
        omega
      have fold_le : ∀ (terms : List (Mono (n + 1) × Int))
          (init : Nat), init ≤ q.size - 1 →
          (∀ term ∈ terms, Mono.degreeOf i term.1 ≤ q.size - 1) →
          terms.foldl
            (fun d term => max d (Mono.degreeOf i term.1)) init ≤
            q.size - 1 := by
        intro terms init hinit hterms
        induction terms generalizing init with
        | nil => exact hinit
        | cons term terms ih =>
            simp only [List.foldl_cons]
            apply ih
            · exact Nat.max_le.mpr ⟨hinit,
                hterms term (List.mem_cons_self ..)⟩
            · intro next hnext
              exact hterms next (List.mem_cons_of_mem term hnext)
      exact fold_le p.termsList 0 (by omega) hterm
    · have htop := DensePoly.coeff_last_ne_zero_of_pos_size q hqpos
      cases hlead : (q.coeff (q.size - 1)).leadingTerm with
      | none =>
          exact False.elim (htop
            ((MvPoly.leadingTerm_eq_none_iff _).mp hlead))
      | some term =>
          rcases term with ⟨m, c⟩
          have hsome :=
            ((MvPoly.leadingTerm_eq_some_iff _ m c).mp hlead).1
          have hm : m ∈ (q.coeff (q.size - 1)).monomials :=
            (MvPoly.mem_monomials_iff_isSome m _).mpr (by
              rw [hsome]
              rfl)
          have hpcoeff := MvPoly.ofUnivariate_coeff (cmp := cmp) i q
            (q.size - 1) m
          have hpmono : MvPoly.insertVar i (q.size - 1) m ∈ p.monomials :=
            (MvPoly.mem_monomials_iff _ p).mpr (by
              change MvPoly.coeff (MvPoly.insertVar i (q.size - 1) m) p ≠ 0
              rw [hpcoeff]
              exact (MvPoly.mem_monomials_iff m _).mp hm)
          unfold MvPoly.monomials at hpmono
          rcases List.mem_map.mp hpmono with ⟨entry, hentry, hfirst⟩
          have hle := List.le_foldl_max_of_mem p.termsList
            (fun term => Mono.degreeOf i term.1) (init := 0) hentry
          rw [hfirst] at hle
          rw [MvPoly.degreeOf_eq]
          unfold MvPoly.foldTerms
          rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
          unfold p at hle
          unfold MvPoly.termsList at hle
          simpa only [MvPoly.degreeOf_insertVar] using hle

/-- A recursive view has no coefficient beyond the selected-variable
degree. -/
private theorem toUnivariate_size_le_degree (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (p : MvPoly (n + 1) Int cmp) :
    (MvPoly.toUnivariate i cmp' p).size ≤ MvPoly.degreeOf i p + 1 := by
  let q := MvPoly.toUnivariate i cmp' p
  change q.size ≤ MvPoly.degreeOf i p + 1
  have hdegree := degreeOf_ofUnivariate (cmp := cmp) i cmp' q
  rw [MvPoly.ofUnivariate_toUnivariate] at hdegree
  by_cases hqzero : q.size = 0
  · rw [(DensePoly.degree?_eq_none_iff q).mpr hqzero] at hdegree
    simp only [Option.getD_none] at hdegree
    omega
  · have hqpos : 0 < q.size := Nat.pos_of_ne_zero hqzero
    rw [DensePoly.degree?_eq_some_of_pos_size q hqpos] at hdegree
    simp only [Option.getD_some] at hdegree
    omega

/-- The recursive coefficient at the selected-variable degree is its
leading coefficient, including for the zero polynomial. -/
private theorem toUnivariate_coeff_degree (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (p : MvPoly (n + 1) Int cmp) :
    (MvPoly.toUnivariate i cmp' p).coeff (MvPoly.degreeOf i p) =
      (MvPoly.toUnivariate i cmp' p).leadingCoeff := by
  let q := MvPoly.toUnivariate i cmp' p
  change q.coeff (MvPoly.degreeOf i p) = q.leadingCoeff
  have hdegree := degreeOf_ofUnivariate (cmp := cmp) i cmp' q
  rw [MvPoly.ofUnivariate_toUnivariate] at hdegree
  by_cases hqzero : q.size = 0
  · have hq : q = 0 := (DensePoly.size_eq_zero_iff q).mp hqzero
    change (MvPoly.toUnivariate i cmp' p).coeff
        (MvPoly.degreeOf i p) =
      (MvPoly.toUnivariate i cmp' p).leadingCoeff
    rw [show MvPoly.toUnivariate i cmp' p = 0 by exact hq]
    rfl
  · have hqpos : 0 < q.size := Nat.pos_of_ne_zero hqzero
    rw [DensePoly.degree?_eq_some_of_pos_size q hqpos] at hdegree
    simp only [Option.getD_some] at hdegree
    rw [hdegree, DensePoly.leadingCoeff_eq_coeff_last q hqpos]

/-! # Leading-coefficient and prefix laws -/

/-- Installing a nonzero top coefficient makes it the exact leading
coefficient in the selected variable. -/
theorem lcIn_setLc (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (L : MvPoly n Int cmp') (p : MvPoly (n + 1) Int cmp)
    (hL : L ≠ 0) :
    lcIn i cmp' (setLc i cmp' L p) = L := by
  unfold lcIn setLc
  rw [MvPoly.toUnivariate_ofUnivariate]
  let q := MvPoly.toUnivariate i cmp' p
  let degree := MvPoly.degreeOf i p
  let size := max q.size (degree + 1)
  let coefficients : Fin size → MvPoly n Int cmp' := fun k =>
    if k.val = degree then L else q.coeff k.val
  change (DensePoly.ofCoeffs (Array.ofFn coefficients)).leadingCoeff = L
  have hsize : size = degree + 1 := by
    unfold size q degree
    exact Nat.max_eq_right (toUnivariate_size_le_degree i cmp' p)
  have hsizepos : 0 < size := by omega
  have htop : (⟨size - 1, by omega⟩ : Fin size).val = degree := by
    change size - 1 = degree
    omega
  calc
    (DensePoly.ofCoeffs (Array.ofFn coefficients)).leadingCoeff =
        coefficients ⟨size - 1, by omega⟩ :=
      leadingCoeff_ofFn_last hsizepos coefficients (by
        unfold coefficients
        rw [ite_eq_left htop]
        exact hL)
    _ = L := by
      unfold coefficients
      rw [ite_eq_left htop]

/-- Installing a nonzero top coefficient preserves the selected-variable
degree, including the degree-zero case. -/
theorem degreeOf_setLc (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (L : MvPoly n Int cmp') (p : MvPoly (n + 1) Int cmp)
    (hL : L ≠ 0) :
    MvPoly.degreeOf i (setLc i cmp' L p) = MvPoly.degreeOf i p := by
  unfold setLc
  let q := MvPoly.toUnivariate i cmp' p
  let degree := MvPoly.degreeOf i p
  let size := max q.size (degree + 1)
  let coefficients : Fin size → MvPoly n Int cmp' := fun k =>
    if k.val = degree then L else q.coeff k.val
  change MvPoly.degreeOf i
      (MvPoly.ofUnivariate (cmp := cmp) i cmp'
        (DensePoly.ofCoeffs (Array.ofFn coefficients))) = degree
  rw [degreeOf_ofUnivariate]
  have hsize : size = degree + 1 := by
    unfold size q degree
    exact Nat.max_eq_right (toUnivariate_size_le_degree i cmp' p)
  have hsizepos : 0 < size := by omega
  have htop : (⟨size - 1, by omega⟩ : Fin size).val = degree := by
    change size - 1 = degree
    omega
  have hpolySize :
      (DensePoly.ofCoeffs (Array.ofFn coefficients)).size = size :=
    size_ofFn_last hsizepos coefficients (by
      unfold coefficients
      rw [ite_eq_left htop]
      exact hL)
  rw [DensePoly.degree?_eq_some_of_pos_size _ (by
    rw [hpolySize]
    exact hsizepos)]
  simp only [Option.getD_some]
  rw [hpolySize]
  omega

/-- Replacing the top slice preserves an image whenever the replacement has
the same value at the image point. -/
theorem imageAt_setLc (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (a : Fin n → Int) (L : MvPoly n Int cmp')
    (p : MvPoly (n + 1) Int cmp)
    (hL : MvPoly.eval a L = MvPoly.eval a (lcIn i cmp' p)) :
    imageAt i cmp' a (setLc i cmp' L p) = imageAt i cmp' a p := by
  apply DensePoly.ext_coeff
  intro k
  rw [imageAt_coeff, imageAt_coeff]
  unfold setLc
  rw [MvPoly.toUnivariate_ofUnivariate]
  let q := MvPoly.toUnivariate i cmp' p
  let degree := MvPoly.degreeOf i p
  let size := max q.size (degree + 1)
  let coefficients : Fin size → MvPoly n Int cmp' := fun j =>
    if j.val = degree then L else q.coeff j.val
  change MvPoly.evalHorner a
      ((DensePoly.ofCoeffs (Array.ofFn coefficients)).coeff k) =
    MvPoly.evalHorner a (q.coeff k)
  rw [DensePoly.coeff_ofCoeffs]
  calc
    MvPoly.evalHorner a ((Array.ofFn coefficients).getD k 0) =
        MvPoly.evalHorner a
          (if h : k < size then coefficients ⟨k, h⟩ else 0) :=
      congrArg (MvPoly.evalHorner a) (arrayOfFn_getD coefficients k)
    _ = MvPoly.evalHorner a (q.coeff k) := by
      by_cases hk : k < size
      · rw [dite_eq_left hk]
        by_cases hdegree : k = degree
        · subst k
          unfold coefficients
          rw [ite_eq_left rfl, MvPoly.evalHorner_eq,
            MvPoly.evalHorner_eq, toUnivariate_coeff_degree]
          simpa [lcIn] using hL
        · unfold coefficients
          rw [ite_eq_right hdegree]
      · rw [dite_eq_right hk]
        have hqsize : q.size ≤ size := by
          unfold size
          exact Nat.le_max_left ..
        have hqzero : q.coeff k = 0 :=
          DensePoly.coeff_eq_zero_of_size_le q
            (Nat.le_trans hqsize (Nat.le_of_not_gt hk))
        rw [hqzero]

/-- Repeated coordinate prefixes retain exactly the smaller prefix. -/
theorem prefixVars_min {k : Nat}
    {order : Mono k → Mono k → Ordering} [IsMonomialOrder order]
    (a b : Nat) (p : MvPoly k Int order) :
    prefixVars a (prefixVars b p) = prefixVars (min a b) p := by
  apply MvPoly.ext
  intro m
  let P : Nat → Prop := fun count =>
    ∀ j : Fin k, count ≤ j.val → Mono.degreeOf j m = 0
  have hP : P (min a b) ↔ P a ∧ P b := by
    constructor
    · intro h
      exact ⟨fun j hj => h j (Nat.le_trans (Nat.min_le_left ..) hj),
        fun j hj => h j (Nat.le_trans (Nat.min_le_right ..) hj)⟩
    · rintro ⟨ha, hb⟩ j hj
      by_cases hab : a ≤ b
      · exact ha j (by simpa [Nat.min_eq_left hab] using hj)
      · have hba : b ≤ a := Nat.le_of_not_ge hab
        exact hb j (by simpa [Nat.min_eq_right hba] using hj)
  unfold prefixVars
  rw [MvPoly.coeff_restrictBy, MvPoly.coeff_restrictBy,
    MvPoly.coeff_restrictBy]
  change (if decide (P a) then (if decide (P b) then _ else 0) else 0) =
    if decide (P (min a b)) then _ else 0
  simp only [decide_eq_true_eq, hP]
  by_cases ha : P a <;> by_cases hb : P b <;> simp_all

/-- Repeated non-main prefixes retain exactly the smaller prefix. -/
theorem prefixNonMain_min (i : Fin (n + 1)) (a b : Nat)
    (p : MvPoly (n + 1) Int cmp) :
    prefixNonMain i a (prefixNonMain i b p) =
      prefixNonMain i (min a b) p := by
  apply MvPoly.ext
  intro m
  let P : Nat → Prop := fun count =>
    ∀ j : Fin n, count ≤ j.val →
      Mono.degreeOf (remainingVar i j) m = 0
  have hP : P (min a b) ↔ P a ∧ P b := by
    constructor
    · intro h
      exact ⟨fun j hj => h j (Nat.le_trans (Nat.min_le_left ..) hj),
        fun j hj => h j (Nat.le_trans (Nat.min_le_right ..) hj)⟩
    · rintro ⟨ha, hb⟩ j hj
      by_cases hab : a ≤ b
      · exact ha j (by simpa [Nat.min_eq_left hab] using hj)
      · have hba : b ≤ a := Nat.le_of_not_ge hab
        exact hb j (by simpa [Nat.min_eq_right hba] using hj)
  unfold prefixNonMain
  rw [MvPoly.coeff_restrictBy, MvPoly.coeff_restrictBy,
    MvPoly.coeff_restrictBy]
  change (if decide (P a) then (if decide (P b) then _ else 0) else 0) =
    if decide (P (min a b)) then _ else 0
  simp only [decide_eq_true_eq, hP]
  by_cases ha : P a <;> by_cases hb : P b <;> simp_all

/-- Build all seeds without any default indexing or prefix truncation. -/
def seedTuple? (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp'] :
    List ZPoly → List (MvPoly n Int cmp') →
      Option (List (MvPoly (n + 1) Int cmp))
  | [], [] => some []
  | F :: Fs, L :: Ls => do
      let tail ← seedTuple? i cmp' Fs Ls
      some (seed i cmp' (prefixVars 0 L) F :: tail)
  | _, _ => none

/-! The elementary seed laws are Phase-1 proof obligations. -/

theorem imageAt_seed (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (a : Fin n → Int) (L : MvPoly n Int cmp') (F : ZPoly)
    (h : MvPoly.eval a L = F.leadingCoeff) :
    imageAt i cmp' a (seed (cmp := cmp) i cmp' L F) = F := by
  apply DensePoly.ext_coeff
  intro k
  rw [imageAt_coeff]
  by_cases hF : F.size = 0
  · have hzero : F = 0 := (DensePoly.size_eq_zero_iff F).mp hF
    subst F
    unfold seed
    rw [ite_eq_left hF]
    have hview : MvPoly.toUnivariate i cmp'
        (0 : MvPoly (n + 1) Int cmp) = 0 := by
      apply DensePoly.ext_coeff
      intro e
      apply MvPoly.ext
      intro m
      rw [MvPoly.toUnivariate_coeff, MvPoly.coeff_zero]
      rfl
    rw [hview]
    rw [MvPoly.evalHorner_eq, MvPoly.eval_eq]
    rfl
  · have hFpos : 0 < F.size := Nat.pos_of_ne_zero hF
    unfold seed
    rw [ite_eq_right hF, MvPoly.toUnivariate_ofUnivariate]
    let coefficients : Fin F.size → MvPoly n Int cmp' := fun j =>
      if j.val + 1 = F.size then L else MvPoly.C (F.coeff j.val)
    change MvPoly.evalHorner a
        ((DensePoly.ofCoeffs (Array.ofFn coefficients)).coeff k) =
      F.coeff k
    rw [DensePoly.coeff_ofCoeffs]
    calc
      MvPoly.evalHorner a ((Array.ofFn coefficients).getD k 0) =
          MvPoly.evalHorner a
            (if hk : k < F.size then coefficients ⟨k, hk⟩ else 0) :=
        congrArg (MvPoly.evalHorner a) (arrayOfFn_getD coefficients k)
      _ = F.coeff k := by
        by_cases hk : k < F.size
        · rw [dite_eq_left hk]
          by_cases htop : k + 1 = F.size
          · have hkLast : k = F.size - 1 := by omega
            unfold coefficients
            rw [ite_eq_left htop, MvPoly.evalHorner_eq, h,
              DensePoly.leadingCoeff_eq_coeff_last F hFpos, hkLast]
          · unfold coefficients
            rw [ite_eq_right htop, MvPoly.evalHorner_eq,
              MvPoly.eval_eq, MvPoly.termsList_C]
            by_cases hcoeff : F.coeff k = 0
            · simp [hcoeff]
            · simp only [ite_eq_right hcoeff, List.foldl_cons,
                List.foldl_nil, Int.zero_add]
              rw [prod_zero, Int.mul_one]
        · rw [dite_eq_right hk]
          have hzero := DensePoly.coeff_eq_zero_of_size_le F
            (Nat.le_of_not_gt hk)
          rw [hzero]
          rw [MvPoly.evalHorner_eq, MvPoly.eval_eq]
          rfl

theorem lcIn_seed (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (L : MvPoly n Int cmp') (F : ZPoly) (hF : F.size ≠ 0) (hL : L ≠ 0) :
    lcIn i cmp' (seed (cmp := cmp) i cmp' L F) = L := by
  have hFpos : 0 < F.size := Nat.pos_of_ne_zero hF
  unfold lcIn seed
  rw [ite_eq_right hF]
  rw [MvPoly.toUnivariate_ofUnivariate]
  let coefficients : Fin F.size → MvPoly n Int cmp' := fun k =>
    if k.val + 1 = F.size then L else MvPoly.C (F.coeff k.val)
  change (DensePoly.ofCoeffs (Array.ofFn coefficients)).leadingCoeff = L
  have htop :
      (⟨F.size - 1, by omega⟩ : Fin F.size).val + 1 = F.size := by
    change F.size - 1 + 1 = F.size
    omega
  calc
    (DensePoly.ofCoeffs (Array.ofFn coefficients)).leadingCoeff =
        coefficients ⟨F.size - 1, by omega⟩ :=
      leadingCoeff_ofFn_last hFpos coefficients (by
        unfold coefficients
        rw [ite_eq_left htop]
        exact hL)
    _ = L := by
      unfold coefficients
      rw [ite_eq_left htop]

theorem degreeOf_seed (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (L : MvPoly n Int cmp') (F : ZPoly) (hL : L ≠ 0) :
    MvPoly.degreeOf i (seed (cmp := cmp) i cmp' L F) =
      F.degree?.getD 0 := by
  by_cases hF : F.size = 0
  · have hzero : F = 0 := (DensePoly.size_eq_zero_iff F).mp hF
    subst F
    simp [seed]
  · have hFpos : 0 < F.size := Nat.pos_of_ne_zero hF
    unfold seed
    rw [ite_eq_right hF]
    let coefficients : Fin F.size → MvPoly n Int cmp' := fun k =>
      if k.val + 1 = F.size then L else MvPoly.C (F.coeff k.val)
    change MvPoly.degreeOf i
        (MvPoly.ofUnivariate (cmp := cmp) i cmp'
          (DensePoly.ofCoeffs (Array.ofFn coefficients))) =
      F.degree?.getD 0
    rw [degreeOf_ofUnivariate]
    have htop :
        (⟨F.size - 1, by omega⟩ : Fin F.size).val + 1 = F.size := by
      change F.size - 1 + 1 = F.size
      omega
    have hsize : (DensePoly.ofCoeffs
        (Array.ofFn coefficients)).size = F.size :=
      size_ofFn_last hFpos coefficients (by
        unfold coefficients
        rw [ite_eq_left htop]
        exact hL)
    rw [DensePoly.degree?_eq_some_of_pos_size F hFpos]
    rw [DensePoly.degree?_eq_some_of_pos_size _ (by
      rw [hsize]
      exact hFpos)]
    rw [hsize]

end Hex.MvHensel
