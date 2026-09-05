/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Norm
public import HexNumberFieldTowerMathlib.FactorGeneric
public import HexBerlekampZassenhausMathlib

public section

/-!
# Correctness of recursive Trager factorization
-/

namespace Hex.NumberTower

/-- A nonconstant tower polynomial has no factorization into two nonconstant
tower polynomials. -/
def PolynomialIrreducible (T : NumberTower) (f : Poly T) : Prop :=
  !f.isZero ∧ 0 < f.degree?.getD 0 ∧
    ∀ g h : Poly T, f = g * h →
      g.degree?.getD 0 = 0 ∨ h.degree?.getD 0 = 0

namespace Factorization

/-- Executable natural power without presupposing a law-bearing monoid
instance on tower coefficients. -/
@[expose]
def polyPow {T : NumberTower} (f : Poly T) : Nat → Poly T
  | 0 => 1
  | n + 1 => polyPow f n * f

/-- Reconstruct a polynomial from a public factorization payload. -/
@[expose]
def reconstruct {T : NumberTower} {f : Poly T}
    (r : Factorization T f) : Poly T :=
  r.factors.foldl
    (fun product factor => product * polyPow factor.1 factor.2)
    (DensePoly.C r.scalar)

/-- Mathematical meaning of a checked factorization payload. Strict
executable ordering of monic factors also rules out associates and duplicate
entries. -/
@[expose]
def Sound {T : NumberTower} {f : Poly T}
    (r : Factorization T f) : Prop :=
  r.reconstruct = f ∧
    (∀ factor ∈ r.factors.toList,
      factor.1.leadingCoeff = 1 ∧
      0 < factor.2 ∧
      PolynomialIrreducible T factor.1) ∧
    Factor.factorsSorted
      (r.factors.map fun factor =>
        (factor.1.toArray.map coeffs, factor.2))

end Factorization

open scoped TowerField

private theorem coeff_ofData_data_public (T : NumberTower)
    (a : Arithmetic.Coeff T.levels.toList) :
    coeffs (T.ofCoeffs a.data) = a.data := by
  rw [coeffs_ofCoeffs, normalizeCoeffs_eq_self]
  simpa [dim] using a.size_eq

private theorem fixedCoeffs_coeffs (T : NumberTower) (a : Elem T) :
    (Arithmetic.Coeff.ofData T.levels.toList (coeffs a)).data = coeffs a := by
  change Arithmetic.fixedCoeffs (levelsDim T.levels.toList) (coeffs a) =
    coeffs a
  apply Array.ext
  · simp [Arithmetic.fixedCoeffs, dim]
  · intro i hi₁ hi₂
    have hi : i < T.dim := by simpa using hi₂
    simp [Arithmetic.fixedCoeffs, Array.getD, hi]

private theorem coeff_ext {levels : List Level}
    {a b : Arithmetic.Coeff levels} (h : a.data = b.data) : a = b := by
  cases a
  cases b
  simp_all

private def elemCoeff (T : NumberTower) (a : Elem T) :
    Arithmetic.Coeff T.levels.toList :=
  ⟨coeffs a, by simpa [dim] using coeffs_size a⟩

/-- Canonical raw coefficients and public tower elements are the same
fixed-width coordinate field. -/
private noncomputable def coeffEquiv (T : NumberTower) :
    let hinjective := coeffDenote_injective T
    let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
    letI : Field (Arithmetic.Coeff T.levels.toList) :=
      Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
    Arithmetic.Coeff T.levels.toList ≃+* Elem T := by
  let hinjective := coeffDenote_injective T
  let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
  letI : Field (Arithmetic.Coeff T.levels.toList) :=
    Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
  refine
    { toFun := fun a => T.ofCoeffs a.data
      invFun := elemCoeff T
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_ }
  · intro a
    apply coeff_ext
    exact coeff_ofData_data_public T a
  · intro a
    apply Elem.ext
    rw [coeff_ofData_data_public]
    rfl
  · intro a b
    apply toComplex_injective T
    rw [map_mul]
    rw [LevelSemantics.toComplex_eq_denote T,
      LevelSemantics.toComplex_eq_denote T,
      LevelSemantics.toComplex_eq_denote T]
    rw [coeff_ofData_data_public, coeff_ofData_data_public,
      coeff_ofData_data_public]
    exact LevelSemantics.coeffDenote_mul T.levels.toList T.valid a b
  · intro a b
    apply toComplex_injective T
    rw [map_add]
    rw [LevelSemantics.toComplex_eq_denote T,
      LevelSemantics.toComplex_eq_denote T,
      LevelSemantics.toComplex_eq_denote T]
    rw [coeff_ofData_data_public, coeff_ofData_data_public,
      coeff_ofData_data_public]
    exact LevelSemantics.coeffDenote_add T.levels.toList a b

private theorem map_rawPoly (T : NumberTower) (f : Poly T) :
    let hinjective := coeffDenote_injective T
    let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
    letI : Field (Arithmetic.Coeff T.levels.toList) :=
      Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
    (HexPolyMathlib.toPolynomial
      (Factor.rawPoly T.levels.toList (f.toArray.map coeffs))).map
        (coeffEquiv T).toRingHom = HexPolyMathlib.toPolynomial f := by
  let hinjective := coeffDenote_injective T
  let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
  letI : Field (Arithmetic.Coeff T.levels.toList) :=
    Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    HexPolyMathlib.coeff_toPolynomial]
  apply Elem.ext
  change coeffs (T.ofCoeffs
      ((Factor.rawPoly T.levels.toList
        (f.toArray.map coeffs)).coeff n).data) = coeffs (f.coeff n)
  rw [coeff_ofData_data_public]
  simp only [Factor.rawPoly, DensePoly.coeff_ofCoeffs]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_map]
  by_cases hn : n < f.size
  · have harray : n < f.toArray.size := by simpa using hn
    rw [Array.getElem?_eq_getElem harray]
    simp only [Option.map_some, Option.getD_some]
    have hcoeff : f.toArray[n] = f.coeff n :=
      (Array.getElem_eq_getD (0 : Elem T) (h := harray)).trans
        (DensePoly.toArray_getD f n)
    rw [hcoeff]
    exact fixedCoeffs_coeffs T (f.coeff n)
  · have harray : f.toArray.size ≤ n := by
      simpa using Nat.le_of_not_gt hn
    rw [Array.getElem?_eq_none harray]
    simp only [Option.map_none, Option.getD_none,
      DensePoly.coeff_eq_zero_of_size_le f
      (Nat.le_of_not_gt hn)]
    change Arithmetic.fixedCoeffs (levelsDim T.levels.toList) #[] =
      coeffs (0 : Elem T)
    rw [coeffs_zero]
    apply Array.ext
    · simp [Arithmetic.fixedCoeffs, dim]
    · intro i hi₁ hi₂
      simp [Arithmetic.fixedCoeffs, Array.getD]

/-- Raw canonical coordinates and the public tower polynomial have the same
fixed complex interpretation. -/
theorem rawPolynomial_rawPoly (T : NumberTower) (f : Poly T) :
    Norm.rawPolynomial T.levels.toList
        (Factor.rawPoly T.levels.toList (f.toArray.map coeffs)) =
      T.toPolynomial f := by
  let hinjective := coeffDenote_injective T
  let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
  letI : Field (Arithmetic.Coeff T.levels.toList) :=
    Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
  rw [Norm.rawPolynomial_eq_map T.levels.toList T.valid hinjective hinv,
    toPolynomial_eq_map, ← map_rawPoly T f, Polynomial.map_map]
  congr 1
  ext a
  change LevelSemantics.coeffDenote T.levels.toList a =
    T.toComplex (T.ofCoeffs a.data)
  rw [LevelSemantics.toComplex_eq_denote, coeff_ofData_data_public]
  rfl

/-- Public tower-polynomial coordinates are canonical raw coordinates. -/
theorem polyCoords_rawPoly (T : NumberTower) (f : Poly T) :
    Factor.polyCoords
        (Factor.rawPoly T.levels.toList (f.toArray.map coeffs)) =
      f.toArray.map coeffs := by
  let hinjective := coeffDenote_injective T
  let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
  letI : Field (Arithmetic.Coeff T.levels.toList) :=
    Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
  let q := Factor.rawPoly T.levels.toList (f.toArray.map coeffs)
  have hmap : (HexPolyMathlib.toPolynomial q).map
      (coeffEquiv T).toRingHom = HexPolyMathlib.toPolynomial f := by
    simpa only [q] using map_rawPoly T f
  by_cases hfzero : f = 0
  · subst f
    have hqzero : q = 0 := by
      apply HexPolyMathlib.equiv.injective
      apply Polynomial.map_injective (coeffEquiv T).toRingHom
        (coeffEquiv T).injective
      simpa using hmap
    change Factor.polyCoords q = (0 : Poly T).toArray.map coeffs
    rw [hqzero]
    have hrawEmpty :
        (0 : DensePoly (Arithmetic.Coeff T.levels.toList)).toArray = #[] :=
      Array.eq_empty_of_size_eq_zero (by simp)
    have hpublicEmpty : (0 : Poly T).toArray = #[] :=
      Array.eq_empty_of_size_eq_zero (by simp)
    rw [Factor.polyCoords, hrawEmpty, hpublicEmpty]
    simp
  · have hfsize : 0 < f.size := Nat.pos_of_ne_zero fun hsize =>
      hfzero ((DensePoly.size_eq_zero_iff f).mp hsize)
    have hqzero : q ≠ 0 := by
      intro hzero
      apply hfzero
      apply HexPolyMathlib.equiv.injective
      rw [hzero, HexPolyMathlib.toPolynomial_zero,
        Polynomial.map_zero] at hmap
      exact hmap.symm
    have hqsize : 0 < q.size := Nat.pos_of_ne_zero fun hsize =>
      hqzero ((DensePoly.size_eq_zero_iff q).mp hsize)
    have hnat := Polynomial.natDegree_map_eq_of_injective
      (f := (coeffEquiv T).toRingHom) (coeffEquiv T).injective
      (HexPolyMathlib.toPolynomial q)
    rw [hmap, HexPolyMathlib.natDegree_toPolynomial,
      HexPolyMathlib.natDegree_toPolynomial,
      DensePoly.degree?_eq_some_of_pos_size q hqsize,
      DensePoly.degree?_eq_some_of_pos_size f hfsize] at hnat
    simp only [Option.getD_some] at hnat
    have hsize : q.size = f.size := by omega
    change Factor.polyCoords q = f.toArray.map coeffs
    apply Array.ext
    · simpa [Factor.polyCoords, hsize]
    · intro i hiq hif
      have hiq' : i < q.toArray.size := by
        simpa [Factor.polyCoords] using hiq
      have hif' : i < f.toArray.size := by simpa using hif
      simp only [Factor.polyCoords, Array.getElem_map]
      have hqi : q.toArray[i]'hiq' = q.coeff i :=
        (Array.getElem_eq_getD (xs := q.toArray) (i := i)
          (h := hiq') (0 : Arithmetic.Coeff T.levels.toList)).trans
          (DensePoly.toArray_getD q i)
      have hi : i < f.size := by simpa using hif
      calc
        (q.toArray[i]'hiq').data = (q.coeff i).data :=
          congrArg Arithmetic.Coeff.data hqi
        _ = coeffs (f.toArray[i]'hif') := by
          simp [q, Factor.rawPoly, DensePoly.coeff_ofCoeffs,
            Array.getD, hi, fixedCoeffs_coeffs]

private theorem toPolynomial_of_polyCoords (T : NumberTower)
    (p : DensePoly (Arithmetic.Coeff T.levels.toList)) :
    let hinjective := coeffDenote_injective T
    let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid
      hinjective
    letI : Field (Arithmetic.Coeff T.levels.toList) :=
      Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
    HexPolyMathlib.toPolynomial
        (DensePoly.ofCoeffs
          ((Factor.polyCoords p).map (ofCoeffs T))) =
      (HexPolyMathlib.toPolynomial p).map (coeffEquiv T).toRingHom := by
  let hinjective := coeffDenote_injective T
  let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
  letI : Field (Arithmetic.Coeff T.levels.toList) :=
    Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
  dsimp only
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    HexPolyMathlib.coeff_toPolynomial]
  change (DensePoly.ofCoeffs
      ((Factor.polyCoords p).map (ofCoeffs T))).coeff n =
    coeffEquiv T (p.coeff n)
  rw [DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?,
    Array.getElem?_map]
  simp only [Factor.polyCoords, Array.getElem?_map]
  by_cases hn : n < p.size
  · have harray : n < p.toArray.size := by simpa using hn
    rw [Array.getElem?_eq_getElem harray]
    simp only [Option.map_some, Option.getD_some]
    have hcoeff : p.toArray[n] = p.coeff n :=
      (Array.getElem_eq_getD
        (0 : Arithmetic.Coeff T.levels.toList) (h := harray)).trans
        (DensePoly.toArray_getD p n)
    rw [hcoeff]
    rfl
  · have harray : p.toArray.size ≤ n := by
      simpa using Nat.le_of_not_gt hn
    rw [Array.getElem?_eq_none harray]
    simp only [Option.map_none, Option.getD_none,
      DensePoly.coeff_eq_zero_of_size_le p
        (Nat.le_of_not_gt hn)]
    exact (coeffEquiv T).map_zero.symm

private theorem publicCoords_of_canonical (T : NumberTower)
    (factor : Array (Array Rat))
    (hcanonical : Factor.polyCoords
      (Factor.rawPoly T.levels.toList factor) = factor) :
    (DensePoly.ofCoeffs (factor.map (ofCoeffs T))).toArray.map coeffs =
      factor := by
  let hinjective := coeffDenote_injective T
  let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
  letI : Field (Arithmetic.Coeff T.levels.toList) :=
    Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
  let p := Factor.rawPoly T.levels.toList factor
  let g : Poly T := DensePoly.ofCoeffs (factor.map (ofCoeffs T))
  have hg : g = DensePoly.ofCoeffs
      ((Factor.polyCoords p).map (ofCoeffs T)) := by
    simp only [g, p, hcanonical]
  have hpolynomial : HexPolyMathlib.toPolynomial g =
      (HexPolyMathlib.toPolynomial p).map (coeffEquiv T).toRingHom := by
    rw [hg]
    exact toPolynomial_of_polyCoords T p
  have hraw : Factor.rawPoly T.levels.toList
      (g.toArray.map coeffs) = p := by
    apply HexPolyMathlib.equiv.injective
    apply Polynomial.map_injective (coeffEquiv T).toRingHom
      (coeffEquiv T).injective
    change
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly T.levels.toList
          (g.toArray.map coeffs))).map (coeffEquiv T).toRingHom =
      (HexPolyMathlib.toPolynomial p).map (coeffEquiv T).toRingHom
    rw [map_rawPoly T g, hpolynomial]
  change g.toArray.map coeffs = factor
  rw [← polyCoords_rawPoly T g, hraw]
  exact hcanonical

/-- The executable factor-theoretic predicate implies Mathlib
irreducibility. -/
theorem PolynomialIrreducible.toMathlib {T : NumberTower} {f : Poly T}
    (hf : PolynomialIrreducible T f) :
    Irreducible (HexPolyMathlib.toPolynomial f) := by
  have hfalse : f.isZero = false := by simpa using hf.1
  have hsize : 0 < f.size := (DensePoly.isZero_eq_false_iff f).mp hfalse
  have hfne : f ≠ 0 := by
    intro hzero
    rw [hzero] at hsize
    simp at hsize
  have hpolyNe : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    apply hfne
    apply HexPolyMathlib.equiv.injective
    simpa using hzero
  refine
    { not_isUnit := ?_
      isUnit_or_isUnit := ?_ }
  · exact Polynomial.not_isUnit_of_natDegree_pos _ (by
      rw [HexPolyMathlib.natDegree_toPolynomial]
      exact hf.2.1)
  · intro a b hab
    let g : Poly T := HexPolyMathlib.ofPolynomial a
    let h : Poly T := HexPolyMathlib.ofPolynomial b
    have hfactor : f = g * h := by
      apply HexPolyMathlib.equiv.injective
      simpa [g, h, HexPolyMathlib.equiv_apply] using hab
    rcases hf.2.2 g h hfactor with hg | hh
    · left
      have ha : a ≠ 0 := by
        intro ha
        apply hpolyNe
        rw [hab, ha, zero_mul]
      apply Polynomial.isUnit_iff_degree_eq_zero.mpr
      rw [Polynomial.degree_eq_natDegree ha]
      have hnat : a.natDegree = g.degree?.getD 0 := by
        rw [← HexPolyMathlib.natDegree_toPolynomial]
        simp [g]
      rw [hnat, hg]
      rfl
    · right
      have hb : b ≠ 0 := by
        intro hb
        apply hpolyNe
        rw [hab, hb, mul_zero]
      apply Polynomial.isUnit_iff_degree_eq_zero.mpr
      rw [Polynomial.degree_eq_natDegree hb]
      have hnat : b.natDegree = h.degree?.getD 0 := by
        rw [← HexPolyMathlib.natDegree_toPolynomial]
        simp [h]
      rw [hnat, hh]
      rfl

/-- Mathlib irreducibility implies the executable factor-theoretic
predicate. -/
theorem PolynomialIrreducible.ofMathlib {T : NumberTower} {f : Poly T}
    (hf : Irreducible (HexPolyMathlib.toPolynomial f)) :
    PolynomialIrreducible T f := by
  have hfne : f ≠ 0 := by
    intro hzero
    apply hf.ne_zero
    rw [hzero, HexPolyMathlib.toPolynomial_zero]
  have hsize : 0 < f.size := Nat.pos_of_ne_zero fun hzero =>
    hfne ((DensePoly.size_eq_zero_iff f).mp hzero)
  refine ⟨by
    have hfalse := (DensePoly.isZero_eq_false_iff f).mpr hsize
    simpa using hfalse,
    ?_, ?_⟩
  · simpa only [HexPolyMathlib.natDegree_toPolynomial] using hf.natDegree_pos
  · intro g h hfactor
    have hpolyFactor : HexPolyMathlib.toPolynomial f =
        HexPolyMathlib.toPolynomial g * HexPolyMathlib.toPolynomial h := by
      rw [← HexPolyMathlib.toPolynomial_mul]
      exact congrArg HexPolyMathlib.toPolynomial hfactor
    rcases hf.isUnit_or_isUnit hpolyFactor with hg | hh
    · left
      simpa only [HexPolyMathlib.natDegree_toPolynomial] using
        Polynomial.natDegree_eq_zero_of_isUnit hg
    · right
      simpa only [HexPolyMathlib.natDegree_toPolynomial] using
        Polynomial.natDegree_eq_zero_of_isUnit hh

/-- The executable-carrier irreducibility predicate coincides with Mathlib
irreducibility of the interpreted polynomial. -/
theorem polynomialIrreducible_iff (T : NumberTower) (f : Poly T) :
    PolynomialIrreducible T f ↔
      Irreducible (HexPolyMathlib.toPolynomial f) :=
  ⟨PolynomialIrreducible.toMathlib, PolynomialIrreducible.ofMathlib⟩

private theorem rawPoly_polyCoords_public (levels : List Level)
    (f : DensePoly (Arithmetic.Coeff levels)) :
    Factor.rawPoly levels (Factor.polyCoords f) = f := by
  rw [Factor.rawPoly, Factor.polyCoords, Array.map_map]
  have harray : f.toArray.map
      (Arithmetic.Coeff.ofData levels ∘ Arithmetic.Coeff.data) =
        f.toArray := by
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp [Function.comp_def]
  rw [harray, DensePoly.ofCoeffs_toArray]

private theorem toPolynomial_rawPow (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (f : DensePoly (Arithmetic.Coeff levels)) (n : Nat) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    HexPolyMathlib.toPolynomial (Factor.polyPow f n) =
      HexPolyMathlib.toPolynomial f ^ n := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [Factor.polyPow]
      · rw [Factor.polyPow, ite_eq_right hn]
        have hhalf : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
        dsimp only
        by_cases heven : n % 2 = 0
        · rw [ite_eq_left heven, HexPolyMathlib.toPolynomial_mul,
            ih (n / 2) hhalf]
          rw [← pow_add]
          congr 1
          omega
        · rw [ite_eq_right heven, HexPolyMathlib.toPolynomial_mul,
            HexPolyMathlib.toPolynomial_mul, ih (n / 2) hhalf]
          rw [← pow_add, ← pow_succ]
          congr 1
          omega

/-- Semantic conversion preserves the executable natural power used in a
public factorization payload. -/
theorem toPolynomial_polyPow (T : NumberTower)
    (f : Poly T) (n : Nat) :
    HexPolyMathlib.toPolynomial (Factorization.polyPow f n) =
      HexPolyMathlib.toPolynomial f ^ n := by
  induction n with
  | zero => simp [Factorization.polyPow]
  | succ n ih =>
      rw [Factorization.polyPow, HexPolyMathlib.toPolynomial_mul, ih,
        pow_succ]

private theorem toPolynomial_factorFold (T : NumberTower)
    (factors : List (Poly T × Nat)) (init : Poly T) :
    HexPolyMathlib.toPolynomial
        (factors.foldl (fun product factor =>
          product * Factorization.polyPow factor.1 factor.2) init) =
      HexPolyMathlib.toPolynomial init *
        (factors.map fun factor =>
          HexPolyMathlib.toPolynomial factor.1 ^ factor.2).prod := by
  induction factors generalizing init with
  | nil => simp
  | cons factor factors ih =>
      rw [List.foldl_cons, ih, List.map_cons, List.prod_cons,
        HexPolyMathlib.toPolynomial_mul,
        toPolynomial_polyPow]
      ac_rfl

/-- A public factorization reconstructs as its scalar times the product of
the corresponding polynomial powers. -/
theorem toPolynomial_reconstruct {T : NumberTower} {f : Poly T}
    (r : Factorization T f) :
    HexPolyMathlib.toPolynomial r.reconstruct =
      Polynomial.C r.scalar *
        (r.factors.toList.map fun factor =>
          HexPolyMathlib.toPolynomial factor.1 ^ factor.2).prod := by
  rw [Factorization.reconstruct, ← Array.foldl_toList,
    toPolynomial_factorFold, HexPolyMathlib.toPolynomial_C]

/-- Complex interpretation of a reconstruction is the scalar times the
product of the interpreted factor powers. -/
theorem semantic_reconstruct {T : NumberTower} {f : Poly T}
    (r : Factorization T f) :
    T.toPolynomial r.reconstruct =
      Polynomial.C (T.toComplex r.scalar) *
        (r.factors.toList.map fun factor =>
          T.toPolynomial factor.1 ^ factor.2).prod := by
  rw [toPolynomial_eq_map, toPolynomial_reconstruct,
    Polynomial.map_mul, Polynomial.map_C]
  rw [Polynomial.map_list_prod, List.map_map]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro factor _hfactor
  rw [Function.comp_apply, Polynomial.map_pow, ← toPolynomial_eq_map]

private theorem map_factorFold (T : NumberTower)
    (factors : List (Poly T × Nat))
    (rawInit : DensePoly (Arithmetic.Coeff T.levels.toList))
    (publicInit : Poly T) :
    let hinjective := coeffDenote_injective T
    let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
    letI : Field (Arithmetic.Coeff T.levels.toList) :=
      Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
    (HexPolyMathlib.toPolynomial rawInit).map (coeffEquiv T).toRingHom =
      HexPolyMathlib.toPolynomial publicInit →
    (HexPolyMathlib.toPolynomial
      (factors.foldl (fun product factor =>
        product * Factor.polyPow
          (Factor.rawPoly T.levels.toList
            (factor.1.toArray.map coeffs)) factor.2) rawInit)).map
        (coeffEquiv T).toRingHom =
      HexPolyMathlib.toPolynomial
        (factors.foldl (fun product factor =>
          product * Factorization.polyPow factor.1 factor.2) publicInit) := by
  let hinjective := coeffDenote_injective T
  let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
  letI : Field (Arithmetic.Coeff T.levels.toList) :=
    Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
  dsimp only
  induction factors generalizing rawInit publicInit with
  | nil =>
      intro hinit
      exact hinit
  | cons factor factors ih =>
      intro hinit
      simp only [List.foldl_cons]
      apply ih
      rw [HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul,
        toPolynomial_rawPow T.levels.toList T.valid hinjective hinv,
        Polynomial.map_pow, map_rawPoly T factor.1,
        HexPolyMathlib.toPolynomial_mul,
        toPolynomial_polyPow T factor.1 factor.2, hinit]

/-- The recursive executable irreducibility test has exactly the intended
factor-theoretic meaning in a validated tower. -/
theorem isIrreducible_iff (T : NumberTower) (f : Poly T) :
    Factor.isIrreducible T.levels.toList
      (f.toArray.map coeffs) ↔
        f.leadingCoeff = 1 ∧ PolynomialIrreducible T f := by
  let hinjective := coeffDenote_injective T
  let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
  letI : Field (Arithmetic.Coeff T.levels.toList) :=
    Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
  let raw := Factor.rawPoly T.levels.toList (f.toArray.map coeffs)
  have hmap : (HexPolyMathlib.toPolynomial raw).map
      (coeffEquiv T).toRingHom = HexPolyMathlib.toPolynomial f := by
    exact map_rawPoly T f
  have hlc : coeffEquiv T raw.leadingCoeff = f.leadingCoeff := by
    change (coeffEquiv T).toRingHom raw.leadingCoeff = f.leadingCoeff
    rw [← HexPolyMathlib.leadingCoeff_toPolynomial raw,
      ← Polynomial.leadingCoeff_map_of_injective (coeffEquiv T).injective,
      hmap, HexPolyMathlib.leadingCoeff_toPolynomial]
  have hlcIff : raw.leadingCoeff = 1 ↔ f.leadingCoeff = 1 := by
    constructor
    · intro h
      rw [← hlc, h]
      exact (coeffEquiv T).map_one
    · intro h
      apply (coeffEquiv T).injective
      change coeffEquiv T raw.leadingCoeff = coeffEquiv T 1
      rw [hlc, h]
      exact (coeffEquiv T).map_one.symm
  have hirrIff : Irreducible (HexPolyMathlib.toPolynomial raw) ↔
      Irreducible (HexPolyMathlib.toPolynomial f) := by
    constructor
    · intro h
      have hmapped := (MulEquiv.irreducible_iff
        (f := (Polynomial.mapEquiv (coeffEquiv T)).toMulEquiv)).mpr h
      change Irreducible ((HexPolyMathlib.toPolynomial raw).map
        (coeffEquiv T).toRingHom) at hmapped
      rwa [hmap] at hmapped
    · intro h
      have hmapped : Irreducible
          ((HexPolyMathlib.toPolynomial raw).map
            (coeffEquiv T).toRingHom) := by
        rwa [hmap]
      exact (MulEquiv.irreducible_iff
        (f := (Polynomial.mapEquiv (coeffEquiv T)).toMulEquiv)).mp hmapped
  change Factor.isIrreducible T.levels.toList
      (f.toArray.map coeffs) = true ↔ _
  have hgeneric : Factor.isIrreducible T.levels.toList
      (f.toArray.map coeffs) = true ↔
        raw.leadingCoeff = 1 ∧
          Irreducible (HexPolyMathlib.toPolynomial raw) := by
    simpa [raw] using
      (isIrreducible_iff_of_injective T.levels.toList T.valid
        hinjective (f.toArray.map coeffs))
  constructor
  · intro hchecker
    rcases hgeneric.mp hchecker with ⟨hmonic, hirreducible⟩
    exact ⟨hlcIff.mp hmonic,
      (polynomialIrreducible_iff T f).mpr (hirrIff.mp hirreducible)⟩
  · rintro ⟨hmonic, hirreducible⟩
    apply hgeneric.mpr
    exact ⟨hlcIff.mpr hmonic,
      hirrIff.mpr ((polynomialIrreducible_iff T f).mp hirreducible)⟩

/-- Every returned Trager factorization satisfies reconstruction,
multiplicity, irreducibility, uniqueness, and ordering. -/
theorem factor?_sound (T : NumberTower) (f : Poly T)
    {r : Factorization T f} (h : T.factor? f = some r) :
    r.Sound := by
  have hcheck := r.checked
  simp only [checkFactorization, Factor.check, Bool.and_eq_true] at hcheck
  let hinjective := coeffDenote_injective T
  let hinv := LevelSemantics.coeffDenote_inv T.levels.toList T.valid hinjective
  letI : Field (Arithmetic.Coeff T.levels.toList) :=
    Norm.coeffFieldPoly T.levels.toList T.valid hinjective hinv
  have hscalar : coeffEquiv T
      (Arithmetic.Coeff.ofData T.levels.toList (coeffs r.scalar)) =
        r.scalar := by
    apply Elem.ext
    change coeffs (T.ofCoeffs
      (Arithmetic.Coeff.ofData T.levels.toList (coeffs r.scalar)).data) =
        coeffs r.scalar
    rw [coeff_ofData_data_public, fixedCoeffs_coeffs]
  have hinit :
      (HexPolyMathlib.toPolynomial
        (DensePoly.C (Arithmetic.Coeff.ofData T.levels.toList
          (coeffs r.scalar)))).map (coeffEquiv T).toRingHom =
        HexPolyMathlib.toPolynomial (DensePoly.C r.scalar) := by
    rw [HexPolyMathlib.toPolynomial_C, Polynomial.map_C,
      HexPolyMathlib.toPolynomial_C]
    exact congrArg Polynomial.C hscalar
  have hfold := map_factorFold T r.factors.toList
    (DensePoly.C (Arithmetic.Coeff.ofData T.levels.toList (coeffs r.scalar)))
    (DensePoly.C r.scalar) hinit
  have hproduct : Factor.factorProduct T.levels.toList (coeffs r.scalar)
      (r.factors.map fun factor =>
        (factor.1.toArray.map coeffs, factor.2)) =
        f.toArray.map coeffs :=
    of_decide_eq_true hcheck.1.1.2
  have hraw := congrArg (Factor.rawPoly T.levels.toList) hproduct
  simp only [Factor.factorProduct, rawPoly_polyCoords_public] at hraw
  have hmapped := congrArg
    (fun p => (HexPolyMathlib.toPolynomial p).map
      (coeffEquiv T).toRingHom) hraw
  have hrawFold :
      (r.factors.map fun factor =>
        (factor.1.toArray.map coeffs, factor.2)).foldl
          (fun product factor => product * Factor.polyPow
            (Factor.rawPoly T.levels.toList factor.1) factor.2)
          (DensePoly.C (Arithmetic.Coeff.ofData T.levels.toList
            (coeffs r.scalar))) =
        r.factors.toList.foldl (fun product factor =>
          product * Factor.polyPow
            (Factor.rawPoly T.levels.toList
              (factor.1.toArray.map coeffs)) factor.2)
          (DensePoly.C (Arithmetic.Coeff.ofData T.levels.toList
            (coeffs r.scalar))) := by
    rw [← Array.foldl_toList]
    simp only [Array.toList_map, List.foldl_map]
  have hreconstruct : r.reconstruct = f := by
    apply HexPolyMathlib.equiv.injective
    change HexPolyMathlib.toPolynomial r.reconstruct =
      HexPolyMathlib.toPolynomial f
    rw [Factorization.reconstruct, ← Array.foldl_toList]
    rw [← map_rawPoly T f, ← hmapped]
    rw [hrawFold]
    exact hfold.symm
  refine ⟨hreconstruct, ?_, hcheck.1.2⟩
  intro factor hfactor
  have hall := hcheck.2
  rw [Array.all_eq_true] at hall
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hfactor
  have hi' : i < r.factors.size := by simpa using hi
  have hentry := hall i (by simpa using hi')
  have hget' : r.factors[i] = factor := by simpa using hget
  simp only [Array.getElem_map, hget'] at hentry
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hentry
  have hirreducible := (isIrreducible_iff T factor.1).mp hentry.2
  exact ⟨hirreducible.1, hentry.1, hirreducible.2⟩

/-- Recursive Trager factorization succeeds for every tower polynomial. -/
theorem factor?_isSome (T : NumberTower) (f : Poly T) :
    (T.factor? f).isSome := by
  let input := f.toArray.map coeffs
  have hrawSome := factorRaw_isSome T.levels.toList T.valid
    (coeffDenote_injective T) input
  obtain ⟨raw, hraw⟩ := Option.isSome_iff_exists.mp hrawSome
  have hrawCheck := factorRaw_check T.levels.toList T.valid
    (coeffDenote_injective T) input
    (by simpa only [input] using polyCoords_rawPoly T f) hraw
  have hparts := hrawCheck
  simp only [Factor.check, Bool.and_eq_true] at hparts
  have hcoordinate := hparts.1.1.1
  rw [Array.all_eq_true_iff_forall_mem] at hcoordinate
  have hfactors :
      (raw.factors.map fun factor =>
        ((DensePoly.ofCoeffs
          (factor.1.map (ofCoeffs T))).toArray.map coeffs,
          factor.2)) = raw.factors := by
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp only [Array.getElem_map]
      apply Prod.ext
      · apply publicCoords_of_canonical T
        exact of_decide_eq_true
          (hcoordinate raw.factors[i] (Array.getElem_mem hi₂))
      · rfl
  have hrawScalar : raw.scalar =
      (Factor.rawPoly T.levels.toList input).leadingCoeff.data := by
    have hraw' := hraw
    simp only [Factor.factorRaw?] at hraw'
    split at hraw'
    · obtain ⟨factors, _, hresult⟩ :=
        Option.bind_eq_some_iff.mp hraw'
      simpa using (congrArg Factor.RawFactorization.scalar
        (Option.some.inj hresult)).symm
    · contradiction
  have hscalar : normalizeCoeffs T raw.scalar = raw.scalar := by
    rw [hrawScalar]
    apply normalizeCoeffs_eq_self
    simpa [dim] using
      (Factor.rawPoly T.levels.toList input).leadingCoeff.size_eq
  have hpublicCheck : checkFactorization f (ofCoeffs T raw.scalar)
      (raw.factors.map fun factor =>
        (DensePoly.ofCoeffs (factor.1.map (ofCoeffs T)), factor.2)) = true := by
    simp only [checkFactorization, coeffs_ofCoeffs, Array.map_map]
    change Factor.check T.levels.toList input
      (normalizeCoeffs T raw.scalar)
      (raw.factors.map fun factor =>
        ((DensePoly.ofCoeffs
          (factor.1.map (ofCoeffs T))).toArray.map coeffs,
          factor.2)) = true
    rw [hscalar, hfactors]
    exact hrawCheck
  unfold NumberTower.factor?
  rw [hraw]
  simp [hpublicCheck]

end Hex.NumberTower
