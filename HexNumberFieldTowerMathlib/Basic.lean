/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower
public import HexNumberFieldMathlib

public section

/-!
# Semantic interpretation of validated number towers

The executable evaluator recursively substitutes each level's selected
absolute root.  This module turns its successful result into a complex-valued
semantic map and states the completeness, injectivity, and level-invariant
obligations needed before law-bearing field structures are installed.
-/

namespace Hex.NumberTower

/-- Checked semantic evaluation of a tower element through all stored fixed
embeddings. -/
@[expose]
noncomputable def eval? (T : NumberTower) (a : Elem T) : Option ℂ :=
  (RawEvaluation.evalCoords? T.levels.toList (coeffs a)).map
    AlgebraicRoot.toComplex

private theorem list_mapM_isSome {A B : Type*} (items : List A)
    (f : A → Option B) (h : ∀ item ∈ items, (f item).isSome) :
    (items.mapM f).isSome := by
  induction items with
  | nil => simp
  | cons item items ih =>
      obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp
        (h item (by simp))
      obtain ⟨values, hvalues⟩ := Option.isSome_iff_exists.mp
        (ih (fun tail htail => h tail (by simp [htail])))
      simp [List.mapM_cons, hvalue, hvalues]

private theorem list_foldlM_isSome {A B : Type*} (items : List A)
    (init : B) (step : B → A → Option B)
    (h : ∀ state item, item ∈ items → (step state item).isSome) :
    (items.foldlM step init).isSome := by
  induction items generalizing init with
  | nil => simp
  | cons item items ih =>
      obtain ⟨next, hnext⟩ := Option.isSome_iff_exists.mp
        (h init item (by simp))
      rw [List.foldlM_cons, hnext]
      exact ih next fun state tail htail => h state tail (by simp [htail])

/-- Raw coordinate evaluation is total at every tower depth. -/
theorem evalCoords_isSome (levels : List Level) (data : Array Rat) :
    (RawEvaluation.evalCoords? levels data).isSome := by
  induction levels generalizing data with
  | nil =>
      simp only [RawEvaluation.evalCoords?]
      obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp
        (AlgebraicPoly.Common.rational?_isSome (data.getD 0 0))
      rw [hvalue]
      simp
  | cons level lower ih =>
      simp only [RawEvaluation.evalCoords?]
      have hcoefficients := list_mapM_isSome (List.range level.degree)
        (fun i => RawEvaluation.evalCoords? lower
          (Arithmetic.block data i (levelsDim lower)))
        (fun i _ => ih (Arithmetic.block data i (levelsDim lower)))
      obtain ⟨coefficients, hcoefficients⟩ :=
        Option.isSome_iff_exists.mp hcoefficients
      rw [hcoefficients]
      exact list_foldlM_isSome coefficients.reverse
        AlgebraicNumber.zero.toRoot
        (fun value coefficient => do
          let product ← value.mul? level.root
          product.add? coefficient)
        (by
          intro value coefficient _
          obtain ⟨product, hproduct⟩ := Option.isSome_iff_exists.mp
            (AlgebraicRoot.mul?_isSome value level.root)
          rw [hproduct]
          exact AlgebraicRoot.add?_isSome product coefficient)

/-- Exact raw tower-polynomial evaluation is total. -/
theorem evalPoly_isSome (levels : List Level) (f : Array (Array Rat))
    (candidate : AlgebraicRoot) :
    (RawEvaluation.evalPoly? levels f candidate).isSome := by
  unfold RawEvaluation.evalPoly?
  apply list_foldlM_isSome f.reverse.toList
  intro state coefficient _
  obtain ⟨product, hproduct⟩ := Option.isSome_iff_exists.mp
    (AlgebraicRoot.mul?_isSome state candidate)
  rw [hproduct]
  obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp
    (evalCoords_isSome levels coefficient)
  rw [hvalue]
  exact AlgebraicRoot.add?_isSome product value

/-- The raw certified-ball evaluator returns a ball at every precision. -/
theorem evalBall_isSome (levels : List Level) (f : Array (Array Rat))
    (candidate : AlgebraicRoot) (prec : Nat) :
    (RawEvaluation.evalBall? levels f candidate prec).isSome := by
  obtain ⟨candidate', hrefine⟩ := Option.isSome_iff_exists.mp
    (RefinedIsolation.refineTo?_isSome candidate.rep ((prec : Int) + 1))
  rw [RawEvaluation.evalBall?, hrefine]
  have hballs : (f.mapM fun coefficient => do
      let value ← RawEvaluation.evalCoords? levels coefficient
      let refined ← value.rep.refineTo? ((prec : Int) + 1)
      some refined.1.1.square.toBall).isSome := by
    apply HexRootsMathlib.array_mapM_isSome
    intro coefficient _
    obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp
      (evalCoords_isSome levels coefficient)
    rw [hvalue]
    obtain ⟨refined, hrefined⟩ := Option.isSome_iff_exists.mp
      (RefinedIsolation.refineTo?_isSome value.rep ((prec : Int) + 1))
    simp [hrefined]
  obtain ⟨balls, hballs⟩ := Option.isSome_iff_exists.mp hballs
  rw [hballs]
  cases hback : balls.back? <;> simp [hback]

/-- Every validated tower element can be evaluated in the stored embedding. -/
theorem eval?_isSome (T : NumberTower) (a : Elem T) :
    (T.eval? a).isSome := by
  obtain ⟨root, hroot⟩ := Option.isSome_iff_exists.mp
    (evalCoords_isSome T.levels.toList (coeffs a))
  simp [eval?, hroot]

/-- A successful recursive evaluation has the value of the returned lazy
algebraic root. -/
theorem eval?_eq (T : NumberTower) (a : Elem T) {root : AlgebraicRoot}
    (h : RawEvaluation.evalCoords? T.levels.toList (coeffs a) = some root) :
    T.eval? a = some root.toComplex := by
  simp [eval?, h]

/-- The complex value of a tower element. The fallback is unreachable by
{name}`Hex.NumberTower.eval?_isSome`. -/
@[expose]
noncomputable def toComplex (T : NumberTower) (a : Elem T) : ℂ :=
  (T.eval? a).getD 0

/-- A successful executable evaluation computes `toComplex`. -/
theorem toComplex_eq (T : NumberTower) (a : Elem T)
    {root : AlgebraicRoot}
    (h : RawEvaluation.evalCoords? T.levels.toList (coeffs a) = some root) :
    T.toComplex a = root.toComplex := by
  simp [toComplex, eval?_eq T a h]

/-- Every structurally valid level list has positive mixed-radix dimension. -/
theorem levelsDim_pos (levels : List Level)
    (hvalid : LevelsValid levels) : 0 < levelsDim levels := by
  induction levels with
  | nil => simp [levelsDim]
  | cons level lower ih =>
      exact Nat.mul_pos (Nat.zero_lt_of_lt hvalid.1.1) (ih hvalid.2.2)

/-- Every validated tower has positive dimension. -/
theorem dim_pos (T : NumberTower) : 0 < T.dim := by
  exact levelsDim_pos T.levels.toList T.valid

namespace LevelSemantics

/-- Direct complex Horner interpretation of raw mixed-radix coordinates. -/
@[expose]
noncomputable def denote : (levels : List Level) → Array Rat → ℂ
  | [], data => (data.getD 0 0 : ℂ)
  | level :: lower, data =>
      let lowerDim := levelsDim lower
      let coefficients := (List.range level.degree).map fun i =>
        denote lower (Arithmetic.block data i lowerDim)
      coefficients.reverse.foldl
        (fun value coefficient =>
          value * level.root.toComplex + coefficient)
        0

/-- Interpret a raw polynomial over a lower tower in `Polynomial ℂ`. -/
@[expose]
noncomputable def polynomial (lower : List Level)
    (f : Array (Array Rat)) : Polynomial ℂ :=
  ∑ i ∈ Finset.range f.size,
    Polynomial.monomial i (denote lower (f.getD i #[]))

private theorem horner_eq_sum (x : ℂ) (coefficients : List ℂ) :
    coefficients.reverse.foldl
        (fun value coefficient => value * x + coefficient) 0 =
      ∑ i ∈ Finset.range coefficients.length,
        coefficients.getD i 0 * x ^ i := by
  induction coefficients with
  | nil => simp
  | cons coefficient coefficients ih =>
      rw [List.reverse_cons, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, List.length_cons]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_zero, pow_zero, mul_one,
        List.getD_cons_succ, pow_succ]
      rw [Finset.sum_mul]
      calc
        _ = coefficient + ∑ i ∈ Finset.range coefficients.length,
              coefficients.getD i 0 * x ^ i * x := add_comm _ _
        _ = coefficient + ∑ i ∈ Finset.range coefficients.length,
              x * x ^ i * coefficients.getD i 0 := by
            apply congrArg (coefficient + ·)
            apply Finset.sum_congr rfl
            intro i hi
            ring
        _ = (∑ i ∈ Finset.range coefficients.length,
              x * x ^ i * coefficients.getD i 0) + coefficient := add_comm _ _
        _ = (∑ i ∈ Finset.range coefficients.length,
              coefficients.getD i 0 * (x ^ i * x)) + coefficient := by
            apply congrArg (· + coefficient)
            apply Finset.sum_congr rfl
            intro i hi
            ring

/-- The raw polynomial interpretation evaluates by ordinary Horner folding. -/
theorem polynomial_eval_horner (levels : List Level)
    (f : Array (Array Rat)) (x : ℂ) :
    (polynomial levels f).eval x = f.toList.foldr
      (fun coefficient value =>
        value * x + denote levels coefficient) 0 := by
  rw [List.foldr_eq_foldl_reverse]
  rw [← List.foldl_map]
  rw [List.map_reverse]
  symm
  rw [horner_eq_sum]
  unfold polynomial
  rw [Polynomial.eval_finsetSum]
  simp only [List.length_map, Array.length_toList]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < f.size := Finset.mem_range.mp hi
  simp [Polynomial.eval_monomial, Array.getD, hi']

/-- Recursive Horner denotation is the finite power sum of its top-level
coefficient blocks. -/
theorem denote_cons (level : Level) (lower : List Level) (data : Array Rat) :
    denote (level :: lower) data =
      ∑ i ∈ Finset.range level.degree,
        denote lower (Arithmetic.block data i (levelsDim lower)) *
          level.root.toComplex ^ i := by
  rw [denote]
  let coefficients := (List.range level.degree).map fun i =>
    denote lower (Arithmetic.block data i (levelsDim lower))
  rw [horner_eq_sum]
  simp only [List.length_map, List.length_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < level.degree := Finset.mem_range.mp hi
  simp [hi']

private theorem block_singleton_zero (q : Rat) (width : Nat) :
    Arithmetic.block #[q] 0 width =
      Arithmetic.fixedCoeffs width #[q] := by
  unfold Arithmetic.block Arithmetic.fixedCoeffs
  congr 1
  apply Vector.ext
  intro i hi
  simp

private theorem block_singleton_succ (q : Rat) (index width : Nat)
    (hwidth : 0 < width) :
    Arithmetic.block #[q] (index + 1) width =
      Arithmetic.fixedCoeffs width #[] := by
  unfold Arithmetic.block Arithmetic.fixedCoeffs
  congr 1
  apply Vector.ext
  intro i hi
  simp [Array.getD, hwidth.ne']

private theorem foldl_add {ι : Type} (x : ℂ) (indices : List ι)
    (f g : ι → ℂ) (a b : ℂ) :
    (indices.map fun i => f i + g i).foldl
        (fun value coefficient => value * x + coefficient) (a + b) =
      (indices.map f).foldl
          (fun value coefficient => value * x + coefficient) a +
        (indices.map g).foldl
          (fun value coefficient => value * x + coefficient) b := by
  induction indices generalizing a b with
  | nil => rfl
  | cons i indices ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [show (a + b) * x + (f i + g i) =
          (a * x + f i) + (b * x + g i) by ring]
      exact ih (a * x + f i) (b * x + g i)

/-- Direct tower denotation is additive on fixed-width coordinates. -/
theorem denote_add (levels : List Level) (a b : Array Rat) :
    denote levels (Arithmetic.addCoords (levelsDim levels) a b) =
      denote levels a + denote levels b := by
  induction levels generalizing a b with
  | nil =>
      simp [denote, Arithmetic.addCoords, levelsDim, Array.getD]
  | cons level lower ih =>
      simp only [denote, levelsDim]
      have hcoeff :
          (List.range level.degree).map (fun i =>
              denote lower (Arithmetic.block
                (Arithmetic.addCoords (level.degree * levelsDim lower) a b)
                i (levelsDim lower))) =
            (List.range level.degree).map (fun i =>
              denote lower (Arithmetic.block a i (levelsDim lower)) +
                denote lower (Arithmetic.block b i (levelsDim lower))) := by
        apply List.map_congr_left
        intro i hi
        rw [Arithmetic.block_add level.degree (levelsDim lower) i a b
          (List.mem_range.mp hi), ih]
      rw [hcoeff]
      simpa only [← List.map_reverse, zero_add] using
        foldl_add level.root.toComplex (List.range level.degree).reverse
          (fun i => denote lower (Arithmetic.block a i (levelsDim lower)))
          (fun i => denote lower (Arithmetic.block b i (levelsDim lower))) 0 0

/-- Direct tower denotation only observes the canonical mixed-radix width. -/
theorem denote_fixed (levels : List Level) (data : Array Rat) :
    denote levels (Arithmetic.fixedCoeffs (levelsDim levels) data) =
      denote levels data := by
  induction levels generalizing data with
  | nil =>
      simp [denote, Arithmetic.fixedCoeffs, levelsDim, Array.getD]
  | cons level lower ih =>
      simp only [denote, levelsDim]
      congr 1
      apply congrArg List.reverse
      apply List.map_congr_left
      intro i hi
      rw [Arithmetic.block_fixed level.degree (levelsDim lower) i data
        (List.mem_range.mp hi), ih]

private theorem denote_empty (levels : List Level) : denote levels #[] = 0 := by
  induction levels with
  | nil => simp [denote, Array.getD]
  | cons level lower ih =>
      rw [denote_cons]
      apply Finset.sum_eq_zero
      intro i hi
      have hblock : Arithmetic.block #[] i (levelsDim lower) =
          Arithmetic.fixedCoeffs (levelsDim lower) #[] := by
        apply Array.ext
        · simp [Arithmetic.block, Arithmetic.fixedCoeffs]
        · intro j hj₁ hj₂
          simp [Arithmetic.block, Arithmetic.fixedCoeffs, Array.getD]
      rw [hblock, denote_fixed, ih]
      simp

private theorem denote_singleton (levels : List Level)
    (hvalid : LevelsValid levels) (q : Rat) :
    denote levels #[q] = (q : ℂ) := by
  induction levels with
  | nil => simp [denote, Array.getD]
  | cons level lower ih =>
      have hlowerDim : 0 < levelsDim lower := levelsDim_pos lower hvalid.2.2
      rw [denote_cons]
      rw [Finset.sum_eq_single 0]
      · rw [block_singleton_zero, denote_fixed, ih hvalid.2.2]
        simp
      · intro i hi hi0
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        rw [block_singleton_succ q j (levelsDim lower) hlowerDim,
          denote_fixed, denote_empty]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr
          (Nat.zero_lt_of_lt hvalid.1.1))).elim

/-- Direct tower denotation is subtractive on fixed-width coordinates. -/
theorem denote_sub (levels : List Level) (a b : Array Rat) :
    denote levels (Arithmetic.subCoords (levelsDim levels) a b) =
      denote levels a - denote levels b := by
  have h := denote_add levels
    (Arithmetic.subCoords (levelsDim levels) a b) b
  rw [Arithmetic.add_subCoords, denote_fixed] at h
  exact eq_sub_of_add_eq h.symm

private theorem foldlM_sound (x : AlgebraicRoot)
    (coefficients : List AlgebraicRoot) (acc : AlgebraicRoot)
    {out : AlgebraicRoot}
    (h : coefficients.foldlM
      (fun value coefficient => do
        let product ← value.mul? x
        product.add? coefficient) acc = some out) :
    out.toComplex =
      (coefficients.map AlgebraicRoot.toComplex).foldl
        (fun value coefficient => value * x.toComplex + coefficient)
        acc.toComplex := by
  induction coefficients generalizing acc out with
  | nil =>
      have hout : acc = out := by simpa using h
      cases hout
      rfl
  | cons coefficient coefficients ih =>
      simp only [List.foldlM_cons] at h
      cases hproduct : acc.mul? x with
      | none => simp [hproduct] at h
      | some product =>
          cases hsum : product.add? coefficient with
          | none => simp [hproduct, hsum] at h
          | some next =>
              have htail :
                  coefficients.foldlM
                    (fun value coefficient => do
                      let product ← value.mul? x
                      product.add? coefficient) next = some out := by
                simpa [hproduct, hsum] using h
              rw [ih next htail]
              simp only [List.map_cons, List.foldl_cons]
              rw [AlgebraicRoot.add?_sound product coefficient hsum,
                AlgebraicRoot.mul?_sound acc x hproduct]

private theorem mapM_sound {ι : Type} (indices : List ι)
    (f : ι → Option AlgebraicRoot) (g : ι → ℂ)
    (hsound : ∀ i root, f i = some root → root.toComplex = g i)
    {roots : List AlgebraicRoot} (h : indices.mapM f = some roots) :
    roots.map AlgebraicRoot.toComplex = indices.map g := by
  induction indices generalizing roots with
  | nil =>
      have hroots : roots = [] := by simpa using h.symm
      subst roots
      rfl
  | cons i indices ih =>
      cases hi : f i with
      | none => simp [List.mapM_cons, hi] at h
      | some root =>
          cases htail : indices.mapM f with
          | none => simp [List.mapM_cons, hi, htail] at h
          | some tail =>
              have hroots : roots = root :: tail := by
                simpa [List.mapM_cons, hi, htail] using h.symm
              subst roots
              simp only [List.map_cons, List.cons.injEq]
              exact ⟨hsound i root hi, ih htail⟩

/-- Successful raw evaluation agrees with direct complex Horner denotation. -/
theorem evalCoords_sound (levels : List Level) (data : Array Rat)
    {root : AlgebraicRoot}
    (h : RawEvaluation.evalCoords? levels data = some root) :
    root.toComplex = denote levels data := by
  induction levels generalizing data root with
  | nil =>
      let q := data.getD 0 0
      simp only [RawEvaluation.evalCoords?] at h
      obtain ⟨value, hvalue, hroot⟩ := Option.bind_eq_some_iff.mp h
      have hroot' : value.toRoot = root := Option.some.inj hroot
      subst root
      rw [AlgebraicNumber.toRoot_toComplex,
        AlgebraicPoly.Common.rational?_sound q hvalue]
      rfl
  | cons level lower ih =>
      simp only [RawEvaluation.evalCoords?] at h
      obtain ⟨roots, hroots, hfold⟩ := Option.bind_eq_some_iff.mp h
      have hsem :
          roots.map AlgebraicRoot.toComplex =
            (List.range level.degree).map (fun i =>
              denote lower
                (Arithmetic.block data i (levelsDim lower))) := by
        apply mapM_sound (List.range level.degree)
          (fun i => RawEvaluation.evalCoords? lower
            (Arithmetic.block data i (levelsDim lower)))
        intro i coefficient hi
        exact ih _ hi
        exact hroots
      rw [foldlM_sound level.root roots.reverse
        AlgebraicNumber.zero.toRoot hfold]
      rw [List.map_reverse, hsem]
      have hzero : AlgebraicNumber.zero.toRoot.toComplex = 0 := by
        rw [AlgebraicNumber.toRoot_toComplex]
        exact AlgebraicNumber.zero_toComplex
      rw [hzero]
      rfl

private theorem evalPolyFold_sound (levels : List Level)
    (candidate : AlgebraicRoot) (coefficients : List (Array Rat))
    (acc : AlgebraicRoot) {out : AlgebraicRoot}
    (h : coefficients.foldlM
      (fun value coefficient => do
        let product ← value.mul? candidate
        let coefficientValue ← RawEvaluation.evalCoords? levels coefficient
        product.add? coefficientValue) acc = some out) :
    out.toComplex = coefficients.foldl
      (fun value coefficient =>
        value * candidate.toComplex + LevelSemantics.denote levels coefficient)
      acc.toComplex := by
  induction coefficients generalizing acc out with
  | nil =>
      have hout : acc = out := by simpa using h
      cases hout
      rfl
  | cons coefficient coefficients ih =>
      simp only [List.foldlM_cons] at h
      cases hproduct : acc.mul? candidate with
      | none => simp [hproduct] at h
      | some product =>
          cases hcoefficient : RawEvaluation.evalCoords? levels coefficient with
          | none => simp [hproduct, hcoefficient] at h
          | some coefficientValue =>
              cases hnext : product.add? coefficientValue with
              | none => simp [hproduct, hcoefficient, hnext] at h
              | some next =>
                  have htail : coefficients.foldlM
                      (fun value coefficient => do
                        let product ← value.mul? candidate
                        let coefficientValue ←
                          RawEvaluation.evalCoords? levels coefficient
                        product.add? coefficientValue) next = some out := by
                    simpa [hproduct, hcoefficient, hnext] using h
                  rw [ih next htail]
                  simp only [List.foldl_cons]
                  rw [AlgebraicRoot.add?_sound product coefficientValue hnext,
                    AlgebraicRoot.mul?_sound acc candidate hproduct,
                    LevelSemantics.evalCoords_sound levels coefficient
                      hcoefficient]

/-- Successful exact evaluation of a raw tower polynomial agrees with its
direct complex polynomial interpretation. -/
theorem evalPoly_sound (levels : List Level) (f : Array (Array Rat))
    (candidate result : AlgebraicRoot)
    (h : RawEvaluation.evalPoly? levels f candidate = some result) :
    result.toComplex = (polynomial levels f).eval candidate.toComplex := by
  unfold RawEvaluation.evalPoly? at h
  rw [evalPolyFold_sound levels candidate f.reverse.toList
    AlgebraicNumber.zero.toRoot h]
  have hzero : AlgebraicNumber.zero.toRoot.toComplex = 0 := by
    rw [AlgebraicNumber.toRoot_toComplex]
    exact AlgebraicNumber.zero_toComplex
  rw [hzero]
  rw [show f.reverse.toList = f.toList.reverse by simp]
  rw [← List.foldl_map, List.map_reverse]
  rw [LevelSemantics.horner_eq_sum]
  unfold polynomial
  rw [Polynomial.eval_finsetSum]
  simp only [List.length_map, Array.length_toList]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < f.size := Finset.mem_range.mp hi
  simp [Polynomial.eval_monomial, Array.getD, hi']

/-- The selected complex interpretation is the direct Horner denotation of
the element's mixed-radix coordinates. -/
theorem toComplex_eq_denote (T : NumberTower) (a : Elem T) :
    T.toComplex a = denote T.levels.toList (coeffs a) := by
  cases h : RawEvaluation.evalCoords? T.levels.toList (coeffs a) with
  | none =>
      have hsome := eval?_isSome T a
      simp [eval?, h] at hsome
  | some root =>
      rw [NumberTower.toComplex_eq T a h, evalCoords_sound _ _ h]

/-- The rational tower embedding has its expected complex value. -/
theorem toComplex_ofRat (T : NumberTower) (q : Rat) :
    T.toComplex (T.ofRat q) = (q : ℂ) := by
  rw [toComplex_eq_denote, ofRat_eq_ofCoeffs, coeffs_ofCoeffs]
  change LevelSemantics.denote T.levels.toList
      (Arithmetic.fixedCoeffs (levelsDim T.levels.toList) #[q]) = (q : ℂ)
  rw [LevelSemantics.denote_fixed,
    LevelSemantics.denote_singleton T.levels.toList T.valid q]

private theorem polynomial_nil (f : Array (Array Rat)) :
    polynomial [] f =
      (HexPolyMathlib.toPolynomial (Factor.toRatPoly f)).map
        (algebraMap Rat ℂ) := by
  ext n
  simp [polynomial, Factor.toRatPoly, denote, Array.getD]
  by_cases hn : n < f.size
  · rw [Finset.sum_eq_single n]
    · simp [hn]
    · intro b hb hbn
      simp [Polynomial.coeff_monomial, hbn]
    · simp [hn]
  · rw [Finset.sum_eq_zero]
    · norm_num [hn]
    · intro b hb
      have hbn : b ≠ n := by
        intro h
        subst b
        exact hn (Finset.mem_range.mp hb)
      simp [Polynomial.coeff_monomial, hbn]

end LevelSemantics

/-- The rational embedding has its expected value in every validated tower. -/
theorem toComplex_ofRat (T : NumberTower) (q : Rat) :
    T.toComplex (T.ofRat q) = (q : ℂ) :=
  LevelSemantics.toComplex_ofRat T q

private theorem norm_horner_le_of_bound {A : Type*} (coefficients : List A)
    (value : A → ℂ) (bound : A → Nat) (z : ℂ) (rootBound : Nat)
    (hz : ‖z‖ ≤ rootBound)
    (hcoeff : ∀ coefficient ∈ coefficients,
      ‖value coefficient‖ ≤ bound coefficient) :
    ‖coefficients.foldr
        (fun coefficient acc => acc * z + value coefficient) 0‖ ≤
      (coefficients.foldr
        (fun coefficient acc => acc * rootBound + bound coefficient) 0 : Nat) := by
  induction coefficients with
  | nil => simp
  | cons coefficient coefficients ih =>
      simp only [List.foldr_cons]
      have hproduct :
          ‖coefficients.foldr
              (fun coefficient acc => acc * z + value coefficient) 0‖ * ‖z‖ ≤
            (coefficients.foldr
              (fun coefficient acc =>
                acc * rootBound + bound coefficient) 0 : Nat) *
              (rootBound : ℝ) := by
        exact mul_le_mul
          (ih fun tail htail => hcoeff tail (by simp [htail])) hz
          (norm_nonneg _) (by positivity)
      calc
        ‖coefficients.foldr
              (fun coefficient acc => acc * z + value coefficient) 0 * z +
            value coefficient‖ ≤
            ‖coefficients.foldr
                (fun coefficient acc => acc * z + value coefficient) 0 * z‖ +
              ‖value coefficient‖ := norm_add_le _ _
        _ = ‖coefficients.foldr
              (fun coefficient acc => acc * z + value coefficient) 0‖ * ‖z‖ +
              ‖value coefficient‖ := by rw [norm_mul]
        _ ≤ (coefficients.foldr
              (fun coefficient acc =>
                acc * rootBound + bound coefficient) 0 : Nat) *
              (rootBound : ℝ) + bound coefficient :=
          add_le_add hproduct (hcoeff coefficient (by simp))
        _ = (coefficients.foldr
              (fun coefficient acc =>
                acc * rootBound + bound coefficient) 0 * rootBound +
              bound coefficient : Nat) := by norm_num

/-- The recursive integer coordinate majorant bounds the selected complex
value of any raw tower coordinate array. -/
theorem LevelSemantics.norm_denote_le_coordsMajorant :
    ∀ (levels : List Level) (data : Array Rat),
      ‖LevelSemantics.denote levels data‖ ≤
        RawEvaluation.coordsMajorant levels data
  | [], data => by
      simpa [LevelSemantics.denote, RawEvaluation.coordsMajorant] using
        PolyQuot.norm_rat_le_ratAbsCeil (data.getD 0 0)
  | level :: lower, data => by
      let indices := List.range level.degree
      let rootBound := 2 ^ cauchyExp level.root.p + 1
      have hz : ‖level.root.toComplex‖ ≤ rootBound :=
        (AlgebraicRoot.norm_lt_rootBound level.root).le
      have hbound : ∀ i ∈ indices,
          ‖LevelSemantics.denote lower
              (Arithmetic.block data i (levelsDim lower))‖ ≤
            RawEvaluation.coordsMajorant lower
              (Arithmetic.block data i (levelsDim lower)) := by
        intro i _
        exact LevelSemantics.norm_denote_le_coordsMajorant lower _
      have hhorner := norm_horner_le_of_bound indices
        (fun i => LevelSemantics.denote lower
          (Arithmetic.block data i (levelsDim lower)))
        (fun i => RawEvaluation.coordsMajorant lower
          (Arithmetic.block data i (levelsDim lower)))
        level.root.toComplex rootBound hz hbound
      simp only [LevelSemantics.denote, RawEvaluation.coordsMajorant]
      rw [show
        ((List.range level.degree).map fun i =>
            LevelSemantics.denote lower
              (Arithmetic.block data i (levelsDim lower))).reverse.foldl
            (fun value coefficient =>
              value * level.root.toComplex + coefficient) 0 =
          (List.range level.degree).reverse.foldl
            (fun value i => value * level.root.toComplex +
              LevelSemantics.denote lower
                (Arithmetic.block data i (levelsDim lower))) 0 by
        rw [← List.map_reverse, List.foldl_map]]
      simpa only [indices, rootBound, List.foldr_eq_foldl_reverse] using hhorner

private theorem getD_push_lt {A : Type*} (xs : Array A) (x fallback : A)
    (i : Nat) (hi : i < xs.size) :
    (xs.push x).getD i fallback = xs.getD i fallback := by
  have hi' : i < (xs.push x).size := by simp; omega
  rw [← Array.getElem_eq_getD fallback (h := hi'),
    Array.getElem_push_lt hi, Array.getElem_eq_getD fallback]

private theorem getD_push_eq {A : Type*} (xs : Array A) (x fallback : A) :
    (xs.push x).getD xs.size fallback = x := by
  have hi : xs.size < (xs.push x).size := by simp
  rw [← Array.getElem_eq_getD fallback (h := hi),
    Array.getElem_push_eq]

private theorem hornerBalls_mem (levels : List Level)
    (coefficients : List (Array Rat)) (balls : List DyadicComplexBall)
    (candidate : ℂ) (candidateBall initBall : DyadicComplexBall)
    (init : ℂ)
    (hcoefficients : List.Forall₂
      (fun coefficient ball =>
        LevelSemantics.denote levels coefficient ∈ ball.set)
      coefficients balls)
    (hcandidate : candidate ∈ candidateBall.set)
    (hinit : init ∈ initBall.set) :
    coefficients.foldr
        (fun coefficient value =>
          value * candidate + LevelSemantics.denote levels coefficient) init ∈
      (balls.foldr
        (fun coefficient value => coefficient.add (candidateBall.mul value))
        initBall).set := by
  induction hcoefficients with
  | nil => exact hinit
  | cons hcoefficient _ ih =>
      simpa only [List.foldr_cons, add_comm, mul_comm] using
        DyadicComplexBall.add_mem hcoefficient
          (DyadicComplexBall.mul_mem hcandidate ih)

private theorem rawHornerBall_bounds (levels : List Level)
    (coefficients : List (Array Rat)) (balls : List DyadicComplexBall)
    (candidate : ℂ) (candidateBall : DyadicComplexBall) (prec : Nat)
    (rootBound : Nat) (init : ℂ) (initBall : DyadicComplexBall)
    (initState : Nat × Nat)
    (hcoefficients : List.Forall₂
      (fun coefficient ball =>
        LevelSemantics.denote levels coefficient ∈ ball.set ∧
          ‖LevelSemantics.denote levels coefficient‖ ≤
            RawEvaluation.coordsMajorant levels coefficient ∧
          ball.realRadius ≤
            (2 : ℝ) ^ (-(prec : Int)))
      coefficients balls)
    (hcandidate : candidate ∈ candidateBall.set)
    (hcandidateNorm : ‖candidate‖ ≤ rootBound)
    (hcandidateRadius : candidateBall.realRadius ≤
      (3 / 4 : ℝ) * (2 : ℝ) ^ (-(prec : Int)))
    (hinit : init ∈ initBall.set)
    (hinitNorm : ‖init‖ ≤ initState.1)
    (hinitRadius : initBall.realRadius ≤
      (initState.2 : ℝ) * (2 : ℝ) ^ (-(prec : Int))) :
    let state := coefficients.foldr
      (fun coefficient state =>
        (state.1 * rootBound +
            RawEvaluation.coordsMajorant levels coefficient,
          2 * state.1 + 2 * rootBound * state.2 + 3 * state.2 + 1))
      initState
    let value := coefficients.foldr
      (fun coefficient value =>
        LevelSemantics.denote levels coefficient + candidate * value) init
    let ball := balls.foldr
      (fun coefficient value =>
        coefficient.add (candidateBall.mul value)) initBall
    value ∈ ball.set ∧ ‖value‖ ≤ state.1 ∧
      ball.realRadius ≤
        (state.2 : ℝ) * (2 : ℝ) ^ (-(prec : Int)) := by
  induction hcoefficients with
  | nil => exact ⟨hinit, hinitNorm, hinitRadius⟩
  | cons hcoefficient htail ih =>
      rename_i coefficient coefficientBall coefficients balls
      simp only [List.foldr_cons]
      obtain ⟨hvalue, hvalueNorm, hvalueRadius⟩ := ih
      let state := coefficients.foldr
        (fun coefficient state =>
          (state.1 * rootBound +
              RawEvaluation.coordsMajorant levels coefficient,
            2 * state.1 + 2 * rootBound * state.2 + 3 * state.2 + 1))
        initState
      let value := coefficients.foldr
        (fun coefficient value =>
          LevelSemantics.denote levels coefficient + candidate * value) init
      let ball := balls.foldr
        (fun coefficient value =>
          coefficient.add (candidateBall.mul value)) initBall
      have hnorm :
          ‖LevelSemantics.denote levels coefficient + candidate * value‖ ≤
            (state.1 * rootBound +
              RawEvaluation.coordsMajorant levels coefficient : Nat) := by
        have hproduct : ‖candidate‖ * ‖value‖ ≤
            (rootBound : ℝ) * (state.1 : ℝ) := by
          exact mul_le_mul hcandidateNorm hvalueNorm (norm_nonneg _)
            (by positivity)
        calc
          ‖LevelSemantics.denote levels coefficient + candidate * value‖ ≤
              ‖LevelSemantics.denote levels coefficient‖ +
                ‖candidate * value‖ :=
            norm_add_le _ _
          _ = ‖LevelSemantics.denote levels coefficient‖ +
              ‖candidate‖ * ‖value‖ := by rw [norm_mul]
          _ ≤ (RawEvaluation.coordsMajorant levels coefficient : ℝ) +
              (rootBound : ℝ) * (state.1 : ℝ) :=
            add_le_add hcoefficient.2.1 hproduct
          _ = (state.1 * rootBound +
              RawEvaluation.coordsMajorant levels coefficient : Nat) := by
            norm_num
            ring
      refine ⟨?_, hnorm, ?_⟩
      · exact DyadicComplexBall.add_mem hcoefficient.1
          (DyadicComplexBall.mul_mem hcandidate hvalue)
      · have hradius := DyadicComplexBall.realRadius_horner_le
          candidateBall ball coefficientBall (rootBound : ℝ)
          (state.1 : ℝ)
          (state.2 : ℝ) ((2 : ℝ) ^ (-(prec : Int)))
          hcandidate hvalue hcoefficient.1 hcandidateNorm hvalueNorm
          hcandidateRadius hvalueRadius hcoefficient.2.2
          (by positivity) (by positivity) (by positivity) (by positivity)
          (by
            rw [← zpow_zero (2 : ℝ)]
            exact zpow_le_zpow_right₀ (by norm_num) (by omega))
        simpa only [state, ball, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat, Nat.cast_one] using hradius

/-- Certified ball evaluation encloses the exact raw tower-polynomial value. -/
theorem rawEvalBall_sound (levels : List Level) (f : Array (Array Rat))
    (candidate : AlgebraicRoot) (prec : Nat) {ball : DyadicComplexBall}
    (hrun : RawEvaluation.evalBall? levels f candidate prec = some ball) :
    (LevelSemantics.polynomial levels f).eval candidate.toComplex ∈ ball.set := by
  rw [RawEvaluation.evalBall?] at hrun
  obtain ⟨candidate', hrefine, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨balls, hballs, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  have hcandidateRoot : candidate'.1.root = candidate.toComplex := by
    calc
      candidate'.1.root = candidate.rep.root :=
        HexRootsMathlib.RefinedIsolation.refineTo_root candidate.rep
          ((prec : Int) + 1) .nkThenPellet hrefine
      _ = candidate.toComplex := rfl
  have hcandidate :
      candidate.toComplex ∈ candidate'.1.1.square.toBall.set := by
    rw [← hcandidateRoot]
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc candidate'.1)
  have hmap := HexRootsMathlib.array_mapM_some_get hballs
  have hentry : ∀ (i : Nat) (hi : i < f.size) (hj : i < balls.size),
      LevelSemantics.denote levels f[i] ∈ balls[i].set := by
    intro i hi hj
    have hstep := hmap.2 i hi hj
    obtain ⟨value, hvalue, hstep⟩ := Option.bind_eq_some_iff.mp hstep
    obtain ⟨refined, hrefined, hstep⟩ := Option.bind_eq_some_iff.mp hstep
    have hball : refined.1.1.square.toBall = balls[i] := Option.some.inj hstep
    have hroot : refined.1.root = value.toComplex := by
      calc
        refined.1.root = value.rep.root :=
          HexRootsMathlib.RefinedIsolation.refineTo_root value.rep
            ((prec : Int) + 1) .nkThenPellet hrefined
        _ = value.toComplex := rfl
    rw [← LevelSemantics.evalCoords_sound levels f[i] hvalue,
      ← hroot, ← hball]
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc refined.1)
  have hentryD : ∀ (i : Nat) (hi : i < f.size) (hj : i < balls.size),
      LevelSemantics.denote levels (f.getD i #[]) ∈
        (balls.getD i DyadicComplexBall.zero).set := by
    intro i hi hj
    rw [← Array.getElem_eq_getD #[] (h := hi),
      ← Array.getElem_eq_getD DyadicComplexBall.zero (h := hj)]
    exact hentry i hi hj
  cases hback : balls.back? with
  | none =>
      have hball : DyadicComplexBall.zero = ball := by
        apply Option.some.inj
        simpa [hback] using hrun
      subst ball
      have hballsEmpty : balls = #[] := Array.back?_eq_none_iff.mp hback
      have hfSize : f.size = 0 := by simpa [hballsEmpty] using hmap.1
      have hf : f = #[] := Array.size_eq_zero_iff.mp hfSize
      rw [hf, LevelSemantics.polynomial_eval_horner]
      simp [DyadicComplexBall.zero, DyadicComplexBall.set,
        DyadicComplexBall.center, DyadicComplexBall.realRadius]
  | some topBall =>
      cases hfback : f.back? with
      | none =>
          have hfEmpty : f = #[] := Array.back?_eq_none_iff.mp hfback
          have hballsEmpty : balls = #[] := by
            apply Array.size_eq_zero_iff.mp
            simpa [hfEmpty] using hmap.1.symm
          have : balls.back? = none := Array.back?_eq_none_iff.mpr hballsEmpty
          rw [this] at hback
          contradiction
      | some topCoefficient =>
          obtain ⟨ballPrefix, hballPrefix⟩ :=
            Array.back?_eq_some_iff.mp hback
          obtain ⟨coefficientPrefix, hcoefficientPrefix⟩ :=
            Array.back?_eq_some_iff.mp hfback
          have hprefixSize : coefficientPrefix.size = ballPrefix.size := by
            have hsize := hmap.1
            rw [hcoefficientPrefix, hballPrefix] at hsize
            simpa using hsize
          have htop : LevelSemantics.denote levels topCoefficient ∈
              topBall.set := by
            have hfBound : coefficientPrefix.size < f.size := by
              simp [hcoefficientPrefix]
            have hbBound : coefficientPrefix.size < balls.size := by
              simp [hballPrefix, hprefixSize]
            have h := hentryD coefficientPrefix.size hfBound hbBound
            rw [hcoefficientPrefix, getD_push_eq, hballPrefix,
              hprefixSize, getD_push_eq] at h
            exact h
          have hprefix : List.Forall₂
              (fun coefficient coefficientBall =>
                LevelSemantics.denote levels coefficient ∈
                  coefficientBall.set)
              coefficientPrefix.toList ballPrefix.toList := by
            rw [List.forall₂_iff_get]
            refine ⟨by simpa using hprefixSize, ?_⟩
            intro i hi hj
            have hi' : i < coefficientPrefix.size := by simpa using hi
            have hj' : i < ballPrefix.size := by simpa using hj
            have h := hentryD i (by
              rw [hcoefficientPrefix]
              simp
              exact Nat.le_of_lt hi') (by
              rw [hballPrefix]
              simp
              exact Nat.le_of_lt hj')
            rw [hcoefficientPrefix,
              getD_push_lt coefficientPrefix topCoefficient #[] i hi',
              hballPrefix,
              getD_push_lt ballPrefix topBall DyadicComplexBall.zero i hj'] at h
            rw [← Array.getElem_eq_getD #[] (h := hi'),
              ← Array.getElem_eq_getD DyadicComplexBall.zero (h := hj')] at h
            simpa [List.get_eq_getElem, ← Array.getElem_toList] using h
          have hfold : balls.foldr
              (fun coefficient value =>
                coefficient.add (candidate'.1.1.square.toBall.mul value))
              topBall (start := balls.size - 1) =
                ballPrefix.toList.foldr
                  (fun coefficient value =>
                    coefficient.add (candidate'.1.1.square.toBall.mul value))
                  topBall := by
            have hsize : balls.size - 1 = ballPrefix.size := by
              rw [hballPrefix]
              simp
            rw [hsize, Array.foldr_eq_foldr_extract]
            rw [hballPrefix,
              Array.extract_push_of_le (le_refl ballPrefix.size)]
            simp
          have hball : balls.foldr
              (fun coefficient value =>
                coefficient.add (candidate'.1.1.square.toBall.mul value))
              topBall (start := balls.size - 1) = ball := by
            apply Option.some.inj
            simpa [hback] using hrun
          subst ball
          rw [hfold, LevelSemantics.polynomial_eval_horner,
            hcoefficientPrefix, Array.toList_push, List.foldr_append]
          simp only [List.foldr_cons, List.foldr_nil, zero_mul, zero_add]
          exact hornerBalls_mem levels coefficientPrefix.toList
            ballPrefix.toList candidate.toComplex
            candidate'.1.1.square.toBall topBall
            (LevelSemantics.denote levels topCoefficient) hprefix hcandidate htop

/-- On canonical raw coordinates, the tower ball evaluator satisfies the
error recurrence used by the bounded zero test. -/
theorem rawEvalBall_radius (levels : List Level) (f : Array (Array Rat))
    (candidate : AlgebraicRoot)
    (hcanonical : Factor.polyCoords (Factor.rawPoly levels f) = f)
    (prec : Nat) {ball : DyadicComplexBall}
    (hrun : RawEvaluation.evalBall? levels f candidate prec = some ball) :
    ball.realRadius ≤
      (Disambiguation.evalMajorant (Factor.rawPoly levels f)
        (fun coefficient =>
          RawEvaluation.coordsMajorant levels coefficient.data)
        candidate.p : ℝ) * (2 : ℝ) ^ (-(prec : Int)) := by
  rw [RawEvaluation.evalBall?] at hrun
  obtain ⟨candidate', hrefine, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨balls, hballs, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  have hcandidateRoot : candidate'.1.root = candidate.toComplex := by
    calc
      candidate'.1.root = candidate.rep.root :=
        HexRootsMathlib.RefinedIsolation.refineTo_root candidate.rep
          ((prec : Int) + 1) .nkThenPellet hrefine
      _ = candidate.toComplex := rfl
  have hcandidate :
      candidate.toComplex ∈ candidate'.1.1.square.toBall.set := by
    rw [← hcandidateRoot]
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc candidate'.1)
  have hcandidateNorm : ‖candidate.toComplex‖ ≤
      (2 ^ cauchyExp candidate.p + 1 : Nat) :=
    (AlgebraicRoot.norm_lt_rootBound candidate).le
  have hcandidateRadius : candidate'.1.1.square.toBall.realRadius ≤
      (3 / 4 : ℝ) * (2 : ℝ) ^ (-(prec : Int)) := by
    apply DyadicComplexBall.realRadius_toBall_le_three_quarters
    exact RefinedIsolation.refineTo?_precision candidate.rep
      ((prec : Int) + 1) .nkThenPellet hrefine
  have hmap := HexRootsMathlib.array_mapM_some_get hballs
  have hentry : ∀ (i : Nat) (hi : i < f.size) (hj : i < balls.size),
      LevelSemantics.denote levels f[i] ∈ balls[i].set ∧
        ‖LevelSemantics.denote levels f[i]‖ ≤
          RawEvaluation.coordsMajorant levels f[i] ∧
        balls[i].realRadius ≤ (2 : ℝ) ^ (-(prec : Int)) := by
    intro i hi hj
    have hstep := hmap.2 i hi hj
    obtain ⟨value, hvalue, hstep⟩ := Option.bind_eq_some_iff.mp hstep
    obtain ⟨refined, hrefined, hstep⟩ :=
      Option.bind_eq_some_iff.mp hstep
    have hball : refined.1.1.square.toBall = balls[i] :=
      Option.some.inj hstep
    have hroot : refined.1.root = value.toComplex := by
      calc
        refined.1.root = value.rep.root :=
          HexRootsMathlib.RefinedIsolation.refineTo_root value.rep
            ((prec : Int) + 1) .nkThenPellet hrefined
        _ = value.toComplex := rfl
    refine ⟨?_,
      LevelSemantics.norm_denote_le_coordsMajorant levels f[i], ?_⟩
    · rw [← LevelSemantics.evalCoords_sound levels f[i] hvalue,
        ← hroot, ← hball]
      exact DyadicComplexBall.mem_toBall
        (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc refined.1)
    · rw [← hball]
      have hradius :=
        DyadicComplexBall.realRadius_toBall_le_three_quarters
          (RefinedIsolation.refineTo?_precision value.rep
            ((prec : Int) + 1) .nkThenPellet hrefined)
      have hnonneg : 0 ≤ (2 : ℝ) ^ (-(prec : Int)) := by positivity
      nlinarith
  have hentryD : ∀ (i : Nat) (hi : i < f.size) (hj : i < balls.size),
      LevelSemantics.denote levels (f.getD i #[]) ∈
          (balls.getD i DyadicComplexBall.zero).set ∧
        ‖LevelSemantics.denote levels (f.getD i #[])‖ ≤
          RawEvaluation.coordsMajorant levels (f.getD i #[]) ∧
        (balls.getD i DyadicComplexBall.zero).realRadius ≤
          (2 : ℝ) ^ (-(prec : Int)) := by
    intro i hi hj
    rw [← Array.getElem_eq_getD #[] (h := hi),
      ← Array.getElem_eq_getD DyadicComplexBall.zero (h := hj)]
    exact hentry i hi hj
  cases hback : balls.back? with
  | none =>
      have hball : DyadicComplexBall.zero = ball := by
        apply Option.some.inj
        simpa [hback] using hrun
      subst ball
      simp [DyadicComplexBall.zero, DyadicComplexBall.realRadius]
  | some topBall =>
      cases hfback : f.back? with
      | none =>
          have hfEmpty : f = #[] := Array.back?_eq_none_iff.mp hfback
          have hballsEmpty : balls = #[] := by
            apply Array.size_eq_zero_iff.mp
            simpa [hfEmpty] using hmap.1.symm
          have : balls.back? = none := Array.back?_eq_none_iff.mpr hballsEmpty
          rw [this] at hback
          contradiction
      | some topCoefficient =>
          obtain ⟨ballPrefix, hballPrefix⟩ :=
            Array.back?_eq_some_iff.mp hback
          obtain ⟨coefficientPrefix, hcoefficientPrefix⟩ :=
            Array.back?_eq_some_iff.mp hfback
          have hprefixSize : coefficientPrefix.size = ballPrefix.size := by
            have hsize := hmap.1
            rw [hcoefficientPrefix, hballPrefix] at hsize
            simpa using hsize
          have htop := hentryD coefficientPrefix.size
            (by simp [hcoefficientPrefix])
            (by simp [hballPrefix, hprefixSize])
          rw [hcoefficientPrefix, getD_push_eq, hballPrefix,
            hprefixSize, getD_push_eq] at htop
          have hprefix : List.Forall₂
              (fun coefficient coefficientBall =>
                LevelSemantics.denote levels coefficient ∈
                    coefficientBall.set ∧
                  ‖LevelSemantics.denote levels coefficient‖ ≤
                    RawEvaluation.coordsMajorant levels coefficient ∧
                  coefficientBall.realRadius ≤
                    (2 : ℝ) ^ (-(prec : Int)))
              coefficientPrefix.toList ballPrefix.toList := by
            rw [List.forall₂_iff_get]
            refine ⟨by simpa using hprefixSize, ?_⟩
            intro i hi hj
            have hi' : i < coefficientPrefix.size := by simpa using hi
            have hj' : i < ballPrefix.size := by simpa using hj
            have h := hentryD i (by
              rw [hcoefficientPrefix]
              simp
              exact Nat.le_of_lt hi') (by
              rw [hballPrefix]
              simp
              exact Nat.le_of_lt hj')
            rw [hcoefficientPrefix,
              getD_push_lt coefficientPrefix topCoefficient #[] i hi',
              hballPrefix,
              getD_push_lt ballPrefix topBall DyadicComplexBall.zero i hj'] at h
            rw [← Array.getElem_eq_getD #[] (h := hi'),
              ← Array.getElem_eq_getD DyadicComplexBall.zero (h := hj')] at h
            simpa [List.get_eq_getElem, ← Array.getElem_toList] using h
          have hfold : balls.foldr
              (fun coefficient value =>
                coefficient.add (candidate'.1.1.square.toBall.mul value))
              topBall (start := balls.size - 1) =
                ballPrefix.toList.foldr
                  (fun coefficient value =>
                    coefficient.add (candidate'.1.1.square.toBall.mul value))
                  topBall := by
            have hsize : balls.size - 1 = ballPrefix.size := by
              rw [hballPrefix]
              simp
            rw [hsize, Array.foldr_eq_foldr_extract]
            rw [hballPrefix,
              Array.extract_push_of_le (le_refl ballPrefix.size)]
            simp
          have hball : balls.foldr
              (fun coefficient value =>
                coefficient.add (candidate'.1.1.square.toBall.mul value))
              topBall (start := balls.size - 1) = ball := by
            apply Option.some.inj
            simpa [hback] using hrun
          subst ball
          rw [hfold]
          let rootBound := 2 ^ cauchyExp candidate.p + 1
          let step := fun (coefficient : Array Rat) (state : Nat × Nat) =>
            (state.1 * rootBound +
                RawEvaluation.coordsMajorant levels coefficient,
              2 * state.1 + 2 * rootBound * state.2 + 3 * state.2 + 1)
          let state := coefficientPrefix.toList.foldr step
            (RawEvaluation.coordsMajorant levels topCoefficient, 1)
          have hbounds := rawHornerBall_bounds levels
            coefficientPrefix.toList ballPrefix.toList candidate.toComplex
            candidate'.1.1.square.toBall prec rootBound
            (LevelSemantics.denote levels topCoefficient) topBall
            (RawEvaluation.coordsMajorant levels topCoefficient, 1)
            hprefix hcandidate (by simpa only [rootBound] using hcandidateNorm)
            hcandidateRadius htop.1 htop.2.1 (by simpa using htop.2.2)
          have hradius :
              (ballPrefix.toList.foldr
                (fun coefficient value =>
                  coefficient.add (candidate'.1.1.square.toBall.mul value))
                topBall).realRadius ≤
                (state.2 : ℝ) * (2 : ℝ) ^ (-(prec : Int)) := by
            simpa only [state, step, rootBound] using hbounds.2.2
          have hlist : f.toList =
              coefficientPrefix.toList ++ [topCoefficient] := by
            rw [hcoefficientPrefix, Array.toList_push]
          have hstate : f.foldr step (0, 0) = state := by
            rw [← Array.foldr_toList, hlist, List.foldr_append]
            simp [state, step]
          have hfoldMap :
              (Factor.rawPoly levels f).toArray.foldr
                (fun coefficient state =>
                  (state.1 * rootBound +
                      RawEvaluation.coordsMajorant levels coefficient.data,
                    2 * state.1 + 2 * rootBound * state.2 +
                      3 * state.2 + 1)) (0, 0) =
                f.foldr step (0, 0) := by
            rw [← Array.foldr_toList, ← Array.foldr_toList]
            have hcanonicalList :
                (Factor.rawPoly levels f).toArray.toList.map
                    Arithmetic.Coeff.data = f.toList := by
              simpa [Factor.polyCoords, Array.toList_map] using
                congrArg Array.toList hcanonical
            rw [← hcanonicalList, List.foldr_map]
          have hmajorant : state.2 ≤
              Disambiguation.evalMajorant (Factor.rawPoly levels f)
                (fun coefficient =>
                  RawEvaluation.coordsMajorant levels coefficient.data)
                candidate.p := by
            unfold Disambiguation.evalMajorant
            dsimp only
            rw [hfoldMap, hstate]
            exact Nat.le_max_right _ _
          exact hradius.trans (mul_le_mul_of_nonneg_right
            (by exact_mod_cast hmajorant) (by positivity))

/-- The checked raw zero test returns exactly semantic vanishing. -/
theorem rawVanishesAt_sound (levels : List Level) (f : Array (Array Rat))
    (candidate : AlgebraicRoot) {keep : Bool}
    (hrun : RawEvaluation.vanishesAt? levels f candidate = some keep) :
    keep ↔
      (LevelSemantics.polynomial levels f).eval candidate.toComplex = 0 := by
  unfold RawEvaluation.vanishesAt? at hrun
  obtain ⟨evaluation, hevaluation, hretain⟩ :=
    Option.bind_eq_some_iff.mp hrun
  have hevaluationSound := LevelSemantics.evalPoly_sound levels f
    candidate evaluation hevaluation
  have hcorrect := Hex.retainZero?_sound
    (HexRootsMathlib.RefinedIsolation.poly_ne_zero evaluation.rep)
    (AlgebraicRoot.toComplex_isRoot evaluation)
    (fun prec ball hball => by
      rw [hevaluationSound]
      exact rawEvalBall_sound levels f candidate prec hball)
    hretain
  simpa only [hevaluationSound] using hcorrect

/-- The bounded raw zero test is total on canonical tower-polynomial
coordinates. -/
theorem rawVanishesAt_isSome (levels : List Level) (f : Array (Array Rat))
    (candidate : AlgebraicRoot)
    (hcanonical : Factor.polyCoords (Factor.rawPoly levels f) = f) :
    (RawEvaluation.vanishesAt? levels f candidate).isSome := by
  obtain ⟨evaluation, hevaluation⟩ := Option.isSome_iff_exists.mp
    (evalPoly_isSome levels f candidate)
  unfold RawEvaluation.vanishesAt?
  rw [hevaluation]
  let polynomial := Factor.rawPoly levels f
  let majorant := Disambiguation.evalMajorant polynomial
    (fun coefficient =>
      RawEvaluation.coordsMajorant levels coefficient.data) candidate.p
  change (retainZero? evaluation.p majorant
    (RawEvaluation.evalBall? levels f candidate)).isSome
  rw [retainZero?]
  split
  · simp
  · have hsearch :
        (evalDisambiguationPrec evaluation.p majorant
          (RawEvaluation.evalBall? levels f candidate)).isSome := by
      let limit := evalDisambiguationLimit evaluation.p majorant
      obtain ⟨ball, hball⟩ := Option.isSome_iff_exists.mp
        (evalBall_isSome levels f candidate limit)
      apply evalDisambiguationPrec_isSome_of_endpoint evaluation.p majorant
        (RawEvaluation.evalBall? levels f candidate) hball
      apply evalDisambiguationLimit_radius_small evaluation.p majorant ball
      have hmajorant : 1 ≤ majorant := by
        dsimp [majorant, Disambiguation.evalMajorant]
        exact Nat.le_max_left _ _
      simpa only [limit, Nat.max_eq_right hmajorant, majorant, polynomial] using
        rawEvalBall_radius levels f candidate hcanonical limit hball
    obtain ⟨prec, hprec⟩ := Option.isSome_iff_exists.mp hsearch
    rw [hprec]
    obtain ⟨ball, hball⟩ := Option.isSome_iff_exists.mp
      (evalBall_isSome levels f candidate prec)
    simp [hball]

private theorem rational_relation_vanishes (level : Level) (lower : List Level)
    (h : level.RationalRelation lower) :
    (LevelSemantics.polynomial lower (level.polynomial lower)).eval
      level.root.toComplex = 0 := by
  obtain ⟨rfl, original, checked, hp, hrelation⟩ := h
  rw [LevelSemantics.polynomial_nil, hrelation,
    HexPolyMathlib.toPolynomial_scale,
    HexPolyZMathlib.toPolynomial_toRatPoly,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
    Polynomial.eval_C]
  have hcomp :
      (algebraMap Rat ℂ).comp (Int.castRingHom Rat) =
        Int.castRingHom ℂ := RingHom.ext_int _ _
  have hpoly :
      (HexPolyZMathlib.toPolyℚ level.root.p).map (algebraMap Rat ℂ) =
        HexRootsMathlib.toPolyℂ level.root.p := by
    dsimp [HexPolyZMathlib.toPolyℚ, HexRootsMathlib.toPolyℂ]
    rw [Polynomial.map_map, hcomp]
  rw [hpoly, AlgebraicRoot.toComplex_isRoot]
  simp

/-- A validated relative relation vanishes at its selected absolute generator.
This is the semantic half of the central level invariant; relative
irreducibility is recorded separately by the checked factorization bridge. -/
theorem level_relation_vanishes (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    (LevelSemantics.polynomial lower (level.polynomial lower)).eval
      level.root.toComplex = 0 := by
  cases hvalid.2.1 with
  | rational relation => exact rational_relation_vanishes level lower relation
  | relative _ _ embedding =>
      exact (rawVanishesAt_sound lower (level.polynomial lower)
        level.root embedding).mp rfl

end Hex.NumberTower
