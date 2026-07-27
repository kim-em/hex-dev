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

/-- Every validated tower element can be evaluated in the stored embedding. -/
theorem eval?_isSome (T : NumberTower) (a : Elem T) :
    (T.eval? a).isSome := by
  sorry

/-- A successful recursive evaluation has the value of the returned lazy
algebraic root. -/
theorem eval?_eq (T : NumberTower) (a : Elem T) {root : AlgebraicRoot}
    (h : RawEvaluation.evalCoords? T.levels.toList (coeffs a) = some root) :
    T.eval? a = some root.toComplex := by
  simp [eval?, h]

/-- The complex value of a tower element. The fallback is unreachable by
`eval?_isSome`. -/
@[expose]
noncomputable def toComplex (T : NumberTower) (a : Elem T) : ℂ :=
  (T.eval? a).getD 0

/-- A successful executable evaluation computes `toComplex`. -/
theorem toComplex_eq (T : NumberTower) (a : Elem T)
    {root : AlgebraicRoot}
    (h : RawEvaluation.evalCoords? T.levels.toList (coeffs a) = some root) :
    T.toComplex a = root.toComplex := by
  simp [toComplex, eval?_eq T a h]

/-- The rational tower embedding has its expected complex value. -/
theorem toComplex_ofRat (T : NumberTower) (q : Rat) :
    T.toComplex (T.ofRat q) = (q : ℂ) := by
  sorry

/-- The fixed complex interpretation is injective. -/
theorem toComplex_injective (T : NumberTower) :
    Function.Injective T.toComplex := by
  sorry

/-- Every validated tower has positive absolute dimension. -/
private theorem levelsDim_pos (levels : List Level)
    (hvalid : LevelsValid levels) : 0 < levelsDim levels := by
  induction levels with
  | nil => simp [levelsDim]
  | cons level lower ih =>
      exact Nat.mul_pos hvalid.1.1 (ih hvalid.2.2)

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
      have hq :
          (coeffs (NumberTower.rat.ofRat q)).getD 0 0 = q := by
        rw [NumberTower.ofRat_eq_ofCoeffs, NumberTower.coeffs_ofCoeffs]
        simp [NumberTower.normalizeCoeffs, dim_pos]
      have hrat :
          RawEvaluation.evalCoords? []
              (coeffs (NumberTower.rat.ofRat q)) = some root := by
        change
          (do
            let value ← AlgebraicPoly.Common.rational?
              ((coeffs (NumberTower.rat.ofRat q)).getD 0 0)
            some value.toRoot) = some root
        rw [hq]
        simpa [RawEvaluation.evalCoords?, q] using h
      have hrat' :
          RawEvaluation.evalCoords? NumberTower.rat.levels.toList
              (coeffs (NumberTower.rat.ofRat q)) = some root := by
        simpa [NumberTower.rat_levels] using hrat
      calc
        root.toComplex = NumberTower.rat.toComplex
            (NumberTower.rat.ofRat q) :=
          (toComplex_eq NumberTower.rat (NumberTower.rat.ofRat q) hrat').symm
        _ = (q : ℂ) := toComplex_ofRat NumberTower.rat q
        _ = denote [] data := rfl
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

/-- Interpret raw lower-tower coordinates through their selected complex
embedding. Validity makes the fallback unreachable. -/
@[expose]
noncomputable def toComplex (lower : List Level) (a : Array Rat) : ℂ :=
  (RawEvaluation.evalCoords? lower a).map AlgebraicRoot.toComplex |>.getD 0

/-- Interpret a raw polynomial over a lower tower in `Polynomial ℂ`. -/
@[expose]
noncomputable def polynomial (lower : List Level)
    (f : Array (Array Rat)) : Polynomial ℂ :=
  f.foldr
    (fun a value => Polynomial.C (toComplex lower a) +
      Polynomial.X * value) 0

end LevelSemantics

/-- A validated relative relation vanishes at its selected absolute generator.
This is the semantic half of the central level invariant; relative
irreducibility is recorded separately by the checked factorization bridge. -/
theorem level_relation_vanishes (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    (LevelSemantics.polynomial lower (level.polynomial lower)).eval
      level.root.toComplex = 0 := by
  sorry

end Hex.NumberTower
