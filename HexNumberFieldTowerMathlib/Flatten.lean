/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Split
public import HexRowReduceMathlib
import HexNumberFieldMathlib.Coordinates
import Mathlib.LinearAlgebra.Basis.Basic

public section

/-!
# Correctness of primitive-element flattening

The executable certificate checks a tower-basis round trip and the primitive
minimal-polynomial relation. Irreducibility and the equal dimension then give
the opposite round trip and multiplicativity.
-/

namespace Hex.NumberTower

namespace Flattening

/-- Mathematical meaning of a checked primitive presentation. -/
def Sound {T : NumberTower} (F : Flattening T) : Prop :=
  letI : ZPoly.CheckedIrreducible F.root.p := F.root.checked
  Function.LeftInverse F.fromPrimitive F.toPrimitive ∧
    Function.RightInverse F.fromPrimitive F.toPrimitive ∧
    (∀ a : Elem T,
      PolyQuot.toComplex (F.toPrimitive a) F.root.rep F.root.rep_mk =
        T.toComplex a) ∧
    (∀ a : PolyQuot F.root.p F.root.x,
      T.toComplex (F.fromPrimitive a) =
        PolyQuot.toComplex a F.root.rep F.root.rep_mk) ∧
    (∀ a b : Elem T,
      F.toPrimitive (a + b) = F.toPrimitive a + F.toPrimitive b) ∧
    (∀ a b : Elem T,
      F.toPrimitive (a * b) = F.toPrimitive a * F.toPrimitive b) ∧
    ∀ a : Elem T, F.toPrimitive a⁻¹ = (F.toPrimitive a)⁻¹

end Flattening

namespace Flatten

open IntermediateField

/-- A recovered runtime generator denotes its selected absolute value in the
fixed tower embedding. -/
def Generator.Matches {T : NumberTower} (generator : Generator T) : Prop :=
  T.toComplex generator.value = generator.root.toComplex

/-- The accumulated tower element denotes the selected primitive value. -/
def Candidate.Matches {T : NumberTower} (candidate : Candidate T) : Prop :=
  T.toComplex candidate.value = candidate.root.toComplex

/-- Every accumulated generator coordinate denotes the corresponding absolute
generator in the candidate presentation. -/
def Candidate.Represents {T : NumberTower} (candidate : Candidate T)
    (generators : List (Generator T)) : Prop :=
  List.Forall₂
    (fun generator coordinate =>
      PolyQuot.toComplex coordinate candidate.root.rep candidate.root.rep_mk =
        generator.root.toComplex)
    generators candidate.coordinates.toList

private def Generator.Describes {T : NumberTower} (generator : Generator T)
    (level : Level) : Prop :=
  generator.degree = level.degree ∧
    generator.root.toComplex = level.root.toComplex

@[simp]
private theorem unitCoords_size (dimension index : Nat) :
    (unitCoords dimension index).size = dimension := by
  simp [unitCoords]

private theorem unitCoords_getElem (dimension index i : Nat)
    (hi : i < dimension) :
    (unitCoords dimension index)[i]'(by simpa using hi) =
      if index = i then 1 else 0 := by
  simp only [unitCoords, Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds (by simpa using hi)]
  simp

private theorem unitCoords_getD (dimension index i : Nat) :
    (unitCoords dimension index).getD i 0 =
      if i < dimension ∧ index = i then 1 else 0 := by
  by_cases hi : i < dimension
  · rw [← Array.getElem_eq_getD 0 (h := by simpa using hi),
      unitCoords_getElem dimension index i hi]
    simp [hi]
  · simp [Array.getD, hi]

private theorem fixedCoeffs_getElem (full : Nat) (data : Array Rat) (i : Nat)
    (hi : i < full) :
    (Arithmetic.fixedCoeffs full data)[i]'(by
      simp [Arithmetic.fixedCoeffs, hi]) = data.getD i 0 := by
  simp [Arithmetic.fixedCoeffs]

private theorem replicatePush_getD (n i : Nat) :
    ((Array.replicate n (0 : Rat)).push 1).getD i 0 =
      if n = i then 1 else 0 := by
  by_cases hi : i < n
  · rw [← Array.getElem_eq_getD 0 (h := by simp; omega),
      Array.getElem_push_lt (by simpa using hi)]
    simp [Nat.ne_of_gt hi]
  · by_cases heq : n = i
    · subst i
      rw [← Array.getElem_eq_getD 0 (h := by simp)]
      simpa using (Array.getElem_push_eq
        (xs := Array.replicate n (0 : Rat)) (x := 1))
    · have hout : ((Array.replicate n (0 : Rat)).push 1).size ≤ i := by
        simp
        omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hout]
      simp [heq]

private theorem unitCoords_fixed (full short index : Nat)
    (_hshort : short ≤ full) (hindex : index < short) :
    unitCoords full index =
      Arithmetic.fixedCoeffs full (unitCoords short index) := by
  apply Array.ext
  · simp [unitCoords, Arithmetic.fixedCoeffs]
  · intro i hiLeft hiRight
    have hif : i < full := by simpa using hiLeft
    rw [unitCoords_getElem full index i hif,
      fixedCoeffs_getElem full (unitCoords short index) i hif,
      unitCoords_getD]
    by_cases hi : index = i <;> simp_all

private theorem unit_generator (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    LevelSemantics.denote (level :: lower)
        (unitCoords (levelsDim (level :: lower)) (levelsDim lower)) =
      level.root.toComplex := by
  have hlower : 0 < levelsDim lower := levelsDim_pos lower hvalid.2.2
  have hindex : levelsDim lower < levelsDim (level :: lower) := by
    simp only [levelsDim]
    simpa [Nat.one_mul] using
      Nat.mul_lt_mul_of_pos_right hvalid.1.1 hlower
  have hcoords : unitCoords (levelsDim (level :: lower))
      (levelsDim lower) =
      Arithmetic.fixedCoeffs (levelsDim (level :: lower))
        ((Array.replicate (levelsDim lower) 0).push 1) := by
    apply Array.ext
    · simp [unitCoords, Arithmetic.fixedCoeffs]
    · intro i hiLeft hiRight
      have hif : i < levelsDim (level :: lower) := by simpa using hiLeft
      rw [unitCoords_getElem _ _ _ hif,
        fixedCoeffs_getElem _ _ _ hif, replicatePush_getD]
  rw [hcoords, LevelSemantics.denote_fixed]
  exact LevelSemantics.denote_generator level lower hvalid hvalid.1.1

private theorem levelsValid_suffix (newer lower : List Level)
    (hvalid : LevelsValid (newer ++ lower)) : LevelsValid lower := by
  induction newer with
  | nil => exact hvalid
  | cons _ newer ih => exact ih hvalid.2.2

private theorem levelsDim_le_prefix (newer lower : List Level)
    (hvalid : LevelsValid (newer ++ lower)) :
    levelsDim lower ≤ levelsDim (newer ++ lower) := by
  induction newer with
  | nil => simp
  | cons head newer ih =>
      have htail : LevelsValid (newer ++ lower) := hvalid.2.2
      have hgrow : levelsDim (newer ++ lower) ≤
          levelsDim (head :: (newer ++ lower)) := by
        simp only [levelsDim]
        exact Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt hvalid.1.1)
      exact (ih htail).trans (by simpa only [List.cons_append] using hgrow)

private theorem unit_level (newer : List Level) (level : Level)
    (lower : List Level)
    (hvalid : LevelsValid (newer ++ (level :: lower))) :
    LevelSemantics.denote (newer ++ (level :: lower))
        (unitCoords (levelsDim (newer ++ (level :: lower)))
          (levelsDim lower)) = level.root.toComplex := by
  induction newer with
  | nil =>
      simpa using unit_generator level lower hvalid
  | cons head newer ih =>
      change LevelSemantics.denote
        (head :: (newer ++ (level :: lower)))
          (unitCoords
            (levelsDim (head :: (newer ++ (level :: lower))))
            (levelsDim lower)) = level.root.toComplex
      have htailValid : LevelsValid (newer ++ (level :: lower)) :=
        hvalid.2.2
      have hbaseValid : LevelsValid (level :: lower) := by
        exact levelsValid_suffix newer (level :: lower) htailValid
      have hshort : levelsDim (newer ++ (level :: lower)) ≤
          levelsDim (head :: (newer ++ (level :: lower))) := by
        simp only [levelsDim]
        exact Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt hvalid.1.1)
      have hindex : levelsDim lower <
          levelsDim (newer ++ (level :: lower)) := by
        have hbase : levelsDim lower < levelsDim (level :: lower) := by
          simp only [levelsDim]
          simpa [Nat.one_mul] using Nat.mul_lt_mul_of_pos_right
            hbaseValid.1.1 (levelsDim_pos lower hbaseValid.2.2)
        exact hbase.trans_le
          (levelsDim_le_prefix newer (level :: lower) htailValid)
      rw [unitCoords_fixed _ _ _ hshort hindex,
        LevelSemantics.denote_fixed,
        LevelSemantics.denote_embed head (newer ++ (level :: lower))
          hvalid (unitCoords (levelsDim (newer ++ (level :: lower)))
            (levelsDim lower)) (by simp [unitCoords])]
      exact ih htailValid

private theorem generatorsAux?_sound (T : NumberTower)
    (newer levels : List Level)
    (hlevels : T.levels.toList = newer ++ levels)
    {state : Array (Generator T) × Nat}
    (h : generatorsAux? T levels = some state) :
    state.2 = levelsDim levels ∧
      ∀ generator ∈ state.1.toList, generator.Matches := by
  induction levels generalizing newer state with
  | nil =>
      simp [generatorsAux?] at h
      subst state
      simp [levelsDim]
  | cons level lower ih =>
      unfold generatorsAux? at h
      obtain ⟨lowerState, hlowerState, h⟩ :=
        Option.bind_eq_some_iff.mp h
      obtain ⟨root, hroot, h⟩ := Option.bind_eq_some_iff.mp h
      have hstate := Option.some.inj h
      subst state
      have hlowerLevels : T.levels.toList =
          (newer ++ [level]) ++ lower := by
        rw [hlevels]
        simp [List.append_assoc]
      obtain ⟨hdimension, hgenerators⟩ :=
        ih (newer ++ [level]) hlowerLevels hlowerState
      constructor
      · simp [levelsDim, hdimension, Nat.mul_comm]
      · intro generator hgenerator
        simp only [Array.toList_push, List.mem_append,
          List.mem_singleton] at hgenerator
        rcases hgenerator with hprevious | hnew
        · exact hgenerators generator hprevious
        · subst generator
          unfold Generator.Matches
          rw [hdimension]
          change T.toComplex
              (T.ofCoeffs (unitCoords T.dim (levelsDim lower))) =
            root.toComplex
          have hvalid : LevelsValid (newer ++ (level :: lower)) := by
            rw [← hlevels]
            exact T.valid
          have hdim : T.dim = levelsDim (newer ++ (level :: lower)) := by
            simp [dim, hlevels]
          rw [LevelSemantics.toComplex_eq_denote, coeffs_ofCoeffs,
            normalizeCoeffs_eq_self T _ (by simp [unitCoords, dim]),
            hlevels, hdim,
            unit_level newer level lower hvalid,
            AlgebraicRoot.exact?_sound level.root hroot]

private theorem generatorsAux?_isSome (T : NumberTower)
    (levels : List Level) : (generatorsAux? T levels).isSome := by
  induction levels with
  | nil => simp [generatorsAux?]
  | cons level lower ih =>
      obtain ⟨state, hstate⟩ := Option.isSome_iff_exists.mp ih
      obtain ⟨root, hroot⟩ := Option.isSome_iff_exists.mp
        (AlgebraicRoot.exact?_isSome level.root)
      simp [generatorsAux?, hstate, hroot]

private theorem generatorsAux?_shape (T : NumberTower) (levels : List Level)
    {state : Array (Generator T) × Nat}
    (h : generatorsAux? T levels = some state) :
    state.1.size = levels.length ∧
      (state.1.toList.map Generator.degree).prod = levelsDim levels := by
  induction levels generalizing state with
  | nil =>
      simp [generatorsAux?] at h
      subst state
      simp [levelsDim]
  | cons level lower ih =>
      unfold generatorsAux? at h
      obtain ⟨lowerState, hlowerState, h⟩ :=
        Option.bind_eq_some_iff.mp h
      obtain ⟨root, hroot, h⟩ := Option.bind_eq_some_iff.mp h
      have hstate := Option.some.inj h
      subst state
      obtain ⟨hsize, hproduct⟩ := ih hlowerState
      constructor
      · simp [hsize]
      · simp [hproduct, levelsDim, Nat.mul_comm]

private theorem generatorsAux?_levels (T : NumberTower) (levels : List Level)
    {state : Array (Generator T) × Nat}
    (h : generatorsAux? T levels = some state) :
    List.Forall₂ Generator.Describes state.1.toList levels.reverse := by
  induction levels generalizing state with
  | nil =>
      simp [generatorsAux?] at h
      subst state
      exact List.Forall₂.nil
  | cons level lower ih =>
      unfold generatorsAux? at h
      obtain ⟨lowerState, hlowerState, h⟩ :=
        Option.bind_eq_some_iff.mp h
      obtain ⟨root, hroot, h⟩ := Option.bind_eq_some_iff.mp h
      have hstate := Option.some.inj h
      subst state
      rw [Array.toList_push, List.reverse_cons]
      apply List.rel_append (ih hlowerState)
      apply List.Forall₂.cons
      · exact ⟨rfl, AlgebraicRoot.exact?_sound level.root hroot⟩
      · exact List.Forall₂.nil

private theorem generators?_sound (T : NumberTower)
    {generators : Array (Generator T)}
    (h : generators? T = some generators) :
    ∀ generator ∈ generators.toList, generator.Matches := by
  unfold generators? at h
  obtain ⟨state, hstate, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases hdimension : state.2 = T.dim
  · simp [hdimension] at h
    subst generators
    exact (generatorsAux?_sound T [] T.levels.toList (by simp)
      hstate).2
  · simp [hdimension] at h

private theorem generators?_isSome (T : NumberTower) :
    (generators? T).isSome := by
  obtain ⟨state, hstate⟩ := Option.isSome_iff_exists.mp
    (generatorsAux?_isSome T T.levels.toList)
  have hdimension := (generatorsAux?_sound T [] T.levels.toList
    (by simp) hstate).1
  unfold generators?
  rw [hstate]
  simp [hdimension, dim]

private theorem generators?_shape (T : NumberTower)
    {generators : Array (Generator T)}
    (h : generators? T = some generators) :
    generators.size = T.levels.size ∧
      (generators.toList.map Generator.degree).prod = T.dim := by
  unfold generators? at h
  obtain ⟨state, hstate, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hsize, hproduct⟩ := generatorsAux?_shape T _ hstate
  by_cases hdimension : state.2 = T.dim
  · simp [hdimension] at h
    subst generators
    exact ⟨by simpa using hsize, by simpa [dim] using hproduct⟩
  · simp [hdimension] at h

private theorem generators?_levels (T : NumberTower)
    {generators : Array (Generator T)}
    (h : generators? T = some generators) :
    List.Forall₂ Generator.Describes generators.toList
      T.levels.toList.reverse := by
  unfold generators? at h
  obtain ⟨state, hstate, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases hdimension : state.2 = T.dim
  · simp [hdimension] at h
    subst generators
    exact generatorsAux?_levels T _ hstate
  · simp [hdimension] at h

private theorem horner_eq_sum (coefficients : List Rat) (z : ℂ) :
    coefficients.foldr
        (fun (coefficient : Rat) (value : ℂ) =>
          value * z + (coefficient : ℂ)) 0 =
      ∑ i ∈ Finset.range coefficients.length,
        (coefficients.getD i 0 : ℂ) * z ^ i := by
  induction coefficients with
  | nil => simp
  | cons coefficient coefficients ih =>
      rw [List.foldr_cons, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero,
        mul_one, pow_succ]
      rw [ih, Finset.sum_mul]
      simp [mul_assoc]

private theorem toList_getD (p : DensePoly Rat) (i : Nat) :
    p.toList.getD i 0 = p.coeff i := by
  rw [DensePoly.toList, List.getD_eq_getElem?_getD,
    Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]
  exact DensePoly.toArray_getD p i

private theorem eval₂_horner (p : DensePoly Rat) (z : ℂ) :
    (HexPolyMathlib.toPolynomial p).eval₂ (algebraMap Rat ℂ) z =
      p.toArray.foldr
        (fun (coefficient : Rat) (value : ℂ) =>
          value * z + (coefficient : ℂ)) 0 := by
  rw [HexPolyMathlib.eval₂_toPolynomial, ← Array.foldr_toList,
    horner_eq_sum]
  apply Finset.sum_congr
  · simp
  · intro i hi
    rw [← toList_getD]
    rfl

private theorem intHorner_eq_sum (coefficients : List Int) (z : ℂ) :
    coefficients.foldr
        (fun (coefficient : Int) (value : ℂ) =>
          value * z + (coefficient : ℂ)) 0 =
      ∑ i ∈ Finset.range coefficients.length,
        (coefficients.getD i 0 : ℂ) * z ^ i := by
  induction coefficients with
  | nil => simp
  | cons coefficient coefficients ih =>
      rw [List.foldr_cons, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero,
        mul_one, pow_succ]
      rw [ih, Finset.sum_mul]
      simp [mul_assoc]

private theorem zpoly_toList_getD (p : ZPoly) (i : Nat) :
    p.toList.getD i 0 = p.coeff i := by
  rw [DensePoly.toList, List.getD_eq_getElem?_getD,
    Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]
  exact DensePoly.toArray_getD p i

private theorem zpoly_eval_horner (p : ZPoly) (z : ℂ) :
    (HexRootsMathlib.toPolyℂ p).eval z =
      p.toArray.foldr
        (fun (coefficient : Int) (value : ℂ) =>
          value * z + (coefficient : ℂ)) 0 := by
  rw [Polynomial.eval_map, HexPolyMathlib.eval₂_toPolynomial,
    ← Array.foldr_toList, intHorner_eq_sum]
  apply Finset.sum_congr
  · simp
  · intro i hi
    rw [← zpoly_toList_getD]
    rfl

private theorem toQAdjoin_complex (a : AlgebraicNumber) :
    PolyQuot.toComplex a.toQAdjoin a.rep a.rep_mk = a.toComplex := by
  unfold AlgebraicNumber.toQAdjoin PolyQuot.toComplex PolyQuot.reduce
  rw [PolyQuot.eval_reduceCoeffs]
  have hpoly : HexPolyMathlib.toPolynomial
      (DensePoly.ofList ([0, 1] : List Rat)) = Polynomial.X := by
    ext n
    rw [HexPolyMathlib.coeff_toPolynomial, DensePoly.coeff_ofList]
    rcases n with _ | (_ | n) <;> simp [Polynomial.coeff_X]; rfl
  rw [hpoly, Polynomial.eval₂_X]
  rfl

private theorem evalRatPoly_transport
    (theta gamma : AlgebraicNumber)
    (coordinate : PolyQuot theta.p theta.x)
    (a : PolyQuot gamma.p gamma.x)
    (ha : PolyQuot.toComplex a gamma.rep gamma.rep_mk = theta.toComplex) :
    PolyQuot.toComplex (evalRatPoly coordinate.coeffs a)
        gamma.rep gamma.rep_mk =
      PolyQuot.toComplex coordinate theta.rep theta.rep_mk := by
  have hcoordinate :
      PolyQuot.toComplex coordinate theta.rep theta.rep_mk =
        coordinate.coeffs.toArray.foldr
          (fun (coefficient : Rat) value =>
            value * theta.toComplex + (coefficient : ℂ)) 0 := by
    unfold PolyQuot.toComplex
    rw [eval₂_horner]
    rfl
  rw [hcoordinate]
  unfold evalRatPoly
  rw [← Array.foldr_toList, ← Array.foldr_toList]
  generalize hcoefficients : coordinate.coeffs.toArray.toList = coefficients
  clear hcoefficients
  induction coefficients with
  | nil => exact PolyQuot.map_zero gamma.rep gamma.rep_mk
  | cons coefficient coefficients ih =>
      rw [List.foldr_cons, List.foldr_cons, PolyQuot.map_add,
        PolyQuot.map_mul, ih, ha, PolyQuot.map_smul, PolyQuot.map_one]
      simp

private theorem fromPrimitiveWith_complex {T : NumberTower}
    {p : ZPoly} {x : SimpleRoot p} (generator : Elem T)
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = x)
    (hgenerator : T.toComplex generator = rep.root)
    (a : PolyQuot p x) :
    T.toComplex (fromPrimitiveWith generator a) =
      PolyQuot.toComplex a rep hrep := by
  unfold fromPrimitiveWith PolyQuot.toComplex
  rw [eval₂_horner]
  rw [← Array.foldr_toList, ← Array.foldr_toList]
  generalize hcoefficients : a.coeffs.toArray.toList = coefficients
  clear hcoefficients
  induction coefficients with
  | nil => simp [map_zero]
  | cons coefficient coefficients ih =>
      rw [List.foldr_cons, List.foldr_cons, map_add, map_mul,
        ih, hgenerator, toComplex_ofRat]

private theorem evalZPoly_complex {T : NumberTower} (f : ZPoly)
    (a : Elem T) :
    T.toComplex (evalZPoly f a) =
      f.toArray.foldr
        (fun (coefficient : Int) (value : ℂ) =>
          value * T.toComplex a + (coefficient : ℂ)) 0 := by
  unfold evalZPoly
  rw [← Array.foldr_toList, ← Array.foldr_toList]
  generalize hcoefficients : f.toArray.toList = coefficients
  clear hcoefficients
  induction coefficients with
  | nil => simp [map_zero]
  | cons coefficient coefficients ih =>
      rw [List.foldr_cons, List.foldr_cons, map_add, map_mul, ih,
        toComplex_ofRat]
      norm_num

private theorem evalZPoly_candidate {T : NumberTower}
    (candidate : Candidate T) (hcandidate : candidate.Matches) :
    evalZPoly candidate.root.p candidate.value = 0 := by
  apply toComplex_injective T
  rw [evalZPoly_complex, map_zero, hcandidate]
  have hroot := AlgebraicRoot.toComplex_isRoot candidate.root.toRoot
  rw [AlgebraicNumber.toRoot_toComplex, zpoly_eval_horner] at hroot
  exact hroot

private theorem toPrimitiveFold_complex {T : NumberTower}
    {p : ZPoly} {x : SimpleRoot p}
    (images : Array (PolyQuot p x)) (a : Elem T)
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = x)
    (indices : List Nat) (initial : PolyQuot p x) :
    PolyQuot.toComplex
        (indices.foldl (fun value i =>
          let coefficient := (coeffs a).getD i 0
          if coefficient = 0 then value
          else value + coefficient • images.getD i 0) initial) rep hrep =
      PolyQuot.toComplex initial rep hrep +
      (indices.map fun i =>
        ((coeffs a).getD i 0 : ℂ) *
          PolyQuot.toComplex (images.getD i 0) rep hrep).sum := by
  induction indices generalizing initial with
  | nil => simp
  | cons i indices ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      by_cases hzero : (coeffs a).getD i 0 = 0
      · rw [ite_eq_left hzero]
        simpa [hzero] using ih initial
      · rw [ite_eq_right hzero, ih, PolyQuot.map_add, PolyQuot.map_smul]
        ring

private theorem toPrimitiveWith_complex {T : NumberTower}
    {p : ZPoly} {x : SimpleRoot p}
    (images : Array (PolyQuot p x)) (a : Elem T)
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = x) :
    PolyQuot.toComplex (toPrimitiveWith images a) rep hrep =
      ((List.range T.dim).map fun i =>
        ((coeffs a).getD i 0 : ℂ) *
          PolyQuot.toComplex (images.getD i 0) rep hrep).sum := by
  unfold toPrimitiveWith
  simpa [PolyQuot.map_zero] using
    toPrimitiveFold_complex images a rep hrep (List.range T.dim) 0

private theorem toPrimitiveWith_add {T : NumberTower}
    {p : ZPoly} {x : SimpleRoot p}
    [ZPoly.CheckedIrreducible p]
    (images : Array (PolyQuot p x)) (a b : Elem T) :
    toPrimitiveWith images (a + b) =
      toPrimitiveWith images a + toPrimitiveWith images b := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  apply PolyQuot.toComplex_injective rep hrep
  change PolyQuot.toComplex (toPrimitiveWith images (a + b)) rep hrep =
    PolyQuot.toComplex
      (toPrimitiveWith images a + toPrimitiveWith images b) rep hrep
  rw [PolyQuot.map_add, toPrimitiveWith_complex,
    toPrimitiveWith_complex, toPrimitiveWith_complex]
  calc
    ((List.range T.dim).map fun i =>
        ((coeffs (a + b)).getD i 0 : ℂ) *
          PolyQuot.toComplex (images.getD i 0) rep hrep).sum =
      ((List.range T.dim).map fun i =>
        (((coeffs a).getD i 0 : ℂ) *
            PolyQuot.toComplex (images.getD i 0) rep hrep) +
          (((coeffs b).getD i 0 : ℂ) *
            PolyQuot.toComplex (images.getD i 0) rep hrep)).sum := by
        congr 1
        apply List.map_congr_left
        intro i hi
        have hiDim : i < T.dim := List.mem_range.mp hi
        rw [coeffs_add]
        simp [Arithmetic.addCoords, Array.getD, hiDim, add_mul]
    _ = _ := @List.sum_map_add Nat ℂ _ (List.range T.dim)
      (fun i => ((coeffs a).getD i 0 : ℂ) *
        PolyQuot.toComplex (images.getD i 0) rep hrep)
      (fun i => ((coeffs b).getD i 0 : ℂ) *
        PolyQuot.toComplex (images.getD i 0) rep hrep)

private theorem toPrimitiveWith_smul {T : NumberTower}
    {p : ZPoly} {x : SimpleRoot p}
    [ZPoly.CheckedIrreducible p]
    (images : Array (PolyQuot p x)) (q : Rat) (a : Elem T) :
    toPrimitiveWith images (q • a) = q • toPrimitiveWith images a := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  apply PolyQuot.toComplex_injective rep hrep
  change PolyQuot.toComplex (toPrimitiveWith images (q • a)) rep hrep =
    PolyQuot.toComplex (q • toPrimitiveWith images a) rep hrep
  rw [PolyQuot.map_smul, toPrimitiveWith_complex,
    toPrimitiveWith_complex]
  calc
    ((List.range T.dim).map fun i =>
        ((coeffs (q • a)).getD i 0 : ℂ) *
          PolyQuot.toComplex (images.getD i 0) rep hrep).sum =
      ((List.range T.dim).map fun i =>
        (q : ℂ) * (((coeffs a).getD i 0 : ℂ) *
          PolyQuot.toComplex (images.getD i 0) rep hrep)).sum := by
        congr 1
        apply List.map_congr_left
        intro i hi
        have hiDim : i < T.dim := List.mem_range.mp hi
        rw [coeffs_smul]
        simp [Array.getD, hiDim, mul_assoc]
    _ = _ := List.sum_map_mul_left (List.range T.dim)
      (fun i => ((coeffs a).getD i 0 : ℂ) *
        PolyQuot.toComplex (images.getD i 0) rep hrep) (q : ℂ)

private theorem candidateAt?_sound (theta alpha : AlgebraicNumber)
    (target index : Nat) {shift : Int} {candidate : AlgebraicNumber}
    (h : candidateAt? theta alpha target index = some (shift, candidate)) :
    candidate.toComplex =
        theta.toComplex + (shift : Rat) * alpha.toComplex ∧
      AlgebraicPoly.Common.degree candidate = target := by
  unfold candidateAt? at h
  cases hshift : AlgebraicPoly.Common.shift? theta alpha
      (Norm.signedShift index) with
  | none => simp [hshift] at h
  | some shifted =>
      by_cases hdegree : AlgebraicPoly.Common.degree shifted = target
      · simp [hshift, hdegree] at h
        obtain ⟨rfl, rfl⟩ := h
        constructor
        · simpa using AlgebraicPoly.Common.shift?_sound theta alpha
            (Norm.signedShift index) hshift
        · exact hdegree
      · simp [hshift, hdegree] at h

private theorem searchRecoveredAux_sound (theta alpha : AlgebraicNumber)
    (target start fuel : Nat) {recovered : Recovered}
    (h : searchRecoveredAux theta alpha target start fuel = some recovered) :
    recovered.root.toComplex =
        theta.toComplex + (recovered.shift : Rat) * alpha.toComplex ∧
      AlgebraicPoly.Common.degree recovered.root = target := by
  induction fuel generalizing start with
  | zero => simp [searchRecoveredAux] at h
  | succ fuel ih =>
      unfold searchRecoveredAux at h
      cases hcandidate : candidateAt? theta alpha target start with
      | none =>
          rw [hcandidate] at h
          exact ih (start + 1) h
      | some candidate =>
          rw [hcandidate] at h
          simp only at h
          rcases candidate with ⟨shift, root⟩
          cases hrecover : recoverPairFast? theta alpha root shift with
          | none =>
              rw [hrecover] at h
              exact ih (start + 1) h
          | some coordinates =>
              rw [hrecover] at h
              rcases coordinates with ⟨thetaCoordinate, alphaCoordinate⟩
              have hrecovered := Option.some.inj h
              subst recovered
              exact candidateAt?_sound theta alpha target start hcandidate

private theorem searchRecovered?_sound (theta alpha : AlgebraicNumber)
    (target : Nat) {recovered : Recovered}
    (h : searchRecovered? theta alpha target = some recovered) :
    recovered.root.toComplex =
        theta.toComplex + (recovered.shift : Rat) * alpha.toComplex := by
  unfold searchRecovered? at h
  cases hfast : searchRecoveredAux theta alpha target 0
      (flattenShiftCount target) with
  | some fast =>
      rw [hfast] at h
      have heq := Option.some.inj h
      subst recovered
      exact (searchRecoveredAux_sound theta alpha target 0
        (flattenShiftCount target) hfast).1
  | none =>
      rw [hfast] at h
      obtain ⟨shifted, hshifted, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨coordinates, hcoordinates, h⟩ :=
        Option.bind_eq_some_iff.mp h
      have heq := Option.some.inj h
      subst recovered
      have hsource := AlgebraicPoly.Common.extendShift?_source theta alpha
        shifted hshifted
      exact AlgebraicPoly.Common.shift?_sound theta alpha shifted.shift
        hsource

private theorem tracePair?_isSome (theta alpha gamma : AlgebraicNumber)
    (htheta : theta.toComplex ∈ Rat⟮gamma.toComplex⟯)
    (halpha : alpha.toComplex ∈ Rat⟮gamma.toComplex⟯) :
    (tracePair? theta alpha gamma).isSome := by
  obtain ⟨powers, hpowers⟩ := Option.isSome_iff_exists.mp
    (AlgebraicPoly.Common.powers?_isSome gamma
      (2 * AlgebraicPoly.Common.degree gamma - 2))
  have hpowersSound := AlgebraicPoly.Common.powers?_sound gamma
    (2 * AlgebraicPoly.Common.degree gamma - 2) hpowers
  have hdegree := AlgebraicPoly.Common.degree_pos gamma
  have hsize : powers.size =
      2 * AlgebraicPoly.Common.degree gamma - 1 := by
    rw [hpowersSound.1]
    omega
  obtain ⟨thetaCoordinate, hthetaCoordinate⟩ :=
    Option.isSome_iff_exists.mp
      (AlgebraicPoly.Common.coordinates?_isSome gamma theta powers
        hsize hpowersSound.2 htheta)
  obtain ⟨alphaCoordinate, halphaCoordinate⟩ :=
    Option.isSome_iff_exists.mp
      (AlgebraicPoly.Common.coordinates?_isSome gamma alpha powers
        hsize hpowersSound.2 halpha)
  simp [tracePair?, hpowers, hthetaCoordinate, halphaCoordinate]

private theorem tracePair?_sound (theta alpha gamma : AlgebraicNumber)
    {coordinates : PolyQuot gamma.p gamma.x × PolyQuot gamma.p gamma.x}
    (h : tracePair? theta alpha gamma = some coordinates) :
    PolyQuot.toComplex coordinates.1 gamma.rep gamma.rep_mk =
        theta.toComplex ∧
      PolyQuot.toComplex coordinates.2 gamma.rep gamma.rep_mk =
        alpha.toComplex := by
  unfold tracePair? at h
  obtain ⟨powers, hpowers, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨thetaCoordinate, hthetaCoordinate, h⟩ :=
    Option.bind_eq_some_iff.mp h
  obtain ⟨alphaCoordinate, halphaCoordinate, h⟩ :=
    Option.bind_eq_some_iff.mp h
  have heq := Option.some.inj h
  subst coordinates
  exact ⟨AlgebraicPoly.Common.coordinates?_sound gamma theta powers
      hthetaCoordinate,
    AlgebraicPoly.Common.coordinates?_sound gamma alpha powers
      halphaCoordinate⟩

private theorem checkCoordinate?_sound (target gamma : AlgebraicNumber)
    (coordinate out : PolyQuot gamma.p gamma.x)
    (h : checkCoordinate? target gamma coordinate = some out) :
    PolyQuot.toComplex out gamma.rep gamma.rep_mk = target.toComplex := by
  let : ZPoly.CheckedIrreducible gamma.p := gamma.checked
  unfold checkCoordinate? at h
  obtain ⟨recovered, hrecovered, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases heq : recovered == target
  · simp only [heq, ↓reduceIte, Option.some.injEq] at h
    subst out
    have hrecoveredEq : recovered = target := beq_iff_eq.mp heq
    rw [← hrecoveredEq]
    exact (PolyQuot.toAlgebraicNumber?_sound coordinate gamma.rep
      gamma.rep_mk hrecovered).symm
  · have hfalse : (recovered == target) = false := by
      cases hvalue : recovered == target <;> simp_all
    simp [hfalse] at h

private theorem checkPair?_sound (theta alpha gamma : AlgebraicNumber)
    (coordinates out : PolyQuot gamma.p gamma.x × PolyQuot gamma.p gamma.x)
    (h : checkPair? theta alpha gamma coordinates = some out) :
    PolyQuot.toComplex out.1 gamma.rep gamma.rep_mk = theta.toComplex ∧
      PolyQuot.toComplex out.2 gamma.rep gamma.rep_mk = alpha.toComplex := by
  unfold checkPair? at h
  obtain ⟨thetaCoordinate, htheta, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨alphaCoordinate, halpha, h⟩ := Option.bind_eq_some_iff.mp h
  have heq := Option.some.inj h
  subst out
  exact ⟨checkCoordinate?_sound theta gamma coordinates.1
      thetaCoordinate htheta,
    checkCoordinate?_sound alpha gamma coordinates.2
      alphaCoordinate halpha⟩

private theorem recoverPairFast?_sound (theta alpha gamma : AlgebraicNumber)
    (shift : Int)
    {coordinates : PolyQuot gamma.p gamma.x × PolyQuot gamma.p gamma.x}
    (h : recoverPairFast? theta alpha gamma shift = some coordinates) :
    PolyQuot.toComplex coordinates.1 gamma.rep gamma.rep_mk =
        theta.toComplex ∧
      PolyQuot.toComplex coordinates.2 gamma.rep gamma.rep_mk =
        alpha.toComplex := by
  unfold recoverPairFast? at h
  by_cases hshift : shift = 0
  · simp [hshift] at h
  · simp only [hshift, ↓reduceIte] at h
    let : ZPoly.CheckedIrreducible gamma.p := gamma.checked
    let gammaCoordinate := gamma.toQAdjoin
    let affine : DensePoly (PolyQuot gamma.p gamma.x) :=
      DensePoly.ofList
        [gammaCoordinate, (-(shift : Rat)) • (1 : PolyQuot gamma.p gamma.x)]
    let thetaRelation := DensePoly.composeImpl (liftZPoly theta.p) affine
    let alphaRelation : DensePoly (PolyQuot gamma.p gamma.x) :=
      liftZPoly alpha.p
    let common := DensePoly.gcd thetaRelation alphaRelation
    by_cases hlinear :
        (common.degree?.getD 0 = 1 && common.leadingCoeff != 0) = true
    · dsimp [common, thetaRelation, alphaRelation, affine,
        gammaCoordinate] at hlinear
      simp only [hlinear, ↓reduceIte] at h
      exact checkPair?_sound theta alpha gamma _ coordinates h
    · have hfalse :
          (common.degree?.getD 0 = 1 && common.leadingCoeff != 0) = false :=
        Bool.eq_false_of_not_eq_true hlinear
      dsimp [common, thetaRelation, alphaRelation, affine,
        gammaCoordinate] at hfalse
      simp [hfalse] at h

private theorem recoverPair?_isSome (theta alpha gamma : AlgebraicNumber)
    (shift : Int)
    (htheta : theta.toComplex ∈ Rat⟮gamma.toComplex⟯)
    (halpha : alpha.toComplex ∈ Rat⟮gamma.toComplex⟯) :
    (recoverPair? theta alpha gamma shift).isSome := by
  have htrace := tracePair?_isSome theta alpha gamma htheta halpha
  unfold recoverPair?
  cases hfast : recoverPairFast? theta alpha gamma shift with
  | none => simp [htrace]
  | some coordinates => simp

private theorem recoverPair?_sound (theta alpha gamma : AlgebraicNumber)
    (shift : Int)
    {coordinates : PolyQuot gamma.p gamma.x × PolyQuot gamma.p gamma.x}
    (h : recoverPair? theta alpha gamma shift = some coordinates) :
    PolyQuot.toComplex coordinates.1 gamma.rep gamma.rep_mk =
        theta.toComplex ∧
      PolyQuot.toComplex coordinates.2 gamma.rep gamma.rep_mk =
        alpha.toComplex := by
  unfold recoverPair? at h
  cases hfast : recoverPairFast? theta alpha gamma shift with
  | none =>
      rw [hfast] at h
      exact tracePair?_sound theta alpha gamma h
  | some fast =>
      rw [hfast] at h
      have heq := Option.some.inj h
      subst coordinates
      exact recoverPairFast?_sound theta alpha gamma shift hfast

private theorem searchRecoveredAux_coordinates
    (theta alpha : AlgebraicNumber) (target start fuel : Nat)
    {recovered : Recovered}
    (h : searchRecoveredAux theta alpha target start fuel = some recovered) :
    PolyQuot.toComplex recovered.thetaCoordinate recovered.root.rep
          recovered.root.rep_mk = theta.toComplex ∧
      PolyQuot.toComplex recovered.alphaCoordinate recovered.root.rep
          recovered.root.rep_mk = alpha.toComplex := by
  induction fuel generalizing start with
  | zero => simp [searchRecoveredAux] at h
  | succ fuel ih =>
      unfold searchRecoveredAux at h
      cases hcandidate : candidateAt? theta alpha target start with
      | none =>
          rw [hcandidate] at h
          exact ih (start + 1) h
      | some candidate =>
          rw [hcandidate] at h
          simp only at h
          rcases candidate with ⟨shift, root⟩
          cases hrecover : recoverPairFast? theta alpha root shift with
          | none =>
              rw [hrecover] at h
              exact ih (start + 1) h
          | some coordinates =>
              rw [hrecover] at h
              rcases coordinates with ⟨thetaCoordinate, alphaCoordinate⟩
              have heq := Option.some.inj h
              subst recovered
              exact recoverPairFast?_sound theta alpha root shift hrecover

private theorem searchRecovered?_coordinates
    (theta alpha : AlgebraicNumber) (target : Nat) {recovered : Recovered}
    (h : searchRecovered? theta alpha target = some recovered) :
    PolyQuot.toComplex recovered.thetaCoordinate recovered.root.rep
          recovered.root.rep_mk = theta.toComplex ∧
      PolyQuot.toComplex recovered.alphaCoordinate recovered.root.rep
          recovered.root.rep_mk = alpha.toComplex := by
  unfold searchRecovered? at h
  cases hfast : searchRecoveredAux theta alpha target 0
      (flattenShiftCount target) with
  | some fast =>
      rw [hfast] at h
      have heq := Option.some.inj h
      subst recovered
      exact searchRecoveredAux_coordinates theta alpha target 0
        (flattenShiftCount target) hfast
  | none =>
      rw [hfast] at h
      obtain ⟨shifted, hshifted, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨coordinates, hcoordinates, h⟩ :=
        Option.bind_eq_some_iff.mp h
      have heq := Option.some.inj h
      subst recovered
      exact recoverPair?_sound theta alpha shifted.value shifted.shift
        hcoordinates

private theorem represents_map {T : NumberTower}
    (current : Candidate T) (generators : List (Generator T))
    (hcurrent : current.Represents generators)
    (recovered : Recovered)
    (htheta : PolyQuot.toComplex recovered.thetaCoordinate recovered.root.rep
      recovered.root.rep_mk = current.root.toComplex) :
    List.Forall₂
      (fun generator coordinate =>
        PolyQuot.toComplex coordinate recovered.root.rep
          recovered.root.rep_mk = generator.root.toComplex)
      generators
      (current.coordinates.map fun coordinate =>
        evalRatPoly coordinate.coeffs recovered.thetaCoordinate).toList := by
  rw [Array.toList_map]
  unfold Candidate.Represents at hcurrent
  generalize current.coordinates.toList = coordinates at hcurrent ⊢
  induction hcurrent with
  | nil => exact .nil
  | cons hcoordinate htail ih =>
      apply List.Forall₂.cons
      · exact (evalRatPoly_transport current.root recovered.root _ _
          htheta).trans hcoordinate
      · exact ih

private theorem searchRecovered?_isSome (theta alpha : AlgebraicNumber)
    (target : Nat) : (searchRecovered? theta alpha target).isSome := by
  unfold searchRecovered?
  cases hfast : searchRecoveredAux theta alpha target 0
      (flattenShiftCount target) with
  | some recovered => simp
  | none =>
      obtain ⟨shifted, hshifted⟩ := Option.isSome_iff_exists.mp
        (AlgebraicPoly.Common.extendShift?_isSome theta alpha)
      have hfield := AlgebraicPoly.Common.extendShift?_field theta alpha
        shifted hshifted
      have htheta : theta.toComplex ∈ Rat⟮shifted.value.toComplex⟯ := by
        rw [hfield]
        exact IntermediateField.mem_adjoin_pair_left Rat
          theta.toComplex alpha.toComplex
      have halpha : alpha.toComplex ∈ Rat⟮shifted.value.toComplex⟯ := by
        rw [hfield]
        exact IntermediateField.mem_adjoin_pair_right Rat
          theta.toComplex alpha.toComplex
      obtain ⟨coordinates, hcoordinates⟩ := Option.isSome_iff_exists.mp
        (recoverPair?_isSome theta alpha shifted.value shifted.shift
          htheta halpha)
      simp [hshifted, hcoordinates]

private theorem candidateFold_matches (T : NumberTower)
    (generators : List (Generator T)) (current out : Candidate T)
    (hcurrent : current.Matches)
    (hgenerators : ∀ generator ∈ generators, generator.Matches)
    (h : generators.foldlM
      (fun current generator => do
        let target := current.dimension * generator.degree
        let recovered ← searchRecovered? current.root generator.root target
        let value := current.value +
          (recovered.shift : Rat) • generator.value
        let coordinates := current.coordinates.map fun
            (coordinate : PolyQuot current.root.p current.root.x) =>
          evalRatPoly coordinate.coeffs recovered.thetaCoordinate
        some ⟨target, recovered.root, value,
          coordinates.push recovered.alphaCoordinate⟩)
      current = some out) :
    out.Matches := by
  induction generators generalizing current with
  | nil =>
      have heq := Option.some.inj h
      subst out
      exact hcurrent
  | cons generator generators ih =>
      rw [List.foldlM_cons] at h
      obtain ⟨next, hnext, htail⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨recovered, hrecovered, hnext⟩ :=
        Option.bind_eq_some_iff.mp hnext
      have hnextEq := Option.some.inj hnext
      subst next
      have hrecoveredSound := searchRecovered?_sound current.root
        generator.root (current.dimension * generator.degree) hrecovered
      have hgenerator := hgenerators generator (by simp)
      have hnextMatches :
          ({ dimension := current.dimension * generator.degree
             root := recovered.root
             value := current.value +
               (recovered.shift : Rat) • generator.value
             coordinates :=
               (current.coordinates.map fun coordinate =>
                 evalRatPoly coordinate.coeffs
                   recovered.thetaCoordinate).push
                 recovered.alphaCoordinate } : Candidate T).Matches := by
        unfold Candidate.Matches
        rw [map_add, map_smul, hcurrent, hgenerator,
          hrecoveredSound]
      exact ih _ hnextMatches
        (fun later hlater => hgenerators later (by simp [hlater])) htail

private theorem candidateFold_represents (T : NumberTower)
    (processed generators : List (Generator T)) (current out : Candidate T)
    (hcurrent : current.Represents processed)
    (h : generators.foldlM
      (fun current generator => do
        let target := current.dimension * generator.degree
        let recovered ← searchRecovered? current.root generator.root target
        let value := current.value +
          (recovered.shift : Rat) • generator.value
        let coordinates := current.coordinates.map fun coordinate =>
          evalRatPoly coordinate.coeffs recovered.thetaCoordinate
        some ⟨target, recovered.root, value,
          coordinates.push recovered.alphaCoordinate⟩)
      current = some out) :
    out.Represents (processed ++ generators) := by
  induction generators generalizing processed current with
  | nil =>
      have heq := Option.some.inj h
      subst out
      simpa using hcurrent
  | cons generator generators ih =>
      rw [List.foldlM_cons] at h
      obtain ⟨next, hnext, htail⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨recovered, hrecovered, hnext⟩ :=
        Option.bind_eq_some_iff.mp hnext
      have hnextEq := Option.some.inj hnext
      subst next
      have hcoordinates := searchRecovered?_coordinates current.root
        generator.root (current.dimension * generator.degree) hrecovered
      have hmapped := represents_map current processed hcurrent recovered
        hcoordinates.1
      have hnextRepresents :
          ({ dimension := current.dimension * generator.degree
             root := recovered.root
             value := current.value +
               (recovered.shift : Rat) • generator.value
             coordinates :=
               (current.coordinates.map fun coordinate =>
                 evalRatPoly coordinate.coeffs
                   recovered.thetaCoordinate).push
                 recovered.alphaCoordinate } : Candidate T).Represents
            (processed ++ [generator]) := by
        unfold Candidate.Represents
        rw [Array.toList_push]
        exact List.rel_append hmapped
          (List.Forall₂.cons hcoordinates.2 List.Forall₂.nil)
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        ih (processed ++ [generator]) _ hnextRepresents htail

private theorem candidateFold_isSome (T : NumberTower)
    (generators : List (Generator T)) (current : Candidate T) :
    (generators.foldlM
      (fun (current : Candidate T) (generator : Generator T) => do
        let target := current.dimension * generator.degree
        let recovered ← searchRecovered? current.root generator.root target
        let value := current.value +
          (recovered.shift : Rat) • generator.value
        let coordinates := current.coordinates.map fun
            (coordinate : PolyQuot current.root.p current.root.x) =>
          evalRatPoly coordinate.coeffs recovered.thetaCoordinate
        some ⟨target, recovered.root, value,
          coordinates.push recovered.alphaCoordinate⟩)
      current).isSome := by
  induction generators generalizing current with
  | nil => simp
  | cons generator generators ih =>
      rw [List.foldlM_cons]
      obtain ⟨recovered, hrecovered⟩ := Option.isSome_iff_exists.mp
        (searchRecovered?_isSome current.root generator.root
          (current.dimension * generator.degree))
      let next : Candidate T :=
        { dimension := current.dimension * generator.degree
          root := recovered.root
          value := current.value +
            (recovered.shift : Rat) • generator.value
          coordinates :=
            (current.coordinates.map fun coordinate =>
              evalRatPoly coordinate.coeffs
                recovered.thetaCoordinate).push
              recovered.alphaCoordinate }
      simpa [hrecovered, next] using ih next

private theorem candidateFold_shape (T : NumberTower)
    (generators : List (Generator T)) (current out : Candidate T)
    (h : generators.foldlM
      (fun current generator => do
        let target := current.dimension * generator.degree
        let recovered ← searchRecovered? current.root generator.root target
        let value := current.value +
          (recovered.shift : Rat) • generator.value
        let coordinates := current.coordinates.map fun coordinate =>
          evalRatPoly coordinate.coeffs recovered.thetaCoordinate
        some ⟨target, recovered.root, value,
          coordinates.push recovered.alphaCoordinate⟩)
      current = some out) :
    out.dimension = current.dimension *
        (generators.map Generator.degree).prod ∧
      out.coordinates.size = current.coordinates.size + generators.length := by
  induction generators generalizing current with
  | nil =>
      have heq := Option.some.inj h
      subst out
      simp
  | cons generator generators ih =>
      rw [List.foldlM_cons] at h
      obtain ⟨next, hnext, htail⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨recovered, hrecovered, hnext⟩ :=
        Option.bind_eq_some_iff.mp hnext
      have hnextEq := Option.some.inj hnext
      subst next
      obtain ⟨hdimension, hcoordinates⟩ := ih _ htail
      constructor
      · simpa [Nat.mul_assoc] using hdimension
      · simp only [List.length_cons]
        simp at hcoordinates
        omega

private theorem candidate?_isSome (T : NumberTower)
    (generators : Array (Generator T)) :
    (candidate? generators).isSome := by
  unfold candidate?
  cases hfirst : generators[0]? with
  | none => simp
  | some first =>
      simpa only using candidateFold_isSome T (generators.toList.drop 1)
        { dimension := first.degree
          root := first.root
          value := first.value
          coordinates := #[first.root.toQAdjoin] }

private theorem candidate?_shape (T : NumberTower)
    (generators : Array (Generator T)) {candidate : Candidate T}
    (h : candidate? generators = some candidate) :
    candidate.dimension =
        (generators.toList.map Generator.degree).prod ∧
      candidate.coordinates.size = generators.size := by
  unfold candidate? at h
  cases hfirst : generators[0]? with
  | none =>
      rw [hfirst] at h
      have heq := Option.some.inj h
      subst candidate
      have hsize : generators.size ≤ 0 :=
        Array.getElem?_eq_none_iff.mp hfirst
      have hempty : generators.toList = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using Nat.eq_zero_of_le_zero hsize
      simp [hempty, Nat.eq_zero_of_le_zero hsize]
  | some first =>
      rw [hfirst] at h
      have hnonempty : generators.toList ≠ [] := by
        intro hempty
        have hsize : generators.size = 0 := by
          simpa using congrArg List.length hempty
        have : generators[0]? = none :=
          Array.getElem?_eq_none_iff.mpr (by omega)
        rw [hfirst] at this
        contradiction
      obtain ⟨head, tail, hlist⟩ := List.exists_cons_of_ne_nil hnonempty
      have hhead : head = first := by
        have hfirst' := hfirst
        rw [← Array.getElem?_toList, hlist] at hfirst'
        simpa using Option.some.inj hfirst'
      subst head
      have htail : generators.toList.drop 1 = tail := by
        rw [hlist]
        rfl
      rw [htail] at h
      obtain ⟨hdimension, hcoordinates⟩ := candidateFold_shape T tail
        { dimension := first.degree
          root := first.root
          value := first.value
          coordinates := #[first.root.toQAdjoin] }
        candidate h
      constructor
      · simpa [hlist] using hdimension
      · have hgensize : generators.size = 1 + tail.length := by
          have := congrArg List.length hlist
          simpa [Nat.add_comm] using this
        simp at hcoordinates
        omega

private theorem candidate?_matches (T : NumberTower)
    (generators : Array (Generator T))
    (hgenerators : ∀ generator ∈ generators.toList, generator.Matches)
    {candidate : Candidate T} (h : candidate? generators = some candidate) :
    candidate.Matches := by
  unfold candidate? at h
  cases hfirst : generators[0]? with
  | none =>
      rw [hfirst] at h
      have heq := Option.some.inj h
      subst candidate
      unfold Candidate.Matches
      change T.toComplex 0 = AlgebraicNumber.zero.toComplex
      rw [map_zero, AlgebraicNumber.zero_eq_zero,
        AlgebraicNumber.zero_toComplex]
  | some first =>
      rw [hfirst] at h
      apply candidateFold_matches T (generators.toList.drop 1)
        { dimension := first.degree
          root := first.root
          value := first.value
          coordinates := #[first.root.toQAdjoin] }
        candidate
      · apply hgenerators first
        apply Array.mem_toList_iff.mpr
        rw [Array.mem_iff_getElem]
        exact ⟨0, (Array.getElem?_eq_some_iff.mp hfirst).1,
          (Array.getElem?_eq_some_iff.mp hfirst).2⟩
      · intro generator hgenerator
        exact hgenerators generator (List.mem_of_mem_drop hgenerator)
      · exact h

private theorem candidate?_represents (T : NumberTower)
    (generators : Array (Generator T)) {candidate : Candidate T}
    (h : candidate? generators = some candidate) :
    candidate.Represents generators.toList := by
  unfold candidate? at h
  cases hfirst : generators[0]? with
  | none =>
      rw [hfirst] at h
      have heq := Option.some.inj h
      subst candidate
      have hsize : generators.size ≤ 0 :=
        Array.getElem?_eq_none_iff.mp hfirst
      have hempty : generators.toList = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using Nat.eq_zero_of_le_zero hsize
      rw [hempty]
      exact List.Forall₂.nil
  | some first =>
      rw [hfirst] at h
      have hnonempty : generators.toList ≠ [] := by
        intro hempty
        have hsize : generators.size = 0 := by simpa using congrArg List.length hempty
        have : generators[0]? = none :=
          Array.getElem?_eq_none_iff.mpr (by omega)
        rw [hfirst] at this
        contradiction
      obtain ⟨head, tail, hlist⟩ := List.exists_cons_of_ne_nil hnonempty
      have hhead : head = first := by
        have hfirst' := hfirst
        rw [← Array.getElem?_toList, hlist] at hfirst'
        simpa using Option.some.inj hfirst'
      subst head
      have hinitial :
          ({ dimension := first.degree
             root := first.root
             value := first.value
             coordinates := #[first.root.toQAdjoin] } : Candidate T).Represents
            [first] := by
        unfold Candidate.Represents
        change List.Forall₂ _ [first] [first.root.toQAdjoin]
        exact List.Forall₂.cons (toQAdjoin_complex first.root)
          List.Forall₂.nil
      have htail : generators.toList.drop 1 = tail := by
        rw [hlist]
        rfl
      rw [htail] at h
      simpa [hlist] using candidateFold_represents T [first] tail
        { dimension := first.degree
          root := first.root
          value := first.value
          coordinates := #[first.root.toQAdjoin] }
        candidate hinitial h

private theorem extendBasis_size {p : ZPoly} {x : SimpleRoot p}
    (basis : Array (PolyQuot p x)) (generator : PolyQuot p x)
    (degree : Nat) :
    (extendBasis basis generator degree).size = basis.size * degree := by
  unfold extendBasis
  let indices := List.range degree
  change ((indices.foldl
      (fun state _ =>
        (state.1 ++ basis.map fun b => b * state.2,
          state.2 * generator)) (#[], 1)).1).size = basis.size * degree
  have hfold : ∀ (entries : List Nat)
      (state : Array (PolyQuot p x) × PolyQuot p x),
      ((entries.foldl
        (fun state _ =>
          (state.1 ++ basis.map fun b => b * state.2,
            state.2 * generator)) state).1).size =
        state.1.size + entries.length * basis.size := by
    intro entries
    induction entries with
    | nil => simp
    | cons index entries ih =>
        intro state
        rw [List.foldl_cons, ih]
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simpa [indices, Nat.mul_comm] using hfold indices (#[], 1)

private theorem zip_degrees (generators : List (Generator T))
    (coordinates : List A) (hsize : generators.length = coordinates.length) :
    ((generators.zip coordinates).map fun entry => entry.1.degree) =
      generators.map Generator.degree := by
  induction generators generalizing coordinates with
  | nil => simp
  | cons generator generators ih =>
      cases coordinates with
      | nil => simp at hsize
      | cons coordinate coordinates =>
          simp only [List.length_cons, Nat.succ.injEq] at hsize
          simp [ih coordinates hsize]

private theorem basisImages_size {T : NumberTower} {p : ZPoly}
    {x : SimpleRoot p} (generators : Array (Generator T))
    (coordinates : Array (PolyQuot p x))
    (hsize : coordinates.size = generators.size) :
    (basisImages generators coordinates).size =
      (generators.toList.map Generator.degree).prod := by
  unfold basisImages
  rw [← Array.foldl_toList]
  have hfold : ∀ (entries : List (Generator T × PolyQuot p x))
      (basis : Array (PolyQuot p x)),
      (entries.foldl
        (fun basis entry => extendBasis basis entry.2 entry.1.degree)
        basis).size =
          basis.size * (entries.map fun entry => entry.1.degree).prod := by
    intro entries
    induction entries with
    | nil => intro basis; simp
    | cons entry entries ih =>
        intro basis
        rw [List.foldl_cons, ih, extendBasis_size]
        simp [Nat.mul_assoc]
  rw [hfold]
  simp only [Array.toList_zip]
  have hlength : generators.toList.length = coordinates.toList.length := by
    simpa using hsize.symm
  rw [zip_degrees generators.toList coordinates.toList hlength]
  simp

/-- Complex power-block enumeration in the same oldest-generator-fastest
order as `extendBasis`. -/
private noncomputable def extendValues (basis : Array ℂ) (generator : ℂ)
    (degree : Nat) : Array ℂ :=
  let state := (List.range degree).foldl
    (fun state _ =>
      (state.1 ++ basis.map fun b => b * state.2,
        state.2 * generator))
    (#[], 1)
  state.1

private theorem extendValues_size (basis : Array ℂ) (generator : ℂ)
    (degree : Nat) :
    (extendValues basis generator degree).size = basis.size * degree := by
  unfold extendValues
  let indices := List.range degree
  change ((indices.foldl
      (fun state _ =>
        (state.1 ++ basis.map fun b => b * state.2,
          state.2 * generator)) (#[], 1)).1).size = basis.size * degree
  have hfold : ∀ (entries : List Nat) (state : Array ℂ × ℂ),
      ((entries.foldl
        (fun state _ =>
          (state.1 ++ basis.map fun b => b * state.2,
            state.2 * generator)) state).1).size =
        state.1.size + entries.length * basis.size := by
    intro entries
    induction entries with
    | nil => simp
    | cons index entries ih =>
        intro state
        rw [List.foldl_cons, ih]
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simpa [indices, Nat.mul_comm] using hfold indices (#[], 1)

private theorem extendValues_blocks (basis : Array ℂ) (generator : ℂ)
    (degree : Nat) :
    extendValues basis generator degree =
      (List.range degree).toArray.flatMap fun exponent =>
        basis.map fun b => b * generator ^ exponent := by
  unfold extendValues
  have hfold : ∀ n,
      (List.range n).foldl
          (fun state _ =>
            (state.1 ++ basis.map fun b => b * state.2,
              state.2 * generator)) (#[], 1) =
        ((List.range n).toArray.flatMap fun exponent =>
            basis.map fun b => b * generator ^ exponent,
          generator ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [List.range_succ, List.foldl_append, ih]
        simp [pow_succ]
  exact congrArg Prod.fst (hfold degree)

private noncomputable def levelBasis :
    (levels : List Level) → Vector ℂ (levelsDim levels)
  | [] => ⟨#[1], by simp [levelsDim]⟩
  | level :: lower =>
      ⟨extendValues (levelBasis lower).toArray level.root.toComplex
          level.degree,
        by rw [extendValues_size]; simp [levelsDim, Nat.mul_comm]⟩

private theorem blockIndex_iff (index exponent width offset : Nat)
    (hwidth : 0 < width) (hoffset : offset < width) :
    index = exponent * width + offset ↔
      index / width = exponent ∧ index % width = offset := by
  constructor
  · intro h
    subst index
    constructor
    · rw [Nat.add_comm, Nat.mul_comm exponent width,
        Nat.add_mul_div_left offset exponent hwidth,
        Nat.div_eq_of_lt hoffset]
      simp
    · rw [Nat.add_comm, Nat.mul_comm exponent width,
        Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hoffset]
  · rintro ⟨hdiv, hmod⟩
    rw [← Nat.mod_add_div index width, hdiv, hmod]
    simp [Nat.add_comm, Nat.mul_comm]

private theorem block_unitCoords (degree width index exponent : Nat)
    (hwidth : 0 < width) (_hindex : index < degree * width)
    (hexponent : exponent < degree) :
    Arithmetic.block (unitCoords (degree * width) index) exponent width =
      if exponent = index / width then unitCoords width (index % width)
      else Arithmetic.fixedCoeffs width #[] := by
  apply Array.ext
  · by_cases heq : exponent = index / width
    · simp [Arithmetic.block, heq, unitCoords]
    · simp [Arithmetic.block, heq, Arithmetic.fixedCoeffs]
  · intro offset hleft hright
    have hoffset : offset < width := by
      simpa [Arithmetic.block] using hleft
    have hglobal : exponent * width + offset < degree * width := by
      calc
        exponent * width + offset < exponent * width + width :=
          Nat.add_lt_add_left hoffset _
        _ = (exponent + 1) * width := by simp [Nat.add_mul]
        _ ≤ degree * width :=
          Nat.mul_le_mul_right width (Nat.succ_le_of_lt hexponent)
    simp only [Arithmetic.block, Vector.getElem_toArray,
      Vector.getElem_ofFn]
    rw [unitCoords_getD]
    by_cases heq : exponent = index / width
    · simp only [ite_eq_left heq] at hright ⊢
      rw [unitCoords_getElem width (index % width) offset hoffset]
      by_cases hsame : index % width = offset
      · have hposition := (blockIndex_iff index exponent width offset
          hwidth hoffset).mpr ⟨heq.symm, hsame⟩
        simp [hglobal, hposition, Nat.mod_eq_of_lt hoffset]
      · have hposition : index ≠ exponent * width + offset := by
          intro hposition
          exact hsame ((blockIndex_iff index exponent width offset
            hwidth hoffset).mp hposition).2
        simp [hglobal, hposition, hsame]
    · simp only [ite_eq_right heq] at hright ⊢
      simp only [Arithmetic.fixedCoeffs, Vector.getElem_toArray,
        Vector.getElem_ofFn, Array.getD, Array.size_empty,
        Nat.not_lt_zero]
      simp only [hglobal, true_and]
      have hne : index ≠ exponent * width + offset := by
        intro hsame
        exact heq ((blockIndex_iff index exponent width offset
          hwidth hoffset).mp hsame).1.symm
      simp [hne]

private theorem extendValues_get (basis : Array ℂ) (generator : ℂ)
    (degree width index : Nat) (hsize : basis.size = width)
    (hwidth : 0 < width) (hindex : index < degree * width) :
    (extendValues basis generator degree)[index]'(by
      rw [extendValues_size, hsize]
      simpa [Nat.mul_comm] using hindex) =
      basis[index % width]'(by rw [hsize]; exact Nat.mod_lt _ hwidth) *
        generator ^ (index / width) := by
  let basisVector : Vector ℂ width := ⟨basis, hsize⟩
  let exponents : Vector Nat degree :=
    ⟨(List.range degree).toArray, by simp⟩
  have hextend : extendValues basis generator degree =
      (exponents.flatMap fun exponent =>
        basisVector.map fun b => b * generator ^ exponent).toArray := by
    rw [extendValues_blocks]
    simp [exponents, basisVector]
  simp only [hextend]
  change (exponents.flatMap fun exponent =>
      basisVector.map fun b => b * generator ^ exponent)[index] = _
  rw [Vector.getElem_flatMap]
  simp [exponents, basisVector]

private theorem levelBasis_get (levels : List Level) (hvalid : LevelsValid levels)
    (index : Nat) (hindex : index < levelsDim levels) :
    (levelBasis levels)[index] =
      LevelSemantics.denote levels (unitCoords (levelsDim levels) index) := by
  induction levels generalizing index with
  | nil =>
      have hzero : index = 0 := by simpa [levelsDim] using hindex
      subst index
      simp [levelBasis, LevelSemantics.denote, unitCoords, Array.getD,
        levelsDim]
  | cons level lower ih =>
      let width := levelsDim lower
      have hwidth : 0 < width := levelsDim_pos lower hvalid.2.2
      have hquot : index / width < level.degree := by
        rw [Nat.div_lt_iff_lt_mul hwidth]
        simpa [width, levelsDim] using hindex
      have hmod : index % width < width := Nat.mod_lt _ hwidth
      change (extendValues (levelBasis lower).toArray level.root.toComplex
          level.degree)[index]'(by
            rw [extendValues_size]
            simpa [width, levelsDim, Nat.mul_comm] using hindex) = _
      rw [extendValues_get (levelBasis lower).toArray level.root.toComplex
        level.degree width index (by simp [width]) hwidth (by
          simpa [width, levelsDim] using hindex)]
      change (levelBasis lower)[index % width] *
        level.root.toComplex ^ (index / width) = _
      rw [ih hvalid.2.2 (index % width) (by simpa [width] using hmod)]
      rw [LevelSemantics.denote_cons]
      rw [Finset.sum_eq_single (index / width)]
      · change _ = LevelSemantics.denote lower
          (Arithmetic.block (unitCoords (level.degree * width) index)
            (index / width) width) * _
        rw [block_unitCoords level.degree width index (index / width)
          hwidth (by simpa [width, levelsDim] using hindex) hquot]
        simp [width]
      · intro exponent hexponent hne
        have hexponent' : exponent < level.degree := Finset.mem_range.mp hexponent
        change LevelSemantics.denote lower
          (Arithmetic.block (unitCoords (level.degree * width) index)
            exponent width) * level.root.toComplex ^ exponent = 0
        rw [block_unitCoords level.degree width index exponent hwidth
          (by simpa [width, levelsDim] using hindex) hexponent']
        rw [ite_eq_right hne]
        change LevelSemantics.denote lower
          (Arithmetic.fixedCoeffs (levelsDim lower) #[]) *
            level.root.toComplex ^ exponent = 0
        rw [LevelSemantics.denote_zero]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hquot)).elim

private theorem extendBasis_values {p : ZPoly} {x : SimpleRoot p}
    (basis : Array (PolyQuot p x)) (generator : PolyQuot p x)
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = x)
    (z : ℂ) (hgenerator : PolyQuot.toComplex generator rep hrep = z)
    (degree : Nat) :
    (extendBasis basis generator degree).map
        (fun a => PolyQuot.toComplex a rep hrep) =
      extendValues
        (basis.map fun a => PolyQuot.toComplex a rep hrep) z degree := by
  unfold extendBasis extendValues
  generalize List.range degree = entries
  have hfold : ∀ (entries : List Nat)
      (qstate : Array (PolyQuot p x) × PolyQuot p x)
      (cstate : Array ℂ × ℂ),
      qstate.1.map (fun a => PolyQuot.toComplex a rep hrep) = cstate.1 →
      PolyQuot.toComplex qstate.2 rep hrep = cstate.2 →
      ((entries.foldl
        (fun state _ =>
          (state.1 ++ basis.map fun b => b * state.2,
            state.2 * generator)) qstate).1).map
          (fun a => PolyQuot.toComplex a rep hrep) =
        (entries.foldl
          (fun state _ =>
            (state.1 ++
                (basis.map fun a => PolyQuot.toComplex a rep hrep).map
                  fun b => b * state.2,
              state.2 * z)) cstate).1 := by
    intro entries
    induction entries with
    | nil => intro qstate cstate houtput hpower; exact houtput
    | cons entry entries ih =>
        intro qstate cstate houtput hpower
        rw [List.foldl_cons, List.foldl_cons]
        apply ih
        · simp only [Array.map_append, Array.map_map]
          rw [houtput]
          congr 1
          apply Array.ext
          · simp
          · intro i hleft hright
            simp [Function.comp_def, PolyQuot.map_mul, hpower]
        · simp [PolyQuot.map_mul, hpower, hgenerator]
  exact hfold entries (#[], 1) (#[], 1)
    (by simp) (PolyQuot.map_one rep hrep)

private theorem basisFold_values {T : NumberTower} {p : ZPoly}
    {x : SimpleRoot p} (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = x)
    {generators : List (Generator T)}
    {coordinates : List (PolyQuot p x)} {levels : List Level}
    (hcoordinates : List.Forall₂
      (fun generator coordinate =>
        PolyQuot.toComplex coordinate rep hrep = generator.root.toComplex)
      generators coordinates)
    (hlevels : List.Forall₂ Generator.Describes generators levels)
    (qbasis : Array (PolyQuot p x)) (cbasis : Array ℂ)
    (hbasis : qbasis.map (fun a => PolyQuot.toComplex a rep hrep) = cbasis) :
    ((generators.zip coordinates).foldl
      (fun basis entry => extendBasis basis entry.2 entry.1.degree)
      qbasis).map (fun a => PolyQuot.toComplex a rep hrep) =
      levels.foldl
        (fun basis level =>
          extendValues basis level.root.toComplex level.degree) cbasis := by
  induction hcoordinates generalizing levels qbasis cbasis with
  | nil =>
      cases hlevels
      exact hbasis
  | cons hcoordinate hcoordinates ih =>
      cases hlevels with
      | cons hlevel hlevels =>
          rcases hlevel with ⟨hdegree, hroot⟩
          simp only [List.zip_cons_cons, List.foldl_cons]
          apply ih hlevels
          rw [hdegree]
          calc
            _ = extendValues
                (qbasis.map fun a => PolyQuot.toComplex a rep hrep)
                _ _ := extendBasis_values qbasis _ rep hrep _
                  (hcoordinate.trans hroot) _
            _ = _ := by rw [hbasis]

private theorem levelBasis_fold (levels : List Level) :
    levels.reverse.foldl
        (fun basis level =>
          extendValues basis level.root.toComplex level.degree) #[1] =
      (levelBasis levels).toArray := by
  induction levels with
  | nil => rfl
  | cons level lower ih =>
      rw [List.reverse_cons, List.foldl_append, ih]
      rfl

private theorem basisImages_values {T : NumberTower}
    (generators : Array (Generator T)) (candidate : Candidate T)
    (hcoordinates : candidate.Represents generators.toList)
    (hlevels : List.Forall₂ Generator.Describes generators.toList
      T.levels.toList.reverse) :
    (basisImages generators candidate.coordinates).map
        (fun a => PolyQuot.toComplex a candidate.root.rep
          candidate.root.rep_mk) =
      (levelBasis T.levels.toList).toArray := by
  unfold basisImages
  rw [← Array.foldl_toList]
  simp only [Array.toList_zip]
  unfold Candidate.Represents at hcoordinates
  calc
    _ = T.levels.toList.reverse.foldl
        (fun basis level =>
          extendValues basis level.root.toComplex level.degree) #[1] := by
      apply basisFold_values candidate.root.rep candidate.root.rep_mk
        hcoordinates hlevels #[1] #[1]
      apply Array.ext
      · simp
      · intro i hleft hright
        have hi : i = 0 := by simpa using hleft
        subst i
        simpa using PolyQuot.map_one candidate.root.rep candidate.root.rep_mk
    _ = _ := levelBasis_fold T.levels.toList

private theorem one_smul_qadjoin {p : ZPoly} {x : SimpleRoot p}
    [ZPoly.CheckedIrreducible p] (a : PolyQuot p x) :
    (1 : Rat) • a = a := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  apply PolyQuot.toComplex_injective rep hrep
  change PolyQuot.toComplex ((1 : Rat) • a) rep hrep =
    PolyQuot.toComplex a rep hrep
  rw [PolyQuot.map_smul]
  simp

private theorem foldl_congr_mem {α β : Type} (xs : List α)
    (f g : β → α → β) (initial : β)
    (h : ∀ value a, a ∈ xs → f value a = g value a) :
    xs.foldl f initial = xs.foldl g initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.foldl_cons]
      rw [h initial a (by simp)]
      apply ih
      intro value b hb
      exact h value b (by simp [hb])

private theorem fold_unit_range {p : ZPoly} {x : SimpleRoot p}
    [ZPoly.CheckedIrreducible p]
    (values : Nat → PolyQuot p x) (index count : Nat) :
    (List.range count).foldl (fun value i =>
      if index = i then value + (1 : Rat) • values i else value) 0 =
        if index < count then values index else 0 := by
  let : Field (PolyQuot p x) := PolyQuot.field p x
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hlt : index < count
      · have hne : index ≠ count := by omega
        have hle : index ≤ count := Nat.le_of_lt hlt
        simp [hlt, hne, hle]
      · by_cases heq : index = count
        · subst index
          simp [one_smul_qadjoin]
        · have hout : ¬ index < count + 1 := by omega
          simp [hlt, heq, hout]

private theorem toPrimitiveWith_unit {T : NumberTower} {p : ZPoly}
    {x : SimpleRoot p} (images : Array (PolyQuot p x))
    [ZPoly.CheckedIrreducible p]
    (index : Nat) (hindex : index < T.dim) :
    toPrimitiveWith images (T.ofCoeffs (unitCoords T.dim index)) =
      images.getD index 0 := by
  unfold toPrimitiveWith
  rw [coeffs_ofCoeffs,
    normalizeCoeffs_eq_self T _ (by simp [unitCoords])]
  rw [foldl_congr_mem (List.range T.dim) _
    (fun value i =>
      if index = i then value + (1 : Rat) • images.getD i 0 else value) 0
    (by
      intro value i hi
      rw [unitCoords_getD]
      by_cases heq : index = i
      · simp [List.mem_range.mp hi, heq]
      · simp [List.mem_range.mp hi, heq])]
  rw [fold_unit_range]
  simp [hindex]

private theorem basisImages_complex (T : NumberTower)
    (generators : Array (Generator T)) (candidate : Candidate T)
    (hgenerators : generators? T = some generators)
    (hcandidate : candidate? generators = some candidate)
    (index : Nat) (hindex : index < T.dim) :
    PolyQuot.toComplex
        (basisImages generators candidate.coordinates |>.getD index 0)
        candidate.root.rep candidate.root.rep_mk =
      T.toComplex (T.ofCoeffs (unitCoords T.dim index)) := by
  let : ZPoly.CheckedIrreducible candidate.root.p := candidate.root.checked
  have hgeneratorShape := generators?_shape T hgenerators
  have hcandidateShape := candidate?_shape T generators hcandidate
  have hcoordinates := candidate?_represents T generators hcandidate
  have hlevels := generators?_levels T hgenerators
  have hvalues := basisImages_values generators candidate hcoordinates hlevels
  let images := basisImages generators candidate.coordinates
  have hvalues' : images.map
      (fun a => PolyQuot.toComplex a candidate.root.rep
        candidate.root.rep_mk) =
      (levelBasis T.levels.toList).toArray := hvalues
  have himages : images.size = T.dim := by
    change (basisImages generators candidate.coordinates).size = T.dim
    rw [basisImages_size generators candidate.coordinates]
    · exact hgeneratorShape.2
    · exact hcandidateShape.2
  have hget := congrArg (fun values : Array ℂ => values.getD index 0) hvalues'
  have hlevelSize : (levelBasis T.levels.toList).toArray.size = T.dim := by
    simp [dim]
  simp only [Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem, Array.size_map, himages, hindex,
    hlevelSize, Option.getD_some] at hget
  change PolyQuot.toComplex (images.getD index 0) candidate.root.rep
    candidate.root.rep_mk = _
  rw [← Array.getElem_eq_getD (0 : PolyQuot candidate.root.p
    candidate.root.x) (h := by rw [himages]; exact hindex)]
  have hget' : PolyQuot.toComplex
      (images[index]'(by rw [himages]; exact hindex))
      candidate.root.rep candidate.root.rep_mk =
      ((levelBasis T.levels.toList).toArray[index]'(by
        rw [hlevelSize]; exact hindex)) := by
    simpa using hget
  rw [hget']
  change (levelBasis T.levels.toList)[index]'(by
    simpa [dim] using hindex) = _
  calc
    _ = LevelSemantics.denote T.levels.toList
        (unitCoords (levelsDim T.levels.toList) index) :=
      levelBasis_get T.levels.toList T.valid index (by
        simpa [dim] using hindex)
    _ = T.toComplex (T.ofCoeffs (unitCoords T.dim index)) := by
      rw [LevelSemantics.toComplex_eq_denote, coeffs_ofCoeffs,
        normalizeCoeffs_eq_self T _ (by simp [unitCoords])]
      rfl

private theorem constructed_basis_roundtrip (T : NumberTower)
    (generators : Array (Generator T)) (candidate : Candidate T)
    (hgenerators : generators? T = some generators)
    (hcandidate : candidate? generators = some candidate)
    (index : Nat) (hindex : index < T.dim) :
    fromPrimitiveWith candidate.value
        (toPrimitiveWith (basisImages generators candidate.coordinates)
          (T.ofCoeffs (unitCoords T.dim index))) =
      T.ofCoeffs (unitCoords T.dim index) := by
  let : ZPoly.CheckedIrreducible candidate.root.p := candidate.root.checked
  rw [toPrimitiveWith_unit _ index hindex]
  apply toComplex_injective T
  rw [fromPrimitiveWith_complex candidate.value candidate.root.rep
    candidate.root.rep_mk]
  · exact basisImages_complex T generators candidate hgenerators hcandidate
      index hindex
  · exact candidate?_matches T generators
      (generators?_sound T hgenerators) hcandidate

private theorem certifies_basis {T : NumberTower} (candidate : Candidate T)
    (images : Array (PolyQuot candidate.root.p candidate.root.x))
    (hcert : certifies candidate images = true) (i : Nat) (hi : i < T.dim) :
    fromPrimitiveWith candidate.value
        (toPrimitiveWith images (T.ofCoeffs (unitCoords T.dim i))) =
      T.ofCoeffs (unitCoords T.dim i) := by
  simp only [certifies, Bool.and_eq_true] at hcert
  have hround := List.all_eq_true.mp hcert.1.2 i
    (List.mem_range.mpr hi)
  simpa only [beq_iff_eq] using hround

end Flatten

/-- Every returned primitive presentation has inverse coordinate maps,
preserves arithmetic, and commutes with the fixed complex embeddings. -/
theorem flatten?_sound (T : NumberTower) {F : Flattening T}
    (h : T.flatten? = some F) :
    F.Sound := by
  unfold NumberTower.flatten? at h
  obtain ⟨generators, hgenerators, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨candidate, hcandidate, h⟩ := Option.bind_eq_some_iff.mp h
  let images := Flatten.basisImages generators candidate.coordinates
  change (if Flatten.certifies candidate images then
      some
        { root := candidate.root
          toPrimitive := Flatten.toPrimitiveWith images
          fromPrimitive := Flatten.fromPrimitiveWith candidate.value }
    else none) = some F at h
  by_cases hcert : Flatten.certifies candidate images = true
  · simp only [hcert, ↓reduceIte, Option.some.injEq] at h
    subst F
    have hgeneratorsSound := Flatten.generators?_sound T hgenerators
    have hcandidateSound := Flatten.candidate?_matches T generators
      hgeneratorsSound hcandidate
    let : ZPoly.CheckedIrreducible candidate.root.p :=
      candidate.root.checked
    let rep := candidate.root.rep
    have hrep : SimpleRoot.mk rep = candidate.root.x :=
      candidate.root.rep_mk
    let : Field (Elem T) := elemField T
    let towerAdd : Elem T →+ ℂ :=
      { toFun := T.toComplex
        map_zero' := by
          change T.toComplex (0 : Elem T) = 0
          exact map_zero T
        map_add' := by
          intro a b
          change T.toComplex (a + b) = T.toComplex a + T.toComplex b
          exact map_add T a b }
    let : Module Rat (Elem T) :=
      Function.Injective.module Rat towerAdd (toComplex_injective T)
        (fun q a => by
          change T.toComplex (q • a) = q • T.toComplex a
          simpa only [Rat.smul_def] using map_smul T q a)
    let coordinates : Elem T ≃ₗ[Rat] (Fin T.dim → Rat) :=
      { toFun := fun a i => (coeffs a).getD i 0
        invFun := fun f => T.ofCoeffs (Array.ofFn f)
        left_inv := by
          intro a
          apply Elem.ext
          rw [coeffs_ofCoeffs, normalizeCoeffs_eq_self T _ (by simp)]
          apply Array.ext
          · simp
          · intro i hi₁ hi₂
            simp
        right_inv := by
          intro f
          funext i
          change (coeffs (T.ofCoeffs (Array.ofFn f))).getD i 0 = f i
          rw [coeffs_ofCoeffs, normalizeCoeffs_eq_self T _ (by simp)]
          simp [Array.getD, i.isLt]
        map_add' := by
          intro a b
          funext i
          change (coeffs (a + b)).getD i 0 =
            (coeffs a).getD i 0 + (coeffs b).getD i 0
          rw [coeffs_add]
          simp [Arithmetic.addCoords, Array.getD, i.isLt]
        map_smul' := by
          intro q a
          funext i
          change (coeffs (q • a)).getD i 0 =
            q * (coeffs a).getD i 0
          rw [coeffs_smul]
          simp [Array.getD, i.isLt] }
    let basis : Module.Basis (Fin T.dim) Rat (Elem T) :=
      Module.Basis.ofEquivFun coordinates
    have hbasis (i : Fin T.dim) :
        basis i = T.ofCoeffs (Flatten.unitCoords T.dim i) := by
      rw [Module.Basis.coe_ofEquivFun]
      apply coordinates.injective
      rw [LinearEquiv.apply_symm_apply]
      funext j
      change (Pi.single i (1 : Rat) : Fin T.dim → Rat) j =
        (coeffs (T.ofCoeffs (Flatten.unitCoords T.dim i))).getD j 0
      rw [coeffs_ofCoeffs,
        normalizeCoeffs_eq_self T _ (by simp [Flatten.unitCoords])]
      rw [Flatten.unitCoords_getD]
      by_cases hij : i = j
      · subst j
        simp
      · have hji : j ≠ i := Ne.symm hij
        have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
        simp [hji, hval, j.isLt]
    let towerMap : Elem T →ₗ[Rat] ℂ :=
      { toFun := T.toComplex
        map_add' := map_add T
        map_smul' := by
          intro q a
          simpa only [RingHom.id_apply, Rat.smul_def] using map_smul T q a }
    let primitiveMap : Elem T →ₗ[Rat] ℂ :=
      { toFun := fun a => PolyQuot.toComplex
          (Flatten.toPrimitiveWith images a) rep hrep
        map_add' := by
          intro a b
          rw [Flatten.toPrimitiveWith_add, PolyQuot.map_add]
        map_smul' := by
          intro q a
          rw [Flatten.toPrimitiveWith_smul]
          simpa only [RingHom.id_apply, Rat.smul_def] using PolyQuot.map_smul q
            (Flatten.toPrimitiveWith images a) rep hrep }
    have hmaps : primitiveMap = towerMap := by
      apply basis.ext
      intro i
      change PolyQuot.toComplex
          (Flatten.toPrimitiveWith images (basis i)) rep hrep =
        T.toComplex (basis i)
      rw [hbasis]
      have hround := Flatten.certifies_basis candidate images hcert i i.isLt
      have hcomplex := congrArg T.toComplex hround
      rw [Flatten.fromPrimitiveWith_complex candidate.value rep hrep
        hcandidateSound] at hcomplex
      exact hcomplex
    have hforward (a : Elem T) :
        PolyQuot.toComplex (Flatten.toPrimitiveWith images a) rep hrep =
          T.toComplex a := by
      change primitiveMap a = towerMap a
      rw [hmaps]
    have hback (a : PolyQuot candidate.root.p candidate.root.x) :
        T.toComplex (Flatten.fromPrimitiveWith candidate.value a) =
          PolyQuot.toComplex a rep hrep :=
      Flatten.fromPrimitiveWith_complex candidate.value rep hrep
        hcandidateSound a
    unfold Flattening.Sound
    dsimp only
    refine ⟨?_, ?_, hforward, hback, ?_, ?_, ?_⟩
    · intro a
      apply toComplex_injective T
      rw [hback, hforward]
    · intro a
      apply PolyQuot.toComplex_injective rep hrep
      change PolyQuot.toComplex
          (Flatten.toPrimitiveWith images
            (Flatten.fromPrimitiveWith candidate.value a)) rep hrep =
        PolyQuot.toComplex a rep hrep
      rw [hforward, hback]
    · exact Flatten.toPrimitiveWith_add images
    · intro a b
      apply PolyQuot.toComplex_injective rep hrep
      change PolyQuot.toComplex
          (Flatten.toPrimitiveWith images (a * b)) rep hrep =
        PolyQuot.toComplex
          (Flatten.toPrimitiveWith images a *
            Flatten.toPrimitiveWith images b) rep hrep
      rw [hforward, map_mul, PolyQuot.map_mul, hforward, hforward]
    · intro a
      apply PolyQuot.toComplex_injective rep hrep
      change PolyQuot.toComplex
          (Flatten.toPrimitiveWith images a⁻¹) rep hrep =
        PolyQuot.toComplex
          (Flatten.toPrimitiveWith images a)⁻¹ rep hrep
      rw [hforward, map_inv, PolyQuot.map_inv, hforward]
  · have hfalse : Flatten.certifies candidate images = false :=
      Bool.eq_false_of_not_eq_true hcert
    simp [hfalse] at h

/-- Exactification, primitive search, and coordinate recovery always produce
a checked primitive presentation. -/
theorem flatten?_isSome (T : NumberTower) :
    T.flatten?.isSome := by
  obtain ⟨generators, hgenerators⟩ := Option.isSome_iff_exists.mp
    (Flatten.generators?_isSome T)
  obtain ⟨candidate, hcandidate⟩ := Option.isSome_iff_exists.mp
    (Flatten.candidate?_isSome T generators)
  let images := Flatten.basisImages generators candidate.coordinates
  have hgeneratorShape := Flatten.generators?_shape T hgenerators
  have hcandidateShape := Flatten.candidate?_shape T generators hcandidate
  have himages : images.size = T.dim := by
    change (Flatten.basisImages generators candidate.coordinates).size = T.dim
    rw [Flatten.basisImages_size generators candidate.coordinates]
    · exact hgeneratorShape.2
    · exact hcandidateShape.2
  have hdimension : candidate.dimension = T.dim :=
    hcandidateShape.1.trans hgeneratorShape.2
  have hround : (List.range T.dim).all (fun i =>
      let basis := T.ofCoeffs (Flatten.unitCoords T.dim i)
      Flatten.fromPrimitiveWith candidate.value
          (Flatten.toPrimitiveWith images basis) == basis) = true := by
    apply List.all_eq_true.mpr
    intro index hindex
    simp only [beq_iff_eq]
    exact Flatten.constructed_basis_roundtrip T generators candidate
      hgenerators hcandidate index (List.mem_range.mp hindex)
  have hcandidateSound := Flatten.candidate?_matches T generators
    (Flatten.generators?_sound T hgenerators) hcandidate
  have hroot := Flatten.evalZPoly_candidate candidate hcandidateSound
  have hcert : Flatten.certifies candidate images = true := by
    simp [Flatten.certifies, himages, hdimension, hround, hroot]
  dsimp only [images] at hcert
  unfold NumberTower.flatten?
  simp [hgenerators, hcandidate, hcert]

/-- The forward primitive coordinate map preserves the fixed complex value. -/
theorem flatten_toComplex (T : NumberTower) {F : Flattening T}
    (h : T.flatten? = some F) (a : Elem T) :
    PolyQuot.toComplex (F.toPrimitive a) F.root.rep F.root.rep_mk =
      T.toComplex a := by
  let : ZPoly.CheckedIrreducible F.root.p := F.root.checked
  exact (flatten?_sound T h).2.2.1 a

/-- The inverse primitive coordinate map preserves the fixed complex value. -/
theorem flatten_fromComplex (T : NumberTower) {F : Flattening T}
    (h : T.flatten? = some F) (a : PolyQuot F.root.p F.root.x) :
    T.toComplex (F.fromPrimitive a) =
      PolyQuot.toComplex a F.root.rep F.root.rep_mk := by
  let : ZPoly.CheckedIrreducible F.root.p := F.root.checked
  exact (flatten?_sound T h).2.2.2.1 a

end Hex.NumberTower
