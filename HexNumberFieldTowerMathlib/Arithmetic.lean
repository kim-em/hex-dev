/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Basic

public section

/-!
# Arithmetic correspondence for tower coordinates

These theorems identify every executable mixed-radix operation with the
corresponding operation in `ℂ`.  They are the proof payload from which the
law-bearing field interface will be assembled without replacing any runtime
operation.
-/

namespace Hex.NumberTower

namespace LevelSemantics

private theorem block_map_mul (q : Rat) (data : Array Rat)
    (index width : Nat) :
    Arithmetic.block (data.map fun c => q * c) index width =
      (Arithmetic.block data index width).map fun c => q * c := by
  apply Array.ext
  · simp [Arithmetic.block]
  · intro i hi₁ hi₂
    simp [Arithmetic.block, Array.getD]

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

/-- Coordinatewise rational scaling commutes with direct tower denotation. -/
theorem denote_smul (levels : List Level) (q : Rat) (data : Array Rat) :
    denote levels (data.map fun c => q * c) =
      (q : ℂ) * denote levels data := by
  induction levels generalizing data with
  | nil =>
      by_cases hdata : 0 < data.size <;>
        simp [denote, Array.getD, hdata]
  | cons level lower ih =>
      rw [denote_cons, denote_cons, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [block_map_mul, ih]
      ring

/-- Evaluate an array of lower-tower coefficient blocks as a power sum. -/
@[expose]
noncomputable def evalBlocks (lower : List Level) (x : ℂ)
    (blocks : Array (Array Rat)) : ℂ :=
  ∑ i ∈ Finset.range blocks.size,
    denote lower (blocks.getD i #[]) * x ^ i

/-- Evaluate a prescribed initial range of lower-tower coefficient blocks. -/
@[expose]
noncomputable def evalUpTo (lower : List Level) (x : ℂ) (count : Nat)
    (blocks : Array (Array Rat)) : ℂ :=
  ∑ i ∈ Finset.range count,
    denote lower (blocks.getD i #[]) * x ^ i

private theorem getD_set! (blocks : Array (Array Rat)) (k i : Nat)
    (value default : Array Rat) (hk : k < blocks.size) :
    (blocks.set! k value).getD i default =
      if k = i then value else blocks.getD i default := by
  by_cases hki : k = i
  · subst i
    simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, hk]
  · simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, hki]

/-- Updating one in-bounds block changes its power-sum value by exactly the
corresponding monomial delta. -/
theorem evalBlocks_set (lower : List Level) (x : ℂ)
    (blocks : Array (Array Rat)) (k : Nat) (value : Array Rat)
    (hk : k < blocks.size) :
    evalBlocks lower x (blocks.set! k value) =
      evalBlocks lower x blocks +
        (denote lower value - denote lower (blocks.getD k #[])) * x ^ k := by
  unfold evalBlocks
  rw [Array.size_set!]
  let indices := Finset.range blocks.size
  have hmem : k ∈ indices := Finset.mem_range.mpr hk
  calc
    _ = (∑ i ∈ indices.erase k,
          denote lower ((blocks.set! k value).getD i #[]) * x ^ i) +
        denote lower ((blocks.set! k value).getD k #[]) * x ^ k := by
          exact (Finset.sum_erase_add _ _ hmem).symm
    _ = (∑ i ∈ indices.erase k,
          denote lower (blocks.getD i #[]) * x ^ i) +
        denote lower value * x ^ k := by
          congr 1
          · apply Finset.sum_congr rfl
            intro i hi
            have hki : k ≠ i := by
              exact fun h => (Finset.mem_erase.mp hi).1 h.symm
            rw [getD_set! blocks k i value #[] hk]
            simp [hki]
          · rw [getD_set! blocks k k value #[] hk]
            simp
    _ = (∑ i ∈ indices,
          denote lower (blocks.getD i #[]) * x ^ i) +
        (denote lower value - denote lower (blocks.getD k #[])) * x ^ k := by
          rw [← Finset.sum_erase_add _ _ hmem]
          ring

/-- Updating one block inside the evaluated range changes its value by the
corresponding monomial delta. -/
theorem evalUpTo_set (lower : List Level) (x : ℂ) (count : Nat)
    (blocks : Array (Array Rat)) (k : Nat) (value : Array Rat)
    (hcount : k < count) (hsize : k < blocks.size) :
    evalUpTo lower x count (blocks.set! k value) =
      evalUpTo lower x count blocks +
        (denote lower value - denote lower (blocks.getD k #[])) * x ^ k := by
  unfold evalUpTo
  let indices := Finset.range count
  have hmem : k ∈ indices := Finset.mem_range.mpr hcount
  calc
    _ = (∑ i ∈ indices.erase k,
          denote lower ((blocks.set! k value).getD i #[]) * x ^ i) +
        denote lower ((blocks.set! k value).getD k #[]) * x ^ k := by
          exact (Finset.sum_erase_add _ _ hmem).symm
    _ = (∑ i ∈ indices.erase k,
          denote lower (blocks.getD i #[]) * x ^ i) +
        denote lower value * x ^ k := by
          congr 1
          · apply Finset.sum_congr rfl
            intro i hi
            have hki : k ≠ i := by
              exact fun h => (Finset.mem_erase.mp hi).1 h.symm
            rw [getD_set! blocks k i value #[] hsize]
            simp [hki]
          · rw [getD_set! blocks k k value #[] hsize]
            simp
    _ = (∑ i ∈ indices,
          denote lower (blocks.getD i #[]) * x ^ i) +
        (denote lower value - denote lower (blocks.getD k #[])) * x ^ k := by
          rw [← Finset.sum_erase_add _ _ hmem]
          ring

/-- Truncation above the evaluated range does not alter its power sum. -/
theorem evalUpTo_take (lower : List Level) (x : ℂ) (count cutoff : Nat)
    (blocks : Array (Array Rat)) (hcount : count ≤ cutoff) :
    evalUpTo lower x count (blocks.take cutoff) =
      evalUpTo lower x count blocks := by
  unfold evalUpTo
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < cutoff := lt_of_lt_of_le (Finset.mem_range.mp hi) hcount
  congr 2
  rw [← Array.shrink_eq_take]
  by_cases hsize : i < blocks.size
  · simp [Array.getD_eq_getD_getElem?, hi', hsize]
  · simp [Array.getD_eq_getD_getElem?, hi', hsize]

private theorem fold_eval {ι : Type} (lower : List Level) (x : ℂ)
    (count size : Nat) (indices : List ι)
    (step : Array (Array Rat) → ι → Array (Array Rat))
    (term : ι → ℂ) (initial : Array (Array Rat))
    (hinitial : initial.size = size)
    (hstep : ∀ work index, index ∈ indices → work.size = size →
      (step work index).size = size ∧
        evalUpTo lower x count (step work index) =
          evalUpTo lower x count work + term index) :
    evalUpTo lower x count (indices.foldl step initial) =
        evalUpTo lower x count initial + (indices.map term).sum ∧
      (indices.foldl step initial).size = size := by
  induction indices generalizing initial with
  | nil => simp [hinitial]
  | cons index indices ih =>
      have hnext := hstep initial index (by simp) hinitial
      have htail := ih (step initial index) hnext.1 (by
        intro work tailIndex hmem hwork
        exact hstep work tailIndex (by simp [hmem]) hwork)
      constructor
      · simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [htail.1, hnext.2]
        ring
      · simpa only [List.foldl_cons] using htail.2

private theorem list_sum_range (count : Nat) (term : Nat → ℂ) :
    ((List.range count).map term).sum =
      ∑ i ∈ Finset.range count, term i := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, ih]
      simp

private theorem convolveRow_eval (lower : List Level) (x : ℂ)
    (degree i : Nat) (a b : Array Rat)
    (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat)) (hdegree : 0 < degree)
    (hi : i < degree) (hsize : work.size = 2 * degree - 1)
    (hmul : ∀ u v, denote lower (multiply u v) =
      denote lower u * denote lower v) :
    evalUpTo lower x (2 * degree - 1)
        (Arithmetic.convolveRow degree (levelsDim lower) i multiply a b work) =
      evalUpTo lower x (2 * degree - 1) work +
        ((List.range degree).map fun j =>
          denote lower (Arithmetic.block a i (levelsDim lower)) *
            denote lower (Arithmetic.block b j (levelsDim lower)) *
              x ^ (i + j)).sum := by
  unfold Arithmetic.convolveRow
  refine (fold_eval lower x (2 * degree - 1) (2 * degree - 1)
    (List.range degree) _ _ work hsize ?_).1
  intro current j hjmem hcurrent
  have hj : j < degree := List.mem_range.mp hjmem
  have hindex : i + j < 2 * degree - 1 := by omega
  have hbound : i + j < current.size := by omega
  constructor
  · simp [hcurrent]
  · rw [evalUpTo_set lower x (2 * degree - 1) current (i + j)
        (Arithmetic.addCoords (levelsDim lower)
          (current.getD (i + j) (Array.replicate (levelsDim lower) 0))
          (multiply (Arithmetic.block a i (levelsDim lower))
            (Arithmetic.block b j (levelsDim lower)))) hindex hbound]
    rw [denote_add, hmul]
    have hold :
        denote lower
            (current.getD (i + j) (Array.replicate (levelsDim lower) 0)) =
          denote lower (current.getD (i + j) #[]) := by
      simp [Array.getD, hbound]
    rw [hold]
    ring

/-- Flattening a top-level block array preserves its finite power sum through
the requested extension degree. -/
theorem denote_flatten (level : Level) (lower : List Level)
    (blocks : Array (Array Rat)) :
    denote (level :: lower)
        (Arithmetic.flattenBlocks level.degree (levelsDim lower) blocks) =
      ∑ i ∈ Finset.range level.degree,
        denote lower (blocks.getD i #[]) * level.root.toComplex ^ i := by
  rw [denote_cons]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Arithmetic.block_flatten level.degree (levelsDim lower) i blocks
    (Finset.mem_range.mp hi), denote_fixed]

/-- The polynomial view of raw blocks evaluates to their finite power sum. -/
theorem polynomial_eval (lower : List Level) (blocks : Array (Array Rat))
    (x : ℂ) :
    (polynomial lower blocks).eval x = evalBlocks lower x blocks := by
  rw [polynomial, Polynomial.eval_finsetSum]
  simp [evalBlocks, Polynomial.eval_monomial]

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

/-- The canonical all-zero block denotes zero at every tower depth. -/
theorem denote_zero (levels : List Level) :
    denote levels (Arithmetic.fixedCoeffs (levelsDim levels) #[]) = 0 := by
  rw [denote_fixed]
  exact denote_empty levels

/-- Fixed-width coordinate negation denotes complex negation. -/
theorem denote_neg (levels : List Level) (data : Array Rat) :
    denote levels (Arithmetic.negCoords (levelsDim levels) data) =
      -denote levels data := by
  have hcoords :
      Arithmetic.negCoords (levelsDim levels) data =
        Arithmetic.subCoords (levelsDim levels)
          (Arithmetic.fixedCoeffs (levelsDim levels) #[]) data := by
    apply Array.ext
    · simp [Arithmetic.negCoords, Arithmetic.subCoords,
        Arithmetic.fixedCoeffs]
    · intro i hi₁ hi₂
      simp [Arithmetic.negCoords, Arithmetic.subCoords,
        Arithmetic.fixedCoeffs, Array.getD]
  rw [hcoords, denote_sub, denote_zero, zero_sub]

private theorem denote_replicate_zero (levels : List Level) :
    denote levels (Array.replicate (levelsDim levels) 0) = 0 := by
  rw [← denote_zero levels]
  congr 1
  apply Array.ext
  · simp [Arithmetic.fixedCoeffs]
  · intro i hi₁ hi₂
    simp [Arithmetic.fixedCoeffs]

private theorem evalUpTo_replicate_zero (lower : List Level) (x : ℂ)
    (count : Nat) :
    evalUpTo lower x count
        (Array.replicate count
          (Array.replicate (levelsDim lower) 0)) = 0 := by
  unfold evalUpTo
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < count := Finset.mem_range.mp hi
  simp [Array.getD, hi', denote_replicate_zero]

private theorem convolve_eval (lower : List Level) (x : ℂ)
    (degree : Nat) (a b : Array Rat)
    (multiply : Array Rat → Array Rat → Array Rat)
    (hdegree : 0 < degree)
    (hmul : ∀ u v, denote lower (multiply u v) =
      denote lower u * denote lower v) :
    evalUpTo lower x (2 * degree - 1)
        (Arithmetic.convolve degree (levelsDim lower) multiply a b) =
      ∑ i ∈ Finset.range degree,
        ∑ j ∈ Finset.range degree,
          denote lower (Arithmetic.block a i (levelsDim lower)) *
            denote lower (Arithmetic.block b j (levelsDim lower)) *
              x ^ (i + j) := by
  let initial : Array (Array Rat) := Array.replicate (2 * degree - 1)
    (Array.replicate (levelsDim lower) 0)
  let term := fun i => ((List.range degree).map fun j =>
    denote lower (Arithmetic.block a i (levelsDim lower)) *
      denote lower (Arithmetic.block b j (levelsDim lower)) *
        x ^ (i + j)).sum
  have hfold := fold_eval lower x (2 * degree - 1) (2 * degree - 1)
    (List.range degree)
    (fun work i => Arithmetic.convolveRow degree (levelsDim lower) i
      multiply a b work) term initial (by simp [initial]) (by
        intro work i hi hsize
        constructor
        · simp [hsize]
        · exact convolveRow_eval lower x degree i a b multiply work hdegree
            (List.mem_range.mp hi) hsize hmul)
  have hlist :
      evalUpTo lower x (2 * degree - 1)
          (Arithmetic.convolve degree (levelsDim lower) multiply a b) =
        ((List.range degree).map term).sum := by
    simpa [Arithmetic.convolve, initial, term,
      evalUpTo_replicate_zero] using hfold.1
  calc
    _ = ((List.range degree).map term).sum := hlist
    _ = ∑ i ∈ Finset.range degree, term i :=
      list_sum_range degree term
    _ = ∑ i ∈ Finset.range degree,
          ∑ j ∈ Finset.range degree,
            denote lower (Arithmetic.block a i (levelsDim lower)) *
              denote lower (Arithmetic.block b j (levelsDim lower)) *
                x ^ (i + j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact list_sum_range degree fun j =>
        denote lower (Arithmetic.block a i (levelsDim lower)) *
          denote lower (Arithmetic.block b j (levelsDim lower)) *
            x ^ (i + j)

private theorem convolve_mul (lower : List Level) (x : ℂ)
    (degree : Nat) (a b : Array Rat)
    (multiply : Array Rat → Array Rat → Array Rat)
    (hdegree : 0 < degree)
    (hmul : ∀ u v, denote lower (multiply u v) =
      denote lower u * denote lower v) :
    evalUpTo lower x (2 * degree - 1)
        (Arithmetic.convolve degree (levelsDim lower) multiply a b) =
      (∑ i ∈ Finset.range degree,
          denote lower (Arithmetic.block a i (levelsDim lower)) * x ^ i) *
        ∑ j ∈ Finset.range degree,
          denote lower (Arithmetic.block b j (levelsDim lower)) * x ^ j := by
  rw [convolve_eval lower x degree a b multiply hdegree hmul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

private theorem reduceCoeffs_eval (lower : List Level) (x : ℂ)
    (degree k : Nat) (defining : Array (Array Rat))
    (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat))
    (hdk : degree ≤ k) (hsize : work.size = k + 1)
    (hmul : ∀ u v, denote lower (multiply u v) =
      denote lower u * denote lower v) :
    let zeroBlock : Array Rat := Array.replicate (levelsDim lower) 0
    let high := work.getD k zeroBlock
    evalUpTo lower x k
        (Arithmetic.reduceCoeffs degree (levelsDim lower) k defining
          multiply work) =
      evalUpTo lower x k work +
        ∑ j ∈ Finset.range degree,
          -(denote lower high * denote lower (defining.getD j zeroBlock) *
            x ^ (k - degree + j)) := by
  let zeroBlock : Array Rat := Array.replicate (levelsDim lower) 0
  let high := work.getD k zeroBlock
  let term := fun j =>
    -(denote lower high * denote lower (defining.getD j zeroBlock) *
      x ^ (k - degree + j))
  have hfold := fold_eval lower x k (k + 1) (List.range degree)
    (fun current j =>
      current.set! (k - degree + j)
        (Arithmetic.subCoords (levelsDim lower)
          (current.getD (k - degree + j) zeroBlock)
          (multiply high (defining.getD j zeroBlock))))
    term work hsize (by
      intro current j hjmem hcurrent
      have hj : j < degree := List.mem_range.mp hjmem
      have hindex : k - degree + j < k := by omega
      have hbound : k - degree + j < current.size := by omega
      constructor
      · simp [hcurrent]
      · rw [evalUpTo_set lower x k current (k - degree + j)
            (Arithmetic.subCoords (levelsDim lower)
              (current.getD (k - degree + j) zeroBlock)
              (multiply high (defining.getD j zeroBlock))) hindex hbound]
        rw [denote_sub, hmul]
        have hold :
            denote lower
                (current.getD (k - degree + j) zeroBlock) =
              denote lower (current.getD (k - degree + j) #[]) := by
          simp [Array.getD, hbound]
        rw [hold]
        ring)
  have hlist :
      evalUpTo lower x k
          (Arithmetic.reduceCoeffs degree (levelsDim lower) k defining
            multiply work) =
        evalUpTo lower x k work + ((List.range degree).map term).sum := by
    simpa [Arithmetic.reduceCoeffs, zeroBlock, high, term] using hfold.1
  calc
    _ = evalUpTo lower x k work + ((List.range degree).map term).sum := hlist
    _ = evalUpTo lower x k work +
          ∑ j ∈ Finset.range degree, term j := by
      rw [list_sum_range]
    _ = evalUpTo lower x k work +
          ∑ j ∈ Finset.range degree,
            -(denote lower high *
              denote lower (defining.getD j zeroBlock) *
                x ^ (k - degree + j)) := rfl

/-- The canonical constant-one block denotes one for every valid lower
tower. -/
theorem denote_one (levels : List Level) (hvalid : LevelsValid levels) :
    denote levels (Arithmetic.fixedCoeffs (levelsDim levels) #[1]) = 1 := by
  induction levels with
  | nil => simp [denote, Arithmetic.fixedCoeffs, levelsDim, Array.getD]
  | cons level lower ih =>
      rw [denote_cons]
      simp only [levelsDim]
      calc
        _ = denote lower (Arithmetic.block
              (Arithmetic.fixedCoeffs
                (level.degree * levelsDim lower) #[1]) 0
              (levelsDim lower)) *
            level.root.toComplex ^ 0 := by
              apply Finset.sum_eq_single 0
              · intro i hi hi0
                rw [Arithmetic.block_one level.degree (levelsDim lower) i
                  (Finset.mem_range.mp hi)]
                simp [hi0, denote_zero]
              · intro hnot
                exact (hnot (Finset.mem_range.mpr hvalid.1.1)).elim
        _ = denote lower
              (Arithmetic.fixedCoeffs (levelsDim lower) #[1]) *
            level.root.toComplex ^ 0 := by
              rw [Arithmetic.block_one level.degree (levelsDim lower) 0
                hvalid.1.1]
              simp
        _ = 1 := by rw [ih hvalid.2.2]; simp

/-- The stored monic relation is the vanishing power sum used by descending
coordinate reduction. -/
theorem relation_sum (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    (∑ j ∈ Finset.range level.degree,
        denote lower (level.defining.getD j #[]) *
          level.root.toComplex ^ j) +
      level.root.toComplex ^ level.degree = 0 := by
  let one := Arithmetic.fixedCoeffs (levelsDim lower) #[1]
  have hbelow (j : Nat) (hj : j < level.degree) :
      (level.defining.push one).getD j #[] = level.defining.getD j #[] := by
    have hj' : j < level.defining.size := by
      simpa [hvalid.1.2.1] using hj
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt, hj']
  have htop :
      (level.defining.push one).getD level.degree #[] = one := by
    rw [← hvalid.1.2.1]
    simp [Array.getD_eq_getD_getElem?]
  have h := level_relation_vanishes level lower hvalid
  rw [polynomial_eval] at h
  simp only [evalBlocks, Level.polynomial, Array.size_push,
    hvalid.1.2.1, Finset.sum_range_succ] at h
  have hsum :
      (∑ j ∈ Finset.range level.degree,
          denote lower ((level.defining.push one).getD j #[]) *
            level.root.toComplex ^ j) =
        ∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j #[]) *
            level.root.toComplex ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbelow j (Finset.mem_range.mp hj)]
  rw [hsum, htop, denote_one lower hvalid.2.2, one_mul] at h
  exact h

private theorem reduceAt_eval (level : Level) (lower : List Level)
    (k : Nat) (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat)) (hvalid : LevelsValid (level :: lower))
    (hdk : level.degree ≤ k) (hsize : work.size = k + 1)
    (hmul : ∀ u v, denote lower (multiply u v) =
      denote lower u * denote lower v) :
    evalUpTo lower level.root.toComplex k
        (Arithmetic.reduceAt level.degree (levelsDim lower) k
          level.defining multiply work) =
      evalUpTo lower level.root.toComplex (k + 1) work := by
  let zeroBlock : Array Rat := Array.replicate (levelsDim lower) 0
  let high := work.getD k zeroBlock
  have hdefault (j : Nat) (hj : j < level.degree) :
      level.defining.getD j zeroBlock = level.defining.getD j #[] := by
    have hj' : j < level.defining.size := by
      simpa [hvalid.1.2.1] using hj
    simp [Array.getD, hj']
  have hrelation :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j zeroBlock) *
            level.root.toComplex ^ j) +
        level.root.toComplex ^ level.degree = 0 := by
    have hsum :
        (∑ j ∈ Finset.range level.degree,
            denote lower (level.defining.getD j zeroBlock) *
              level.root.toComplex ^ j) =
          ∑ j ∈ Finset.range level.degree,
            denote lower (level.defining.getD j #[]) *
              level.root.toComplex ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hdefault j (Finset.mem_range.mp hj)]
    rw [hsum]
    exact relation_sum level lower hvalid
  have hrelation' :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j zeroBlock) *
            level.root.toComplex ^ j) =
        -level.root.toComplex ^ level.degree := by
    linear_combination hrelation
  have hcorrection :
      (∑ j ∈ Finset.range level.degree,
          -(denote lower high *
            denote lower (level.defining.getD j zeroBlock) *
              level.root.toComplex ^ (k - level.degree + j))) =
        denote lower high * level.root.toComplex ^ k := by
    calc
      _ = -(∑ j ∈ Finset.range level.degree,
            denote lower high *
              denote lower (level.defining.getD j zeroBlock) *
                level.root.toComplex ^ (k - level.degree + j)) := by
              rw [Finset.sum_neg_distrib]
      _ = -(denote lower high * level.root.toComplex ^ (k - level.degree) *
            ∑ j ∈ Finset.range level.degree,
              denote lower (level.defining.getD j zeroBlock) *
                level.root.toComplex ^ j) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [pow_add]
              ring
      _ = denote lower high * level.root.toComplex ^ (k - level.degree) *
            level.root.toComplex ^ level.degree := by
              rw [hrelation']
              ring
      _ = denote lower high * level.root.toComplex ^ k := by
              rw [mul_assoc, ← pow_add]
              congr 2
              omega
  have heval_succ :
      evalUpTo lower level.root.toComplex (k + 1) work =
        evalUpTo lower level.root.toComplex k work +
          denote lower high * level.root.toComplex ^ k := by
    have hk : k < work.size := by omega
    unfold evalUpTo
    rw [Finset.sum_range_succ]
    simp [high, Array.getD, hk]
  rw [Arithmetic.reduceAt,
    evalUpTo_take lower level.root.toComplex k k _ (Nat.le_refl k),
    reduceCoeffs_eval lower level.root.toComplex level.degree k
      level.defining multiply work hdk hsize hmul,
    hcorrection, heval_succ]

/-- Descending reduction preserves evaluation at the current algebraic root. -/
private theorem reduce_eval (level : Level) (lower : List Level)
    (fuel : Nat) (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat)) (hvalid : LevelsValid (level :: lower))
    (hsize : work.size = level.degree + fuel)
    (hmul : ∀ u v, denote lower (multiply u v) =
      denote lower u * denote lower v) :
    evalUpTo lower level.root.toComplex level.degree
        (Arithmetic.reduce level.degree (levelsDim lower) level.defining
          multiply fuel work) =
      evalUpTo lower level.root.toComplex (level.degree + fuel) work := by
  induction fuel generalizing work with
  | zero =>
      simp only [Arithmetic.reduce]
      simpa using
        evalUpTo_take lower level.root.toComplex level.degree level.degree
          work (Nat.le_refl level.degree)
  | succ fuel ih =>
      let next :=
        Arithmetic.reduceAt level.degree (levelsDim lower)
          (level.degree + fuel) level.defining multiply work
      have hnext : next.size = level.degree + fuel := by
        apply Arithmetic.reduceAt_size
        omega
      simp only [Arithmetic.reduce]
      rw [ih next hnext]
      simpa [next, Nat.add_assoc] using
        reduceAt_eval level lower (level.degree + fuel) multiply work hvalid
          (Nat.le_add_right level.degree fuel) (by omega) hmul

/-- Recursive convolution and monic reduction denote complex
multiplication. -/
theorem denote_mul (levels : List Level) (hvalid : LevelsValid levels)
    (a b : Array Rat) :
    denote levels (Arithmetic.mulCoords levels a b) =
      denote levels a * denote levels b := by
  induction levels generalizing a b with
  | nil =>
      by_cases ha : 0 < a.size <;> by_cases hb : 0 < b.size <;>
        simp [Arithmetic.mulCoords, denote, Array.getD, ha, hb]
  | cons level lower ih =>
      have hdegree : 0 < level.degree := hvalid.1.1
      have hlower : LevelsValid lower := hvalid.2.2
      have hmul : ∀ u v, denote lower (Arithmetic.mulCoords lower u v) =
          denote lower u * denote lower v := fun u v => ih hlower u v
      simp only [Arithmetic.mulCoords]
      rw [if_neg (Nat.ne_of_gt hdegree)]
      rw [denote_flatten]
      change evalUpTo lower level.root.toComplex level.degree
          (Arithmetic.reduce level.degree (levelsDim lower) level.defining
            (Arithmetic.mulCoords lower) (level.degree - 1)
            (Arithmetic.convolve level.degree (levelsDim lower)
              (Arithmetic.mulCoords lower) a b)) =
        denote (level :: lower) a * denote (level :: lower) b
      rw [reduce_eval level lower (level.degree - 1)
        (Arithmetic.mulCoords lower)
        (Arithmetic.convolve level.degree (levelsDim lower)
          (Arithmetic.mulCoords lower) a b) hvalid (by simp; omega) hmul]
      rw [show level.degree + (level.degree - 1) =
          2 * level.degree - 1 by omega]
      rw [convolve_mul lower level.root.toComplex level.degree a b
        (Arithmetic.mulCoords lower) hdegree hmul]
      rw [denote_cons, denote_cons]

/-! ### Canonical coefficient denotation -/

/-- Complex denotation restricted to the canonical fixed-width coefficient
carrier used by recursive inversion. -/
@[expose]
noncomputable def coeffDenote (levels : List Level)
    (a : Arithmetic.Coeff levels) : ℂ :=
  denote levels a.data

@[simp]
theorem coeffDenote_zero (levels : List Level) :
    coeffDenote levels (0 : Arithmetic.Coeff levels) = 0 := by
  change denote levels
      (Arithmetic.fixedCoeffs (levelsDim levels) #[]) = 0
  exact denote_zero levels

@[simp]
theorem coeffDenote_one (levels : List Level) (hvalid : LevelsValid levels) :
    coeffDenote levels (1 : Arithmetic.Coeff levels) = 1 := by
  change denote levels
      (Arithmetic.fixedCoeffs (levelsDim levels) #[1]) = 1
  exact denote_one levels hvalid

theorem coeffDenote_add (levels : List Level)
    (a b : Arithmetic.Coeff levels) :
    coeffDenote levels (a + b) = coeffDenote levels a + coeffDenote levels b := by
  change denote levels (Arithmetic.addCoords (levelsDim levels) a.data b.data) =
    denote levels a.data + denote levels b.data
  exact denote_add levels a.data b.data

theorem coeffDenote_sub (levels : List Level)
    (a b : Arithmetic.Coeff levels) :
    coeffDenote levels (a - b) = coeffDenote levels a - coeffDenote levels b := by
  change denote levels (Arithmetic.subCoords (levelsDim levels) a.data b.data) =
    denote levels a.data - denote levels b.data
  exact denote_sub levels a.data b.data

theorem coeffDenote_neg (levels : List Level) (a : Arithmetic.Coeff levels) :
    coeffDenote levels (-a) = -coeffDenote levels a := by
  change denote levels (Arithmetic.negCoords (levelsDim levels) a.data) =
    -denote levels a.data
  exact denote_neg levels a.data

theorem coeffDenote_mul (levels : List Level) (hvalid : LevelsValid levels)
    (a b : Arithmetic.Coeff levels) :
    coeffDenote levels (a * b) = coeffDenote levels a * coeffDenote levels b := by
  change denote levels (Arithmetic.mulCoords levels a.data b.data) =
    denote levels a.data * denote levels b.data
  exact denote_mul levels hvalid a.data b.data

/-- Rational coordinate scaling on canonical coefficients. -/
@[expose]
def coeffSmul (levels : List Level) (q : Rat)
    (a : Arithmetic.Coeff levels) : Arithmetic.Coeff levels :=
  Arithmetic.Coeff.ofData levels (a.data.map fun c => q * c)

theorem coeffDenote_smul (levels : List Level) (q : Rat)
    (a : Arithmetic.Coeff levels) :
    coeffDenote levels (coeffSmul levels q a) =
      (q : ℂ) * coeffDenote levels a := by
  rw [coeffDenote, coeffSmul, Arithmetic.Coeff.ofData, denote_fixed,
    denote_smul]
  rfl

/-- Natural powers using the executable coefficient multiplication. -/
@[expose]
def coeffPow {levels : List Level} (a : Arithmetic.Coeff levels) :
    Nat → Arithmetic.Coeff levels
  | 0 => 1
  | n + 1 => coeffPow a n * a

theorem coeffDenote_pow (levels : List Level) (hvalid : LevelsValid levels)
    (a : Arithmetic.Coeff levels) (n : Nat) :
    coeffDenote levels (coeffPow a n) = coeffDenote levels a ^ n := by
  induction n with
  | zero => simp [coeffPow, coeffDenote_one levels hvalid]
  | succ n ih =>
      rw [coeffPow, coeffDenote_mul levels hvalid, ih, pow_succ]

/-- Integer powers using the executable coefficient inverse for negative
exponents. -/
@[expose]
def coeffZPow {levels : List Level} (a : Arithmetic.Coeff levels) :
    Int → Arithmetic.Coeff levels
  | .ofNat n => coeffPow a n
  | .negSucc n => (coeffPow a (n + 1))⁻¹

/-- Canonical coefficients at one level list have unique complex denotation. -/
@[expose]
def DenoteInjective (levels : List Level) : Prop :=
  Function.Injective (coeffDenote levels)

/-- Transfer a lawful field structure to canonical executable coefficients
once recursive inversion is known to preserve complex denotation. Auxiliary
casts, scalar actions, and powers are chosen through rational coordinate
scaling and the existing executable operations. -/
@[expose, reducible]
noncomputable def coeffField (levels : List Level) (hvalid : LevelsValid levels)
    (hinjective : DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      coeffDenote levels a⁻¹ = (coeffDenote levels a)⁻¹) :
    Field (Arithmetic.Coeff levels) := by
  letI : SMul Nat (Arithmetic.Coeff levels) :=
    ⟨fun n a => coeffSmul levels (n : Rat) a⟩
  letI : SMul Int (Arithmetic.Coeff levels) :=
    ⟨fun n a => coeffSmul levels (n : Rat) a⟩
  letI : SMul ℚ≥0 (Arithmetic.Coeff levels) :=
    ⟨fun q a => coeffSmul levels (q : Rat) a⟩
  letI : SMul ℚ (Arithmetic.Coeff levels) :=
    ⟨fun q a => coeffSmul levels q a⟩
  letI : Pow (Arithmetic.Coeff levels) Nat :=
    ⟨fun a n => coeffPow a n⟩
  letI : Pow (Arithmetic.Coeff levels) Int :=
    ⟨fun a n => coeffZPow a n⟩
  letI : NatCast (Arithmetic.Coeff levels) :=
    ⟨fun n => coeffSmul levels (n : Rat) 1⟩
  letI : IntCast (Arithmetic.Coeff levels) :=
    ⟨fun n => coeffSmul levels (n : Rat) 1⟩
  letI : NNRatCast (Arithmetic.Coeff levels) :=
    ⟨fun q => coeffSmul levels (q : Rat) 1⟩
  letI : RatCast (Arithmetic.Coeff levels) :=
    ⟨fun q => coeffSmul levels q 1⟩
  apply Function.Injective.field (coeffDenote levels) hinjective
  · exact coeffDenote_zero levels
  · exact coeffDenote_one levels hvalid
  · exact coeffDenote_add levels
  · exact coeffDenote_mul levels hvalid
  · exact coeffDenote_neg levels
  · exact coeffDenote_sub levels
  · exact hinv
  · intro a b
    change coeffDenote levels (a * b⁻¹) =
      coeffDenote levels a / coeffDenote levels b
    rw [coeffDenote_mul levels hvalid, hinv]
    rfl
  · intro n a
    change coeffDenote levels (coeffSmul levels (n : Rat) a) =
      n • coeffDenote levels a
    rw [coeffDenote_smul, nsmul_eq_mul]
    rfl
  · intro n a
    change coeffDenote levels (coeffSmul levels (n : Rat) a) =
      n • coeffDenote levels a
    rw [coeffDenote_smul, zsmul_eq_mul]
    rfl
  · intro q a
    change coeffDenote levels (coeffSmul levels (q : Rat) a) =
      q • coeffDenote levels a
    rw [coeffDenote_smul, NNRat.smul_def]
    rfl
  · intro q a
    change coeffDenote levels (coeffSmul levels q a) =
      q • coeffDenote levels a
    rw [coeffDenote_smul, Rat.smul_def]
  · exact coeffDenote_pow levels hvalid
  · intro a n
    cases n with
    | ofNat n => exact coeffDenote_pow levels hvalid a n
    | negSucc n =>
        change coeffDenote levels (coeffPow a (n + 1))⁻¹ =
          coeffDenote levels a ^ Int.negSucc n
        rw [hinv, coeffDenote_pow levels hvalid a (n + 1)]
        rfl
  · intro n
    change coeffDenote levels (coeffSmul levels (n : Rat) 1) = (n : ℂ)
    rw [coeffDenote_smul, coeffDenote_one levels hvalid]
    simp
  · intro n
    change coeffDenote levels (coeffSmul levels (n : Rat) 1) = (n : ℂ)
    rw [coeffDenote_smul, coeffDenote_one levels hvalid]
    simp
  · intro q
    change coeffDenote levels (coeffSmul levels (q : Rat) 1) = (q : ℂ)
    rw [coeffDenote_smul, coeffDenote_one levels hvalid]
    simp
  · intro q
    change coeffDenote levels (coeffSmul levels q 1) = (q : ℂ)
    rw [coeffDenote_smul, coeffDenote_one levels hvalid]
    simp

/-- Canonical coefficient denotation bundled as a ring homomorphism for the
transferred executable field. -/
@[expose]
noncomputable def coeffHom (levels : List Level) (hvalid : LevelsValid levels)
    (hinjective : DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      coeffDenote levels a⁻¹ = (coeffDenote levels a)⁻¹) :
    letI : Field (Arithmetic.Coeff levels) :=
      coeffField levels hvalid hinjective hinv
    Arithmetic.Coeff levels →+* ℂ := by
  letI : Field (Arithmetic.Coeff levels) :=
    coeffField levels hvalid hinjective hinv
  exact
    { toFun := coeffDenote levels
      map_zero' := by
        change denote levels
          (Arithmetic.fixedCoeffs (levelsDim levels) #[]) = 0
        exact denote_zero levels
      map_one' := by
        change denote levels
          (Arithmetic.fixedCoeffs (levelsDim levels) #[1]) = 1
        exact denote_one levels hvalid
      map_add' := by
        intro a b
        change denote levels
            (Arithmetic.addCoords (levelsDim levels) a.data b.data) =
          denote levels a.data + denote levels b.data
        exact denote_add levels a.data b.data
      map_mul' := by
        intro a b
        change denote levels (Arithmetic.mulCoords levels a.data b.data) =
          denote levels a.data * denote levels b.data
        exact denote_mul levels hvalid a.data b.data }

private theorem fixedCoeffs_eq_self (levels : List Level)
    (a : Arithmetic.Coeff levels) :
    Arithmetic.fixedCoeffs (levelsDim levels) a.data = a.data := by
  apply Array.ext
  · simp [Arithmetic.fixedCoeffs, a.size_eq]
  · intro i hi₁ hi₂
    simp [Arithmetic.fixedCoeffs, Array.getD, hi₂]

private theorem coeff_eq_of_data_eq {levels : List Level}
    {a b : Arithmetic.Coeff levels} (h : a.data = b.data) : a = b := by
  cases a with
  | mk ad ha =>
      cases b with
      | mk bd hb =>
          simp only at h
          cases h
          rfl

/-- Evaluate a prescribed coefficient range of an executable dense polynomial
through lower-tower denotation. -/
@[expose]
noncomputable def denseEval (lower : List Level) (x : ℂ) (degree : Nat)
    (f : DensePoly (Arithmetic.Coeff lower)) : ℂ :=
  ∑ i ∈ Finset.range degree, coeffDenote lower (f.coeff i) * x ^ i

/-- Evaluation of executable dense polynomials after transferring the lawful
lower-tower field structure. -/
@[expose]
noncomputable def denseMap (lower : List Level) (x : ℂ)
    (hvalid : LevelsValid lower) (hinjective : DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid hinjective hinv
    DensePoly (Arithmetic.Coeff lower) → ℂ := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid hinjective hinv
  exact fun f => (HexPolyMathlib.toPolynomial f).eval₂
    (coeffHom lower hvalid hinjective hinv) x

/-- Ring-hom evaluation agrees with the prescribed coefficient sum whenever
the polynomial has degree below that range. -/
theorem denseMap_eq_denseEval (lower : List Level) (x : ℂ)
    (hvalid : LevelsValid lower) (hinjective : DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹)
    (degree : Nat) (f : DensePoly (Arithmetic.Coeff lower))
    (hdegree : f.degree?.getD 0 < degree) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid hinjective hinv
    denseMap lower x hvalid hinjective hinv f =
      denseEval lower x degree f := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid hinjective hinv
  rw [denseMap,
    Polynomial.eval₂_eq_sum_range'
      (coeffHom lower hvalid hinjective hinv)
      (by simpa using hdegree) x,
    denseEval]
  simp [coeffHom, HexPolyMathlib.coeff_toPolynomial]

/-- Dense evaluation preserves multiplication. -/
theorem denseMap_mul (lower : List Level) (x : ℂ)
    (hvalid : LevelsValid lower) (hinjective : DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹)
    (f g : DensePoly (Arithmetic.Coeff lower)) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid hinjective hinv
    denseMap lower x hvalid hinjective hinv (f * g) =
      denseMap lower x hvalid hinjective hinv f *
        denseMap lower x hvalid hinjective hinv g := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid hinjective hinv
  simp [denseMap, HexPolyMathlib.toPolynomial_mul, Polynomial.eval₂_mul]

/-- Dense evaluation preserves addition. -/
theorem denseMap_add (lower : List Level) (x : ℂ)
    (hvalid : LevelsValid lower) (hinjective : DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹)
    (f g : DensePoly (Arithmetic.Coeff lower)) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid hinjective hinv
    denseMap lower x hvalid hinjective hinv (f + g) =
      denseMap lower x hvalid hinjective hinv f +
        denseMap lower x hvalid hinjective hinv g := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid hinjective hinv
  simp [denseMap, HexPolyMathlib.toPolynomial_add, Polynomial.eval₂_add]

/-- Dense evaluation sends coefficient scaling to scalar multiplication. -/
theorem denseMap_scale (lower : List Level) (x : ℂ)
    (hvalid : LevelsValid lower) (hinjective : DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹)
    (c : Arithmetic.Coeff lower)
    (f : DensePoly (Arithmetic.Coeff lower)) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid hinjective hinv
    denseMap lower x hvalid hinjective hinv (DensePoly.scale c f) =
      coeffDenote lower c * denseMap lower x hvalid hinjective hinv f := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid hinjective hinv
  simp [denseMap, HexPolyMathlib.toPolynomial_scale, Polynomial.eval₂_mul,
    coeffHom]

/-- Dense evaluation of a constant is lower-tower denotation. -/
theorem denseMap_C (lower : List Level) (x : ℂ)
    (hvalid : LevelsValid lower) (hinjective : DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹)
    (c : Arithmetic.Coeff lower) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid hinjective hinv
    denseMap lower x hvalid hinjective hinv (DensePoly.C c) =
      coeffDenote lower c := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid hinjective hinv
  simp [denseMap, coeffHom]

/-- Dense evaluation sends zero to zero. -/
theorem denseMap_zero (lower : List Level) (x : ℂ)
    (hvalid : LevelsValid lower) (hinjective : DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid hinjective hinv
    denseMap lower x hvalid hinjective hinv 0 = 0 := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid hinjective hinv
  simp [denseMap]

private theorem toPolynomial_dvd {R : Type*} [CommSemiring R] [DecidableEq R]
    {f g : DensePoly R} : f ∣ g →
      HexPolyMathlib.toPolynomial f ∣ HexPolyMathlib.toPolynomial g := by
  rintro ⟨q, rfl⟩
  exact ⟨HexPolyMathlib.toPolynomial q, by simp⟩

private theorem toPolynomial_ne_zero {R : Type*} [CommRing R] [DecidableEq R]
    {f : DensePoly R} (hf : f ≠ 0) : HexPolyMathlib.toPolynomial f ≠ 0 := by
  intro hzero
  apply hf
  calc
    f = HexPolyMathlib.ofPolynomial (HexPolyMathlib.toPolynomial f) :=
      (HexPolyMathlib.ofPolynomial_toPolynomial f).symm
    _ = 0 := by rw [hzero, HexPolyMathlib.ofPolynomial_zero]

private theorem eq_C_leadingCoeff_of_size_one {R : Type*} [Zero R]
    [DecidableEq R] (f : DensePoly R) (hsize : f.size = 1) :
    f = DensePoly.C f.leadingCoeff := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C]
  by_cases hn : n = 0
  · subst n
    rw [DensePoly.leadingCoeff_eq_coeff_last f (by omega), hsize]
    rfl
  · rw [if_neg hn]
    exact DensePoly.coeff_eq_zero_of_size_le f (by omega)

/-- The first prescribed coefficient range of a dense polynomial, exposed as
lower-tower coordinate blocks. -/
@[expose]
def denseBlocks (degree : Nat) {lower : List Level}
    (f : DensePoly (Arithmetic.Coeff lower)) : Array (Array Rat) :=
  (Vector.ofFn fun i : Fin degree => (f.coeff i).data).toArray

/-- Embed a lower-coefficient dense polynomial as one canonical coefficient at
the extended level. -/
@[expose]
def liftDense (level : Level) (lower : List Level)
    (f : DensePoly (Arithmetic.Coeff lower)) :
    Arithmetic.Coeff (level :: lower) :=
  ⟨Arithmetic.flattenBlocks level.degree (levelsDim lower)
      (denseBlocks level.degree f), by simp [levelsDim]⟩

/-- Dense-polynomial coefficient embedding denotes its finite evaluation. -/
theorem coeffDenote_liftDense (level : Level) (lower : List Level)
    (f : DensePoly (Arithmetic.Coeff lower)) :
    coeffDenote (level :: lower) (liftDense level lower f) =
      denseEval lower level.root.toComplex level.degree f := by
  rw [coeffDenote, liftDense, denote_flatten, denseEval]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < level.degree := Finset.mem_range.mp hi
  simp [denseBlocks, coeffDenote, Array.getD, hi']

/-- Flattening an explicit range of dense coefficients denotes the prescribed
finite dense evaluation. -/
theorem denote_flatten_dense (level : Level) (lower : List Level)
    (f : DensePoly (Arithmetic.Coeff lower)) :
    denote (level :: lower)
        (Arithmetic.flattenBlocks level.degree (levelsDim lower)
          (((List.range level.degree).map fun i => (f.coeff i).data).toArray)) =
      denseEval lower level.root.toComplex level.degree f := by
  rw [denote_flatten, denseEval]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < level.degree := Finset.mem_range.mp hi
  simp [coeffDenote, Array.getD, hi']

/-- Injective extended-level denotation rules out every nonzero vanishing
dense polynomial below the defining degree. -/
theorem dense_eq_zero_of_eval (level : Level) (lower : List Level)
    (hinjective : DenoteInjective (level :: lower))
    (f : DensePoly (Arithmetic.Coeff lower))
    (hdegree : f.degree?.getD 0 < level.degree)
    (heval : denseEval lower level.root.toComplex level.degree f = 0) :
    f = 0 := by
  have hlift : liftDense level lower f = liftDense level lower 0 := by
    apply hinjective
    rw [coeffDenote_liftDense, coeffDenote_liftDense, heval]
    simp [denseEval, coeffDenote_zero]
  apply DensePoly.ext_coeff
  intro n
  by_cases hn : n < level.degree
  · have hblock := congrArg
      (fun c : Arithmetic.Coeff (level :: lower) =>
        Arithmetic.block c.data n (levelsDim lower)) hlift
    simp only [liftDense] at hblock
    rw [Arithmetic.block_flatten level.degree (levelsDim lower) n
        (denseBlocks level.degree f) hn,
      Arithmetic.block_flatten level.degree (levelsDim lower) n
        (denseBlocks level.degree 0) hn] at hblock
    have hf : (denseBlocks level.degree f).getD n #[] =
        (f.coeff n).data := by
      simp [denseBlocks, Array.getD, hn]
    have hz : (denseBlocks level.degree
        (0 : DensePoly (Arithmetic.Coeff lower))).getD n #[] =
        ((0 : DensePoly (Arithmetic.Coeff lower)).coeff n).data := by
      simp [denseBlocks, Array.getD, hn]
    rw [hf, hz, fixedCoeffs_eq_self lower (f.coeff n),
      fixedCoeffs_eq_self lower
        ((0 : DensePoly (Arithmetic.Coeff lower)).coeff n)] at hblock
    exact coeff_eq_of_data_eq hblock
  · rw [DensePoly.coeff_zero]
    apply DensePoly.coeff_eq_zero_of_size_le
    by_cases hf : f.size = 0
    · omega
    · have hdeg : f.degree?.getD 0 = f.size - 1 := by
        simp [DensePoly.degree?, hf]
      rw [hdeg] at hdegree
      omega

/-- The inversion input polynomial evaluates to the denotation of its top-level
coordinate array. -/
theorem denseEval_value (level : Level) (lower : List Level) (a : Array Rat) :
    denseEval lower level.root.toComplex level.degree
        (Arithmetic.Coeff.value level lower a) =
      denote (level :: lower) a := by
  rw [denseEval, denote_cons]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < level.degree := Finset.mem_range.mp hi
  congr 1
  simp [Arithmetic.Coeff.value, Arithmetic.Coeff.ofData,
    coeffDenote, Array.getD, hi', denote_fixed]

/-- The executable monic level relation evaluates to zero at the stored root. -/
theorem denseEval_relation (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    denseEval lower level.root.toComplex (level.degree + 1)
        (Arithmetic.Coeff.relation level lower) = 0 := by
  rw [denseEval, Finset.sum_range_succ]
  have hbelow : ∀ j < level.degree,
      (Arithmetic.Coeff.relation level lower).coeff j =
        Arithmetic.Coeff.ofData lower (level.defining.getD j #[]) := by
    intro j hj
    rw [Arithmetic.Coeff.relation, DensePoly.coeff_ofCoeffs]
    have hj' : j <
        (((List.range level.degree).map fun i =>
          Arithmetic.Coeff.ofData lower
            (level.defining.getD i #[])).toArray).size := by
      simpa using hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hj']
    simp [Array.getD_eq_getD_getElem?]
  have htop : (Arithmetic.Coeff.relation level lower).coeff level.degree = 1 := by
    simp [Arithmetic.Coeff.relation, Array.getD]
  have hsum :
      (∑ j ∈ Finset.range level.degree,
          coeffDenote lower
              ((Arithmetic.Coeff.relation level lower).coeff j) *
            level.root.toComplex ^ j) =
        ∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j #[]) *
            level.root.toComplex ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbelow j (Finset.mem_range.mp hj)]
    simp [Arithmetic.Coeff.ofData, coeffDenote, denote_fixed]
  rw [hsum]
  rw [htop, coeffDenote_one lower hvalid.2.2]
  simpa using relation_sum level lower hvalid

/-- The inversion input polynomial lies strictly below the current defining
degree. -/
theorem value_degree_lt (level : Level) (lower : List Level) (a : Array Rat)
    (hdegree : 0 < level.degree) :
    (Arithmetic.Coeff.value level lower a).degree?.getD 0 < level.degree := by
  have hsize : (Arithmetic.Coeff.value level lower a).size ≤ level.degree :=
    (DensePoly.size_ofCoeffs_le _).trans (by
      simp)
  by_cases hzero : (Arithmetic.Coeff.value level lower a).size = 0
  · simp [DensePoly.degree?, hzero, hdegree]
  · rw [DensePoly.degree?_eq_some_of_pos_size _ (Nat.pos_of_ne_zero hzero),
      Option.getD_some]
    omega

/-- The executable relation retains its monic top coefficient and therefore
has exactly defining degree plus one stored coefficients. -/
theorem relation_size (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    (Arithmetic.Coeff.relation level lower).size = level.degree + 1 := by
  have hle : (Arithmetic.Coeff.relation level lower).size ≤
      level.degree + 1 := (DensePoly.size_ofCoeffs_le _).trans (by
    simp)
  have htop : (Arithmetic.Coeff.relation level lower).coeff level.degree = 1 := by
    simp [Arithmetic.Coeff.relation, Array.getD]
  have hone : (1 : Arithmetic.Coeff lower) ≠ 0 := by
    intro h
    have hmap := congrArg (coeffDenote lower) h
    rw [coeffDenote_one lower hvalid.2.2, coeffDenote_zero lower] at hmap
    exact one_ne_zero hmap
  have hnle : ¬ (Arithmetic.Coeff.relation level lower).size ≤
      level.degree := by
    intro hsize
    exact hone (htop.symm.trans
      (DensePoly.coeff_eq_zero_of_size_le _ hsize))
  omega

/-- The executable relation has its advertised defaulted degree. -/
theorem relation_degree (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    (Arithmetic.Coeff.relation level lower).degree?.getD 0 = level.degree := by
  rw [DensePoly.degree?_eq_some_of_pos_size _ (by
      rw [relation_size level lower hvalid]
      omega), Option.getD_some, relation_size level lower hvalid]
  omega

/-- For a nonzero input, the executable one-sided extended gcd with the
defining relation returns a nonzero constant gcd. -/
theorem xgcdLeft_size_one (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : DenoteInjective (level :: lower))
    (hlowerInjective : DenoteInjective lower)
    (hinv : ∀ b : Arithmetic.Coeff lower,
      coeffDenote lower b⁻¹ = (coeffDenote lower b)⁻¹)
    (a : Array Rat) (ha : denote (level :: lower) a ≠ 0) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid.2.2 hlowerInjective hinv
    (DensePoly.xgcdLeft (Arithmetic.Coeff.value level lower a)
      (Arithmetic.Coeff.relation level lower)).gcd.size = 1 := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid.2.2 hlowerInjective hinv
  let value := Arithmetic.Coeff.value level lower a
  let relation := Arithmetic.Coeff.relation level lower
  let result := DensePoly.xgcdLeft value relation
  let gcd := result.gcd
  change gcd.size = 1
  have hvalueDegree : value.degree?.getD 0 < level.degree :=
    value_degree_lt level lower a hvalid.1.1
  have hrelationDegree : relation.degree?.getD 0 = level.degree :=
    relation_degree level lower hvalid
  have hvalueMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv value = denote (level :: lower) a := by
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv level.degree value hvalueDegree]
    exact denseEval_value level lower a
  have hrelationMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv relation = 0 := by
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv (level.degree + 1) relation (by omega)]
    exact denseEval_relation level lower hvalid
  have hvalueNe : value ≠ 0 := by
    intro hzero
    apply ha
    rw [← hvalueMap, hzero,
      denseMap_zero lower level.root.toComplex hvalid.2.2
        hlowerInjective hinv]
  have hrelationNe : relation ≠ 0 := by
    intro hzero
    have hsize := relation_size level lower hvalid
    change relation.size = level.degree + 1 at hsize
    rw [hzero, DensePoly.size_zero] at hsize
    omega
  have hgcdDvdValue : gcd ∣ value := by
    change result.gcd ∣ value
    rw [DensePoly.xgcdLeft_gcd_eq_xgcd, DensePoly.xgcd_gcd_eq_gcd]
    exact DensePoly.gcd_dvd_left value relation
  have hgcdDvdRelation : gcd ∣ relation := by
    change result.gcd ∣ relation
    rw [DensePoly.xgcdLeft_gcd_eq_xgcd, DensePoly.xgcd_gcd_eq_gcd]
    exact DensePoly.gcd_dvd_right value relation
  have hgcdNe : gcd ≠ 0 := by
    intro hzero
    rcases hgcdDvdValue with ⟨q, hq⟩
    apply hvalueNe
    rw [hq, hzero]
    exact DensePoly.zero_mul q
  have hgcdDegree : gcd.degree?.getD 0 < level.degree := by
    have hpolyValue : HexPolyMathlib.toPolynomial value ≠ 0 :=
      toPolynomial_ne_zero hvalueNe
    have hle := Polynomial.natDegree_le_of_dvd
      (toPolynomial_dvd hgcdDvdValue) hpolyValue
    rw [HexPolyMathlib.natDegree_toPolynomial,
      HexPolyMathlib.natDegree_toPolynomial] at hle
    exact hle.trans_lt hvalueDegree
  have hgcdMapNe : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv gcd ≠ 0 := by
    intro hmap
    apply hgcdNe
    apply dense_eq_zero_of_eval level lower hinjective gcd hgcdDegree
    rw [← denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv level.degree gcd hgcdDegree]
    exact hmap
  rcases hgcdDvdRelation with ⟨factor, hfactor⟩
  have hfactorNe : factor ≠ 0 := by
    intro hzero
    apply hrelationNe
    rw [hfactor, hzero]
    rw [DensePoly.mul_comm_poly gcd 0]
    exact DensePoly.zero_mul gcd
  have hgcdDegreeZero : gcd.degree?.getD 0 = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hgcdPos
    have hfactorDegree : factor.degree?.getD 0 < level.degree := by
      have hgcdPolyNe : HexPolyMathlib.toPolynomial gcd ≠ 0 :=
        toPolynomial_ne_zero hgcdNe
      have hfactorPolyNe : HexPolyMathlib.toPolynomial factor ≠ 0 :=
        toPolynomial_ne_zero hfactorNe
      have hsum : level.degree =
          gcd.degree?.getD 0 + factor.degree?.getD 0 := by
        calc
          level.degree = (HexPolyMathlib.toPolynomial relation).natDegree := by
            simpa using hrelationDegree.symm
          _ = (HexPolyMathlib.toPolynomial (gcd * factor)).natDegree := by
            rw [← hfactor]
          _ = (HexPolyMathlib.toPolynomial gcd *
                HexPolyMathlib.toPolynomial factor).natDegree := by
            rw [HexPolyMathlib.toPolynomial_mul]
          _ = (HexPolyMathlib.toPolynomial gcd).natDegree +
                (HexPolyMathlib.toPolynomial factor).natDegree := by
            rw [Polynomial.natDegree_mul hgcdPolyNe hfactorPolyNe]
          _ = gcd.degree?.getD 0 + factor.degree?.getD 0 := by
            rw [HexPolyMathlib.natDegree_toPolynomial,
              HexPolyMathlib.natDegree_toPolynomial]
      omega
    have hfactorMap : denseMap lower level.root.toComplex hvalid.2.2
        hlowerInjective hinv factor = 0 := by
      have hproduct :
          denseMap lower level.root.toComplex hvalid.2.2 hlowerInjective hinv gcd *
              denseMap lower level.root.toComplex hvalid.2.2 hlowerInjective hinv factor = 0 := by
        rw [← denseMap_mul lower level.root.toComplex hvalid.2.2
          hlowerInjective hinv gcd factor, ← hfactor]
        exact hrelationMap
      exact (mul_eq_zero.mp hproduct).resolve_left hgcdMapNe
    apply hfactorNe
    apply dense_eq_zero_of_eval level lower hinjective factor hfactorDegree
    rw [← denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv level.degree factor hfactorDegree]
    exact hfactorMap
  have hgcdSizePos : 0 < gcd.size := by
    by_contra hpos
    apply hgcdNe
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le gcd (by omega)
  rw [DensePoly.degree?_eq_some_of_pos_size gcd hgcdSizePos,
    Option.getD_some] at hgcdDegreeZero
  omega

/-- The normalized extended-gcd coefficient used by executable inversion
denotes the reciprocal of a nonzero top-level coordinate array. -/
theorem denote_xgcd_inverse (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : DenoteInjective (level :: lower))
    (hlowerInjective : DenoteInjective lower)
    (hinv : ∀ b : Arithmetic.Coeff lower,
      coeffDenote lower b⁻¹ = (coeffDenote lower b)⁻¹)
    (a : Array Rat) (ha : denote (level :: lower) a ≠ 0) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid.2.2 hlowerInjective hinv
    let value := Arithmetic.Coeff.value level lower a
    let relation := Arithmetic.Coeff.relation level lower
    let result := DensePoly.xgcdLeft value relation
    let c := result.gcd.leadingCoeff
    let normalized := DensePoly.scale c⁻¹ result.left % relation
    denote (level :: lower)
        (Arithmetic.flattenBlocks level.degree (levelsDim lower)
          (((List.range level.degree).map fun i =>
            (normalized.coeff i).data).toArray)) =
      (denote (level :: lower) a)⁻¹ := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid.2.2 hlowerInjective hinv
  let value := Arithmetic.Coeff.value level lower a
  let relation := Arithmetic.Coeff.relation level lower
  let result := DensePoly.xgcdLeft value relation
  let c := result.gcd.leadingCoeff
  let scaled := DensePoly.scale c⁻¹ result.left
  change denote (level :: lower)
      (Arithmetic.flattenBlocks level.degree (levelsDim lower)
        (((List.range level.degree).map fun i =>
          ((scaled % relation).coeff i).data).toArray)) = _
  have hvalueDegree : value.degree?.getD 0 < level.degree :=
    value_degree_lt level lower a hvalid.1.1
  have hrelationDegree : relation.degree?.getD 0 = level.degree :=
    relation_degree level lower hvalid
  have hvalueMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv value = denote (level :: lower) a := by
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv level.degree value hvalueDegree]
    exact denseEval_value level lower a
  have hrelationMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv relation = 0 := by
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv (level.degree + 1) relation (by omega)]
    exact denseEval_relation level lower hvalid
  have hgcdSize : result.gcd.size = 1 := by
    exact xgcdLeft_size_one level lower hvalid hinjective hlowerInjective
      hinv a ha
  have hcNe : c ≠ 0 := by
    exact DensePoly.leadingCoeff_ne_zero_of_pos_size result.gcd
      (by rw [hgcdSize]; exact Nat.zero_lt_one)
  have hgcdC : result.gcd = DensePoly.C c :=
    eq_C_leadingCoeff_of_size_one result.gcd hgcdSize
  have hbezout :
      result.left * value +
          (DensePoly.xgcd value relation).right * relation = result.gcd := by
    have h := DensePoly.xgcd_bezout value relation
    dsimp only at h
    rw [← DensePoly.xgcdLeft_left_eq_xgcd value relation,
      ← DensePoly.xgcdLeft_gcd_eq_xgcd value relation] at h
    exact h
  have hmapBezout := congrArg
    (denseMap lower level.root.toComplex hvalid.2.2 hlowerInjective hinv)
    hbezout
  rw [denseMap_add, denseMap_mul, denseMap_mul, hrelationMap, mul_zero,
    add_zero, hgcdC, denseMap_C] at hmapBezout
  have hcMapNe : coeffDenote lower c ≠ 0 := by
    intro hmap
    apply hcNe
    apply hlowerInjective
    rw [hmap, coeffDenote_zero]
  have hscaledMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv scaled =
      (coeffDenote lower c)⁻¹ *
        denseMap lower level.root.toComplex hvalid.2.2
          hlowerInjective hinv result.left := by
    rw [denseMap_scale]
    exact congrArg (· * denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv result.left) (hinv c)
  have hnormalizedMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv (scaled % relation) =
      denseMap lower level.root.toComplex hvalid.2.2
        hlowerInjective hinv scaled := by
    have hdivision := EuclideanDomain.mod_add_div
      (HexPolyMathlib.toPolynomial scaled)
      (HexPolyMathlib.toPolynomial relation)
    have hmapDivision := congrArg
      (Polynomial.eval₂ (coeffHom lower hvalid.2.2 hlowerInjective hinv)
        level.root.toComplex) hdivision
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul] at hmapDivision
    have hrelationPolynomial :
        (HexPolyMathlib.toPolynomial relation).eval₂
            (coeffHom lower hvalid.2.2 hlowerInjective hinv)
            level.root.toComplex = 0 := hrelationMap
    rw [hrelationPolynomial, zero_mul, add_zero] at hmapDivision
    rw [denseMap, HexPolyMathlib.toPolynomial_mod, denseMap]
    exact hmapDivision
  have hnormalizedDegree : (scaled % relation).degree?.getD 0 < level.degree := by
    rw [← hrelationDegree]
    exact DensePoly.mod_degree_lt_of_pos_degree scaled relation (by
      rw [hrelationDegree]
      exact hvalid.1.1)
  rw [denote_flatten_dense, ← denseMap_eq_denseEval lower
    level.root.toComplex hvalid.2.2 hlowerInjective hinv level.degree
    (scaled % relation) hnormalizedDegree, hnormalizedMap, hscaledMap]
  apply (mul_eq_one_iff_eq_inv₀ ha).mp
  rw [mul_assoc, ← hvalueMap, hmapBezout]
  exact inv_mul_cancel₀ hcMapNe

/-- A lower-tower coefficient embedded as the constant coefficient of one
extension level. -/
@[expose]
def liftCoeff (level : Level) (lower : List Level)
    (a : Arithmetic.Coeff lower) : Arithmetic.Coeff (level :: lower) :=
  ⟨Arithmetic.flattenBlocks level.degree (levelsDim lower) #[a.data], by
    simp [levelsDim]⟩

/-- Constant-block embedding preserves coefficient denotation. -/
theorem coeffDenote_lift (level : Level) (lower : List Level)
    (hdegree : 0 < level.degree) (a : Arithmetic.Coeff lower) :
    coeffDenote (level :: lower) (liftCoeff level lower a) =
      coeffDenote lower a := by
  rw [coeffDenote, liftCoeff, denote_flatten]
  change (∑ i ∈ Finset.range level.degree,
      denote lower ((#[a.data] : Array (Array Rat)).getD i #[]) *
        level.root.toComplex ^ i) = denote lower a.data
  calc
    _ = denote lower ((#[a.data] : Array (Array Rat)).getD 0 #[]) *
        level.root.toComplex ^ 0 := by
      apply Finset.sum_eq_single 0
      · intro i hi hi0
        have hget : (#[a.data] : Array (Array Rat)).getD i #[] = #[] := by
          simp [Array.getD, hi0]
        rw [hget, ← denote_fixed lower #[], denote_zero]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hdegree)).elim
    _ = denote lower a.data := by simp [Array.getD]

/-- Injectivity at an extension level implies injectivity for its lower
coefficient tower. -/
theorem DenoteInjective.tail (level : Level) (lower : List Level)
    (hdegree : 0 < level.degree) (hinjective : DenoteInjective (level :: lower)) :
    DenoteInjective lower := by
  intro a b hab
  have hlift : liftCoeff level lower a = liftCoeff level lower b := by
    apply hinjective
    rw [coeffDenote_lift level lower hdegree,
      coeffDenote_lift level lower hdegree]
    exact hab
  have hblock := congrArg
    (fun c : Arithmetic.Coeff (level :: lower) =>
      Arithmetic.block c.data 0 (levelsDim lower)) hlift
  simp only [liftCoeff] at hblock
  rw [Arithmetic.block_flatten level.degree (levelsDim lower) 0 #[a.data]
      hdegree,
    Arithmetic.block_flatten level.degree (levelsDim lower) 0 #[b.data]
      hdegree] at hblock
  simp [Array.getD] at hblock
  rw [fixedCoeffs_eq_self lower a, fixedCoeffs_eq_self lower b] at hblock
  cases a with
  | mk ad ha =>
      cases b with
      | mk bd hb =>
          simp only at hblock
          cases hblock
          rfl

/-- The executable fixed-width all-zero test is equivalent to semantic zero
when canonical coefficient denotation is injective. -/
theorem fixed_all_zero_iff (levels : List Level)
    (hinjective : DenoteInjective levels) (a : Array Rat) :
    (Arithmetic.fixedCoeffs (levelsDim levels) a).all (fun q => q = 0) = true ↔
      denote levels a = 0 := by
  constructor
  · intro hall
    rw [← denote_fixed levels a]
    have hdata : Arithmetic.fixedCoeffs (levelsDim levels) a =
        Arithmetic.fixedCoeffs (levelsDim levels) #[] := by
      apply Array.ext
      · simp [Arithmetic.fixedCoeffs]
      · intro i hi₁ hi₂
        have hi := (Array.all_eq_true.mp hall) i hi₁
        simpa [Arithmetic.fixedCoeffs, Array.getD] using hi
    rw [hdata, denote_zero]
  · intro hdenote
    have hcoeff : Arithmetic.Coeff.ofData levels a = 0 := by
      apply hinjective
      change denote levels (Arithmetic.fixedCoeffs (levelsDim levels) a) =
        coeffDenote levels 0
      rw [denote_fixed, hdenote, coeffDenote_zero]
    have hdata := congrArg Arithmetic.Coeff.data hcoeff
    change Arithmetic.fixedCoeffs (levelsDim levels) a =
      Arithmetic.fixedCoeffs (levelsDim levels) #[] at hdata
    rw [Array.all_eq_true]
    intro i hi
    have hentry := congrArg (fun data : Array Rat => data.getD i 0) hdata
    have hiBound : i < levelsDim levels := by
      simpa [Arithmetic.fixedCoeffs] using hi
    simpa [Arithmetic.fixedCoeffs, Array.getD, hiBound] using hentry

/-- Recursive extended-gcd coordinates denote complex inversion at every
validated tower depth, including the executable `0⁻¹ = 0` convention. -/
theorem denote_invCoords (levels : List Level) (hvalid : LevelsValid levels)
    (hinjective : DenoteInjective levels) (a : Array Rat) :
    denote levels (Arithmetic.invCoords levels a) = (denote levels a)⁻¹ := by
  induction levels generalizing a with
  | nil =>
      rw [show Arithmetic.invCoords [] a =
        #[if a.getD 0 0 = 0 then 0 else (a.getD 0 0)⁻¹] from rfl]
      simp only [denote]
      by_cases h : a[0]?.getD 0 = 0 <;> simp [h]
  | cons level lower ih =>
      have hlowerInjective : DenoteInjective lower :=
        DenoteInjective.tail level lower hvalid.1.1 hinjective
      have hlowerInv : ∀ b : Arithmetic.Coeff lower,
          coeffDenote lower b⁻¹ = (coeffDenote lower b)⁻¹ := by
        intro b
        change denote lower
            (Arithmetic.fixedCoeffs (levelsDim lower)
              (Arithmetic.invCoords lower b.data)) =
          (denote lower b.data)⁻¹
        rw [denote_fixed]
        exact ih hvalid.2.2 hlowerInjective b.data
      letI : Field (Arithmetic.Coeff lower) :=
        coeffField lower hvalid.2.2 hlowerInjective hlowerInv
      let zeroTest :=
        (Arithmetic.fixedCoeffs
          (level.degree * levelsDim lower) a).all (fun q => q = 0)
      by_cases hzero : zeroTest = true
      · have hdenote : denote (level :: lower) a = 0 :=
          (fixed_all_zero_iff (level :: lower) hinjective a).mp (by
            simpa [zeroTest, levelsDim] using hzero)
        have hrep : Array.replicate (level.degree * levelsDim lower) 0 =
            Arithmetic.fixedCoeffs (levelsDim (level :: lower)) #[] := by
          apply Array.ext
          · simp [levelsDim, Arithmetic.fixedCoeffs]
          · intro i hi₁ hi₂
            simp [Arithmetic.fixedCoeffs, Array.getD]
        rw [Arithmetic.invCoords]
        rw [show (Arithmetic.fixedCoeffs
            (level.degree * levelsDim lower) a).all (fun q => q = 0) = true by
          simpa [zeroTest] using hzero]
        simp only [if_true]
        rw [hrep, denote_zero, hdenote]
        simp
      · have ha : denote (level :: lower) a ≠ 0 := by
          intro hdenote
          apply hzero
          simpa [zeroTest, levelsDim] using
            (fixed_all_zero_iff (level :: lower) hinjective a).mpr hdenote
        have hgcdSize := xgcdLeft_size_one level lower hvalid hinjective
          hlowerInjective hlowerInv a ha
        let value := Arithmetic.Coeff.value level lower a
        let relation := Arithmetic.Coeff.relation level lower
        let result := DensePoly.xgcdLeft value relation
        have hcNe : result.gcd.leadingCoeff ≠ 0 := by
          exact DensePoly.leadingCoeff_ne_zero_of_pos_size result.gcd
            (by rw [hgcdSize]; exact Nat.zero_lt_one)
        rw [Arithmetic.invCoords]
        rw [show (Arithmetic.fixedCoeffs
            (level.degree * levelsDim lower) a).all (fun q => q = 0) = false by
          exact Bool.eq_false_of_not_eq_true hzero]
        simp only [Bool.false_eq_true, if_false]
        rw [if_pos hgcdSize, if_neg hcNe]
        exact denote_xgcd_inverse level lower hvalid hinjective
          hlowerInjective hlowerInv a ha

end LevelSemantics

/-- The canonical coefficient denotation of a certified tower is injective. -/
theorem coeffDenote_injective (T : NumberTower) :
    LevelSemantics.DenoteInjective T.levels.toList := by
  intro a b hab
  have ha : normalizeCoeffs T a.data = a.data :=
    normalizeCoeffs_eq_self T a.data (by simpa [dim] using a.size_eq)
  have hb : normalizeCoeffs T b.data = b.data :=
    normalizeCoeffs_eq_self T b.data (by simpa [dim] using b.size_eq)
  have helem : ofCoeffs T a.data = ofCoeffs T b.data := by
    apply toComplex_injective T
    rw [LevelSemantics.toComplex_eq_denote T (ofCoeffs T a.data),
      LevelSemantics.toComplex_eq_denote T (ofCoeffs T b.data),
      coeffs_ofCoeffs, coeffs_ofCoeffs, ha, hb]
    exact hab
  have hdata : a.data = b.data := by
    simpa [ha, hb] using congrArg coeffs helem
  cases a with
  | mk ad hasize =>
      cases b with
      | mk bd hbsize =>
          simp only at hdata
          cases hdata
          rfl

/-- Executable zero denotes complex zero. -/
theorem map_zero (T : NumberTower) :
    T.toComplex (0 : Elem T) = 0 := by
  rw [zero_eq_ofRat]
  simpa using toComplex_ofRat T 0

/-- Executable one denotes complex one. -/
theorem map_one (T : NumberTower) :
    T.toComplex (1 : Elem T) = 1 := by
  rw [one_eq_ofRat]
  simpa using toComplex_ofRat T 1

/-- Coordinate addition computes complex addition. -/
theorem map_add (T : NumberTower) (a b : Elem T) :
    T.toComplex (a + b) = T.toComplex a + T.toComplex b := by
  rw [LevelSemantics.toComplex_eq_denote T (a + b),
    LevelSemantics.toComplex_eq_denote T a,
    LevelSemantics.toComplex_eq_denote T b, coeffs_add]
  simpa [dim] using
    LevelSemantics.denote_add T.levels.toList (coeffs a) (coeffs b)

/-- Coordinate negation computes complex negation. -/
theorem map_neg (T : NumberTower) (a : Elem T) :
    T.toComplex (-a) = -T.toComplex a := by
  have h := map_add T a (-a)
  rw [NumberTower.add_neg_self, map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Coordinate subtraction computes complex subtraction. -/
theorem map_sub (T : NumberTower) (a b : Elem T) :
    T.toComplex (a - b) = T.toComplex a - T.toComplex b := by
  rw [NumberTower.sub_eq_add_neg, map_add, map_neg]
  rfl

/-- Recursive reduced multiplication computes complex multiplication. -/
theorem map_mul (T : NumberTower) (a b : Elem T) :
    T.toComplex (a * b) = T.toComplex a * T.toComplex b := by
  rw [LevelSemantics.toComplex_eq_denote T (a * b),
    LevelSemantics.toComplex_eq_denote T a,
    LevelSemantics.toComplex_eq_denote T b, coeffs_mul]
  exact LevelSemantics.denote_mul T.levels.toList T.valid (coeffs a) (coeffs b)

/-- Recursive extended-gcd inversion computes complex inversion, including
the executable convention `0⁻¹ = 0`. -/
theorem map_inv (T : NumberTower) (a : Elem T) :
    T.toComplex a⁻¹ = (T.toComplex a)⁻¹ := by
  rw [LevelSemantics.toComplex_eq_denote T a⁻¹,
    LevelSemantics.toComplex_eq_denote T a, coeffs_inv]
  exact LevelSemantics.denote_invCoords T.levels.toList T.valid
    (coeffDenote_injective T) (coeffs a)

/-- Tower division computes complex division. -/
theorem map_div (T : NumberTower) (a b : Elem T) :
    T.toComplex (a / b) = T.toComplex a / T.toComplex b := by
  change T.toComplex (a * b⁻¹) = _
  rw [map_mul, map_inv]
  rfl

/-- The executable rational scalar action is semantic scalar multiplication. -/
theorem map_smul (T : NumberTower) (q : Rat) (a : Elem T) :
    T.toComplex (q • a) = (q : ℂ) * T.toComplex a := by
  rw [LevelSemantics.toComplex_eq_denote T (q • a),
    LevelSemantics.toComplex_eq_denote T a, coeffs_smul,
    LevelSemantics.denote_smul]

/-- The Boolean zero test recognizes exactly semantic zero. -/
theorem isZero_iff (T : NumberTower) (a : Elem T) :
    NumberTower.isZero a ↔ T.toComplex a = 0 := by
  rw [NumberTower.isZero_iff_eq_zero]
  constructor
  · rintro rfl
    exact map_zero T
  · intro h
    apply toComplex_injective T
    rw [h, map_zero]

/-- Mixed-radix coordinate equality is exactly semantic equality. -/
theorem eq_iff_toComplex (T : NumberTower) (a b : Elem T) :
    a = b ↔ T.toComplex a = T.toComplex b := by
  constructor
  · exact fun h => congrArg T.toComplex h
  · intro h
    exact @toComplex_injective T a b h

namespace Extension

/-- An extension embedding preserves the fixed absolute embedding. This is a
property of checked constructors, not of arbitrary `Extension` records. -/
def PreservesEmbedding {T : NumberTower} (E : Extension T) : Prop :=
  ∀ a, E.tower.toComplex (E.embed a) = T.toComplex a

/-- The distinguished generator denotes the extension's stored absolute
root. -/
def GeneratorValue {T : NumberTower} (E : Extension T) : Prop :=
  E.tower.toComplex E.gen = E.root.toComplex

end Extension

end Hex.NumberTower
