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

end LevelSemantics

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
  sorry

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
