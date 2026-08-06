/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Basic

public section

/-!
# Generic arithmetic correspondence for tower coordinates

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

/-- Evaluate top-level mixed-radix coordinates at an arbitrary conjugate of
the newest generator while retaining the fixed lower embedding. -/
@[expose]
noncomputable def evalAt (level : Level) (lower : List Level)
    (x : ℂ) (data : Array Rat) : ℂ :=
  ∑ i ∈ Finset.range level.degree,
    denote lower (Arithmetic.block data i (levelsDim lower)) * x ^ i

/-- Flattening explicit top-level blocks preserves arbitrary-conjugate
evaluation. -/
theorem evalAt_flatten (level : Level) (lower : List Level) (x : ℂ)
    (blocks : Array (Array Rat)) :
    evalAt level lower x
        (Arithmetic.flattenBlocks level.degree (levelsDim lower) blocks) =
      evalUpTo lower x level.degree blocks := by
  unfold evalAt evalUpTo
  apply Finset.sum_congr rfl
  intro i hi
  rw [Arithmetic.block_flatten level.degree (levelsDim lower) i blocks
    (Finset.mem_range.mp hi), denote_fixed]

/-- Fixed-width normalization does not change arbitrary-conjugate
evaluation. -/
theorem evalAt_fixed (level : Level) (lower : List Level) (x : ℂ)
    (data : Array Rat) :
    evalAt level lower x
        (Arithmetic.fixedCoeffs
          (level.degree * levelsDim lower) data) =
      evalAt level lower x data := by
  unfold evalAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [Arithmetic.block_fixed level.degree (levelsDim lower) i data
    (Finset.mem_range.mp hi), denote_fixed]

/-- The selected stored root specializes arbitrary-conjugate evaluation back
to canonical tower denotation. -/
theorem evalAt_root (level : Level) (lower : List Level) (data : Array Rat) :
    evalAt level lower level.root.toComplex data =
      denote (level :: lower) data := by
  rw [evalAt, denote_cons]

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

/-- A fixed-width lower coordinate vector occupies the constant block of the
next extension level. -/
theorem denote_embed (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) (data : Array Rat)
    (hsize : data.size = levelsDim lower) :
    denote (level :: lower) data = denote lower data := by
  rw [denote_cons]
  have hblockZero : Arithmetic.block data 0 (levelsDim lower) = data := by
    apply Array.ext
    · simp [Arithmetic.block, hsize]
    · intro j hj₁ hj₂
      simp [Arithmetic.block, Array.getD, hj₂]
  calc
    _ = denote lower (Arithmetic.block data 0 (levelsDim lower)) *
        level.root.toComplex ^ 0 := by
      apply Finset.sum_eq_single 0
      · intro i hi hi0
        have hiOne : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
        have hblock : Arithmetic.block data i (levelsDim lower) =
            Arithmetic.fixedCoeffs (levelsDim lower) #[] := by
          apply Array.ext
          · simp [Arithmetic.block, Arithmetic.fixedCoeffs]
          · intro j hj₁ hj₂
            have hwidthLe : levelsDim lower ≤ i * levelsDim lower := by
              simpa [Nat.one_mul] using
                Nat.mul_le_mul_right (levelsDim lower) hiOne
            have hglobal : data.size ≤ i * levelsDim lower + j := by
              omega
            simp [Arithmetic.block, Arithmetic.fixedCoeffs, Array.getD, hglobal]
        rw [hblock, denote_zero]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr
          (Nat.zero_lt_of_lt hvalid.1.1))).elim
    _ = denote lower data := by
      rw [hblockZero]
      simp

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
                exact (hnot (Finset.mem_range.mpr
                  (Nat.zero_lt_of_lt hvalid.1.1))).elim
        _ = denote lower
              (Arithmetic.fixedCoeffs (levelsDim lower) #[1]) *
            level.root.toComplex ^ 0 := by
              rw [Arithmetic.block_one level.degree (levelsDim lower) 0
                (Nat.zero_lt_of_lt hvalid.1.1)]
              simp
        _ = 1 := by rw [ih hvalid.2.2]; simp

/-- A one-coordinate rational constant has its usual complex value at every
validated tower depth. -/
theorem denote_rat (levels : List Level) (hvalid : LevelsValid levels)
    (q : Rat) : denote levels #[q] = (q : ℂ) := by
  have hone : denote levels #[1] = 1 := by
    rw [← denote_fixed levels #[1]]
    exact denote_one levels hvalid
  simpa [hone] using denote_smul levels q #[1]

@[simp]
theorem evalAt_zero (level : Level) (lower : List Level)
    (_hvalid : LevelsValid (level :: lower)) (x : ℂ) :
    evalAt level lower x
        (0 : Arithmetic.Coeff (level :: lower)).data = 0 := by
  change evalAt level lower x
      (Arithmetic.fixedCoeffs (level.degree * levelsDim lower) #[]) = 0
  unfold evalAt
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < level.degree := Finset.mem_range.mp hi
  rw [Arithmetic.block_fixed level.degree (levelsDim lower) i #[] hi']
  have hempty : Arithmetic.fixedCoeffs (levelsDim lower)
      (Arithmetic.block #[] i (levelsDim lower)) =
        Arithmetic.fixedCoeffs (levelsDim lower) #[] := by
    apply Array.ext
    · simp [Arithmetic.fixedCoeffs]
    · intro j hj₁ hj₂
      simp [Arithmetic.fixedCoeffs, Arithmetic.block, Array.getD]
  rw [hempty, denote_zero]
  simp

@[simp]
theorem evalAt_one (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) (x : ℂ) :
    evalAt level lower x
        (1 : Arithmetic.Coeff (level :: lower)).data = 1 := by
  change evalAt level lower x
      (Arithmetic.fixedCoeffs (level.degree * levelsDim lower) #[1]) = 1
  unfold evalAt
  calc
    _ = denote lower
          (Arithmetic.block
            (Arithmetic.fixedCoeffs (level.degree * levelsDim lower) #[1])
            0 (levelsDim lower)) * x ^ 0 := by
        apply Finset.sum_eq_single 0
        · intro i hi hi0
          rw [Arithmetic.block_one level.degree (levelsDim lower) i
            (Finset.mem_range.mp hi)]
          simp [hi0, denote_zero]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr
            (Nat.zero_lt_of_lt hvalid.1.1))).elim
    _ = denote lower
          (Arithmetic.fixedCoeffs (levelsDim lower) #[1]) * x ^ 0 := by
        rw [Arithmetic.block_one level.degree (levelsDim lower) 0
          (Nat.zero_lt_of_lt hvalid.1.1)]
        simp
    _ = 1 := by rw [denote_one lower hvalid.2.2]; simp

theorem evalAt_add (level : Level) (lower : List Level)
    (_hvalid : LevelsValid (level :: lower)) (x : ℂ)
    (a b : Arithmetic.Coeff (level :: lower)) :
    evalAt level lower x (a + b).data =
      evalAt level lower x a.data + evalAt level lower x b.data := by
  unfold evalAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < level.degree := Finset.mem_range.mp hi
  change denote lower
      (Arithmetic.block
        (Arithmetic.addCoords (level.degree * levelsDim lower) a.data b.data)
        i (levelsDim lower)) * x ^ i = _
  rw [Arithmetic.block_add level.degree (levelsDim lower) i a.data b.data hi',
    denote_add]
  ring

/-- The mixed-radix basis coordinate immediately after the lower block
denotes the newly adjoined generator. -/
theorem denote_generator (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) (hdegree : 1 < level.degree) :
    denote (level :: lower)
        ((Array.replicate (levelsDim lower) 0).push 1) =
      level.root.toComplex := by
  let width := levelsDim lower
  let data := (Array.replicate width (0 : Rat)).push 1
  have hwidth : 0 < width := levelsDim_pos lower hvalid.2.2
  have hblockOne : Arithmetic.block data 1 width =
      Arithmetic.fixedCoeffs width #[1] := by
    unfold Arithmetic.block Arithmetic.fixedCoeffs
    congr 1
    apply Vector.ext
    intro j hjWidth
    simp only [Vector.getElem_ofFn, Nat.one_mul]
    by_cases hj : j = 0
    · subst j
      have hindex : width < data.size := by simp [data]
      simp only [Nat.add_zero]
      rw [← Array.getElem_eq_getD (0 : Rat) (h := hindex)]
      change ((Array.replicate width (0 : Rat)).push 1)[width] = 1
      simpa using
        (Array.getElem_push_eq (xs := Array.replicate width (0 : Rat)) (x := 1))
    · have hglobal : data.size ≤ width + j := by
        simp [data]
        omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hglobal]
      simp [Array.getD, hj]
  have hblockOther (i : Nat) (hi : i ≠ 1) :
      Arithmetic.block data i width = Arithmetic.fixedCoeffs width #[] := by
    unfold Arithmetic.block Arithmetic.fixedCoeffs
    congr 1
    apply Vector.ext
    intro j hjWidth
    simp only [Vector.getElem_ofFn]
    rcases Nat.eq_zero_or_pos i with rfl | hiPos
    · have hindex : j < data.size := by
        simp [data]
        omega
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [← Array.getElem_eq_getD (0 : Rat) (h := hindex)]
      have hreplicate : j < (Array.replicate width (0 : Rat)).size := by
        simpa using hjWidth
      change ((Array.replicate width (0 : Rat)).push 1)[j] = 0
      rw [Array.getElem_push_lt hreplicate,
        Array.getElem_replicate hreplicate]
    · have hiTwo : 2 ≤ i := by omega
      have htwice : width * 2 ≤ width * i :=
        Nat.mul_le_mul_left width hiTwo
      have hglobal : data.size ≤ i * width + j := by
        simp [data]
        rw [Nat.mul_comm i width]
        omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hglobal]
      rfl
  change denote (level :: lower) data = _
  rw [denote_cons]
  calc
    _ = denote lower (Arithmetic.block data 1 width) *
        level.root.toComplex ^ 1 := by
      apply Finset.sum_eq_single 1
      · intro i hi hiOne
        rw [hblockOther i hiOne, denote_zero]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hdegree)).elim
    _ = level.root.toComplex := by
      rw [hblockOne, denote_one lower hvalid.2.2]
      simp

/-- The mixed-radix basis coordinate immediately after the lower block
evaluates to the chosen conjugate of the newest generator. -/
theorem evalAt_generator (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) (hdegree : 1 < level.degree)
    (x : ℂ) :
    evalAt level lower x
        ((Array.replicate (levelsDim lower) 0).push 1) = x := by
  let width := levelsDim lower
  let data := (Array.replicate width (0 : Rat)).push 1
  have hwidth : 0 < width := levelsDim_pos lower hvalid.2.2
  have hblockOne : Arithmetic.block data 1 width =
      Arithmetic.fixedCoeffs width #[1] := by
    unfold Arithmetic.block Arithmetic.fixedCoeffs
    congr 1
    apply Vector.ext
    intro j hjWidth
    simp only [Vector.getElem_ofFn, Nat.one_mul]
    by_cases hj : j = 0
    · subst j
      have hindex : width < data.size := by simp [data]
      simp only [Nat.add_zero]
      rw [← Array.getElem_eq_getD (0 : Rat) (h := hindex)]
      change ((Array.replicate width (0 : Rat)).push 1)[width] = 1
      simpa using
        (Array.getElem_push_eq (xs := Array.replicate width (0 : Rat)) (x := 1))
    · have hglobal : data.size ≤ width + j := by
        simp [data]
        omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hglobal]
      simp [Array.getD, hj]
  have hblockOther (i : Nat) (hi : i ≠ 1) :
      Arithmetic.block data i width = Arithmetic.fixedCoeffs width #[] := by
    unfold Arithmetic.block Arithmetic.fixedCoeffs
    congr 1
    apply Vector.ext
    intro j hjWidth
    simp only [Vector.getElem_ofFn]
    rcases Nat.eq_zero_or_pos i with rfl | hiPos
    · have hindex : j < data.size := by
        simp [data]
        omega
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [← Array.getElem_eq_getD (0 : Rat) (h := hindex)]
      have hreplicate : j < (Array.replicate width (0 : Rat)).size := by
        simpa using hjWidth
      change ((Array.replicate width (0 : Rat)).push 1)[j] = 0
      rw [Array.getElem_push_lt hreplicate,
        Array.getElem_replicate hreplicate]
    · have hiTwo : 2 ≤ i := by omega
      have htwice : width * 2 ≤ width * i :=
        Nat.mul_le_mul_left width hiTwo
      have hglobal : data.size ≤ i * width + j := by
        simp [data]
        rw [Nat.mul_comm i width]
        omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hglobal]
      rfl
  change evalAt level lower x data = _
  unfold evalAt
  calc
    _ = denote lower (Arithmetic.block data 1 width) * x ^ 1 := by
      apply Finset.sum_eq_single 1
      · intro i hi hiOne
        rw [hblockOther i hiOne, denote_zero]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hdegree)).elim
    _ = x := by
      rw [hblockOne, denote_one lower hvalid.2.2]
      simp

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

/-- One descending reduction step preserves evaluation at any zero of the
mapped monic level relation. -/
private theorem reduceAt_eval_of_relation (level : Level) (lower : List Level)
    (x : ℂ)
    (hrelationInput :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0)
    (k : Nat) (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat)) (hvalid : LevelsValid (level :: lower))
    (hdk : level.degree ≤ k) (hsize : work.size = k + 1)
    (hmul : ∀ u v, denote lower (multiply u v) =
      denote lower u * denote lower v) :
    evalUpTo lower x k
        (Arithmetic.reduceAt level.degree (levelsDim lower) k
          level.defining multiply work) =
      evalUpTo lower x (k + 1) work := by
  let zeroBlock : Array Rat := Array.replicate (levelsDim lower) 0
  let high := work.getD k zeroBlock
  have hdefault (j : Nat) (hj : j < level.degree) :
      level.defining.getD j zeroBlock = level.defining.getD j #[] := by
    have hj' : j < level.defining.size := by
      simpa [hvalid.1.2.1] using hj
    simp [Array.getD, hj']
  have hrelation :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j zeroBlock) * x ^ j) +
        x ^ level.degree = 0 := by
    have hsum :
        (∑ j ∈ Finset.range level.degree,
            denote lower (level.defining.getD j zeroBlock) * x ^ j) =
          ∑ j ∈ Finset.range level.degree,
            denote lower (level.defining.getD j #[]) * x ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hdefault j (Finset.mem_range.mp hj)]
    rw [hsum]
    exact hrelationInput
  have hrelation' :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j zeroBlock) * x ^ j) =
        -x ^ level.degree := by
    linear_combination hrelation
  have hcorrection :
      (∑ j ∈ Finset.range level.degree,
          -(denote lower high *
            denote lower (level.defining.getD j zeroBlock) *
              x ^ (k - level.degree + j))) =
        denote lower high * x ^ k := by
    calc
      _ = -(∑ j ∈ Finset.range level.degree,
            denote lower high *
              denote lower (level.defining.getD j zeroBlock) *
                x ^ (k - level.degree + j)) := by
              rw [Finset.sum_neg_distrib]
      _ = -(denote lower high * x ^ (k - level.degree) *
            ∑ j ∈ Finset.range level.degree,
              denote lower (level.defining.getD j zeroBlock) * x ^ j) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [pow_add]
              ring
      _ = denote lower high * x ^ (k - level.degree) *
            x ^ level.degree := by
              rw [hrelation']
              ring
      _ = denote lower high * x ^ k := by
              rw [mul_assoc, ← pow_add]
              congr 2
              omega
  have heval_succ :
      evalUpTo lower x (k + 1) work =
        evalUpTo lower x k work + denote lower high * x ^ k := by
    have hk : k < work.size := by omega
    unfold evalUpTo
    rw [Finset.sum_range_succ]
    simp [high, Array.getD, hk]
  rw [Arithmetic.reduceAt,
    evalUpTo_take lower x k k _ (Nat.le_refl k),
    reduceCoeffs_eval lower x level.degree k level.defining multiply work
      hdk hsize hmul,
    hcorrection, heval_succ]

/-- Full descending reduction preserves evaluation at any zero of the mapped
monic relation. -/
private theorem reduce_eval_of_relation (level : Level) (lower : List Level)
    (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0)
    (fuel : Nat) (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat)) (hvalid : LevelsValid (level :: lower))
    (hsize : work.size = level.degree + fuel)
    (hmul : ∀ u v, denote lower (multiply u v) =
      denote lower u * denote lower v) :
    evalUpTo lower x level.degree
        (Arithmetic.reduce level.degree (levelsDim lower) level.defining
          multiply fuel work) =
      evalUpTo lower x (level.degree + fuel) work := by
  induction fuel generalizing work with
  | zero =>
      simp only [Arithmetic.reduce]
      simpa using evalUpTo_take lower x level.degree level.degree work
        (Nat.le_refl level.degree)
  | succ fuel ih =>
      let next := Arithmetic.reduceAt level.degree (levelsDim lower)
        (level.degree + fuel) level.defining multiply work
      have hnext : next.size = level.degree + fuel := by
        apply Arithmetic.reduceAt_size
        omega
      simp only [Arithmetic.reduce]
      rw [ih next hnext]
      simpa [next, Nat.add_assoc] using
        reduceAt_eval_of_relation level lower x hrelation
          (level.degree + fuel) multiply work hvalid
          (Nat.le_add_right level.degree fuel) (by omega) hmul

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
      have hdegree : 0 < level.degree := Nat.zero_lt_of_lt hvalid.1.1
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

/-- Recursive reduced multiplication is respected by evaluation at every
complex zero of the mapped top-level relation. -/
theorem evalAt_mul (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0)
    (a b : Array Rat) :
    evalAt level lower x (Arithmetic.mulCoords (level :: lower) a b) =
      evalAt level lower x a * evalAt level lower x b := by
  have hdegree : 0 < level.degree := Nat.zero_lt_of_lt hvalid.1.1
  have hmul : ∀ u v,
      denote lower (Arithmetic.mulCoords lower u v) =
        denote lower u * denote lower v :=
    denote_mul lower hvalid.2.2
  simp only [Arithmetic.mulCoords]
  rw [if_neg (Nat.ne_of_gt hdegree)]
  rw [evalAt_flatten]
  change evalUpTo lower x level.degree
      (Arithmetic.reduce level.degree (levelsDim lower) level.defining
        (Arithmetic.mulCoords lower) (level.degree - 1)
        (Arithmetic.convolve level.degree (levelsDim lower)
          (Arithmetic.mulCoords lower) a b)) =
    evalAt level lower x a * evalAt level lower x b
  rw [reduce_eval_of_relation level lower x hrelation
    (level.degree - 1) (Arithmetic.mulCoords lower)
    (Arithmetic.convolve level.degree (levelsDim lower)
      (Arithmetic.mulCoords lower) a b) hvalid (by simp; omega) hmul]
  rw [show level.degree + (level.degree - 1) =
      2 * level.degree - 1 by omega]
  rw [convolve_mul lower x level.degree a b
    (Arithmetic.mulCoords lower) hdegree hmul]
  rw [evalAt, evalAt]

/-! # Canonical coefficient denotation -/

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

@[simp]
theorem coeff_ofData_data (levels : List Level)
    (a : Arithmetic.Coeff levels) :
    Arithmetic.Coeff.ofData levels a.data = a := by
  apply coeff_eq_of_data_eq
  exact fixedCoeffs_eq_self levels a

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

/-- Evaluation at the selected generator distinguishes all lower-coefficient
polynomials below the defining degree. This is the exact semantic consequence
of irreducibility needed to construct the next tower embedding. -/
def Separates (level : Level) (lower : List Level) : Prop :=
  ∀ f g : DensePoly (Arithmetic.Coeff lower),
    f.degree?.getD 0 < level.degree →
    g.degree?.getD 0 < level.degree →
    denseEval lower level.root.toComplex level.degree f =
    denseEval lower level.root.toComplex level.degree g →
    f = g

/-- Rational fixed-width coefficients have unique complex denotation. -/
theorem DenoteInjective.nil : DenoteInjective [] := by
  intro a b hab
  apply coeff_eq_of_data_eq
  have haSize : a.data.size = 1 := by
    simpa [levelsDim] using a.size_eq
  have hbSize : b.data.size = 1 := by
    simpa [levelsDim] using b.size_eq
  have hvalue : a.data.getD 0 0 = b.data.getD 0 0 := by
    change ((a.data.getD 0 0 : Rat) : ℂ) =
      ((b.data.getD 0 0 : Rat) : ℂ) at hab
    exact_mod_cast hab
  apply Array.ext
  · omega
  · intro i hai hbi
    have hi : i = 0 := by omega
    subst i
    simpa [Array.getD, haSize, hbSize] using hvalue

private theorem value_injective (level : Level) (lower : List Level)
    (hlowerDim : 0 < levelsDim lower)
    {a b : Arithmetic.Coeff (level :: lower)}
    (hvalue : Arithmetic.Coeff.value level lower a.data =
      Arithmetic.Coeff.value level lower b.data) :
    a = b := by
  apply coeff_eq_of_data_eq
  apply Array.ext
  · exact a.size_eq.trans b.size_eq.symm
  · intro k hka hkb
    have hk : k < level.degree * levelsDim lower := by
      have hka' := hka
      rw [a.size_eq] at hka'
      simpa [levelsDim] using hka'
    let i := k / levelsDim lower
    let j := k % levelsDim lower
    have hi : i < level.degree := by
      dsimp [i]
      exact (Nat.div_lt_iff_lt_mul hlowerDim).2 (by
        simpa [Nat.mul_comm] using hk)
    have hj : j < levelsDim lower := by
      exact Nat.mod_lt _ hlowerDim
    have hcoefficient := congrArg
      (fun f : DensePoly (Arithmetic.Coeff lower) => f.coeff i) hvalue
    have hblock : Arithmetic.block a.data i (levelsDim lower) =
        Arithmetic.block b.data i (levelsDim lower) := by
      simp only [Arithmetic.Coeff.value, DensePoly.coeff_ofCoeffs]
        at hcoefficient
      have hdata := congrArg Arithmetic.Coeff.data hcoefficient
      simpa [Arithmetic.Coeff.ofData, Arithmetic.fixedCoeffs,
        Arithmetic.block, Array.getD, hi] using hdata
    have hentry := congrArg
      (fun data : Array Rat => data.getD j 0) hblock
    have hkdecomp : i * levelsDim lower + j = k := by
      dsimp [i, j]
      rw [Nat.mul_comm]
      exact Nat.div_add_mod k (levelsDim lower)
    simp [Arithmetic.block, Array.getD, hj] at hentry
    rw [hkdecomp] at hentry
    simpa [hka, hkb] using hentry

/-- Separating evaluation at one level extends injectivity of the lower fixed
embedding to injectivity of the next canonical coefficient carrier. -/
theorem DenoteInjective.cons (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) (hseparates : Separates level lower) :
    DenoteInjective (level :: lower) := by
  intro a b hab
  apply value_injective level lower (levelsDim_pos lower hvalid.2.2)
  apply hseparates
  · exact value_degree_lt level lower a.data
      (Nat.zero_lt_of_lt hvalid.1.1)
  · exact value_degree_lt level lower b.data
      (Nat.zero_lt_of_lt hvalid.1.1)
  · rw [denseEval_value, denseEval_value]
    exact hab

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

/-- An irreducible defining relation that vanishes at the selected generator
makes evaluation injective below its degree. -/
theorem separates_of_irreducible (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hlowerInjective : DenoteInjective lower)
    (hlowerInv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid.2.2 hlowerInjective hlowerInv
    Irreducible (HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level lower)) →
      Separates level lower := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid.2.2 hlowerInjective hlowerInv
  intro hirreducible
  let ι : Arithmetic.Coeff lower →+* ℂ :=
    coeffHom lower hvalid.2.2 hlowerInjective hlowerInv
  letI : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
  let relation := Arithmetic.Coeff.relation level lower
  let p := HexPolyMathlib.toPolynomial relation
  have hpMonic : p.Monic := by
    rw [Polynomial.Monic.def]
    change (HexPolyMathlib.toPolynomial relation).leadingCoeff = 1
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    change relation.leadingCoeff = 1
    rw [DensePoly.leadingCoeff_eq_coeff_last relation (by
      rw [relation_size level lower hvalid]
      omega), relation_size level lower hvalid]
    simp [relation, Arithmetic.Coeff.relation, Array.getD]
  have hpEval : Polynomial.aeval level.root.toComplex p = 0 := by
    change denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hlowerInv relation = 0
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hlowerInv (level.degree + 1) relation (by
        rw [relation_degree level lower hvalid]
        omega)]
    exact denseEval_relation level lower hvalid
  have hpMin : p = minpoly (Arithmetic.Coeff lower)
      level.root.toComplex :=
    minpoly.eq_of_irreducible_of_monic hirreducible hpEval hpMonic
  intro f g hf hg heval
  let fp := HexPolyMathlib.toPolynomial f
  let gp := HexPolyMathlib.toPolynomial g
  have hmap : Polynomial.aeval level.root.toComplex fp =
      Polynomial.aeval level.root.toComplex gp := by
    change denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hlowerInv f =
        denseMap lower level.root.toComplex hvalid.2.2
          hlowerInjective hlowerInv g
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
        hlowerInjective hlowerInv level.degree f hf,
      denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
        hlowerInjective hlowerInv level.degree g hg]
    exact heval
  have hzero : Polynomial.aeval level.root.toComplex (fp - gp) = 0 := by
    rw [map_sub, hmap, sub_self]
  have hdvd : p ∣ fp - gp := by
    rw [hpMin]
    exact minpoly.dvd (Arithmetic.Coeff lower) level.root.toComplex hzero
  have hdiff : fp - gp = 0 := by
    by_contra hne
    have hlower := Polynomial.natDegree_le_of_dvd hdvd hne
    have hupper : (fp - gp).natDegree < level.degree :=
      (Polynomial.natDegree_sub_le fp gp).trans_lt (max_lt
        (by simpa [fp] using hf) (by simpa [gp] using hg))
    have hpDegree : p.natDegree = level.degree := by
      simpa [p, relation] using relation_degree level lower hvalid
    rw [hpDegree] at hlower
    omega
  have hpoly : fp = gp := sub_eq_zero.mp hdiff
  calc
    f = HexPolyMathlib.ofPolynomial fp := by
      simp [fp]
    _ = HexPolyMathlib.ofPolynomial gp := by rw [hpoly]
    _ = g := by simp [gp]

/-- Injectivity of canonical extended coordinates forces the monic level
relation to be the minimal polynomial of the selected generator over the
lower coefficient field. -/
theorem relation_irreducible_of_injective (level : Level)
    (lower : List Level) (hvalid : LevelsValid (level :: lower))
    (hinjective : DenoteInjective (level :: lower))
    (hlowerInjective : DenoteInjective lower)
    (hlowerInv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid.2.2 hlowerInjective hlowerInv
    Irreducible (HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level lower)) := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid.2.2 hlowerInjective hlowerInv
  let relation := Arithmetic.Coeff.relation level lower
  let p := HexPolyMathlib.toPolynomial relation
  let ι : Arithmetic.Coeff lower →+* ℂ :=
    coeffHom lower hvalid.2.2 hlowerInjective hlowerInv
  letI : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
  have hpMonic : p.Monic := by
    rw [Polynomial.Monic.def]
    change (HexPolyMathlib.toPolynomial relation).leadingCoeff = 1
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    change relation.leadingCoeff = 1
    rw [DensePoly.leadingCoeff_eq_coeff_last relation (by
      rw [relation_size level lower hvalid]
      omega), relation_size level lower hvalid]
    simp [relation, Arithmetic.Coeff.relation, Array.getD]
  have hpEval : Polynomial.aeval level.root.toComplex p = 0 := by
    change denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hlowerInv relation = 0
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hlowerInv (level.degree + 1) relation (by
        rw [relation_degree level lower hvalid]
        omega)]
    exact denseEval_relation level lower hvalid
  have hintegral : IsIntegral (Arithmetic.Coeff lower)
      level.root.toComplex := ⟨p, hpMonic, hpEval⟩
  let q := minpoly (Arithmetic.Coeff lower) level.root.toComplex
  have hqDegree : level.degree ≤ q.natDegree := by
    by_contra hdegree
    have hlt : q.natDegree < level.degree := by omega
    let dense : DensePoly (Arithmetic.Coeff lower) :=
      HexPolyMathlib.ofPolynomial q
    have hdenseDegree : dense.degree?.getD 0 < level.degree := by
      rw [← HexPolyMathlib.natDegree_toPolynomial]
      simpa [dense]
    have hdenseEval :
        denseEval lower level.root.toComplex level.degree dense = 0 := by
      rw [← denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
        hlowerInjective hlowerInv level.degree dense hdenseDegree]
      simp only [denseMap, dense,
        HexPolyMathlib.toPolynomial_ofPolynomial]
      change q.eval₂ ι level.root.toComplex = 0
      rw [← RingHom.algebraMap_toAlgebra ι]
      rw [← Polynomial.aeval_def]
      exact minpoly.aeval _ _
    have hdenseZero : dense = 0 :=
      dense_eq_zero_of_eval level lower hinjective dense
        hdenseDegree hdenseEval
    have hqZero : q = 0 := by
      have hmapped := congrArg HexPolyMathlib.toPolynomial hdenseZero
      simpa [dense] using hmapped
    exact (minpoly.ne_zero hintegral) hqZero
  have hpDegree : p.natDegree = level.degree := by
    simpa [p, relation] using relation_degree level lower hvalid
  have hqDvd : q ∣ p := minpoly.dvd _ _ hpEval
  have hpEq : p = q := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hintegral) hpMonic hqDvd
    rw [hpDegree]
    exact hqDegree
  change Irreducible p
  rw [hpEq]
  exact minpoly.irreducible hintegral

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
    value_degree_lt level lower a (Nat.zero_lt_of_lt hvalid.1.1)
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
    value_degree_lt level lower a (Nat.zero_lt_of_lt hvalid.1.1)
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
      exact Nat.zero_lt_of_lt hvalid.1.1)
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
    (hdegree : 1 < level.degree) (hinjective : DenoteInjective (level :: lower)) :
    DenoteInjective lower := by
  have hpositive : 0 < level.degree := Nat.zero_lt_of_lt hdegree
  intro a b hab
  have hlift : liftCoeff level lower a = liftCoeff level lower b := by
    apply hinjective
    rw [coeffDenote_lift level lower hpositive,
      coeffDenote_lift level lower hpositive]
    exact hab
  have hblock := congrArg
    (fun c : Arithmetic.Coeff (level :: lower) =>
      Arithmetic.block c.data 0 (levelsDim lower)) hlift
  simp only [liftCoeff] at hblock
  rw [Arithmetic.block_flatten level.degree (levelsDim lower) 0 #[a.data]
      hpositive,
    Arithmetic.block_flatten level.degree (levelsDim lower) 0 #[b.data]
      hpositive] at hblock
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
        DenoteInjective.tail level lower
          hvalid.1.1 hinjective
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

/-- Executable inversion of a canonical coefficient preserves denotation at
any validated level list with an injective fixed embedding. -/
theorem coeffDenote_inv (levels : List Level) (hvalid : LevelsValid levels)
    (hinjective : DenoteInjective levels) (a : Arithmetic.Coeff levels) :
    coeffDenote levels a⁻¹ = (coeffDenote levels a)⁻¹ := by
  change denote levels
      (Arithmetic.fixedCoeffs (levelsDim levels)
        (Arithmetic.invCoords levels a.data)) =
    (denote levels a.data)⁻¹
  rw [denote_fixed]
  exact denote_invCoords levels hvalid hinjective a.data

/-- Evaluation at any complex zero of the mapped defining relation is a ring
homomorphism from the canonical top-level coefficient field. -/
@[expose]
noncomputable def conjugateHom (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : DenoteInjective (level :: lower))
    (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0) :
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffField (level :: lower) hvalid hinjective
        (coeffDenote_inv (level :: lower) hvalid hinjective)
    Arithmetic.Coeff (level :: lower) →+* ℂ := by
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffField (level :: lower) hvalid hinjective
      (coeffDenote_inv (level :: lower) hvalid hinjective)
  exact
    { toFun := fun a => evalAt level lower x a.data
      map_zero' := evalAt_zero level lower hvalid x
      map_one' := evalAt_one level lower hvalid x
      map_add' := evalAt_add level lower hvalid x
      map_mul' := fun a b =>
        evalAt_mul level lower hvalid x hrelation a.data b.data }

@[simp]
theorem conjugateHom_apply (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : DenoteInjective (level :: lower))
    (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0)
    (a : Arithmetic.Coeff (level :: lower)) :
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffField (level :: lower) hvalid hinjective
        (coeffDenote_inv (level :: lower) hvalid hinjective)
    conjugateHom level lower hvalid hinjective x hrelation a =
      evalAt level lower x a.data := by
  rfl

/-- Executable inversion at the rational base preserves denotation. -/
theorem coeffDenote_inv_nil (a : Arithmetic.Coeff []) :
    coeffDenote [] a⁻¹ = (coeffDenote [] a)⁻¹ := by
  change denote []
      (Arithmetic.fixedCoeffs (levelsDim [])
        (Arithmetic.invCoords [] a.data)) =
    (denote [] a.data)⁻¹
  rw [denote_fixed]
  exact denote_invCoords [] trivial DenoteInjective.nil a.data

/-- Canonical base-tower coefficients are the rational field. -/
@[expose, reducible]
noncomputable def coeffFieldNil : Field (Arithmetic.Coeff []) :=
  coeffField [] (by exact trivial) DenoteInjective.nil coeffDenote_inv_nil

/-- Canonical base-tower coefficients are ring-equivalent to the rationals. -/
noncomputable def coeffRatEquiv :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    Arithmetic.Coeff [] ≃+* Rat := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  refine
    { toFun := fun a => a.data.getD 0 0
      invFun := fun q => Arithmetic.Coeff.ofData [] #[q]
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_mul' := ?_ }
  · intro a
    cases a with
    | mk data hsize =>
        have hdata : Arithmetic.fixedCoeffs (levelsDim []) #[data.getD 0 0] =
            data := by
          apply Array.ext
          · simp [Arithmetic.fixedCoeffs, levelsDim, hsize]
          · intro i hi₁ hi₂
            have hi : i = 0 := by
              simp [Arithmetic.fixedCoeffs, levelsDim] at hi₁
              omega
            subst i
            simp [Arithmetic.fixedCoeffs, levelsDim, Array.getD, hsize]
        have coeff_ext (x y : Arithmetic.Coeff [])
            (h : x.data = y.data) : x = y := by
          cases x with
          | mk xdata xsize =>
              cases y with
              | mk ydata ysize =>
                  simp only at h
                  subst ydata
                  rfl
        exact coeff_ext _ _ hdata
  · intro q
    change (Arithmetic.fixedCoeffs (levelsDim []) #[q]).getD 0 0 = q
    simp [Arithmetic.fixedCoeffs, levelsDim, Array.getD]
  · intro a b
    change (Arithmetic.mulCoords [] a.data b.data).getD 0 0 =
      a.data.getD 0 0 * b.data.getD 0 0
    simp [Arithmetic.mulCoords, Array.getD]
  · intro a b
    change (Arithmetic.addCoords (levelsDim []) a.data b.data).getD 0 0 =
      a.data.getD 0 0 + b.data.getD 0 0
    simp [Arithmetic.addCoords, levelsDim, Array.getD]

@[simp]
theorem coeffRatEquiv_ofData (data : Array Rat) :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    coeffRatEquiv (Arithmetic.Coeff.ofData [] data) = data.getD 0 0 := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  change (Arithmetic.fixedCoeffs (levelsDim []) data).getD 0 0 =
    data.getD 0 0
  simp [Arithmetic.fixedCoeffs, levelsDim, Array.getD]

/-- Mapping a raw base-tower polynomial through the canonical rational
equivalence recovers the rational polynomial stored by its coordinates. -/
theorem map_rawPoly_nil (f : Array (Array Rat)) :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    (HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)).map
        coeffRatEquiv.toRingHom =
      HexPolyMathlib.toPolynomial (Factor.toRatPoly f) := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  ext n
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    HexPolyMathlib.coeff_toPolynomial]
  by_cases hn : n < f.size
  · simp [Factor.rawPoly, Factor.toRatPoly, DensePoly.coeff_ofCoeffs,
      Array.getD, hn, coeffRatEquiv_ofData]
  · simp [Factor.rawPoly, Factor.toRatPoly, DensePoly.coeff_ofCoeffs,
      Array.getD, hn]
    exact coeffRatEquiv.map_zero

/-- The rational-base arm of the recursive checker proves ordinary
irreducibility after transporting canonical base coefficients to `Rat`. -/
theorem isIrreducible_nil_toMathlib (f : Array (Array Rat))
    (hcheck : Factor.isIrreducible [] f = true) :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    Irreducible (HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)) := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  simp only [Factor.isIrreducible, Bool.and_eq_true] at hcheck
  have hdegree := hcheck.1.1.1
  have hirreducible := hcheck.2
  have hdegree' : 0 < (Factor.rawPoly [] f).degree?.getD 0 :=
    of_decide_eq_true hdegree
  let raw := Factor.toRatPoly f
  let primitive := ZPoly.ratPolyPrimitivePart raw
  have hirreducibleInt :
      Irreducible (HexPolyZMathlib.toPolynomial primitive) :=
    (ZPoly.Irreducible_iff_polynomialIrreducible primitive).mp
      ((ZPoly.isIrreducible_iff primitive).mp hirreducible)
  have hprimitiveNe : primitive ≠ 0 := by
    intro hzero
    apply hirreducibleInt.ne_zero
    rw [hzero]
    exact HexPolyZMathlib.toPolynomial_zero
  have hprimitiveRatNe : HexPolyZMathlib.toPolyℚ primitive ≠ 0 :=
    HexPolyZMathlib.toPolyℚ_ne_zero hprimitiveNe
  have hrawDegree :
      0 < (HexPolyMathlib.toPolynomial raw).natDegree := by
    rw [← map_rawPoly_nil f,
      Polynomial.natDegree_map_eq_of_injective coeffRatEquiv.injective,
      HexPolyMathlib.natDegree_toPolynomial]
    exact hdegree'
  obtain ⟨unit, hunit⟩ :=
    ZPoly.ratPolyPrimitivePart_rational_associate raw
  have hunitNe : unit ≠ 0 := by
    intro hzero
    have hrawZero : HexPolyMathlib.toPolynomial raw = 0 := by
      rw [hunit, hzero]
      simp
    rw [hrawZero] at hrawDegree
    simp at hrawDegree
  have hassociate :
      HexPolyMathlib.toPolynomial raw =
        Polynomial.C unit * HexPolyZMathlib.toPolyℚ primitive := by
    rw [hunit, HexPolyMathlib.toPolynomial_scale,
      HexPolyZMathlib.toPolynomial_toRatPoly]
  have hprimitiveDegree :
      0 < (HexPolyZMathlib.toPolyℚ primitive).natDegree := by
    have hdegreeEq := congrArg Polynomial.natDegree hassociate
    rw [Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr hunitNe) hprimitiveRatNe] at hdegreeEq
    have hdegreeEq' :
        (HexPolyMathlib.toPolynomial raw).natDegree =
          (HexPolyZMathlib.toPolyℚ primitive).natDegree := by
      simpa using hdegreeEq
    exact hdegreeEq' ▸ hrawDegree
  have hdegreeInt :
      (HexPolyZMathlib.toPolynomial primitive).natDegree ≠ 0 := by
    rw [← Polynomial.natDegree_map_eq_of_injective
      (f := Int.castRingHom Rat) Int.cast_injective
      (HexPolyZMathlib.toPolynomial primitive)]
    exact Nat.ne_of_gt hprimitiveDegree
  have hirreducibleRat :
      Irreducible (HexPolyZMathlib.toPolyℚ primitive) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (hirreducibleInt.isPrimitive hdegreeInt)).mp hirreducibleInt
  have hrawIrreducible :
      Irreducible (HexPolyMathlib.toPolynomial raw) := by
    rw [hassociate, mul_comm]
    exact (irreducible_mul_isUnit
      (Polynomial.isUnit_C.mpr hunitNe.isUnit)).mpr hirreducibleRat
  apply (MulEquiv.irreducible_iff
    (f := (Polynomial.mapEquiv coeffRatEquiv).toMulEquiv)).mp
  change Irreducible
    ((HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)).map
      coeffRatEquiv.toRingHom)
  rw [map_rawPoly_nil]
  exact hrawIrreducible

/-- Mapping the executable base relation through the canonical rational
equivalence recovers its raw rational polynomial. -/
theorem map_relation_nil (level : Level) (hstruct : level.Structural 1) :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    (HexPolyMathlib.toPolynomial (Arithmetic.Coeff.relation level [])).map
        coeffRatEquiv.toRingHom =
      HexPolyMathlib.toPolynomial
        (Factor.toRatPoly (level.polynomial [])) := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  ext n
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    HexPolyMathlib.coeff_toPolynomial]
  have hsize : level.defining.size = level.degree := hstruct.2.1
  have htop : Arithmetic.fixedCoeffs (levelsDim []) #[1] = #[1] := by
    apply Array.ext
    · simp [Arithmetic.fixedCoeffs, levelsDim]
    · intro i hi₁ hi₂
      simp [Arithmetic.fixedCoeffs, levelsDim, Array.getD]
  have hpoly : level.polynomial [] = level.defining.push #[1] := by
    simp [Level.polynomial, htop]
  have hrat : Factor.toRatPoly (level.polynomial []) =
      DensePoly.ofCoeffs
        ((level.defining.map fun coefficient => coefficient.getD 0 0).push 1) := by
    rw [hpoly]
    simp [Factor.toRatPoly, Array.getD]
  by_cases hn : n < level.degree
  · have hndef : n < level.defining.size := by simpa [hsize] using hn
    have hleft : (Arithmetic.Coeff.relation level []).coeff n =
        Arithmetic.Coeff.ofData [] (level.defining.getD n #[]) := by
      simp [Arithmetic.Coeff.relation]
      rw [List.getElem?_append_left (by simpa using hn),
        List.getElem?_map, List.getElem?_range hn]
      simp [Array.getElem?_eq_getElem hndef]
    have hright : (Factor.toRatPoly (level.polynomial [])).coeff n =
        (level.defining.getD n #[]).getD 0 0 := by
      rw [hrat, DensePoly.coeff_ofCoeffs,
        Array.getD_eq_getD_getElem?, Array.getElem?_push_lt (by
          simpa [hsize] using hn)]
      simp only [Option.getD_some]
      rw [Array.getElem_map]
      have hd : level.defining.getD n #[] = level.defining[n] := by
        rw [Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem hndef]
        rfl
      rw [hd]
    rw [hleft, hright]
    change coeffRatEquiv
        (Arithmetic.Coeff.ofData [] (level.defining.getD n #[])) = _
    exact coeffRatEquiv_ofData (level.defining.getD n #[])
  · by_cases heq : n = level.degree
    · subst n
      have hleft : (Arithmetic.Coeff.relation level []).coeff level.degree =
          1 := by
        simp [Arithmetic.Coeff.relation]
      have hright :
          (Factor.toRatPoly (level.polynomial [])).coeff level.degree = 1 := by
        rw [hrat, DensePoly.coeff_ofCoeffs,
          Array.getD_eq_getD_getElem?]
        have hdegree : level.degree =
            (level.defining.map fun coefficient => coefficient.getD 0 0).size := by
          simp [hsize]
        rw [hdegree, Array.getElem?_push_size]
        rfl
      rw [hleft, hright, map_one]
    · have hgt : level.degree < n := by omega
      have hnle : ¬ n ≤ level.degree := by omega
      have hleft : (Arithmetic.Coeff.relation level []).coeff n = 0 := by
        simp [Arithmetic.Coeff.relation, hnle]
        change Arithmetic.Coeff.ofData [] #[] = (0 : Arithmetic.Coeff [])
        rfl
      have hright : (Factor.toRatPoly (level.polynomial [])).coeff n = 0 := by
        rw [hrat, DensePoly.coeff_ofCoeffs,
          Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none (by simp [hsize]; omega)]
        change (0 : Rat) = 0
        rfl
      rw [hleft, hright, map_zero]

/-- A rational-presentation certificate makes the executable base relation
irreducible over the canonical base coefficient field. -/
theorem relation_irreducible_rational (level : Level)
    (hstruct : level.Structural 1) (hrelation : level.RationalRelation []) :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    Irreducible (HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level [])) := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  obtain ⟨_, original, checked, hp, hraw⟩ := hrelation
  letI : ZPoly.CheckedIrreducible original := checked
  have hirrOriginal :
      Irreducible (HexPolyZMathlib.toPolyℚ original) :=
    ZPoly.CheckedIrreducible.irreducibleRat original
  have hirrRoot :
      Irreducible (HexPolyZMathlib.toPolyℚ level.root.p) := by
    rw [hp]
    unfold ZPoly.normalizePrimitiveSign
    split <;> rename_i hsign
    · have hunit : IsUnit (Polynomial.C (-1 : Rat)) :=
        Polynomial.isUnit_C.mpr (by norm_num)
      have hirrNeg :
          Irreducible
            (HexPolyZMathlib.toPolyℚ original * Polynomial.C (-1 : Rat)) :=
        (irreducible_mul_isUnit hunit).mpr hirrOriginal
      simpa [HexPolyZMathlib.toPolyℚ,
        HexPolyMathlib.toPolynomial_scale, mul_comm] using hirrNeg
    · exact hirrOriginal
  have hlcInt : level.root.p.leadingCoeff ≠ 0 :=
    ne_of_gt level.root.pos_lc
  have hlcRat : (level.root.p.leadingCoeff : Rat) ≠ 0 :=
    fun h => hlcInt (Rat.intCast_eq_zero_iff.mp h)
  have hscaleUnit :
      IsUnit (Polynomial.C ((level.root.p.leadingCoeff : Rat)⁻¹)) :=
    Polynomial.isUnit_C.mpr (inv_ne_zero hlcRat).isUnit
  have hirrRaw :
      Irreducible (HexPolyMathlib.toPolynomial
        (Factor.toRatPoly (level.polynomial []))) := by
    rw [hraw, HexPolyMathlib.toPolynomial_scale,
      HexPolyZMathlib.toPolynomial_toRatPoly, mul_comm]
    exact (irreducible_mul_isUnit hscaleUnit).mpr hirrRoot
  apply (MulEquiv.irreducible_iff
    (f := (Polynomial.mapEquiv coeffRatEquiv).toMulEquiv)).mp
  change Irreducible
    ((HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level [])).map coeffRatEquiv.toRingHom)
  rw [map_relation_nil level hstruct]
  exact hirrRaw

/-- Every validated one-level presentation has injective canonical complex
denotation.  Rational-presentation certificates use their stored primitive
associate; relative certificates over the rational base use the recursive
factor checker base case. -/
theorem DenoteInjective.singleton (level : Level)
    (hvalid : LevelsValid [level]) : DenoteInjective [level] := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  have hrelation : Irreducible (HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level [])) := by
    cases hvalid.2.1 with
    | rational hrat =>
        exact relation_irreducible_rational level hvalid.1 hrat
    | relative _ hchecker _ =>
        have hraw := isIrreducible_nil_toMathlib
          (level.polynomial []) hchecker
        have heq : Arithmetic.Coeff.relation level [] =
            Factor.rawPoly [] (level.polynomial []) := by
          apply (HexPolyMathlib.equiv
            (R := Arithmetic.Coeff [])).injective
          apply (Polynomial.mapEquiv coeffRatEquiv).injective
          change (HexPolyMathlib.toPolynomial
              (Arithmetic.Coeff.relation level [])).map
                coeffRatEquiv.toRingHom =
            (HexPolyMathlib.toPolynomial
              (Factor.rawPoly [] (level.polynomial []))).map
                coeffRatEquiv.toRingHom
          rw [map_relation_nil level hvalid.1,
            map_rawPoly_nil (level.polynomial [])]
        rw [heq]
        exact hraw
  exact DenoteInjective.cons level [] hvalid
    (separates_of_irreducible level [] hvalid DenoteInjective.nil
      coeffDenote_inv_nil hrelation)

end LevelSemantics

/-- Injectivity of canonical raw coefficient denotation induces injectivity of
the public fixed-width tower interpretation. -/
theorem toComplex_injective_of_denote (T : NumberTower)
    (hinjective : LevelSemantics.DenoteInjective T.levels.toList) :
    Function.Injective T.toComplex := by
  intro a b hab
  apply Elem.ext
  let ca := Arithmetic.Coeff.ofData T.levels.toList (coeffs a)
  let cb := Arithmetic.Coeff.ofData T.levels.toList (coeffs b)
  have hca : ca.data = coeffs a := by
    change Arithmetic.fixedCoeffs (levelsDim T.levels.toList) (coeffs a) =
      coeffs a
    apply Array.ext
    · simp [Arithmetic.fixedCoeffs, dim]
    · intro i hi₁ hi₂
      have hi : i < T.dim := by simpa using hi₂
      simp [Arithmetic.fixedCoeffs, Array.getD, hi]
  have hcb : cb.data = coeffs b := by
    change Arithmetic.fixedCoeffs (levelsDim T.levels.toList) (coeffs b) =
      coeffs b
    apply Array.ext
    · simp [Arithmetic.fixedCoeffs, dim]
    · intro i hi₁ hi₂
      have hi : i < T.dim := by simpa using hi₂
      simp [Arithmetic.fixedCoeffs, Array.getD, hi]
  have hcoeff : ca = cb := by
    apply hinjective
    change LevelSemantics.denote T.levels.toList ca.data =
      LevelSemantics.denote T.levels.toList cb.data
    rw [hca, hcb]
    rw [← LevelSemantics.toComplex_eq_denote T a,
      ← LevelSemantics.toComplex_eq_denote T b]
    exact hab
  exact hca.symm.trans
    ((congrArg Arithmetic.Coeff.data hcoeff).trans hcb)

end Hex.NumberTower
