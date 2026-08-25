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

/-- Extracting a coordinate block commutes with coordinatewise rational
scaling. -/
theorem block_map_mul (q : Rat) (data : Array Rat)
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

/-- Defaulted read after an in-bounds `set!`: position `k` holds the new
value and every other position is unchanged. -/
theorem getD_set! (blocks : Array (Array Rat)) (k i : Nat)
    (value default : Array Rat) (hk : k < blocks.size) :
    (blocks.set! k value).getD i default =
      if k = i then value else blocks.getD i default := by
  by_cases hki : k = i
  · subst i
    simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, hk]
  · simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, hki]

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

/-- Generic accumulation principle for coordinate folds: if every step
preserves the working size and adds one term to the evaluated power sum, the
fold adds the sum of all terms. -/
theorem fold_eval {ι : Type} (lower : List Level) (x : ℂ)
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

/-- A sum over `List.range` agrees with the corresponding `Finset.range`
sum. -/
theorem list_sum_range (count : Nat) (term : Nat → ℂ) :
    ((List.range count).map term).sum =
      ∑ i ∈ Finset.range count, term i := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, ih]
      simp

/-- One convolution row adds exactly the monomial contributions of block `i`
of `a` against every block of `b`. -/
theorem convolveRow_eval (lower : List Level) (x : ℂ)
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

/-- The empty coordinate array denotes zero at every tower height. -/
theorem denote_empty (levels : List Level) : denote levels #[] = 0 := by
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

/-- The zero-filled coordinate array of full width denotes zero. -/
theorem denote_replicate_zero (levels : List Level) :
    denote levels (Array.replicate (levelsDim levels) 0) = 0 := by
  rw [← denote_zero levels]
  congr 1
  apply Array.ext
  · simp [Arithmetic.fixedCoeffs]
  · intro i hi₁ hi₂
    simp [Arithmetic.fixedCoeffs]

/-- A power sum over zero-filled blocks vanishes. -/
theorem evalUpTo_replicate_zero (lower : List Level) (x : ℂ)
    (count : Nat) :
    evalUpTo lower x count
        (Array.replicate count
          (Array.replicate (levelsDim lower) 0)) = 0 := by
  unfold evalUpTo
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < count := Finset.mem_range.mp hi
  simp [Array.getD, hi', denote_replicate_zero]

/-- The executable convolution evaluates to the double sum of blockwise
products weighted by `x ^ (i + j)`. -/
theorem convolve_eval (lower : List Level) (x : ℂ)
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

/-- The executable convolution evaluates to the product of the two operand
power sums: schoolbook multiplication is correct under denotation. -/
theorem convolve_mul (lower : List Level) (x : ℂ)
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

/-- One coefficient-reduction step subtracts the top block times each
defining coefficient at the correspondingly shifted position. -/
theorem reduceCoeffs_eval (lower : List Level) (x : ℂ)
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

/-- Conjugate evaluation sends the zero coefficient to `0`. -/
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

/-- Conjugate evaluation sends the one coefficient to `1`. -/
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

/-- Conjugate evaluation is additive. -/
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
theorem reduceAt_eval_of_relation (level : Level) (lower : List Level)
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
theorem reduce_eval_of_relation (level : Level) (lower : List Level)
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

/-- Full degree reduction at the stored root preserves the evaluated power
sum: each subtracted multiple of the monic defining relation vanishes at the
root, so the reduced width-`k` array evaluates like the original width-`k+1`
array. -/
theorem reduceAt_eval (level : Level) (lower : List Level)
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
theorem reduce_eval (level : Level) (lower : List Level)
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

/-- Coefficient denotation sends the zero coefficient to `0`. -/
@[simp]
theorem coeffDenote_zero (levels : List Level) :
    coeffDenote levels (0 : Arithmetic.Coeff levels) = 0 := by
  change denote levels
      (Arithmetic.fixedCoeffs (levelsDim levels) #[]) = 0
  exact denote_zero levels

/-- Coefficient denotation sends the one coefficient to `1`. -/
@[simp]
theorem coeffDenote_one (levels : List Level) (hvalid : LevelsValid levels) :
    coeffDenote levels (1 : Arithmetic.Coeff levels) = 1 := by
  change denote levels
      (Arithmetic.fixedCoeffs (levelsDim levels) #[1]) = 1
  exact denote_one levels hvalid

/-- Coefficient denotation is additive over the executable addition. -/
theorem coeffDenote_add (levels : List Level)
    (a b : Arithmetic.Coeff levels) :
    coeffDenote levels (a + b) = coeffDenote levels a + coeffDenote levels b := by
  change denote levels (Arithmetic.addCoords (levelsDim levels) a.data b.data) =
    denote levels a.data + denote levels b.data
  exact denote_add levels a.data b.data

/-- Coefficient denotation respects the executable subtraction. -/
theorem coeffDenote_sub (levels : List Level)
    (a b : Arithmetic.Coeff levels) :
    coeffDenote levels (a - b) = coeffDenote levels a - coeffDenote levels b := by
  change denote levels (Arithmetic.subCoords (levelsDim levels) a.data b.data) =
    denote levels a.data - denote levels b.data
  exact denote_sub levels a.data b.data

/-- Coefficient denotation respects the executable negation. -/
theorem coeffDenote_neg (levels : List Level) (a : Arithmetic.Coeff levels) :
    coeffDenote levels (-a) = -coeffDenote levels a := by
  change denote levels (Arithmetic.negCoords (levelsDim levels) a.data) =
    -denote levels a.data
  exact denote_neg levels a.data

/-- Coefficient denotation is multiplicative over the executable mixed-radix
multiplication. -/
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

/-- Coefficient denotation turns the executable rational scaling into
multiplication by the embedded rational. -/
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

/-- Coefficient denotation turns the executable natural power into the
complex power. -/
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

/-- Canonical coefficient data is already the right width, so zero-padding
fixes it. -/
theorem fixedCoeffs_eq_self (levels : List Level)
    (a : Arithmetic.Coeff levels) :
    Arithmetic.fixedCoeffs (levelsDim levels) a.data = a.data := by
  apply Array.ext
  · simp [Arithmetic.fixedCoeffs, a.size_eq]
  · intro i hi₁ hi₂
    simp [Arithmetic.fixedCoeffs, Array.getD, hi₂]

/-- Canonical coefficients with equal coordinate data are equal. -/
theorem coeff_eq_of_data_eq {levels : List Level}
    {a b : Arithmetic.Coeff levels} (h : a.data = b.data) : a = b := by
  cases a with
  | mk ad ha =>
      cases b with
      | mk bd hb =>
          simp only at h
          cases h
          rfl

/-- Rebuilding a canonical coefficient from its own data is the identity. -/
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

end LevelSemantics

end Hex.NumberTower
