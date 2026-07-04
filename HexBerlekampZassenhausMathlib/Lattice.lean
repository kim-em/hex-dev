/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Basic
public import HexBerlekampZassenhausMathlib.SignatureClasses
public import HexLLLMathlib.ShortVector

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
BHKS lattice-side objects for the van Hoeij `W ⊆ L'` adequacy (#8519).

Resurrected (from the pre-#8411 `Lattice.lean`, commit 6bf20977^) and adapted
to the current `Matrix.rowReduce` / `vecMul` API: the projected-row spans, the
`0/1` support indicators, the `RecoveredLift` certificate, the Gram-Schmidt
prefix-survivor lemma (Klüners Lemma 1: any lattice vector within the cut
radius lies in the retained prefix span), and the cut-projection producer
`cutProjectionHypotheses_of_shortVectors` that places each true support's
indicator in the executable projected row span.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

namespace BHKS


/--
The reduced matrix stored in the BHKS projected-row trace generates the same
integer row lattice as the original BHKS basis.  This carries
`lllNative.shortVectors`'s `.toArray` output back to the certified LLL
lattice-preservation theorem `Hex.lllNative_memLattice_iff`.
-/
theorem traceReducedMatrix_memLattice_iff
    (L : Hex.BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (v : Vector Int (L.factorCount + L.coeffWidth)) :
    Hex.Matrix.memLattice (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix v ↔
      Hex.Matrix.memLattice L.basis v := by
  rw [Hex.bhksProjectedRowsTrace_reducedMatrix_eq]
  exact Hex.lllNative_memLattice_iff L.basis (3 / 4)
    Hex.lll_delta_lower Hex.lll_delta_upper hrows v

/-- The projected integer rows of the executable BHKS cut as a Mathlib matrix. -/
def projectedRowsIntMatrix (L : Hex.BhksProjectedRows) :
    Matrix (Fin L.projectedRows.size) (Fin L.factorCount) ℤ :=
  fun i j => (L.projectedRows.getD i.val #[]).getD j.val 0

/-- The projected rational rows of the executable BHKS cut as a Mathlib matrix. -/
@[expose]
def projectedRowsRatMatrix (L : Hex.BhksProjectedRows) :
    Matrix (Fin L.projectedRows.size) (Fin L.factorCount) ℚ :=
  fun i j => ((L.projectedRows.getD i.val #[]).getD j.val 0 : ℚ)

/--
The integer row span represented by the executable projected BHKS rows.  This
is the proof-facing `L' <= Z^r`.
-/
@[expose]
def projectedRowSpanInt (L : Hex.BhksProjectedRows) :
    Submodule ℤ (Fin L.factorCount → ℤ) :=
  Submodule.span ℤ (Set.range fun i : Fin L.projectedRows.size =>
    Matrix.row (projectedRowsIntMatrix L) i)

/--
The rational row space represented by the same executable projected rows.  This
is the row-space input used by the RREF equivalence-class stage.
-/
@[expose]
def projectedRowSpaceRat (L : Hex.BhksProjectedRows) :
    Submodule ℚ (Fin L.factorCount → ℚ) :=
  Submodule.span ℚ (Set.range fun i : Fin L.projectedRows.size =>
    Matrix.row (projectedRowsRatMatrix L) i)

/-- Cast an integer vector over the lifted-factor indices to a rational vector. -/
@[expose]
def intVectorToRat {r : Nat} (v : Fin r → ℤ) : Fin r → ℚ :=
  fun i => (v i : ℚ)

/-- A `0/1` indicator vector for a support of lifted factor indices. -/
@[expose]
def indicatorVector {r : Nat} (S : Set (Fin r)) : Fin r → ℤ :=
  by
    classical
    exact fun i => if i ∈ S then 1 else 0

@[simp, grind =] theorem indicatorVector_apply_mem {r : Nat} (S : Set (Fin r))
    {i : Fin r} (hi : i ∈ S) :
    indicatorVector S i = 1 := by
  simp [indicatorVector, hi]

@[simp, grind =] theorem indicatorVector_apply_not_mem {r : Nat} (S : Set (Fin r))
    {i : Fin r} (hi : i ∉ S) :
    indicatorVector S i = 0 := by
  simp [indicatorVector, hi]

/-- Each coordinate of an indicator vector has squared real norm at most one. -/
theorem indicatorVector_sq_apply_le_one {r : Nat} (S : Set (Fin r)) (i : Fin r) :
    ((((indicatorVector S i : ℤ) : ℝ) ^ 2)) ≤ 1 := by
  classical
  by_cases hi : i ∈ S
  · rw [indicatorVector_apply_mem S hi]
    norm_num
  · rw [indicatorVector_apply_not_mem S hi]
    norm_num

/-- The squared real norm of a `0/1` indicator vector is at most the ambient
dimension. -/
theorem indicatorVector_sq_sum_le_factorCount {r : Nat} (S : Set (Fin r)) :
    (∑ i : Fin r, ((((indicatorVector S i : ℤ) : ℝ) ^ 2))) ≤ (r : ℝ) := by
  calc
    (∑ i : Fin r, ((((indicatorVector S i : ℤ) : ℝ) ^ 2)))
        ≤ ∑ _i : Fin r, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun i _hi => indicatorVector_sq_apply_le_one S i)
    _ = (r : ℝ) := by
          simp

/-- The BHKS cut-radius expression dominates the squared norm of every
true-support indicator vector. -/
theorem indicatorVector_sq_sum_le_bhksCutRadiusSq4
    (L : Hex.BhksLatticeBasis) (S : Set (Fin L.factorCount)) :
    (∑ i : Fin L.factorCount, ((((indicatorVector S i : ℤ) : ℝ) ^ 2))) ≤
      (Hex.bhksCutRadiusSq4 L : ℝ) := by
  have hnorm := indicatorVector_sq_sum_le_factorCount S
  have hfactor_le_cut :
      (L.factorCount : ℝ) ≤ (Hex.bhksCutRadiusSq4 L : ℝ) := by
    unfold Hex.bhksCutRadiusSq4
    have hnat :
        L.factorCount ≤ 4 * L.factorCount + L.coeffWidth * L.factorCount * L.factorCount := by
      exact Nat.le_trans (Nat.le_mul_of_pos_left L.factorCount (by decide : 0 < 4))
        (Nat.le_add_right _ _)
    exact_mod_cast hnat
  exact hnorm.trans hfactor_le_cut

/-- Projected-row form of `indicatorVector_sq_sum_le_bhksCutRadiusSq4`, stated
against the cut-radius field stored by the executable Gram-Schmidt cut output. -/
theorem indicatorVector_sq_sum_le_projectedRows_cutRadiusSq4
    (L : Hex.BhksLatticeBasis)
    (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (S : Set (Fin (Hex.bhksProjectedRows L hrows).factorCount)) :
    (∑ i : Fin (Hex.bhksProjectedRows L hrows).factorCount,
        ((((indicatorVector S i : ℤ) : ℝ) ^ 2))) ≤
      ((Hex.bhksProjectedRows L hrows).cutRadiusSq4 : ℝ) := by
  exact indicatorVector_sq_sum_le_bhksCutRadiusSq4 L S


/-- A support of lifted local-factor indices for a BHKS lattice basis. -/
abbrev LiftedFactorSupport (L : Hex.BhksLatticeBasis) :=
  Set (Fin L.factorCount)

/-- The `0/1` indicator vector attached to a lifted-factor support. -/
def liftedFactorIndicator (L : Hex.BhksLatticeBasis) (S : LiftedFactorSupport L) :
    Fin L.factorCount → ℤ :=
  indicatorVector S

/--
Product of the lifted factors selected by a support, using the factor order
stored in the BHKS lattice basis.  The definition indexes by `factorCount`
rather than the raw array size so it remains well-typed for abstract
`BhksLatticeBasis` values; `TrueFactorLift.basis_eq` ties these together for
the executable basis.
-/
@[expose]
def supportProduct (L : Hex.BhksLatticeBasis) (S : LiftedFactorSupport L) :
    Hex.ZPoly :=
  by
    classical
    exact Array.polyProduct <|
      (((List.finRange L.factorCount).filter fun i => decide (i ∈ S)).map
        fun i => L.liftedFactors.getD i.val 1).toArray

/--
Sum of the per-selected-factor executable CLD quotients, taken over the same
factor order as `supportProduct`.  Its `j`-th coefficient is the pre-`psiCut`,
pre-indicator column-`j` entry of the true-factor CLD vector; the centering
(`psiCut`) and indicator weighting are layered on top by the tight-column work
(`#7651`).
-/
@[expose]
def supportCldSum (L : Hex.BhksLatticeBasis) (S : LiftedFactorSupport L)
    (f : Hex.ZPoly) (p a : Nat) : Hex.ZPoly :=
  by
    classical
    exact
      (((List.finRange L.factorCount).filter fun i => decide (i ∈ S)).map
        fun i => Hex.cldQuotientMod f (L.liftedFactors.getD i.val 1) p a).sum


/--
Proof-facing package for a true factor recovered from the selected lifted-factor
product by the executable centered/dilated recovery path.

This is parallel to `TrueFactorLift`, but it deliberately does not assert the
raw integer equality `supportProduct L S = factor`.  The recovery algorithm
only exposes the centered representative modulo `p ^ a`, dilated by the
leading coefficient of `f`, as the recovered integer factor.  Downstream lemmas
that only need the BHKS support, factor/cofactor identity, and recovered product
shape should consume this package instead of strengthening their hypotheses back
to raw selected-product equality.
-/
structure RecoveredLift
    (L : Hex.BhksLatticeBasis) (S : LiftedFactorSupport L) where
  f : Hex.ZPoly
  p : Nat
  a : Nat
  liftedFactors : Array Hex.ZPoly
  basis_eq : L = Hex.bhksLatticeBasis f p a liftedFactors
  factor : Hex.ZPoly
  cofactor : Hex.ZPoly
  factor_mul : factor * cofactor = f
  recovered_eq :
    Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff f)
        (Hex.centeredLiftPoly (supportProduct L S) (p ^ a)) =
      factor

/-- A left fold accumulating `g` over a list equals the running accumulator plus
the sum of the mapped list; the start-from-`acc` form used to read a fold-sum off
at `acc = 0`. -/
private theorem foldl_add_eq_acc_add_listSum {M : Type*} [AddCommMonoid M]
    {α : Type*} (l : List α) (g : α → M) (acc : M) :
    l.foldl (fun acc i => acc + g i) acc = acc + (l.map g).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, add_assoc]

/-- A fold-sum over `List.finRange n` equals the finite sum over `Fin n`. -/
private theorem finRange_foldl_add_eq_sum {M : Type*} [AddCommMonoid M] {n : Nat}
    (g : Fin n → M) :
    (List.finRange n).foldl (fun acc i => acc + g i) 0 = ∑ i, g i := by
  rw [foldl_add_eq_acc_add_listSum, zero_add, Fin.sum_univ_def]

/-- The entry of a row combination at column `k` is the explicit finite sum, over
the row index, of the column-`k` matrix entries weighted by the coefficients. -/
theorem vecMul_getElem_eq_sum {n m : Nat}
    (M : Hex.Matrix ℤ n m) (c : Vector ℤ n) (k : Fin m) :
    (Hex.Matrix.vecMul c M)[k] = ∑ i : Fin n, M[i][k] * c[i] := by
  show (Hex.Matrix.transpose M * c)[k] = _
  rw [Hex.Matrix.getElem_mulVec]
  unfold Vector.dotProduct
  rw [finRange_foldl_add_eq_sum
    (g := fun i : Fin n => (Hex.Matrix.row (Hex.Matrix.transpose M) k)[i] * c[i])]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Hex.Matrix.getElem_row, Hex.Matrix.getElem_transpose]


/--
Certificate for an arbitrary short BHKS lattice vector whose first block is the
indicator of a true lifted-factor support.

This is the projection surface needed by period-adjusted BHKS arguments: the
short vector need not be the zero-period-row `trueFactorCLDVector`; it only has
to lie in the BHKS row lattice, project to the support indicator, and satisfy
the tight cut radius bound.
-/
structure SupportShortVectorData
    (L : Hex.BhksLatticeBasis) (S : LiftedFactorSupport L) where
  vector : Vector ℤ (L.factorCount + L.coeffWidth)
  memLattice : Hex.Matrix.memLattice L.basis vector
  project_eq :
    ∀ i : Fin L.factorCount,
      vector[(⟨i.val, Nat.lt_add_right L.coeffWidth i.isLt⟩ :
        Fin (L.factorCount + L.coeffWidth))] = indicatorVector S i
  four_mul_sq_norm_le :
    4 * (∑ i : Fin (L.factorCount + L.coeffWidth),
      ((((vector[i] : ℤ) : ℝ) ^ 2))) ≤ (Hex.bhksCutRadiusSq4 L : ℝ)


/--
The BHKS block-form predicate: `L.basis` is the all-coefficients CLD row basis
`[ I | A_tilde ; 0 | diag ]` built by `bhksLatticeEntry` from `L`'s own data.
This holds definitionally for `Hex.bhksLatticeBasis` (see
`bhksLatticeBasis_blockForm`) and is the only fact the canonical coordinate
producers need about the basis.
-/
@[expose]
def BhksBlockForm (L : Hex.BhksLatticeBasis) : Prop :=
  L.basis =
    Hex.Matrix.ofFn
      (Hex.bhksLatticeEntry L.factorCount L.coeffWidth L.p L.precision
        L.cutThresholds L.cldRows)

/-- The executable `bhksLatticeBasis` has block form by construction. -/
theorem bhksLatticeBasis_blockForm
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly) :
    BhksBlockForm (Hex.bhksLatticeBasis f p a liftedFactors) := rfl


namespace RecoveredLift

/-- A recovered lift package supplies the BHKS block form used by coordinate
and norm-bound reducers. -/
theorem blockForm
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : RecoveredLift L S) :
    BhksBlockForm L := by
  rcases D with ⟨f, p, a, liftedFactors, basis_eq, factor, cofactor, factor_mul,
    recovered_eq⟩
  cases basis_eq
  exact bhksLatticeBasis_blockForm f p a liftedFactors

/-- The packaged basis carries exactly the lifted-factor array used to build
the executable BHKS lattice. -/
theorem liftedFactors_eq
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : RecoveredLift L S) :
    L.liftedFactors = D.liftedFactors := by
  rcases D with ⟨f, p, a, liftedFactors, basis_eq, factor, cofactor, factor_mul,
    recovered_eq⟩
  cases basis_eq
  rfl

/-- The packaged basis carries exactly the cut thresholds computed from the
input polynomial and prime. -/
theorem cutThresholds_eq
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : RecoveredLift L S) :
    L.cutThresholds = Hex.bhksCutThresholds D.f D.p := by
  rcases D with ⟨f, p, a, liftedFactors, basis_eq, factor, cofactor, factor_mul,
    recovered_eq⟩
  cases basis_eq
  rfl

/-- The packaged basis carries exactly the CLD rows computed from the concrete
lifted factors. -/
theorem cldRows_eq
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : RecoveredLift L S) :
    L.cldRows = D.liftedFactors.map (fun g => Hex.cldCoeffs D.f D.p D.a g) := by
  rcases D with ⟨f, p, a, liftedFactors, basis_eq, factor, cofactor, factor_mul,
    recovered_eq⟩
  cases basis_eq
  rfl

/-- The packaged basis factor count is exactly the concrete lifted-factor
array size. -/
theorem factorCount_eq
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : RecoveredLift L S) :
    L.factorCount = D.liftedFactors.size := by
  rcases D with ⟨f, p, a, liftedFactors, basis_eq, factor, cofactor, factor_mul,
    recovered_eq⟩
  cases basis_eq
  rfl

/-- The packaged basis coefficient width is exactly the input polynomial degree
used by the executable CLD rows. -/
theorem coeffWidth_eq
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : RecoveredLift L S) :
    L.coeffWidth = D.f.degree?.getD 0 := by
  rcases D with ⟨f, p, a, liftedFactors, basis_eq, factor, cofactor, factor_mul,
    recovered_eq⟩
  cases basis_eq
  rfl

/-- The packaged basis modulus base is exactly the recovered lift's prime. -/
theorem p_eq
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : RecoveredLift L S) :
    L.p = D.p := by
  rcases D with ⟨f, p, a, liftedFactors, basis_eq, factor, cofactor, factor_mul,
    recovered_eq⟩
  cases basis_eq
  rfl

/-- The packaged basis precision is exactly the recovered lift's Hensel
precision. -/
theorem precision_eq
    {L : Hex.BhksLatticeBasis} {S : LiftedFactorSupport L}
    (D : RecoveredLift L S) :
    L.precision = D.a := by
  rcases D with ⟨f, p, a, liftedFactors, basis_eq, factor, cofactor, factor_mul,
    recovered_eq⟩
  cases basis_eq
  rfl

end RecoveredLift

@[expose]
def supportEquivalent {r : Nat} (trueSupports : Set (Set (Fin r)))
    (j k : Fin r) : Prop :=
  ∀ S ∈ trueSupports, (j ∈ S ↔ k ∈ S)

/-- Nat-indexed form of `supportEquivalent`, convenient for filtering
`List.range r` while retaining proof irrelevance for the bounds. -/
@[expose]
def supportEquivalentAt {r : Nat} (trueSupports : Set (Set (Fin r)))
    (j k : Nat) : Prop :=
  ∃ (hj : j < r) (hk : k < r),
    supportEquivalent trueSupports ⟨j, hj⟩ ⟨k, hk⟩

theorem supportEquivalentAt_iff {r : Nat}
    (trueSupports : Set (Set (Fin r))) {j k : Nat}
    (hj : j < r) (hk : k < r) :
    supportEquivalentAt trueSupports j k ↔
      supportEquivalent trueSupports ⟨j, hj⟩ ⟨k, hk⟩ := by
  constructor
  · intro h
    rcases h with ⟨hj', hk', h⟩
    simpa using h
  · intro h
    exact ⟨hj, hk, h⟩

theorem supportEquivalentAt_refl {r : Nat}
    (trueSupports : Set (Set (Fin r))) {j : Nat} (hj : j < r) :
    supportEquivalentAt trueSupports j j := by
  exact ⟨hj, hj, by intro S hS; simp⟩

theorem supportEquivalentAt_symm {r : Nat}
    (trueSupports : Set (Set (Fin r))) {j k : Nat}
    (h : supportEquivalentAt trueSupports j k) :
    supportEquivalentAt trueSupports k j := by
  rcases h with ⟨hj, hk, h⟩
  exact ⟨hk, hj, by intro S hS; exact (h S hS).symm⟩

theorem supportEquivalentAt_trans {r : Nat}
    (trueSupports : Set (Set (Fin r))) {i j k : Nat}
    (hij : supportEquivalentAt trueSupports i j)
    (hjk : supportEquivalentAt trueSupports j k) :
    supportEquivalentAt trueSupports i k := by
  rcases hij with ⟨hi, hj, hij⟩
  rcases hjk with ⟨hj', hk, hjk⟩
  exact ⟨hi, hk, by intro S hS; exact (hij S hS).trans (hjk S hS)⟩

/-- Minimum representatives of support-equivalence classes, emitted in
ascending column order. -/
@[expose]
def supportRepresentativeColumns {r : Nat}
    (trueSupports : Set (Set (Fin r))) : List Nat :=
  by
    classical
    exact (List.range r).filter
      (fun j =>
        ((List.range j).filter
          (fun k => decide (supportEquivalentAt trueSupports k j))).isEmpty)

/-- The support-equivalence class represented by `rep`, listed in ascending
column order. -/
def supportClassMembers {r : Nat}
    (trueSupports : Set (Set (Fin r))) (rep : Nat) : List Nat :=
  by
    classical
    exact (List.range r).filter
      (fun j => decide (supportEquivalentAt trueSupports j rep))

/-- Canonical partition of columns by true-support membership signatures. -/
@[expose]
def supportPartitionByMinColumn {r : Nat}
    (trueSupports : Set (Set (Fin r))) : List (List Nat) :=
  (supportRepresentativeColumns trueSupports).map
    (fun rep => supportClassMembers trueSupports rep)

/-- The executable indicator-array shape for a finite Nat-indexed class. -/
@[expose]
def classIndicatorArray (r : Nat) (members : List Nat) : Array Int :=
  ((List.range r).map (fun i => if i ∈ members then (1 : Int) else 0)).toArray

@[simp, grind =] theorem classIndicatorArray_size (r : Nat) (members : List Nat) :
    (classIndicatorArray r members).size = r := by
  unfold classIndicatorArray
  simp

theorem classIndicatorArray_getD
    (r : Nat) (members : List Nat) (i : Nat) :
    (classIndicatorArray r members).getD i 0 =
      if i < r ∧ i ∈ members then 1 else 0 := by
  unfold classIndicatorArray
  by_cases hi : i < r
  · simp [Array.getD, hi]
  · have hsize :
        ((List.range r).map (fun i => if i ∈ members then (1 : Int) else 0)).length = r := by
      simp
    simp [Array.getD, hi, hsize]

theorem classIndicatorArray_bits (r : Nat) (members : List Nat) :
    ∀ i, i < (classIndicatorArray r members).size →
      (classIndicatorArray r members).getD i 0 = 0 ∨
        (classIndicatorArray r members).getD i 0 = 1 := by
  intro i hi
  rw [classIndicatorArray_size] at hi
  rw [classIndicatorArray_getD]
  by_cases hmem : i ∈ members
  · simp [hi, hmem]
  · simp [hi, hmem]

theorem classIndicatorArray_has_one_of_mem
    (r : Nat) (members : List Nat) {i : Nat}
    (hi : i < r) (hmem : i ∈ members) :
    (classIndicatorArray r members).getD i 0 = 1 := by
  rw [classIndicatorArray_getD]
  simp [hi, hmem]


theorem mem_supportRepresentativeColumns_iff {r : Nat}
    (trueSupports : Set (Set (Fin r))) (rep : Nat) :
    rep ∈ supportRepresentativeColumns trueSupports ↔
      rep < r ∧
        ∀ k, k < rep → ¬ supportEquivalentAt trueSupports k rep := by
  classical
  unfold supportRepresentativeColumns
  rw [List.mem_filter]
  simp only [List.mem_range, List.isEmpty_iff]
  constructor
  · rintro ⟨hlt, hfilter⟩
    refine ⟨hlt, ?_⟩
    intro k hk heq
    have : k ∈ (List.range rep).filter
        (fun k => decide (supportEquivalentAt trueSupports k rep)) := by
      rw [List.mem_filter]
      exact ⟨List.mem_range.mpr hk, by simpa using heq⟩
    rw [hfilter] at this
    exact List.not_mem_nil this
  · rintro ⟨hlt, hfresh⟩
    refine ⟨hlt, ?_⟩
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro k hk
    rw [List.mem_filter] at hk
    exact hfresh k (List.mem_range.mp hk.1) (by simpa using hk.2)

theorem supportRepresentativeColumns_lt {r : Nat}
    (trueSupports : Set (Set (Fin r))) {rep : Nat}
    (hrep : rep ∈ supportRepresentativeColumns trueSupports) : rep < r :=
  ((mem_supportRepresentativeColumns_iff trueSupports rep).mp hrep).1

theorem supportRepresentativeColumns_min {r : Nat}
    (trueSupports : Set (Set (Fin r))) {rep : Nat}
    (hrep : rep ∈ supportRepresentativeColumns trueSupports) :
    ∀ k, k < rep → ¬ supportEquivalentAt trueSupports k rep :=
  ((mem_supportRepresentativeColumns_iff trueSupports rep).mp hrep).2

theorem mem_supportClassMembers_iff {r : Nat}
    (trueSupports : Set (Set (Fin r))) (rep j : Nat) :
    j ∈ supportClassMembers trueSupports rep ↔
      j < r ∧ supportEquivalentAt trueSupports j rep := by
  classical
  unfold supportClassMembers
  rw [List.mem_filter]
  simp [List.mem_range]

theorem supportClassMembers_rep_mem {r : Nat}
    (trueSupports : Set (Set (Fin r))) {rep : Nat}
    (hrep : rep ∈ supportRepresentativeColumns trueSupports) :
    rep ∈ supportClassMembers trueSupports rep := by
  rw [mem_supportClassMembers_iff]
  exact ⟨supportRepresentativeColumns_lt trueSupports hrep,
    supportEquivalentAt_refl trueSupports
      (supportRepresentativeColumns_lt trueSupports hrep)⟩

theorem supportClassMembers_mem_iff_fin {r : Nat}
    (trueSupports : Set (Set (Fin r))) {rep j : Nat}
    (hj : j < r) (hrep : rep < r) :
    j ∈ supportClassMembers trueSupports rep ↔
      supportEquivalent trueSupports ⟨j, hj⟩ ⟨rep, hrep⟩ := by
  rw [mem_supportClassMembers_iff, supportEquivalentAt_iff trueSupports hj hrep]
  simp [hj]


private theorem foldl_cut_ge_of_bound {N : Nat} (g : Fin N → Bool) (bound : Nat) :
    ∀ (l : List (Fin N)) (init : Nat),
      bound ≤ init → (∀ i ∈ l, bound ≤ i.val + 1) →
      bound ≤ l.foldl (fun acc i => if g i then i.val + 1 else acc) init := by
  intro l
  induction l with
  | nil => intro init hinit _; simpa using hinit
  | cons a tl ih =>
      intro init hinit hbnd
      apply ih
      · by_cases hga : g a
        · simp only [hga, if_true]; exact hbnd a (by simp)
        · simp only [hga, Bool.false_eq_true, if_false]; exact hinit
      · intro i hi; exact hbnd i (List.mem_cons_of_mem a hi)

/-- The cut fold over a strictly increasing index list reaches at least
`k.val + 1` once a passing index `k` has been processed. -/
private theorem foldl_cut_ge {N : Nat} (g : Fin N → Bool) (k : Fin N) :
    ∀ (l : List (Fin N)) (init : Nat),
      l.Pairwise (· < ·) → k ∈ l → g k = true →
      k.val + 1 ≤ l.foldl (fun acc i => if g i then i.val + 1 else acc) init := by
  intro l
  induction l with
  | nil => intro init _ hk _; simp at hk
  | cons a tl ih =>
      intro init hpw hk hgk
      rw [List.pairwise_cons] at hpw
      obtain ⟨hahead, htl⟩ := hpw
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hk with rfl | hktl
      · have hstep : (if g k then k.val + 1 else init) = k.val + 1 := by simp [hgk]
        rw [hstep]
        refine foldl_cut_ge_of_bound g (k.val + 1) tl (k.val + 1) (le_refl _) ?_
        intro i hi
        have hlt : k.val < i.val := hahead i hi
        omega
      · exact ih _ htl hktl hgk

/-- A Gram-Schmidt index that passes the executable cut test lies strictly below
the retained prefix length `bhksCutPrefixCount`, so its row is kept. -/
theorem bhksWithinGramSchmidtCut_lt_prefixCount
    (L : Hex.BhksLatticeBasis)
    (reduced : Hex.Matrix Int (L.factorCount + L.coeffWidth)
        (L.factorCount + L.coeffWidth))
    (k : Fin (L.factorCount + L.coeffWidth))
    (hk : Hex.bhksWithinGramSchmidtCut L
        (Hex.GramSchmidt.Int.gramDetVec reduced) k = true) :
    k.val < Hex.bhksCutPrefixCount L reduced := by
  unfold Hex.bhksCutPrefixCount
  exact foldl_cut_ge
    (fun i => Hex.bhksWithinGramSchmidtCut L (Hex.GramSchmidt.Int.gramDetVec reduced) i)
    k (List.finRange _) 0 (List.pairwise_lt_finRange _) (List.mem_finRange k) hk

/-- The executable cut test passes at index `i` once the stored leading
Gram determinant at `i` is nonzero and the radius inequality on the consecutive
determinant ratio holds. -/
theorem bhksWithinGramSchmidtCut_eq_true_of_le
    (L : Hex.BhksLatticeBasis)
    (dets : Vector Nat (L.factorCount + L.coeffWidth + 1))
    (i : Fin (L.factorCount + L.coeffWidth))
    (hne : dets.get ⟨i.val, by omega⟩ ≠ 0)
    (hle : 4 * ((dets.get ⟨i.val + 1, by omega⟩ : ℚ) /
        (dets.get ⟨i.val, by omega⟩ : ℚ)) ≤ (Hex.bhksCutRadiusSq4 L : ℚ)) :
    Hex.bhksWithinGramSchmidtCut L dets i = true := by
  unfold Hex.bhksWithinGramSchmidtCut
  rw [if_neg hne]
  exact decide_eq_true hle

/--
**BHKS prefix survivor-span (Lemma 5.7, forward).**

Any lattice vector `v` of the reduced BHKS basis whose squared length passes the
cut test (`4·‖v‖² ≤ bhksCutRadiusSq4`) lies in the integer span of the retained
prefix rows `b_0 … b_{t-1}`, where `t = bhksCutPrefixCount`.

The cut keeps a row `i` iff `4·‖b*_i‖² ≤ bhksCutRadiusSq4`, i.e.
`‖b*_i‖² ≤ bhksCutRadiusSq4 / 4`; the hypothesis is the matching tight bound on
`v` (four times its squared norm within the radius), *not* the loose
`‖v‖² ≤ bhksCutRadiusSq4`.
-/
theorem mem_prefixSubmodule_of_normSq_le
    (L : Hex.BhksLatticeBasis)
    (reduced : Hex.Matrix Int (L.factorCount + L.coeffWidth)
        (L.factorCount + L.coeffWidth))
    (hind : Hex.GramSchmidt.Int.independent reduced)
    (v : Vector Int (L.factorCount + L.coeffWidth))
    (hv : Hex.Matrix.memLattice reduced v)
    (hnorm : 4 * ((Vector.normSq v : Int) : ℚ) ≤ (Hex.bhksCutRadiusSq4 L : ℚ)) :
    HexMatrixMathlib.vectorEquiv v ∈
      HexLLLMathlib.prefixSubmodule reduced (Hex.bhksCutPrefixCount L reduced) := by
  by_cases hv0 : v = 0
  · subst hv0
    have hz : HexMatrixMathlib.vectorEquiv (0 : Vector Int (L.factorCount + L.coeffWidth))
        = (0 : Fin (L.factorCount + L.coeffWidth) → ℤ) := by
      funext i
      simp [HexMatrixMathlib.vectorEquiv]
    rw [hz]
    exact Submodule.zero_mem _
  · obtain ⟨k, c, hcv, hck, hzero_above, hbasis_norm⟩ :=
      Hex.GramSchmidt.Int.exists_top_index_normSq_le_of_memLattice reduced hind v hv hv0
    -- The top index `k` passes the cut test.
    set dets := Hex.GramSchmidt.Int.gramDetVec reduced with hdets
    have sw := Hex.GramSchmidt.Int.StepWitness.ofGram reduced
    have hd0 : dets.get ⟨k.val, by omega⟩
        = Hex.GramSchmidt.Int.gramDet reduced k.val (Nat.le_of_lt k.isLt) :=
      Hex.GramSchmidt.Int.gramDetVec_eq_gramDet reduced sw k.val (Nat.le_of_lt k.isLt)
    have hd1 : dets.get ⟨k.val + 1, by omega⟩
        = Hex.GramSchmidt.Int.gramDet reduced (k.val + 1) k.isLt :=
      Hex.GramSchmidt.Int.gramDetVec_eq_gramDet reduced sw (k.val + 1) k.isLt
    have hd0pos : 0 < Hex.GramSchmidt.Int.gramDet reduced k.val (Nat.le_of_lt k.isLt) := by
      rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
      · simp only [hk0]
        rw [Hex.GramSchmidt.Int.gramDet_zero]
        exact Nat.one_pos
      · exact Hex.GramSchmidt.Int.gramDet_pos reduced hind k.val (Nat.le_of_lt k.isLt) hkpos
    have hne : dets.get ⟨k.val, by omega⟩ ≠ 0 := by
      rw [hd0]; omega
    -- `‖b*_k‖² = gramDet(k+1)/gramDet(k)`.
    have hbnsq := Hex.GramSchmidt.Int.basis_normSq reduced hind k.val k.isLt
    have hpass : Hex.bhksWithinGramSchmidtCut L dets k = true := by
      refine bhksWithinGramSchmidtCut_eq_true_of_le L dets k hne ?_
      rw [hd0, hd1]
      -- goal: 4 * (gramDet(k+1)/gramDet(k)) ≤ radius
      rw [← hbnsq]
      -- goal: 4 * ‖b*_k‖² ≤ radius, with ‖b*_k‖² ≤ ‖v‖²
      calc 4 * Vector.normSq ((Hex.GramSchmidt.Int.basis reduced).row ⟨k.val, k.isLt⟩)
          ≤ 4 * ((Vector.normSq v : Int) : ℚ) := by
            have := hbasis_norm
            nlinarith [hbasis_norm]
        _ ≤ (Hex.bhksCutRadiusSq4 L : ℚ) := hnorm
    have hklt : k.val < Hex.bhksCutPrefixCount L reduced :=
      bhksWithinGramSchmidtCut_lt_prefixCount L reduced k (by rw [← hdets]; exact hpass)
    -- `c` vanishes at and above the retained prefix length.
    have hc : ∀ i : Fin (L.factorCount + L.coeffWidth),
        Hex.bhksCutPrefixCount L reduced ≤ i.val → c[i] = 0 := by
      intro i hi
      exact hzero_above i (by omega)
    have := HexLLLMathlib.vecMul_mem_prefixSubmodule_of_vector
      reduced c (Hex.bhksCutPrefixCount L reduced) hc
    rwa [hcv] at this

/--
Cut hypotheses needed to connect the executable projected rows to the abstract
true-factor supports.  Later B4/B5 work discharges `indicator_mem_projected`
from the BHKS norm bound and Gram-Schmidt cut soundness.
-/
structure CutProjectionHypotheses
    (L : Hex.BhksProjectedRows) (trueSupports : Set (Set (Fin L.factorCount))) where
  indicator_mem_projected :
    ∀ S : trueSupports, indicatorVector S.1 ∈ projectedRowSpanInt L

/-- Direct caller-facing form of the cut hypothesis for one true support. -/
theorem indicatorVector_mem_projectedRowSpan_of_cut
    (L : Hex.BhksProjectedRows) (trueSupports : Set (Set (Fin L.factorCount)))
    (hcut : CutProjectionHypotheses L trueSupports) (S : trueSupports) :
    indicatorVector S.1 ∈ projectedRowSpanInt L :=
  hcut.indicator_mem_projected S

theorem projectedRow_mem_projectedRowSpanInt
    (L : Hex.BhksProjectedRows) (i : Fin L.projectedRows.size) :
    Matrix.row (projectedRowsIntMatrix L) i ∈ projectedRowSpanInt L := by
  exact Submodule.subset_span ⟨i, rfl⟩

/-!
### True-factor cut-projection producer

The following bridges the BHKS prefix survivor-span lemma
(`mem_prefixSubmodule_of_normSq_le`) to `CutProjectionHypotheses` *without*
routing through `CutRetention`.  A true factor's CLD vector is a genuine short
lattice vector; the survivor-span lemma places it in the integer span of the
retained prefix rows, and projecting that span to the first `factorCount`
coordinates lands in `projectedRowSpanInt`, exactly where the executable cut
stores the projected rows.
-/

/-- Projection onto the first `r` coordinates as a `ℤ`-linear map. -/
@[expose]
def projFirst (r n : Nat) : (Fin (r + n) → ℤ) →ₗ[ℤ] (Fin r → ℤ) where
  toFun w := fun i => w (Fin.castAdd n i)
  map_add' a b := by funext i; simp
  map_smul' c a := by funext i; simp

@[simp, grind =] theorem projFirst_apply (r n : Nat) (w : Fin (r + n) → ℤ) (i : Fin r) :
    projFirst r n w i = w (Fin.castAdd n i) := rfl

/-- The squared Euclidean norm is the explicit sum of squared coordinates. -/
private theorem normSq_eq_sum {n : Nat} (v : Vector Int n) :
    Vector.normSq v = ∑ i : Fin n, v[i] ^ 2 := by
  unfold Vector.normSq Vector.dotProduct
  rw [finRange_foldl_add_eq_sum (g := fun i => v[i] * v[i])]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- An array `getD` at an in-bounds index is the indexed element. -/
private theorem array_getD_of_lt {α : Type*} (a : Array α) (k : Nat)
    (hk : k < a.size) (d : α) :
    a.getD k d = a[k]'hk := by
  simp [Array.getD, hk]

/-- `init`'s elements persist through the conditional-push fold. -/
private theorem mem_foldl_push_if_of_mem_init {α β : Type*}
    (p : α → Prop) [DecidablePred p] (g : α → β) (x : β) :
    ∀ (l : List α) (init : Array β), x ∈ init →
      x ∈ l.foldl (fun acc i => if p i then acc.push (g i) else acc) init := by
  intro l
  induction l with
  | nil => intro init hx; simpa using hx
  | cons a as ih =>
      intro init hx
      simp only [List.foldl_cons]
      by_cases hp : p a
      · rw [if_pos hp]; exact ih _ (Array.mem_push.mpr (Or.inl hx))
      · rw [if_neg hp]; exact ih _ hx

/-- A passing element `g i₀` of the conditional-push fold appears in the result. -/
private theorem mem_foldl_push_if {α β : Type*}
    (p : α → Prop) [DecidablePred p] (g : α → β) (i₀ : α) (hp₀ : p i₀) :
    ∀ (l : List α) (init : Array β), i₀ ∈ l →
      g i₀ ∈ l.foldl (fun acc i => if p i then acc.push (g i) else acc) init := by
  intro l
  induction l with
  | nil => intro init h; exact absurd h List.not_mem_nil
  | cons a as ih =>
      intro init h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | hmem
      · rw [if_pos hp₀]
        exact mem_foldl_push_if_of_mem_init p g (g i₀) as _
          (Array.mem_push.mpr (Or.inr rfl))
      · by_cases hp : p a
        · rw [if_pos hp]; exact ih _ hmem
        · rw [if_neg hp]; exact ih _ hmem

/-- The projected-indicator array reads off the first-`r`-block coordinate. -/
private theorem bhksProjectIndicator_getD {r n : Nat}
    (v : Vector Int (r + n)) (j : Fin r) :
    (Hex.bhksProjectIndicator r n v).getD j.val 0 = v[Fin.castAdd n j] := by
  have hsize : (Hex.bhksProjectIndicator r n v).size = r := by
    simp [Hex.bhksProjectIndicator]
  have hjlt : j.val < (Hex.bhksProjectIndicator r n v).size := by
    rw [hsize]; exact j.isLt
  have hjrn : j.val < r + n := Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right r n)
  rw [array_getD_of_lt _ _ hjlt]
  simp only [Hex.bhksProjectIndicator, List.getElem_toArray, List.getElem_map,
    List.getElem_range, dif_pos hjrn]
  rfl

/-- A retained prefix row, projected to its first block, is a generator of the
executable projected integer row span. -/
theorem projFirst_vectorEquiv_row_mem
    (L : Hex.BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (i : Fin (L.factorCount + L.coeffWidth))
    (hi : i.val <
        Hex.bhksCutPrefixCount L (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix) :
    projFirst L.factorCount L.coeffWidth
        (HexMatrixMathlib.vectorEquiv
          (Hex.Matrix.row (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix i))
      ∈ projectedRowSpanInt (Hex.bhksProjectedRows L hrows) := by
  set reduced := (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix with hred
  set P := Hex.bhksProjectedRows L hrows with hP
  set el := Hex.bhksProjectIndicator L.factorCount L.coeffWidth (Hex.Matrix.row reduced i)
    with hel
  have hmemArr : el ∈ P.projectedRows := by
    show el ∈ Hex.bhksCutProjectReducedRows L reduced
    exact mem_foldl_push_if (fun k => k.val < Hex.bhksCutPrefixCount L reduced)
      (fun k => Hex.bhksProjectIndicator L.factorCount L.coeffWidth
        (Hex.Matrix.row reduced k)) i hi (List.finRange _) #[] (List.mem_finRange i)
  obtain ⟨k, hk, hkeq⟩ := Array.mem_iff_getElem.mp hmemArr
  have heq : projFirst L.factorCount L.coeffWidth
      (HexMatrixMathlib.vectorEquiv (Hex.Matrix.row reduced i))
        = Matrix.row (projectedRowsIntMatrix P) ⟨k, hk⟩ := by
    funext j
    rw [projFirst_apply, HexMatrixMathlib.vectorEquiv_apply, Hex.Matrix.getElem_row]
    simp only [Matrix.row, projectedRowsIntMatrix]
    rw [array_getD_of_lt _ _ hk, hkeq, hel, bhksProjectIndicator_getD,
      Hex.Matrix.getElem_row]
  rw [heq]
  exact projectedRow_mem_projectedRowSpanInt P ⟨k, hk⟩

/-- Projecting a vector of the retained prefix submodule to its first block lands
in the executable projected integer row span. -/
theorem projFirst_mem_projectedRowSpanInt_of_mem_prefixSubmodule
    (L : Hex.BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (w : Fin (L.factorCount + L.coeffWidth) → ℤ)
    (hw : w ∈ HexLLLMathlib.prefixSubmodule
        (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix
        (Hex.bhksCutPrefixCount L (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix)) :
    projFirst L.factorCount L.coeffWidth w ∈
      projectedRowSpanInt (Hex.bhksProjectedRows L hrows) := by
  unfold HexLLLMathlib.prefixSubmodule at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact projFirst_vectorEquiv_row_mem L hrows i.1 i.2
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

/--
Build `CutProjectionHypotheses` from any per-support short vector in the BHKS
row lattice.

The vector may include nonzero diagonal-period row coefficients.  The prefix
survivor-span lemma only needs lattice membership plus the tight cut-radius
bound, and the final projection only needs the first block to be the support
indicator.
-/
def cutProjectionHypotheses_of_shortVectors
    (L : Hex.BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (hbasis : L.basis.independent)
    (trueSupports : Set (Set (Fin (Hex.bhksProjectedRows L hrows).factorCount)))
    (data : ∀ S : trueSupports, SupportShortVectorData L S.1) :
    CutProjectionHypotheses (Hex.bhksProjectedRows L hrows) trueSupports where
  indicator_mem_projected S := by
    set v := (data S).vector with hv
    have hind : (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix.independent := by
      rw [Hex.bhksProjectedRowsTrace_reducedMatrix_eq]
      exact Hex.lllNative_independent L.basis (3 / 4) Hex.lll_delta_lower
        Hex.lll_delta_upper hrows hbasis
    have hmemRed :
        Hex.Matrix.memLattice (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix v :=
      (traceReducedMatrix_memLattice_iff L hrows v).mpr (by
        simpa [hv] using (data S).memLattice)
    have hnorm :
        4 * ((Vector.normSq v : Int) : ℚ) ≤ (Hex.bhksCutRadiusSq4 L : ℚ) := by
      have ht := (data S).four_mul_sq_norm_le
      rw [← hv] at ht
      have hsum :
          (∑ i : Fin (L.factorCount + L.coeffWidth), (((v[i] : Int) : ℝ) ^ 2))
            = ((Vector.normSq v : Int) : ℝ) := by
        rw [normSq_eq_sum]; push_cast; ring
      rw [hsum] at ht
      have hZ : 4 * (Vector.normSq v : Int) ≤ (Hex.bhksCutRadiusSq4 L : Int) := by
        have hr : ((4 * Vector.normSq v : Int) : ℝ)
            ≤ ((Hex.bhksCutRadiusSq4 L : Int) : ℝ) := by push_cast at ht ⊢; linarith
        exact_mod_cast hr
      exact_mod_cast hZ
    have hpref := mem_prefixSubmodule_of_normSq_le L
      (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix hind v hmemRed hnorm
    have hmem := projFirst_mem_projectedRowSpanInt_of_mem_prefixSubmodule L hrows
      (HexMatrixMathlib.vectorEquiv v) hpref
    have hproj : projFirst L.factorCount L.coeffWidth (HexMatrixMathlib.vectorEquiv v)
        = indicatorVector S.1 := by
      funext i
      rw [projFirst_apply, HexMatrixMathlib.vectorEquiv_apply]
      exact (data S).project_eq i
    rwa [hproj] at hmem

/--
**True-factor cut-projection producer.**

Build `CutProjectionHypotheses` for a family of true-factor supports directly
from their CLD-vector certificates (`TrueFactorCLDVectorData`), their tight
norm bounds (`TrueFactorCLDTightNormBound`), and independence of the BHKS basis.
Each true support's indicator vector is the first block of a genuine short
lattice vector, which the prefix survivor-span lemma places in the retained
prefix span; projecting to the first `factorCount` coordinates lands the
indicator in `projectedRowSpanInt`.  This route does **not** pass through
`CutRetention`.
-/

theorem projectedRow_mem_projectedRowSpaceRat
    (L : Hex.BhksProjectedRows) (i : Fin L.projectedRows.size) :
    Matrix.row (projectedRowsRatMatrix L) i ∈ projectedRowSpaceRat L := by
  exact Submodule.subset_span ⟨i, rfl⟩

/-- `intVectorToRat` of the zero vector is the zero rational vector. -/
@[simp, grind =] theorem intVectorToRat_zero {r : Nat} :
    intVectorToRat (0 : Fin r → ℤ) = 0 := by
  funext i
  simp [intVectorToRat]

/-- `intVectorToRat` commutes with pointwise addition. -/
@[simp, grind =] theorem intVectorToRat_add {r : Nat} (u v : Fin r → ℤ) :
    intVectorToRat (u + v) = intVectorToRat u + intVectorToRat v := by
  funext i
  simp [intVectorToRat, Pi.add_apply]

/-- `intVectorToRat` of an integer-scalar multiple is the rational-cast scalar
times the rational vector. -/
@[simp, grind =] theorem intVectorToRat_intSmul {r : Nat} (n : ℤ) (v : Fin r → ℤ) :
    intVectorToRat (n • v) = (n : ℚ) • intVectorToRat v := by
  funext i
  simp only [intVectorToRat, Pi.smul_apply, smul_eq_mul, Int.cast_mul]

/-- Membership in the integer span carries over to membership of the
rational-cast vector in the rational span of the rational-cast generators. -/
theorem intVectorToRat_mem_span_rat_of_mem_span_int
    {r : Nat} {S : Set (Fin r → ℤ)} {v : Fin r → ℤ}
    (hv : v ∈ Submodule.span ℤ S) :
    intVectorToRat v ∈ Submodule.span ℚ (intVectorToRat '' S) := by
  induction hv using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span ⟨w, hw, rfl⟩
  | zero =>
      rw [intVectorToRat_zero]
      exact Submodule.zero_mem _
  | add u w _ _ hu hw =>
      rw [intVectorToRat_add]
      exact Submodule.add_mem _ hu hw
  | smul n w _ hw =>
      rw [intVectorToRat_intSmul]
      exact Submodule.smul_mem _ _ hw

/-- The rational projected row is the pointwise rational cast of the integer
projected row.  Both `projectedRowsRatMatrix` and `projectedRowsIntMatrix` read
the same underlying `L.projectedRows` array; the only difference is the
codomain. -/
theorem row_projectedRowsRatMatrix_eq_intVectorToRat
    (L : Hex.BhksProjectedRows) (i : Fin L.projectedRows.size) :
    Matrix.row (projectedRowsRatMatrix L) i =
      intVectorToRat (Matrix.row (projectedRowsIntMatrix L) i) := by
  funext j
  simp [Matrix.row, projectedRowsRatMatrix, projectedRowsIntMatrix,
    intVectorToRat]

/-- The range of the rational projected rows is the image of the range of the
integer projected rows under `intVectorToRat`. -/
theorem range_row_projectedRowsRatMatrix_eq_image
    (L : Hex.BhksProjectedRows) :
    (Set.range fun i : Fin L.projectedRows.size =>
        Matrix.row (projectedRowsRatMatrix L) i) =
      intVectorToRat ''
        (Set.range fun i : Fin L.projectedRows.size =>
          Matrix.row (projectedRowsIntMatrix L) i) := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Matrix.row (projectedRowsIntMatrix L) i, ⟨i, rfl⟩,
      (row_projectedRowsRatMatrix_eq_intVectorToRat L i).symm⟩
  · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (row_projectedRowsRatMatrix_eq_intVectorToRat L i)⟩

end BHKS

end

end HexBerlekampZassenhausMathlib
