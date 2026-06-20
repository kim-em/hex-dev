import HexMatrixMathlib.Determinant.Core
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
No-pivot Bareiss loop invariant for `hex-matrix-mathlib`.

This module proves the recursive bordered-minor invariant of the no-pivot
Bareiss recurrence: after `k` regular Bareiss steps, the trailing entries of
the working matrix agree with the corresponding bordered-minor determinants of
the source matrix, and the previous pivot agrees with the determinant of the
leading prefix of size `k`. As an immediate corollary, when all leading-prefix
determinants are nonzero (`NonzeroBareissPivots`), the loop never takes the
singular branch.

The invariant proof composes the bordered-minor `stepMatrix` update lemma
(`Hex.Matrix.stepMatrix_borderedMinor_update`) with the bordered-minor
specialization of Desnanot-Jacobi (`desnanot_jacobi_borderedMinor` in the
parent module) and the exact-division equation
(`bareissExactDiv_borderedMinor_of_mul_eq`).
-/

namespace HexMatrixMathlib

universe u

variable {n : Nat}

/-- The `k`-bordered minor of `M` at the corner row/column `⟨k, hk⟩` is exactly
the `(k + 1)`-leading prefix of `M`. This identifies the trailing-corner entry
under the no-pivot Bareiss invariant with a leading-prefix determinant. -/
theorem borderedMinor_corner_eq_leadingPrefix {R : Type u}
    [Lean.Grind.Ring R]
    (M : Hex.Matrix R n n) (k : Nat) (hk : k < n) :
    Hex.Matrix.borderedMinor M k hk ⟨k, hk⟩ ⟨k, hk⟩ =
      Hex.Matrix.leadingPrefix M (k + 1) (Nat.succ_le_of_lt hk) := by
  apply Vector.ext
  intro r _hr
  apply Vector.ext
  intro c _hc
  by_cases hrk : r < k <;> by_cases hck : c < k
  · simp [Hex.Matrix.borderedMinor, Hex.Matrix.leadingPrefix, Hex.Matrix.ofFn,
      hrk, hck]
  · have hc_eq : c = k := by omega
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.leadingPrefix, Hex.Matrix.ofFn,
      hrk, hc_eq]
  · have hr_eq : r = k := by omega
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.leadingPrefix, Hex.Matrix.ofFn,
      hck, hr_eq]
  · have hr_eq : r = k := by omega
    have hc_eq : c = k := by omega
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.leadingPrefix, Hex.Matrix.ofFn,
      hr_eq, hc_eq]

/-- Hypothesis used by the no-pivot Bareiss soundness proof: every leading
prefix determinant up to size `n` is nonzero. -/
def NonzeroBareissPivots (M : Hex.Matrix Int n n) : Prop :=
  ∀ k : Fin n,
    Hex.Matrix.det
      (Hex.Matrix.leadingPrefix M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) ≠ 0

/-- Bordered-minor invariant of the no-pivot Bareiss recurrence:
- `singularStep` is `none` (no pivot has been zero yet);
- the previous pivot equals the determinant of the leading prefix of size
  `state.step` (which is `1` for `state.step = 0`);
- the previous pivot is nonzero (so the next step's exact division is valid);
- every trailing entry `(i, j)` with `state.step ≤ i.val` and
  `state.step ≤ j.val` agrees with the determinant of the
  `state.step`-bordered minor with trailing row `i` and column `j`.

The implication on diagonal entries (`state.matrix[k][k]` agrees with the
leading-prefix determinant of size `k + 1`) follows from `trailing_eq` taken
at `i = j = ⟨k, _⟩` together with `borderedMinor_corner_eq_leadingPrefix`. -/
structure BareissNoPivotInvariant
    (source : Hex.Matrix Int n n) (state : Hex.Matrix.BareissState n) : Prop where
  singular_none : state.singularStep = none
  step_le : state.step ≤ n
  prevPivot_eq :
    state.prevPivot =
      Hex.Matrix.det (Hex.Matrix.leadingPrefix source state.step step_le)
  prevPivot_ne : state.prevPivot ≠ 0
  trailing_eq :
    ∀ (h : state.step < n) (i j : Fin n)
        (_ : state.step ≤ i.val) (_ : state.step ≤ j.val),
      state.matrix[i][j] =
        Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step h i j)

/-- The initial Bareiss no-pivot state satisfies the bordered-minor invariant:
the matrix is the source itself, and the previous-pivot convention is
`det (leadingPrefix _ 0 _) = 1`. -/
theorem bareissNoPivotInvariant_initial (M : Hex.Matrix Int n n) :
    BareissNoPivotInvariant M (Hex.Matrix.noPivotInitialState M) where
  singular_none := rfl
  step_le := Nat.zero_le _
  prevPivot_eq := by
    show (1 : Int) = Hex.Matrix.det (Hex.Matrix.leadingPrefix M 0 (Nat.zero_le n))
    simp
  prevPivot_ne := by
    show (1 : Int) ≠ 0
    decide
  trailing_eq := by
    intro h i j _hi _hj
    -- For `state.step = 0`, the bordered minor is the `1 × 1` block with the
    -- single entry `M[i][j]`.
    show M[i][j] = Hex.Matrix.det (Hex.Matrix.borderedMinor M 0 h i j)
    rw [Hex.Matrix.det_one_by_one]
    show M[i][j] =
        (Hex.Matrix.borderedMinor M 0 h i j)[(Fin.last 0)][(Fin.last 0)]
    rw [Hex.Matrix.borderedMinor_entry_last_last]

/-- One regular no-pivot Bareiss step preserves the bordered-minor invariant.
Given a state satisfying the invariant with `state.step + 1 < n` and a nonzero
diagonal pivot, the state produced by one `noPivotLoop` iteration also
satisfies the invariant. -/
private theorem bareissNoPivotInvariant_step
    (source : Hex.Matrix Int n n) (state : Hex.Matrix.BareissState n)
    (hinv : BareissNoPivotInvariant source state)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] ≠ 0) :
    BareissNoPivotInvariant source
      { step := state.step + 1
        matrix := Hex.Matrix.stepMatrix state.matrix state.step
          (state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
            (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)]) state.prevPivot
        prevPivot := state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
          (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)]
        rowSwaps := state.rowSwaps
        singularStep := none } where
  singular_none := rfl
  step_le := Nat.le_of_lt hDone
  prevPivot_eq := by
    -- Pivot at step k equals det (leadingPrefix source (k + 1) _), via
    -- trailing_eq @ (i = j = ⟨k, _⟩) and borderedMinor_corner_eq_leadingPrefix.
    have hk : state.step < n := Nat.lt_of_succ_lt hDone
    have hkk :
        state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] =
          Hex.Matrix.det
            (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, hk⟩ : Fin n) (⟨state.step, hk⟩ : Fin n)) :=
      hinv.trailing_eq hk ⟨state.step, hk⟩ ⟨state.step, hk⟩
        (Nat.le_refl _) (Nat.le_refl _)
    show state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] = _
    rw [hkk, borderedMinor_corner_eq_leadingPrefix source state.step hk]
  prevPivot_ne := hp
  trailing_eq := by
    intro hnext i j hi hj
    -- Unfold the structure projection so omega can see through it.
    change state.step + 1 ≤ i.val at hi
    change state.step + 1 ≤ j.val at hj
    have hk : state.step < n := Nat.lt_of_succ_lt hDone
    have hi' : state.step < i.val := hi
    have hj' : state.step < j.val := hj
    -- The pivot for the borderedMinor update is the `(k, k)` entry of
    -- `state.matrix`, which by `trailing_eq` equals
    -- `det (borderedMinor source state.step _ ⟨k, _⟩ ⟨k, _⟩)`.
    have hpivot_eq :
        state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] =
          Hex.Matrix.det
            (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n)
              (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) :=
      hinv.trailing_eq hk ⟨state.step, hk⟩ ⟨state.step, hk⟩
        (Nat.le_refl _) (Nat.le_refl _)
    -- `current[i][j]` agrees with the bordered minor at (i, j), via trailing_eq.
    have hentry :
        state.matrix[i][j] =
          Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk i j) :=
      hinv.trailing_eq hk i j (Nat.le_of_lt hi') (Nat.le_of_lt hj')
    -- `current[i][⟨k, _⟩]` agrees with the bordered minor at (i, ⟨k, _⟩).
    have hleft :
        state.matrix[i][(⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)] =
          Hex.Matrix.det
            (Hex.Matrix.borderedMinor source state.step hk i
              (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) :=
      hinv.trailing_eq hk i ⟨state.step, Nat.lt_trans hi' i.isLt⟩
        (Nat.le_of_lt hi') (Nat.le_refl _)
    -- `current[⟨k, _⟩][j]` agrees with the bordered minor at (⟨k, _⟩, j).
    have htop :
        state.matrix[(⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n)][j] =
          Hex.Matrix.det
            (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n) j) :=
      hinv.trailing_eq hk ⟨state.step, Nat.lt_trans hj' j.isLt⟩ j
        (Nat.le_refl _) (Nat.le_of_lt hj')
    -- Desnanot-Jacobi gives the exact-division premise.
    have hdesnanot :
        Hex.Matrix.det (Hex.Matrix.borderedMinor source (state.step + 1) hnext i j) *
            state.prevPivot =
          Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n)
              (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) *
            Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk i j) -
            Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
              i (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) *
            Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n) j) := by
      rw [hinv.prevPivot_eq]
      exact desnanot_jacobi_borderedMinor source state.step hk hnext i j hi' hj'
    have hexact :
        Hex.Matrix.exactDiv
            (Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n)
              (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) *
              Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk i j) -
              Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
                i (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) *
              Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
                (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n) j))
            state.prevPivot =
          Hex.Matrix.det (Hex.Matrix.borderedMinor source (state.step + 1) hnext i j) :=
      bareissExactDiv_borderedMinor_of_mul_eq source state.step hk hnext i j
        hi' hj' state.prevPivot hinv.prevPivot_ne hdesnanot
    -- Apply `stepMatrix_borderedMinor_update` to obtain the updated entry.
    show (Hex.Matrix.stepMatrix state.matrix state.step
        (state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)])
        state.prevPivot)[i][j] =
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (state.step + 1) hnext i j)
    exact Hex.Matrix.stepMatrix_borderedMinor_update source state.matrix
      state.step hk hnext i j hi' hj'
      (state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)])
      state.prevPivot hpivot_eq hentry hleft htop hexact

/-- Public regular no-swap step surface for the row-pivoted Bareiss proof.
When the current diagonal pivot is already nonzero, the row-pivoted loop takes
the same regular step as the no-pivot loop, so the bordered-minor invariant is
preserved by the existing no-pivot step proof. -/
theorem bareissPivotInvariant_regular_no_swap
    (source : Hex.Matrix Int n n) (state : Hex.Matrix.BareissState n)
    (hinv : BareissNoPivotInvariant source state)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    BareissNoPivotInvariant source
      { step := state.step + 1
        matrix := Hex.Matrix.stepMatrix state.matrix state.step
          state.matrix[state.step][state.step] state.prevPivot
        prevPivot := state.matrix[state.step][state.step]
        rowSwaps := state.rowSwaps
        singularStep := none } :=
  bareissNoPivotInvariant_step source state hinv hDone hp

/-- In the pivot-search failure branch, the current pivot column is zero at
and below the current step. -/
theorem bareissPivotNoPivot_column_eq_zero
    (state : Hex.Matrix.BareissState n) (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    ∀ i : Fin n, state.step ≤ i.val →
      state.matrix[i][
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)] =
        0 := by
  intro i hi
  by_cases heq : i.val = state.step
  · have hiFin :
        i = (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ :
          Fin n) :=
      Fin.ext heq
    rw [hiFin]
    simpa using hp0
  · have hstart : state.step + 1 ≤ i.val := by omega
    exact Hex.Matrix.findPivot?_eq_zero_of_none state.matrix
      (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
      (state.step + 1) hfind i hstart

/-- In the pivot-search failure branch, the bordered-minor invariant identifies
the zero current pivot with the next leading-prefix determinant. -/
theorem bareissPivotNoPivot_leadingPrefix_det_eq_zero
    (source : Hex.Matrix Int n n) (state : Hex.Matrix.BareissState n)
    (hinv : BareissNoPivotInvariant source state)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    Hex.Matrix.det
      (Hex.Matrix.leadingPrefix source (state.step + 1)
        (Nat.succ_le_of_lt (Nat.lt_of_succ_lt hDone))) = 0 := by
  have hcol := bareissPivotNoPivot_column_eq_zero state hDone hp0 hfind
  have hk : state.step < n := Nat.lt_of_succ_lt hDone
  have hpivot :
      state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] =
        0 := hcol ⟨state.step, hk⟩ (Nat.le_refl _)
  have hpivot_det :
      state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] =
        Hex.Matrix.det
          (Hex.Matrix.borderedMinor source state.step hk
            (⟨state.step, hk⟩ : Fin n) (⟨state.step, hk⟩ : Fin n)) :=
    hinv.trailing_eq hk ⟨state.step, hk⟩ ⟨state.step, hk⟩
      (Nat.le_refl _) (Nat.le_refl _)
  rw [hpivot_det, borderedMinor_corner_eq_leadingPrefix source state.step hk] at hpivot
  exact hpivot

/-- One-step zero propagation for the singular row-pivoted Bareiss branch.

If the current `k`-bordered trailing pivot column is zero at every row at or
below `k`, then every `(k + 1)`-bordered minor one step deeper is zero.  The
proof is the Desnanot-Jacobi recurrence: both numerator terms contain a zero
minor from the failed pivot column, and the previous leading-prefix pivot is
nonzero, so the next determinant must vanish. -/
theorem borderedMinor_zero_column_succ_det_eq_zero_of_entries
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (hprev :
      Hex.Matrix.det (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk)) ≠ 0)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val)
    (hcorner :
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
          (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) = 0)
    (hleft :
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
          i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) = 0) :
    Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) = 0 := by
  have hdesnanot :=
    desnanot_jacobi_borderedMinor source k hk hnext i j hi hj
  have hmul_zero :
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) *
          Hex.Matrix.det (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk)) = 0 := by
    calc
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) *
          Hex.Matrix.det (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk))
          =
        Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i j) -
        Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j) := hdesnanot
      _ =
        0 * Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i j) -
        0 * Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j) := by
          congr 1
          · exact congrArg
              (fun x =>
                x * Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i j))
              hcorner
          · exact congrArg
              (fun x =>
                x * Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
                  (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
              hleft
      _ = 0 := by ring
  exact (Int.mul_eq_zero.mp hmul_zero).resolve_right hprev

/-- Column-shaped form of `borderedMinor_zero_column_succ_det_eq_zero_of_entries`.
This is the API used by the singular row-pivoted Bareiss branch: failed pivot
search supplies a zero current pivot column, and the bordered-minor invariant
transports that to this determinant column hypothesis. -/
theorem borderedMinor_zero_column_succ_det_eq_zero
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (hprev :
      Hex.Matrix.det (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk)) ≠ 0)
    (hcol : ∀ i : Fin n, k ≤ i.val →
      Hex.Matrix.det
        (Hex.Matrix.borderedMinor source k hk i (⟨k, hk⟩ : Fin n)) = 0)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) :
    Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) = 0 :=
  borderedMinor_zero_column_succ_det_eq_zero_of_entries source k hk hnext hprev
    i j hi hj
    (by
      simpa using
        hcol (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) (Nat.le_refl _))
    (by
      simpa using hcol i (Nat.le_of_lt hi))

private theorem findPivot?_some_ne_current
    (state : Hex.Matrix.BareissState n) (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    pivot ≠ (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n) := by
  intro hpivot
  have hge :
      state.step + 1 ≤ pivot.val :=
    Hex.Matrix.findPivot?_ge_start state.matrix
      (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
      (state.step + 1) hfind
  have hval : pivot.val = state.step := by
    simpa using congrArg Fin.val hpivot
  omega

/-- In the row-swap regular branch, the Hex determinant of the working matrix
flips sign. This is the determinant-side row-swap fact needed by the
row-pivoted Bareiss invariant. -/
theorem bareissPivotRegularSwap_det
    (state : Hex.Matrix.BareissState n) (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    Hex.Matrix.det
        (Hex.Matrix.rowSwap state.matrix
          (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
          pivot) =
      -Hex.Matrix.det state.matrix := by
  apply Hex.Matrix.det_rowSwap
  intro hcurrent
  exact findPivot?_some_ne_current state hDone hfind hcurrent.symm

/-- Swapping source rows `kFin` and `pivot`, both indexed at `≥ k`, leaves the
size-`k` leading prefix unchanged. Used in the row-pivoted Bareiss invariant
to identify `prevPivot` with the leading-prefix determinant of the row-swapped
source matrix. -/
private theorem leadingPrefix_rowSwap_eq_of_le {R : Type u}
    (M : Hex.Matrix R n n) (k : Nat) (hk : k ≤ n)
    (kFin pivot : Fin n) (hkF : k ≤ kFin.val) (hp : k ≤ pivot.val) :
    Hex.Matrix.leadingPrefix (Hex.Matrix.rowSwap M kFin pivot) k hk =
      Hex.Matrix.leadingPrefix M k hk := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  have hr_lt : r < n := Nat.lt_of_lt_of_le hr hk
  have h_r_ne_kFin : (⟨r, hr_lt⟩ : Fin n) ≠ kFin := by
    intro h
    have hval : r = kFin.val := by simpa using congrArg Fin.val h
    omega
  have h_r_ne_pivot : (⟨r, hr_lt⟩ : Fin n) ≠ pivot := by
    intro h
    have hval : r = pivot.val := by simpa using congrArg Fin.val h
    omega
  show ((Hex.Matrix.rowSwap M kFin pivot).leadingPrefix k hk)[(⟨r, hr⟩ : Fin k)][
      (⟨c, hc⟩ : Fin k)] =
    (M.leadingPrefix k hk)[(⟨r, hr⟩ : Fin k)][(⟨c, hc⟩ : Fin k)]
  rw [Hex.Matrix.leadingPrefix_entry, Hex.Matrix.leadingPrefix_entry]
  simp only [Hex.Matrix.rowSwap_getElem, if_neg h_r_ne_pivot, if_neg h_r_ne_kFin]

/-- Auxiliary: a row of `rowSwap M kFin pivot` with index `r` not equal to
either swap target equals the corresponding row of `M`. -/
private theorem rowSwap_getElem_of_ne {R : Type u}
    (M : Hex.Matrix R n n) (kFin pivot r : Fin n) (c : Fin n)
    (hr_ne_kFin : r ≠ kFin) (hr_ne_pivot : r ≠ pivot) :
    (Hex.Matrix.rowSwap M kFin pivot)[r][c] = M[r][c] := by
  rw [Hex.Matrix.rowSwap_getElem]
  rw [if_neg hr_ne_pivot, if_neg hr_ne_kFin]

/-- Reading row `r` of `rowSwap M kFin pivot` returns row `swap_idx r` of `M`,
where `swap_idx kFin pivot r = if r = pivot then kFin else if r = kFin then pivot else r`. -/
private theorem rowSwap_getElem_swap_eq {R : Type u}
    (M : Hex.Matrix R n n) (kFin pivot r : Fin n) (c : Fin n) :
    (Hex.Matrix.rowSwap M kFin pivot)[r][c] =
      M[if r = pivot then kFin else if r = kFin then pivot else r][c] := by
  rw [Hex.Matrix.rowSwap_getElem]
  by_cases hrp : r = pivot
  · simp only [if_pos hrp]
  · by_cases hrk : r = kFin
    · simp only [if_neg hrp, if_pos hrk]
    · simp only [if_neg hrp, if_neg hrk]

/-- Swapping source rows `kFin` and `pivot` (with `kFin.val = k` and
`k + 1 ≤ pivot.val`) commutes with the bordered-minor construction at level
`k`: the leading rows are unchanged, and the border row at index `i` of the
swapped source equals the border row at the swap-permuted index of the
original source. -/
private theorem borderedMinor_rowSwap_source_row {R : Type u}
    (M : Hex.Matrix R n n) (k : Nat) (hk : k < n)
    (kFin pivot : Fin n) (hkF : kFin.val = k) (hp : k + 1 ≤ pivot.val)
    (i j : Fin n) :
    Hex.Matrix.borderedMinor (Hex.Matrix.rowSwap M kFin pivot) k hk i j =
      Hex.Matrix.borderedMinor M k hk
        (if i = pivot then kFin else if i = kFin then pivot else i) j := by
  -- The bordered-minor body computes a row index `rr` and column index `cc`,
  -- then reads `M[rr][cc]`. For r < k, rr = ⟨r, _⟩ on both sides, so the
  -- equation reduces to a row equality on M (modulo the source row swap).
  -- For r = k, rr = i on LHS and rr = swap_idx i on RHS; the row equality
  -- is exactly `rowSwap_getElem`.
  apply Vector.ext
  intro r _hr
  apply Vector.ext
  intro c _hc
  by_cases hrk : r < k
  · have hr_lt : r < n := Nat.lt_trans hrk hk
    have h_r_ne_kFin : (⟨r, hr_lt⟩ : Fin n) ≠ kFin := by
      intro h
      have hval : r = kFin.val := by simpa using congrArg Fin.val h
      omega
    have h_r_ne_pivot : (⟨r, hr_lt⟩ : Fin n) ≠ pivot := by
      intro h
      have hval : r = pivot.val := by simpa using congrArg Fin.val h
      omega
    by_cases hck : c < k
    · have hc_lt : c < n := Nat.lt_trans hck hk
      simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hrk, hck]
      show (Hex.Matrix.rowSwap M kFin pivot)[(⟨r, hr_lt⟩ : Fin n)][(⟨c, hc_lt⟩ : Fin n)] =
          M[(⟨r, hr_lt⟩ : Fin n)][(⟨c, hc_lt⟩ : Fin n)]
      exact rowSwap_getElem_of_ne M kFin pivot ⟨r, hr_lt⟩ _ h_r_ne_kFin h_r_ne_pivot
    · simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hrk, hck]
      show (Hex.Matrix.rowSwap M kFin pivot)[(⟨r, hr_lt⟩ : Fin n)][j] =
          M[(⟨r, hr_lt⟩ : Fin n)][j]
      exact rowSwap_getElem_of_ne M kFin pivot ⟨r, hr_lt⟩ _ h_r_ne_kFin h_r_ne_pivot
  · by_cases hck : c < k
    · have hc_lt : c < n := Nat.lt_trans hck hk
      simp only [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, Vector.getElem_ofFn,
        hrk, hck, dif_pos, dif_neg, not_false_iff]
      show (Hex.Matrix.rowSwap M kFin pivot)[i][(⟨c, hc_lt⟩ : Fin n)] = _
      exact rowSwap_getElem_swap_eq M kFin pivot i _
    · simp only [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, Vector.getElem_ofFn,
        hrk, hck, dif_neg, not_false_iff]
      show (Hex.Matrix.rowSwap M kFin pivot)[i][j] = _
      exact rowSwap_getElem_swap_eq M kFin pivot i j

/-- Public regular swap-only step surface for the row-pivoted Bareiss proof.
When the current diagonal pivot is zero and `findPivot?` returns a later row,
the row-pivoted loop swaps source rows `state.step` and `pivot` before applying
the stepMatrix update. Under that source rewrite, the bordered-minor invariant
transports across the source row swap: the working matrix is `rowSwap`'d to
match, the row-swap counter increments, and `state.step` is unchanged.

The subsequent stepMatrix update is then handled by
`bareissPivotInvariant_regular_no_swap` applied to the swapped source. -/
theorem bareissPivotInvariant_regular_swap
    (source : Hex.Matrix Int n n) (state : Hex.Matrix.BareissState n)
    (hinv : BareissNoPivotInvariant source state)
    (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    BareissNoPivotInvariant
      (Hex.Matrix.rowSwap source
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        pivot)
      { state with
          matrix := Hex.Matrix.rowSwap state.matrix
            (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
            pivot
          rowSwaps := state.rowSwaps + 1 } := by
  have hk : state.step < n := Nat.lt_of_succ_lt hDone
  set kFin : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
  have hkF_val : kFin.val = state.step := rfl
  have hp_ge :
      state.step + 1 ≤ pivot.val :=
    Hex.Matrix.findPivot?_ge_start state.matrix kFin (state.step + 1) hfind
  refine
    { singular_none := hinv.singular_none
      step_le := hinv.step_le
      prevPivot_eq := ?_
      prevPivot_ne := hinv.prevPivot_ne
      trailing_eq := ?_ }
  · -- Leading prefix of size state.step is unchanged: kFin and pivot both
    -- have value ≥ state.step.
    have hkF_ge : state.step ≤ kFin.val := Nat.le_of_eq hkF_val.symm
    have hp_le : state.step ≤ pivot.val := Nat.le_of_succ_le hp_ge
    rw [leadingPrefix_rowSwap_eq_of_le source state.step hinv.step_le kFin pivot
      hkF_ge hp_le]
    exact hinv.prevPivot_eq
  · intro hnext i j hi hj
    -- The working matrix entry at (i, j) under rowSwap rewrites by cases on i.
    rw [Hex.Matrix.rowSwap_getElem]
    -- The bordered minor at (i, j) of the row-swapped source equals the
    -- bordered minor of the original source with the border row swapped.
    rw [borderedMinor_rowSwap_source_row source state.step hk kFin pivot hkF_val
      hp_ge i j]
    by_cases hip : i = pivot
    · simp only [if_pos hip]
      -- Need: state.matrix[kFin][j] = det (borderedMinor source state.step _ kFin j).
      have hkFin_le : state.step ≤ kFin.val := Nat.le_of_eq hkF_val.symm
      exact hinv.trailing_eq hk kFin j hkFin_le hj
    · by_cases hik : i = kFin
      · simp only [if_neg hip, if_pos hik]
        -- Need: state.matrix[pivot][j] = det (borderedMinor source state.step _ pivot j).
        have hp_step : state.step ≤ pivot.val := Nat.le_of_succ_le hp_ge
        exact hinv.trailing_eq hk pivot j hp_step hj
      · simp only [if_neg hip, if_neg hik]
        exact hinv.trailing_eq hk i j hi hj

private theorem bareissSign_succ (swaps : Nat) :
    (if (swaps + 1) % 2 = 0 then (1 : Int) else -1) =
      -(if swaps % 2 = 0 then (1 : Int) else -1) := by
  omega

/-- Incrementing the row-swap counter flips the Bareiss sign. -/
theorem bareissData_sign_succ (data : Hex.Matrix.BareissData n) :
    ({ data with rowSwaps := data.rowSwaps + 1 }).sign = -data.sign := by
  simp [Hex.Matrix.BareissData.sign, bareissSign_succ]

private def bareissStateSign (state : Hex.Matrix.BareissState n) : Int :=
  if state.rowSwaps % 2 = 0 then 1 else -1

/-- Row-pivoted Bareiss invariant. The current working state is interpreted as
a no-pivot Bareiss state for a logical source obtained from the original source
by the row swaps already performed; the sign field records the determinant
relation back to the original source. -/
def BareissPivotInvariant
    (source : Hex.Matrix Int n n) (state : Hex.Matrix.BareissState n) : Prop :=
  ∃ logicalSource : Hex.Matrix Int n n,
    Hex.Matrix.det source = bareissStateSign state * Hex.Matrix.det logicalSource ∧
      BareissNoPivotInvariant logicalSource state

/-- The initial row-pivoted Bareiss state satisfies the pivoted invariant with
the original matrix as its logical source. -/
theorem bareissPivotInvariant_initial (M : Hex.Matrix Int n n) :
    BareissPivotInvariant M (Hex.Matrix.noPivotInitialState M) :=
  ⟨M, by simp [bareissStateSign, Hex.Matrix.noPivotInitialState],
    bareissNoPivotInvariant_initial M⟩

/-- A regular row-pivoted Bareiss step that does not swap rows preserves the
pivoted invariant. -/
theorem bareissPivotInvariant_regular_no_swap_step
    (source : Hex.Matrix Int n n) (state : Hex.Matrix.BareissState n)
    (hinv : BareissPivotInvariant source state)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    BareissPivotInvariant source
      { step := state.step + 1
        matrix := Hex.Matrix.stepMatrix state.matrix state.step
          state.matrix[state.step][state.step] state.prevPivot
        prevPivot := state.matrix[state.step][state.step]
        rowSwaps := state.rowSwaps
        singularStep := none } := by
  rcases hinv with ⟨logicalSource, hdet, hnopiv⟩
  exact ⟨logicalSource, hdet,
    bareissPivotInvariant_regular_no_swap logicalSource state hnopiv hDone hp⟩

private theorem bareissPivotInvariant_swap_source
    (source : Hex.Matrix Int n n) (state : Hex.Matrix.BareissState n)
    (hinv : BareissPivotInvariant source state)
    (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    BareissPivotInvariant source
      { state with
          matrix := Hex.Matrix.rowSwap state.matrix
            (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
            pivot
          rowSwaps := state.rowSwaps + 1 } := by
  rcases hinv with ⟨logicalSource, hdet, hnopiv⟩
  set kFin : Fin n :=
    ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
  have hpivot_ne : pivot ≠ kFin :=
    findPivot?_some_ne_current state hDone hfind
  refine ⟨Hex.Matrix.rowSwap logicalSource kFin pivot, ?_, ?_⟩
  · have hswap :
        Hex.Matrix.det (Hex.Matrix.rowSwap logicalSource kFin pivot) =
          -Hex.Matrix.det logicalSource :=
      Hex.Matrix.det_rowSwap logicalSource kFin pivot hpivot_ne.symm
    rw [hswap]
    simpa [bareissStateSign, bareissSign_succ, neg_mul, mul_neg, neg_neg] using hdet
  · simpa [kFin] using
      bareissPivotInvariant_regular_swap logicalSource state hnopiv hDone hfind

private theorem pivotLoop_swap_pivot_ne_zero
    (state : Hex.Matrix.BareissState n)
    (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    (Hex.Matrix.rowSwap state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        pivot)[state.step][state.step] ≠ 0 := by
  set kFin : Fin n :=
    ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
  have hpivot_ne : pivot ≠ kFin :=
    findPivot?_some_ne_current state hDone hfind
  have hpivot :
      state.matrix[pivot][kFin] ≠ 0 :=
    Hex.Matrix.findPivot?_some_ne_zero state.matrix kFin (state.step + 1) hfind
  have hentry :
      (Hex.Matrix.rowSwap state.matrix kFin pivot)[kFin][kFin] =
        state.matrix[pivot][kFin] := by
    rw [Hex.Matrix.rowSwap_getElem]
    simp [hpivot_ne.symm]
  simpa [kFin] using hentry ▸ hpivot

/-- A regular row-pivoted Bareiss step that swaps rows preserves the pivoted
invariant. -/
theorem bareissPivotInvariant_regular_swap_step
    (source : Hex.Matrix Int n n) (state : Hex.Matrix.BareissState n)
    (hinv : BareissPivotInvariant source state)
    (hDone : state.step + 1 < n)
    {pivot : Fin n}
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot) :
    BareissPivotInvariant source
      { step := state.step + 1
        matrix := Hex.Matrix.stepMatrix
          (Hex.Matrix.rowSwap state.matrix
            (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
            pivot)
          state.step
          ((Hex.Matrix.rowSwap state.matrix
            (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
            pivot)[state.step][state.step])
          state.prevPivot
        prevPivot :=
          (Hex.Matrix.rowSwap state.matrix
            (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
            pivot)[state.step][state.step]
        rowSwaps := state.rowSwaps + 1
        singularStep := none } := by
  have hswapped :=
    bareissPivotInvariant_swap_source source state hinv hDone hfind
  exact bareissPivotInvariant_regular_no_swap_step source
    { state with
        matrix := Hex.Matrix.rowSwap state.matrix
          (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
          pivot
        rowSwaps := state.rowSwaps + 1 }
    hswapped hDone (pivotLoop_swap_pivot_ne_zero state hDone hfind)

/-- Recursive row-pivoted Bareiss invariant. If a `pivotLoop` run finishes with
no singular step, then the final state still satisfies the pivoted invariant. -/
theorem pivotLoop_invariant_of_singularStep_eq_none
    (source : Hex.Matrix Int n n)
    (fuel : Nat) (state : Hex.Matrix.BareissState n)
    (hinv : BareissPivotInvariant source state)
    (hregular : (Hex.Matrix.pivotLoop fuel state).singularStep = none) :
    BareissPivotInvariant source (Hex.Matrix.pivotLoop fuel state) := by
  induction fuel generalizing state with
  | zero =>
      simpa [Hex.Matrix.pivotLoop] using hinv
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp0 : state.matrix[state.step][state.step] = 0
        · set kFin : Fin n :=
            ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
          cases hfind :
              Hex.Matrix.findPivot? state.matrix kFin (state.step + 1) with
          | none =>
              have hloop :=
                Hex.Matrix.pivotLoop_singular_branch_no_pivot fuel state hDone hp0
                  (by simpa [kFin] using hfind)
              rw [hloop] at hregular
              simp at hregular
          | some pivot =>
              have hp :=
                pivotLoop_swap_pivot_ne_zero state hDone (by simpa [kFin] using hfind)
              rw [Hex.Matrix.pivotLoop_regular_branch_swap fuel state hDone hp0
                (by simpa [kFin] using hfind) hp]
              apply ih
              · exact bareissPivotInvariant_regular_swap_step source state hinv hDone
                  (by simpa [kFin] using hfind)
              · simpa [Hex.Matrix.pivotLoop_regular_branch_swap fuel state hDone hp0
                  (by simpa [kFin] using hfind) hp] using hregular
        · rw [Hex.Matrix.pivotLoop_regular_branch_no_swap fuel state hDone hp0]
          apply ih
          · exact bareissPivotInvariant_regular_no_swap_step source state hinv hDone hp0
          · simpa [Hex.Matrix.pivotLoop_regular_branch_no_swap fuel state hDone hp0]
              using hregular
      · simpa [Hex.Matrix.pivotLoop_done fuel state hDone] using hinv

/-- The recursive no-pivot Bareiss invariant: starting from any state that
satisfies `BareissNoPivotInvariant`, if every future leading-prefix determinant
(from `state.step` up to `n`) is nonzero, then the invariant continues to hold
after running `noPivotLoop` for any amount of fuel. -/
theorem noPivotLoop_invariant
    (source : Hex.Matrix Int n n)
    (fuel : Nat) (state : Hex.Matrix.BareissState n)
    (hinv : BareissNoPivotInvariant source state)
    (hpivots : ∀ (k : Fin n), state.step ≤ k.val →
      Hex.Matrix.det
        (Hex.Matrix.leadingPrefix source (k.val + 1) (Nat.succ_le_of_lt k.isLt))
          ≠ 0) :
    BareissNoPivotInvariant source (Hex.Matrix.noPivotLoop fuel state) := by
  induction fuel generalizing state with
  | zero =>
      simp [Hex.Matrix.noPivotLoop]
      exact hinv
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · have hk : state.step < n := Nat.lt_of_succ_lt hDone
        -- The pivot at the current step is nonzero by hpivots applied to
        -- `⟨state.step, hk⟩ : Fin n`, after rewriting through the invariant.
        have hpivot_idx :
            state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] =
              Hex.Matrix.det
                (Hex.Matrix.leadingPrefix source (state.step + 1)
                  (Nat.succ_le_of_lt hk)) := by
          rw [hinv.trailing_eq hk ⟨state.step, hk⟩ ⟨state.step, hk⟩
            (Nat.le_refl _) (Nat.le_refl _)]
          rw [borderedMinor_corner_eq_leadingPrefix source state.step hk]
        have hp_ne :
            state.matrix[(⟨state.step, hk⟩ : Fin n)][
              (⟨state.step, hk⟩ : Fin n)] ≠ 0 := by
          rw [hpivot_idx]
          exact hpivots ⟨state.step, hk⟩ (Nat.le_refl _)
        rw [Hex.Matrix.noPivotLoop_regular_branch fuel state hDone hp_ne]
        -- Apply IH on the next state.
        apply ih
        · exact bareissNoPivotInvariant_step source state hinv hDone hp_ne
        · intro k' hk'
          change state.step + 1 ≤ k'.val at hk'
          exact hpivots k' (Nat.le_of_succ_le hk')
      · simp [Hex.Matrix.noPivotLoop_done fuel state hDone]
        exact hinv

/-- Under `NonzeroBareissPivots`, the no-pivot Bareiss recurrence run from the
initial state satisfies the bordered-minor invariant. -/
theorem bareissNoPivotInvariant_holds
    (M : Hex.Matrix Int n n) (h : NonzeroBareissPivots M) :
    BareissNoPivotInvariant M
      (Hex.Matrix.noPivotLoop n (Hex.Matrix.noPivotInitialState M)) :=
  noPivotLoop_invariant M n (Hex.Matrix.noPivotInitialState M)
    (bareissNoPivotInvariant_initial M)
    (fun k _ => h k)

/-- Immediate consequence of the bordered-minor invariant: under
`NonzeroBareissPivots`, the no-pivot Bareiss recurrence never takes the
singular branch. -/
theorem noPivotLoop_singularStep_eq_none
    (M : Hex.Matrix Int n n) (h : NonzeroBareissPivots M) :
    (Hex.Matrix.noPivotLoop n (Hex.Matrix.noPivotInitialState M)).singularStep =
      none :=
  (bareissNoPivotInvariant_holds M h).singular_none

/-- Public corollary: under `NonzeroBareissPivots`, the executable no-pivot
Bareiss data records no singular step. -/
theorem bareissNoPivotData_singularStep_eq_none
    (M : Hex.Matrix Int n n) (h : NonzeroBareissPivots M) :
    (Hex.Matrix.bareissNoPivotData M).singularStep = none := by
  show (Hex.Matrix.noPivotLoop n (Hex.Matrix.noPivotInitialState M)).singularStep
      = none
  exact noPivotLoop_singularStep_eq_none M h

/-- Outcome-driven companion of `noPivotLoop_invariant`: if the no-pivot
Bareiss loop run from a valid invariant state does NOT record a singular step
during its `fuel` iterations, the invariant continues to hold afterward. The
non-singular outcome guarantees every visited pivot was nonzero, which is the
hypothesis the inductive step needs.

This is the no-pivot analog of `pivotLoop_invariant_of_singularStep_eq_none`. -/
theorem noPivotLoop_invariant_of_singularStep_eq_none
    (source : Hex.Matrix Int n n)
    (fuel : Nat) (state : Hex.Matrix.BareissState n)
    (hinv : BareissNoPivotInvariant source state)
    (hregular : (Hex.Matrix.noPivotLoop fuel state).singularStep = none) :
    BareissNoPivotInvariant source (Hex.Matrix.noPivotLoop fuel state) := by
  induction fuel generalizing state with
  | zero =>
      simpa [Hex.Matrix.noPivotLoop] using hinv
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp0 :
            state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
              (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0
        · rw [Hex.Matrix.noPivotLoop_singular_branch fuel state hDone hp0] at hregular
          simp at hregular
        · rw [Hex.Matrix.noPivotLoop_regular_branch fuel state hDone hp0]
          apply ih
          · exact bareissNoPivotInvariant_step source state hinv hDone hp0
          · simpa [Hex.Matrix.noPivotLoop_regular_branch fuel state hDone hp0]
              using hregular
      · simpa [Hex.Matrix.noPivotLoop_done fuel state hDone] using hinv

/-- The no-pivot Bareiss loop preserves the bound `state.step + 1 ≤ n`. -/
private theorem noPivotLoop_step_succ_le
    (fuel : Nat) (state : Hex.Matrix.BareissState n) (h : state.step + 1 ≤ n) :
    (Hex.Matrix.noPivotLoop fuel state).step + 1 ≤ n := by
  induction fuel generalizing state with
  | zero =>
      show state.step + 1 ≤ n
      exact h
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp :
            state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
              (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0
        · rw [Hex.Matrix.noPivotLoop_singular_branch fuel state hDone hp]
          exact h
        · rw [Hex.Matrix.noPivotLoop_regular_branch fuel state hDone hp]
          apply ih
          show state.step + 1 + 1 ≤ n
          omega
      · rw [Hex.Matrix.noPivotLoop_done fuel state hDone]
        exact h

/-- Under `NonzeroBareissPivots`, the no-pivot Bareiss loop run with enough
fuel reaches a final step satisfying `state.step + 1 ≥ n`. -/
private theorem noPivotLoop_step_succ_ge
    (fuel : Nat) (state : Hex.Matrix.BareissState n)
    (source : Hex.Matrix Int n n)
    (hinv : BareissNoPivotInvariant source state)
    (hpivots : ∀ (k : Fin n), state.step ≤ k.val →
      Hex.Matrix.det
        (Hex.Matrix.leadingPrefix source (k.val + 1) (Nat.succ_le_of_lt k.isLt))
          ≠ 0)
    (hfuel : n ≤ state.step + fuel + 1) :
    n ≤ (Hex.Matrix.noPivotLoop fuel state).step + 1 := by
  induction fuel generalizing state with
  | zero =>
      show n ≤ state.step + 1
      omega
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · have hk : state.step < n := Nat.lt_of_succ_lt hDone
        have hpivot_idx :
            state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] =
              Hex.Matrix.det
                (Hex.Matrix.leadingPrefix source (state.step + 1)
                  (Nat.succ_le_of_lt hk)) := by
          rw [hinv.trailing_eq hk ⟨state.step, hk⟩ ⟨state.step, hk⟩
            (Nat.le_refl _) (Nat.le_refl _)]
          rw [borderedMinor_corner_eq_leadingPrefix source state.step hk]
        have hp_ne :
            state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] ≠ 0 := by
          rw [hpivot_idx]
          exact hpivots ⟨state.step, hk⟩ (Nat.le_refl _)
        rw [Hex.Matrix.noPivotLoop_regular_branch fuel state hDone hp_ne]
        apply ih
        · exact bareissNoPivotInvariant_step source state hinv hDone hp_ne
        · intro k' hk'
          change state.step + 1 ≤ k'.val at hk'
          exact hpivots k' (Nat.le_of_succ_le hk')
        · show n ≤ state.step + 1 + fuel + 1
          omega
      · rw [Hex.Matrix.noPivotLoop_done fuel state hDone]
        show n ≤ state.step + 1
        omega

/-- The leading prefix of size `n` of an `n × n` matrix is the matrix itself. -/
private theorem leadingPrefix_self {R : Type u} [Lean.Grind.Ring R]
    (M : Hex.Matrix R n n) (h : n ≤ n) :
    Hex.Matrix.leadingPrefix M n h = M := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [Hex.Matrix.leadingPrefix, Hex.Matrix.ofFn]

/-- Helper: under the bordered-minor invariant, when the recurrence step
equals `k`, the `(k, k)` entry of the working matrix equals `Hex.Matrix.det M`.
Stated with `state` as an explicit free variable so that `state.step = k` can
be substituted via `subst`. -/
private theorem trailing_corner_entry_eq_det
    (k : Nat) (M : Hex.Matrix Int (k + 1) (k + 1))
    (state : Hex.Matrix.BareissState (k + 1))
    (hinv : BareissNoPivotInvariant M state)
    (hstep : state.step = k) :
    state.matrix[(⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))][
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))] = Hex.Matrix.det M := by
  obtain ⟨step', matrix', prev', swaps', sing'⟩ := state
  -- Force the structure projection in `hstep` to reduce so `subst` applies.
  change step' = k at hstep
  -- `subst hstep` substitutes `k` with `step'` (Lean's preferred direction).
  subst hstep
  have hk' : step' < step' + 1 := Nat.lt_succ_self step'
  have h_trail :=
    hinv.trailing_eq hk' ⟨step', hk'⟩ ⟨step', hk'⟩ (Nat.le_refl _) (Nat.le_refl _)
  change matrix'[(⟨step', hk'⟩ : Fin (step' + 1))][
      (⟨step', hk'⟩ : Fin (step' + 1))] = Hex.Matrix.det M
  change matrix'[(⟨step', hk'⟩ : Fin (step' + 1))][
      (⟨step', hk'⟩ : Fin (step' + 1))] =
    Hex.Matrix.det
      (Hex.Matrix.borderedMinor M step' hk' ⟨step', hk'⟩ ⟨step', hk'⟩) at h_trail
  rw [h_trail, borderedMinor_corner_eq_leadingPrefix M step' hk',
    leadingPrefix_self M (Nat.succ_le_of_lt hk')]

/-- Capstone: under `NonzeroBareissPivots`, the no-pivot Bareiss recurrence
computes the Mathlib determinant of the source matrix. -/
theorem bareissNoPivot_eq_det
    (M : Hex.Matrix Int n n) (h : NonzeroBareissPivots M) :
    Hex.Matrix.bareissNoPivot M = Matrix.det (matrixEquiv M) := by
  -- The no-pivot Bareiss data has `singularStep = none` (no zero pivot) and
  -- `rowSwaps = 0` (the no-pivot loop never swaps rows), giving sign `1`.
  have hdata_sing : (Hex.Matrix.bareissNoPivotData M).singularStep = none :=
    bareissNoPivotData_singularStep_eq_none M h
  have hdata_swaps : (Hex.Matrix.bareissNoPivotData M).rowSwaps = 0 := by
    show (Hex.Matrix.noPivotLoop n (Hex.Matrix.noPivotInitialState M)).rowSwaps = 0
    rw [Hex.Matrix.noPivotLoop_rowSwaps]
    rfl
  have hdata_sign : (Hex.Matrix.bareissNoPivotData M).sign = 1 := by
    unfold Hex.Matrix.BareissData.sign
    rw [hdata_swaps]
    decide
  match n, M, h with
  | 0, M, _ =>
      -- Empty matrix: Hex side is `sign = 1` by `det_zero_eq`,
      -- Mathlib side is `1` by `Matrix.det_isEmpty`.
      show (Hex.Matrix.bareissNoPivotData M).det = Matrix.det (matrixEquiv M)
      rw [Hex.Matrix.BareissData.det_zero_eq _ hdata_sing, hdata_sign,
        Matrix.det_isEmpty]
  | k + 1, M, h =>
      have hinv := bareissNoPivotInvariant_holds M h
      have hk : k < k + 1 := Nat.lt_succ_self k
      -- The final step equals `k = (k + 1) - 1`.
      have hstep_le :
          (Hex.Matrix.noPivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)).step + 1 ≤
            k + 1 :=
        noPivotLoop_step_succ_le (k + 1) (Hex.Matrix.noPivotInitialState M)
          (by show 0 + 1 ≤ k + 1; omega)
      have hstep_ge :
          k + 1 ≤
            (Hex.Matrix.noPivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)).step
              + 1 := by
        apply noPivotLoop_step_succ_ge (k + 1)
          (Hex.Matrix.noPivotInitialState M) M
          (bareissNoPivotInvariant_initial M)
        · intro k' _
          exact h k'
        · show k + 1 ≤ 0 + (k + 1) + 1
          omega
      have hstep_eq :
          (Hex.Matrix.noPivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)).step
            = k := by
        omega
      -- The (k, k) entry of the final matrix equals `det M`.
      have hentry :
          (Hex.Matrix.noPivotLoop (k + 1)
              (Hex.Matrix.noPivotInitialState M)).matrix[(⟨k, hk⟩ : Fin (k + 1))][
                (⟨k, hk⟩ : Fin (k + 1))] =
            Hex.Matrix.det M :=
        trailing_corner_entry_eq_det k M
          (Hex.Matrix.noPivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M))
          hinv hstep_eq
      -- Combine: BareissData.det = sign * (k, k) entry = 1 * det M = det M.
      show (Hex.Matrix.bareissNoPivotData M).det = Matrix.det (matrixEquiv M)
      rw [Hex.Matrix.BareissData.det_succ_eq _ hdata_sing, hdata_sign, one_mul,
        show (Hex.Matrix.bareissNoPivotData M).matrix[(⟨k, hk⟩ : Fin (k + 1))][
            (⟨k, hk⟩ : Fin (k + 1))] = Hex.Matrix.det M from hentry]
      exact det_eq M

/-! ### Failed Bareiss column dependence

Helper for the row-pivoted singular Bareiss branch: if the pivot search at
level `k` fails (the entire `k`-bordered trailing column is zero) and the
preceding leading-prefix determinant is nonzero, then there is an explicit
linear combination of the columns of `source` — with coefficients given by the
signed `k × k` cofactors of the leading prefix augmented with column `k` —
that vanishes at every row. The coefficient on column `k` is
`Hex.Matrix.det (Hex.Matrix.leadingPrefix source k _)`, which is nonzero by
hypothesis. The follow-up issue closes the determinant via
`Matrix.det_updateCol_sum` and the duplicate-column determinant identity. -/

/-- The `k × (k+1)` top block used to define the failed-pivot column
dependence: leading `k` rows of `source`, restricted to columns `0..k-1`
followed by column `k`. -/
private def failedBareissTopBlock
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) :
    Matrix (Fin k) (Fin (k + 1)) Int :=
  fun s c =>
    if hc : c.val < k then
      matrixEquiv source (⟨s.val, Nat.lt_trans s.isLt hk⟩ : Fin n)
        (⟨c.val, Nat.lt_trans hc hk⟩ : Fin n)
    else
      matrixEquiv source (⟨s.val, Nat.lt_trans s.isLt hk⟩ : Fin n) ⟨k, hk⟩

/-- Coefficient function for the failed-pivot column dependence. The value at
`c` is `(-1)^(k + c.val) * det(failedBareissTopBlock with column c removed)` for
`c.val ≤ k` and `0` otherwise. The coefficient on column `k` is
`det (leadingPrefix source k _)`; see `failedBareissColumn_at_pivot`. -/
noncomputable def failedBareissColumn
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) :
    Fin n → Int :=
  fun c =>
    if hc : c.val ≤ k then
      (-1) ^ (k + c.val) *
        Matrix.det
          ((failedBareissTopBlock source k hk).submatrix id
            (⟨c.val, Nat.lt_succ_of_le hc⟩ : Fin (k + 1)).succAbove)
    else 0

theorem failedBareissColumn_above_pivot
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n)
    (c : Fin n) (hc : k < c.val) :
    failedBareissColumn source k hk c = 0 := by
  show (if h : c.val ≤ k then _ else (0 : Int)) = 0
  rw [dif_neg (Nat.not_le_of_lt hc)]

private theorem failedBareissTopBlock_apply_lt
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n)
    (s : Fin k) (c : Fin (k + 1)) (hc : c.val < k) :
    failedBareissTopBlock source k hk s c =
      matrixEquiv source (⟨s.val, Nat.lt_trans s.isLt hk⟩ : Fin n)
        (⟨c.val, Nat.lt_trans hc hk⟩ : Fin n) := by
  show (if h : c.val < k then _ else _) = _
  rw [dif_pos hc]

private theorem failedBareissTopBlock_apply_last
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n)
    (s : Fin k) :
    failedBareissTopBlock source k hk s (Fin.last k) =
      matrixEquiv source (⟨s.val, Nat.lt_trans s.isLt hk⟩ : Fin n) ⟨k, hk⟩ := by
  show (if h : (Fin.last k : Fin (k + 1)).val < k then _ else _) = _
  simp only [Fin.val_last]
  rw [dif_neg (Nat.lt_irrefl k)]

private theorem failedBareissTopBlock_succAbove_last
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) :
    (failedBareissTopBlock source k hk).submatrix id (Fin.last k).succAbove =
      matrixEquiv (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk)) := by
  ext s t
  show failedBareissTopBlock source k hk s ((Fin.last k).succAbove t) = _
  rw [Fin.succAbove_last]
  have ht : (t.castSucc : Fin (k + 1)).val < k := by
    show t.val < k; exact t.isLt
  rw [failedBareissTopBlock_apply_lt source k hk s t.castSucc ht]
  show matrixEquiv source _ _ = matrixEquiv (Hex.Matrix.leadingPrefix _ _ _) _ _
  rw [matrixEquiv_apply, matrixEquiv_apply, Hex.Matrix.leadingPrefix_entry]
  rfl

theorem failedBareissColumn_at_pivot
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) :
    failedBareissColumn source k hk ⟨k, hk⟩ =
      Hex.Matrix.det (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk)) := by
  show (if hc : (⟨k, hk⟩ : Fin n).val ≤ k then
      (-1) ^ (k + (⟨k, hk⟩ : Fin n).val) *
        Matrix.det ((failedBareissTopBlock source k hk).submatrix id
          (⟨(⟨k, hk⟩ : Fin n).val, Nat.lt_succ_of_le hc⟩ : Fin (k + 1)).succAbove)
      else 0) = _
  rw [dif_pos (le_refl k)]
  have hsign : (-1 : Int) ^ (k + k) = 1 := by
    rw [← Nat.two_mul, pow_mul]; norm_num
  show (-1 : Int) ^ (k + k) *
      Matrix.det ((failedBareissTopBlock source k hk).submatrix id
        (Fin.last k).succAbove) = _
  rw [hsign, one_mul, failedBareissTopBlock_succAbove_last, ← det_eq]
  rfl

/-- The bordered minor's `(Fin.last k, c')` entry equals
`matrixEquiv source r ⟨c'.val, _⟩` (independent of which subcase of `c'.val < k`
vs `c'.val = k` we are in). -/
private theorem matrixEquiv_borderedMinor_apply_last
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) (r : Fin n)
    (c' : Fin (k + 1)) :
    ((matrixEquiv source).submatrix
        (fun r' : Fin (k + 1) =>
          if hr : r'.val < k then (⟨r'.val, Nat.lt_trans hr hk⟩ : Fin n) else r)
        (fun c'' : Fin (k + 1) =>
          if hc : c''.val < k then (⟨c''.val, Nat.lt_trans hc hk⟩ : Fin n) else
            ⟨k, hk⟩))
        (Fin.last k) c' =
      matrixEquiv source r
        (⟨c'.val, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ c'.isLt) hk⟩ : Fin n) := by
  show matrixEquiv source
      (if hr : (Fin.last k : Fin (k + 1)).val < k then _ else r)
      (if hc : c'.val < k then (⟨c'.val, Nat.lt_trans hc hk⟩ : Fin n) else
        ⟨k, hk⟩) = _
  simp only [Fin.val_last]
  rw [dif_neg (Nat.lt_irrefl k)]
  by_cases hcv : c'.val < k
  · rw [dif_pos hcv]
  · have hc_eq : c'.val = k :=
      Nat.le_antisymm (Nat.le_of_lt_succ c'.isLt) (Nat.not_lt.mp hcv)
    rw [dif_neg hcv]
    show matrixEquiv source r (⟨k, hk⟩ : Fin n) =
      matrixEquiv source r (⟨c'.val, Nat.lt_of_le_of_lt
        (Nat.le_of_lt_succ c'.isLt) hk⟩ : Fin n)
    rw [show (⟨c'.val, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ c'.isLt) hk⟩ : Fin n) =
        (⟨k, hk⟩ : Fin n) from Fin.ext hc_eq]

/-- The cofactor minor of the bordered minor (with the last row removed) equals
the corresponding submatrix of the top block. -/
private theorem submatrix_borderedMinor_succAbove_last_eq_topBlock
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) (r : Fin n)
    (c' : Fin (k + 1)) :
    ((matrixEquiv source).submatrix
        (fun r' : Fin (k + 1) =>
          if hr : r'.val < k then (⟨r'.val, Nat.lt_trans hr hk⟩ : Fin n) else r)
        (fun c'' : Fin (k + 1) =>
          if hc : c''.val < k then (⟨c''.val, Nat.lt_trans hc hk⟩ : Fin n) else
            ⟨k, hk⟩)).submatrix
        (Fin.last k).succAbove c'.succAbove =
      (failedBareissTopBlock source k hk).submatrix id c'.succAbove := by
  ext s t
  show matrixEquiv source
      (if hr : ((Fin.last k).succAbove s).val < k then
        (⟨((Fin.last k).succAbove s).val, Nat.lt_trans hr hk⟩ : Fin n) else r)
      (if hc : (c'.succAbove t).val < k then
        (⟨(c'.succAbove t).val, Nat.lt_trans hc hk⟩ : Fin n) else ⟨k, hk⟩) =
    failedBareissTopBlock source k hk s (c'.succAbove t)
  rw [Fin.succAbove_last]
  have hslt : (s.castSucc : Fin (k + 1)).val < k := s.isLt
  rw [dif_pos hslt]
  by_cases hctlt : (c'.succAbove t).val < k
  · rw [dif_pos hctlt]
    rw [failedBareissTopBlock_apply_lt source k hk s (c'.succAbove t) hctlt]
    rfl
  · have hctlt' : k ≤ (c'.succAbove t).val := Nat.not_lt.mp hctlt
    have hct_eq : (c'.succAbove t).val = k := by
      have := (c'.succAbove t).isLt
      omega
    rw [dif_neg hctlt]
    have h_succAbove_eq : c'.succAbove t = Fin.last k := Fin.ext hct_eq
    rw [h_succAbove_eq]
    rw [failedBareissTopBlock_apply_last source k hk s]
    rfl

/-- For any source row `r`, the dot product of `failedBareissColumn` with row
`r` of `source` equals the determinant of the `(k+1)`-bordered minor with
trailing row `r` and trailing column `⟨k, _⟩`. This is the cofactor expansion
of the bordered minor along its last row. -/
private theorem failedBareissColumn_dot_row_eq_borderedMinor_det
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) (r : Fin n) :
    ∑ c : Fin n, failedBareissColumn source k hk c * matrixEquiv source r c =
      Matrix.det
        (matrixEquiv (Hex.Matrix.borderedMinor source k hk r ⟨k, hk⟩)) := by
  -- Embedding φ : Fin (k+1) → Fin n.
  let φ : Fin (k + 1) → Fin n :=
    fun c' => ⟨c'.val, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ c'.isLt) hk⟩
  have hφ_apply : ∀ c' : Fin (k + 1), (φ c').val = c'.val := fun _ => rfl
  have hφ_inj : Function.Injective φ := by
    intro c₁ c₂ h
    apply Fin.ext
    have := congrArg Fin.val h
    simpa [φ] using this
  -- LHS = sum over the image of φ (other terms vanish since failedBareissColumn = 0).
  have hLHS :
      ∑ c : Fin n, failedBareissColumn source k hk c * matrixEquiv source r c =
        ∑ c' : Fin (k + 1),
          failedBareissColumn source k hk (φ c') * matrixEquiv source r (φ c') := by
    have h_others_zero : ∀ c ∈ (Finset.univ : Finset (Fin n)),
        c ∉ (Finset.univ : Finset (Fin (k + 1))).image φ →
        failedBareissColumn source k hk c * matrixEquiv source r c = 0 := by
      intro c _ hcnotin
      have hck : k < c.val := by
        by_contra h
        apply hcnotin
        have h' : c.val ≤ k := Nat.not_lt.mp h
        exact Finset.mem_image.mpr
          ⟨⟨c.val, Nat.lt_succ_of_le h'⟩, Finset.mem_univ _, Fin.ext rfl⟩
      rw [failedBareissColumn_above_pivot source k hk c hck, zero_mul]
    rw [← Finset.sum_subset
        ((Finset.univ : Finset (Fin (k + 1))).image φ).subset_univ h_others_zero]
    rw [Finset.sum_image (fun a _ b _ h => hφ_inj h)]
  rw [hLHS]
  -- RHS via cofactor expansion along the last row.
  rw [matrixEquiv_borderedMinor source k hk r ⟨k, hk⟩,
      Matrix.det_succ_row _ (Fin.last k)]
  apply Finset.sum_congr rfl
  intro c' _
  -- Compare the c'-th terms on both sides.
  have hφc'_le : (φ c').val ≤ k := Nat.le_of_lt_succ c'.isLt
  have hφc'_eq_c' : (⟨(φ c').val, Nat.lt_succ_of_le hφc'_le⟩ : Fin (k + 1)) = c' :=
    Fin.ext rfl
  have hα_eq :
      failedBareissColumn source k hk (φ c') =
        (-1) ^ (k + c'.val) *
          Matrix.det
            ((failedBareissTopBlock source k hk).submatrix id c'.succAbove) := by
    show (if hc : (φ c').val ≤ k then _ else (0 : Int)) = _
    rw [dif_pos hφc'_le, hφc'_eq_c', hφ_apply]
  rw [hα_eq, matrixEquiv_borderedMinor_apply_last source k hk r c',
      submatrix_borderedMinor_succAbove_last_eq_topBlock source k hk r c']
  -- Now reduce both sides to a normal form.
  show (-1 : Int) ^ (k + c'.val) *
      Matrix.det ((failedBareissTopBlock source k hk).submatrix id c'.succAbove) *
      matrixEquiv source r (φ c') =
    (-1 : Int) ^ ((Fin.last k : Fin (k + 1)).val + c'.val) *
      matrixEquiv source r
        (⟨c'.val, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ c'.isLt) hk⟩ : Fin n) *
      Matrix.det ((failedBareissTopBlock source k hk).submatrix id c'.succAbove)
  simp only [Fin.val_last]
  show (-1 : Int) ^ (k + c'.val) * _ * matrixEquiv source r (φ c') =
    (-1 : Int) ^ (k + c'.val) * matrixEquiv source r (φ c') * _
  ring

/-- For row `r` with `r.val < k`, the bordered minor at level `k` with trailing
row `r` has two equal rows (the `r.val`-th leading row and the trailing row),
so its determinant is zero. -/
private theorem matrixEquiv_borderedMinor_det_eq_zero_of_row_lt
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) (r : Fin n) (hr : r.val < k) :
    Matrix.det
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk r ⟨k, hk⟩)) = 0 := by
  rw [matrixEquiv_borderedMinor source k hk r ⟨k, hk⟩]
  -- The rows ⟨r.val, Nat.lt_succ_of_lt hr⟩ : Fin (k+1) and Fin.last k are distinct
  -- (since r.val < k) and yield equal rows of the matrix (both equal source row r).
  apply Matrix.det_zero_of_row_eq (i := (⟨r.val, Nat.lt_succ_of_lt hr⟩ : Fin (k + 1)))
    (j := Fin.last k)
  · intro h
    have hv : r.val = k := by simpa using congrArg Fin.val h
    omega
  funext c
  show matrixEquiv source
      (if h : (⟨r.val, Nat.lt_succ_of_lt hr⟩ : Fin (k + 1)).val < k then _ else r) _ =
    matrixEquiv source
      (if h : (Fin.last k : Fin (k + 1)).val < k then _ else r) _
  rw [dif_pos hr]
  simp only [Fin.val_last]
  rw [dif_neg (Nat.lt_irrefl k)]

/-- **Failed Bareiss column dependence.**

If the leading-prefix determinant of `source` at size `k` is nonzero, and the
`k`-bordered minors with trailing column `⟨k, _⟩` all vanish for trailing rows
at or beyond `k`, then there is an explicit linear combination of the columns
of `source` — vanishing in every row — whose coefficient on column `k` equals
the leading-prefix determinant (and is therefore nonzero). The coefficients on
columns past `k` are zero.

The construction is the standard cofactor/adjugate trick: cofactor expansion
along the last row of the `(k+1)`-bordered minors yields the coefficient
function `failedBareissColumn`. -/
theorem failed_bareiss_column_dependence
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n)
    (hprev :
      Hex.Matrix.det (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk)) ≠ 0)
    (hcol :
      ∀ i : Fin n, k ≤ i.val →
        Hex.Matrix.det
          (Hex.Matrix.borderedMinor source k hk i (⟨k, hk⟩ : Fin n)) = 0) :
    ∃ α : Fin n → Int,
      α ⟨k, hk⟩ ≠ 0 ∧
        (∀ c : Fin n, k < c.val → α c = 0) ∧
        (matrixEquiv source).mulVec α = 0 := by
  refine ⟨failedBareissColumn source k hk, ?_,
    fun c hc => failedBareissColumn_above_pivot source k hk c hc, ?_⟩
  · rw [failedBareissColumn_at_pivot source k hk]; exact hprev
  funext r
  show ∑ c : Fin n,
      matrixEquiv source r c * failedBareissColumn source k hk c = 0
  -- Use commutativity to match the dot-product orientation.
  have h_comm :
      ∑ c : Fin n, matrixEquiv source r c * failedBareissColumn source k hk c =
        ∑ c : Fin n, failedBareissColumn source k hk c * matrixEquiv source r c := by
    apply Finset.sum_congr rfl
    intros c _
    exact mul_comm _ _
  rw [h_comm, failedBareissColumn_dot_row_eq_borderedMinor_det source k hk r]
  by_cases hrk : r.val < k
  · exact matrixEquiv_borderedMinor_det_eq_zero_of_row_lt source k hk r hrk
  · have hrk' : k ≤ r.val := Nat.not_lt.mp hrk
    rw [← det_eq]
    exact hcol r hrk'

/-- **Failed Bareiss column ⟹ source determinant is zero.**

If the leading-prefix determinant of `source` at size `k` is nonzero but every
`k`-bordered minor with trailing column `⟨k, _⟩` and trailing row at or below
`k` vanishes, then `Hex.Matrix.det source = 0`.

This is the Mathlib-side theorem consumed by the row-pivoted singular Bareiss
packaging: failed pivot search at level `k` produces a zero pivot column,
which the bordered-minor invariant transports to the determinant column
hypothesis here. The proof obtains a nonzero kernel vector for
`matrixEquiv source` from `failed_bareiss_column_dependence`, then closes the
determinant via `Matrix.exists_mulVec_eq_zero_iff`. -/
theorem det_eq_zero_of_bareiss_failed_column
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n)
    (hprev :
      Hex.Matrix.det (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk)) ≠ 0)
    (hcol : ∀ i : Fin n, k ≤ i.val →
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i ⟨k, hk⟩) = 0) :
    Hex.Matrix.det source = 0 := by
  obtain ⟨α, hα_ne, _hα_above, hmulvec⟩ :=
    failed_bareiss_column_dependence source k hk hprev hcol
  have hdet_zero : Matrix.det (matrixEquiv source) = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨α, ?_, hmulvec⟩
    intro hα_zero
    apply hα_ne
    simpa using congrFun hα_zero ⟨k, hk⟩
  exact (det_eq source).trans hdet_zero

/-- If row-pivoted Bareiss pivot search fails in a state satisfying the
pivoted invariant, then the original source determinant is zero. -/
theorem bareissPivotInvariant_singular_no_pivot_det_eq_zero
    (source : Hex.Matrix Int n n) (state : Hex.Matrix.BareissState n)
    (hinv : BareissPivotInvariant source state)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      Hex.Matrix.findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    Hex.Matrix.det source = 0 := by
  rcases hinv with ⟨logicalSource, hdet, hnopiv⟩
  have hk : state.step < n := Nat.lt_of_succ_lt hDone
  have hprev :
      Hex.Matrix.det
          (Hex.Matrix.leadingPrefix logicalSource state.step (Nat.le_of_lt hk)) ≠ 0 := by
    rw [← hnopiv.prevPivot_eq]
    exact hnopiv.prevPivot_ne
  have hzero_col := bareissPivotNoPivot_column_eq_zero state hDone hp0 hfind
  have hcol : ∀ i : Fin n, state.step ≤ i.val →
      Hex.Matrix.det
          (Hex.Matrix.borderedMinor logicalSource state.step hk i ⟨state.step, hk⟩) =
        0 := by
    intro i hi
    have hentry :
        state.matrix[i][(⟨state.step, hk⟩ : Fin n)] = 0 :=
      hzero_col i hi
    have htrail :
        state.matrix[i][(⟨state.step, hk⟩ : Fin n)] =
          Hex.Matrix.det
            (Hex.Matrix.borderedMinor logicalSource state.step hk i ⟨state.step, hk⟩) :=
      hnopiv.trailing_eq hk i ⟨state.step, hk⟩ hi (Nat.le_refl _)
    rw [← htrail]
    exact hentry
  have hlogical_zero :
      Hex.Matrix.det logicalSource = 0 :=
    det_eq_zero_of_bareiss_failed_column logicalSource state.step hk hprev hcol
  rw [hlogical_zero, mul_zero] at hdet
  exact hdet

/-- If a row-pivoted Bareiss loop reaches any singular step from a state
satisfying the pivoted invariant, then the original source determinant is
zero. -/
theorem pivotLoop_singularStep_ne_none_det_eq_zero
    (source : Hex.Matrix Int n n)
    (fuel : Nat) (state : Hex.Matrix.BareissState n)
    (hinv : BareissPivotInvariant source state)
    (hsing : (Hex.Matrix.pivotLoop fuel state).singularStep ≠ none) :
    Hex.Matrix.det source = 0 := by
  induction fuel generalizing state with
  | zero =>
      rcases hinv with ⟨_, _, hnopiv⟩
      simp [Hex.Matrix.pivotLoop, hnopiv.singular_none] at hsing
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp0 : state.matrix[state.step][state.step] = 0
        · set kFin : Fin n :=
            ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
          cases hfind :
              Hex.Matrix.findPivot? state.matrix kFin (state.step + 1) with
          | none =>
              exact bareissPivotInvariant_singular_no_pivot_det_eq_zero source state hinv
                hDone hp0 (by simpa [kFin] using hfind)
          | some pivot =>
              have hp :=
                pivotLoop_swap_pivot_ne_zero state hDone (by simpa [kFin] using hfind)
              apply ih
              · exact bareissPivotInvariant_regular_swap_step source state hinv hDone
                  (by simpa [kFin] using hfind)
              · simpa [Hex.Matrix.pivotLoop_regular_branch_swap fuel state hDone hp0
                  (by simpa [kFin] using hfind) hp] using hsing
        · apply ih
          · exact bareissPivotInvariant_regular_no_swap_step source state hinv hDone hp0
          · simpa [Hex.Matrix.pivotLoop_regular_branch_no_swap fuel state hDone hp0]
              using hsing
      · rcases hinv with ⟨_, _, hnopiv⟩
        simp [Hex.Matrix.pivotLoop_done fuel state hDone, hnopiv.singular_none] at hsing

/-- Some specific singular step recorded by `pivotLoop` forces the source
determinant to be zero. -/
theorem pivotLoop_singularStep_eq_some_det_eq_zero
    (source : Hex.Matrix Int n n)
    (fuel : Nat) (state : Hex.Matrix.BareissState n)
    (hinv : BareissPivotInvariant source state) {k : Nat}
    (hsing : (Hex.Matrix.pivotLoop fuel state).singularStep = some k) :
    Hex.Matrix.det source = 0 :=
  pivotLoop_singularStep_ne_none_det_eq_zero source fuel state hinv (by
    rw [hsing]
    simp)

/-- The public row-pivoted Bareiss loop, started from the initial state,
records a singular step only when the input determinant is zero. -/
theorem pivotLoop_initial_singularStep_ne_none_det_eq_zero
    (M : Hex.Matrix Int n n)
    (hsing :
      (Hex.Matrix.pivotLoop n (Hex.Matrix.noPivotInitialState M)).singularStep ≠ none) :
    Hex.Matrix.det M = 0 :=
  pivotLoop_singularStep_ne_none_det_eq_zero M n (Hex.Matrix.noPivotInitialState M)
    (bareissPivotInvariant_initial M) hsing

/-- Data-facing singular branch theorem for the final row-pivoted Bareiss
capstone. -/
theorem bareissData_singularStep_ne_none_det_eq_zero
    (M : Hex.Matrix Int n n)
    (hsing : (Hex.Matrix.bareissData M).singularStep ≠ none) :
    Hex.Matrix.det M = 0 := by
  apply pivotLoop_initial_singularStep_ne_none_det_eq_zero M
  intro hregular
  apply hsing
  simpa [Hex.Matrix.bareissData_eq_finish_pivotLoop, Hex.Matrix.finish] using hregular

private theorem pivotLoop_step_succ_le
    (fuel : Nat) (state : Hex.Matrix.BareissState n) (h : state.step + 1 ≤ n) :
    (Hex.Matrix.pivotLoop fuel state).step + 1 ≤ n := by
  induction fuel generalizing state with
  | zero =>
      show state.step + 1 ≤ n
      exact h
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp0 : state.matrix[state.step][state.step] = 0
        · set kFin : Fin n :=
            ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
          cases hfind :
              Hex.Matrix.findPivot? state.matrix kFin (state.step + 1) with
          | none =>
              rw [Hex.Matrix.pivotLoop_singular_branch_no_pivot fuel state hDone hp0
                (by simpa [kFin] using hfind)]
              exact h
          | some pivot =>
              have hp :=
                pivotLoop_swap_pivot_ne_zero state hDone (by simpa [kFin] using hfind)
              rw [Hex.Matrix.pivotLoop_regular_branch_swap fuel state hDone hp0
                (by simpa [kFin] using hfind) hp]
              apply ih
              show state.step + 1 + 1 ≤ n
              omega
        · rw [Hex.Matrix.pivotLoop_regular_branch_no_swap fuel state hDone hp0]
          apply ih
          show state.step + 1 + 1 ≤ n
          omega
      · rw [Hex.Matrix.pivotLoop_done fuel state hDone]
        exact h

private theorem pivotLoop_step_succ_ge_of_regular
    (fuel : Nat) (state : Hex.Matrix.BareissState n)
    (hregular : (Hex.Matrix.pivotLoop fuel state).singularStep = none)
    (hfuel : n ≤ state.step + fuel + 1) :
    n ≤ (Hex.Matrix.pivotLoop fuel state).step + 1 := by
  induction fuel generalizing state with
  | zero =>
      show n ≤ state.step + 1
      omega
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp0 : state.matrix[state.step][state.step] = 0
        · set kFin : Fin n :=
            ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
          cases hfind :
              Hex.Matrix.findPivot? state.matrix kFin (state.step + 1) with
          | none =>
              have hloop :=
                Hex.Matrix.pivotLoop_singular_branch_no_pivot fuel state hDone hp0
                  (by simpa [kFin] using hfind)
              rw [hloop] at hregular
              simp at hregular
          | some pivot =>
              have hp :=
                pivotLoop_swap_pivot_ne_zero state hDone (by simpa [kFin] using hfind)
              rw [Hex.Matrix.pivotLoop_regular_branch_swap fuel state hDone hp0
                (by simpa [kFin] using hfind) hp]
              apply ih
              · simpa [Hex.Matrix.pivotLoop_regular_branch_swap fuel state hDone hp0
                  (by simpa [kFin] using hfind) hp] using hregular
              · show n ≤ state.step + 1 + fuel + 1
                omega
        · rw [Hex.Matrix.pivotLoop_regular_branch_no_swap fuel state hDone hp0]
          apply ih
          · simpa [Hex.Matrix.pivotLoop_regular_branch_no_swap fuel state hDone hp0]
              using hregular
          · show n ≤ state.step + 1 + fuel + 1
            omega
      · rw [Hex.Matrix.pivotLoop_done fuel state hDone]
        show n ≤ state.step + 1
        omega

private theorem pivotLoop_initial_regular_step_eq_pred
    (M : Hex.Matrix Int (k + 1) (k + 1))
    (hregular :
      (Hex.Matrix.pivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)).singularStep =
        none) :
    (Hex.Matrix.pivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)).step = k := by
  have hle :
      (Hex.Matrix.pivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)).step + 1 ≤
        k + 1 :=
    pivotLoop_step_succ_le (k + 1) (Hex.Matrix.noPivotInitialState M)
      (by show 0 + 1 ≤ k + 1; omega)
  have hge :
      k + 1 ≤
        (Hex.Matrix.pivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)).step + 1 :=
    pivotLoop_step_succ_ge_of_regular (k + 1) (Hex.Matrix.noPivotInitialState M)
      hregular (by show k + 1 ≤ 0 + (k + 1) + 1; omega)
  omega

/-- Mathlib-side correctness theorem for the packaged row-pivoted Bareiss
data: its `.det` field equals Mathlib's determinant of the corresponding
matrix. Proven directly here by combining the row-pivot invariant with the
singular-branch determinant-zero theorem above. -/
theorem bareissData_eq_mathlib_det (M : Hex.Matrix Int n n) :
    (Hex.Matrix.bareissData M).det = Matrix.det (matrixEquiv M) := by
  by_cases hregular : (Hex.Matrix.bareissData M).singularStep = none
  · have hpiv :
        BareissPivotInvariant M
          (Hex.Matrix.pivotLoop n (Hex.Matrix.noPivotInitialState M)) := by
      apply pivotLoop_invariant_of_singularStep_eq_none M n
        (Hex.Matrix.noPivotInitialState M) (bareissPivotInvariant_initial M)
      simpa [Hex.Matrix.bareissData_eq_finish_pivotLoop, Hex.Matrix.finish] using hregular
    rcases hpiv with ⟨logicalSource, hdet, hnopiv⟩
    match n, M, logicalSource, hdet, hnopiv, hregular with
    | 0, M, logicalSource, hdet, hnopiv, hregular =>
        have hdata_sign : (Hex.Matrix.bareissData M).sign =
            bareissStateSign (Hex.Matrix.pivotLoop 0 (Hex.Matrix.noPivotInitialState M)) := by
          simp [Hex.Matrix.bareissData_eq_finish_pivotLoop, Hex.Matrix.finish,
            Hex.Matrix.BareissData.sign, bareissStateSign]
        have hlogical_det : Hex.Matrix.det logicalSource = 1 := by
          change Hex.Matrix.det logicalSource = 1
          exact (det_eq logicalSource).trans (by rw [Matrix.det_isEmpty])
        have hsource_det : Hex.Matrix.det M = (Hex.Matrix.bareissData M).sign := by
          rw [hdet]
          rw [hlogical_det, mul_one]
          exact hdata_sign.symm
        rw [Hex.Matrix.BareissData.det_zero_eq _ hregular]
        rw [← hsource_det]
        exact det_eq M
    | k + 1, M, logicalSource, hdet, hnopiv, hregular =>
        have hloop_regular :
            (Hex.Matrix.pivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)).singularStep =
              none := by
          simpa [Hex.Matrix.bareissData_eq_finish_pivotLoop, Hex.Matrix.finish] using hregular
        have hstep :
            (Hex.Matrix.pivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)).step = k :=
          pivotLoop_initial_regular_step_eq_pred M hloop_regular
        have hentry :
            (Hex.Matrix.pivotLoop (k + 1)
                (Hex.Matrix.noPivotInitialState M)).matrix[
                  (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))][
                  (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))] =
              Hex.Matrix.det logicalSource :=
          trailing_corner_entry_eq_det k logicalSource
            (Hex.Matrix.pivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M))
            hnopiv hstep
        have hsign :
            (Hex.Matrix.bareissData M).sign =
              bareissStateSign
                (Hex.Matrix.pivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)) := by
          simp [Hex.Matrix.bareissData_eq_finish_pivotLoop, Hex.Matrix.finish,
            Hex.Matrix.BareissData.sign, bareissStateSign]
        have hdata_entry :
            (Hex.Matrix.bareissData M).matrix[
                  (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))][
                  (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))] =
              Hex.Matrix.det logicalSource := by
          simpa [Hex.Matrix.bareissData_eq_finish_pivotLoop, Hex.Matrix.finish] using hentry
        rw [Hex.Matrix.BareissData.det_succ_eq _ hregular]
        rw [hdata_entry, hsign]
        rw [← hdet]
        exact det_eq M
  · have hdata_zero : (Hex.Matrix.bareissData M).det = 0 := by
      unfold Hex.Matrix.BareissData.det
      split
      · rfl
      · contradiction
    have hhex_zero : Hex.Matrix.det M = 0 :=
      bareissData_singularStep_ne_none_det_eq_zero M hregular
    rw [hdata_zero, ← hhex_zero]
    exact det_eq M

/-- Row-pivoted Bareiss determinant soundness, exposed against Mathlib's
determinant for downstream Mathlib-side callers. -/
theorem bareiss_eq_mathlib_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M) := by
  rw [Hex.Matrix.bareiss_eq_bareissData_det M]
  exact bareissData_eq_mathlib_det M

/-- Restatement of `BareissNoPivotInvariant.trailing_eq` packaged so the step
field is given by an external equation rather than appearing inside dependent
proof terms. Lets callers consume `trailing_eq` at an arbitrary numeric step
value `s` known to equal `state.step` without manually transporting the
inequality proofs. -/
private theorem trailing_eq_at_step
    {M : Hex.Matrix Int n n} {state : Hex.Matrix.BareissState n}
    (hinv : BareissNoPivotInvariant M state)
    (s : Nat) (hs : s < n) (hstep : s = state.step)
    (a c : Fin n) (hsa : s ≤ a.val) (hsc : s ≤ c.val) :
    state.matrix[a][c] =
      Hex.Matrix.det (Hex.Matrix.borderedMinor M s hs a c) := by
  subst hstep
  exact hinv.trailing_eq hs a c hsa hsc

/-- Off-step generalisation of the no-pivot Bareiss bordered-minor
identification. After `k + 1` no-pivot Bareiss iterations on `M`, every entry
at `(a, c)` with `k + 1 ≤ a.val, c.val` equals the determinant of the
`(k + 2) × (k + 2)` bordered minor of `M` with trailing row `a` and column
`c`, provided the partial loop records no singular step.

Composes `noPivotLoop_invariant_of_singularStep_eq_none` (the invariant
propagates through a non-singular partial pass), `BareissNoPivotInvariant`
(the trailing-block entries equal bordered-minor determinants), and
`noPivotLoop_step_eq_add_of_singularStep_none` (the partial pass advances
`step` by exactly the fuel consumed). -/
theorem noPivotLoop_full_eq_borderedMinor_det
    (M : Hex.Matrix Int n n) (k : Nat) (hk : k + 1 < n)
    (a c : Fin n) (hak : k + 1 ≤ a.val) (hck : k + 1 ≤ c.val)
    (h_no_sing :
      (Hex.Matrix.noPivotLoop (k + 1)
          (Hex.Matrix.noPivotInitialState M)).singularStep = none) :
    (Hex.Matrix.noPivotLoop (k + 1)
        (Hex.Matrix.noPivotInitialState M)).matrix[a][c] =
      Hex.Matrix.det (Hex.Matrix.borderedMinor M (k + 1) hk a c) := by
  have hinv : BareissNoPivotInvariant M
      (Hex.Matrix.noPivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)) :=
    noPivotLoop_invariant_of_singularStep_eq_none M (k + 1)
      (Hex.Matrix.noPivotInitialState M) (bareissNoPivotInvariant_initial M)
      h_no_sing
  have hstep_eq :
      k + 1 =
        (Hex.Matrix.noPivotLoop (k + 1) (Hex.Matrix.noPivotInitialState M)).step := by
    have h_room : (Hex.Matrix.noPivotInitialState M).step + (k + 1) + 1 ≤ n := by
      change 0 + (k + 1) + 1 ≤ n
      omega
    have h := Hex.Matrix.noPivotLoop_step_eq_add_of_singularStep_none (k + 1)
      (Hex.Matrix.noPivotInitialState M) rfl h_room h_no_sing
    rw [h]
    show k + 1 = 0 + (k + 1)
    omega
  exact trailing_eq_at_step hinv (k + 1) hk hstep_eq a c hak hck

end HexMatrixMathlib
