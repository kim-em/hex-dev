import HexMatrixMathlib.Determinant

/-!
No-pivot Bareiss loop invariant for `hex-matrix-mathlib`.

This module proves the recursive bordered-minor invariant of the no-pivot
Bareiss recurrence: after `k` regular Bareiss steps, the trailing entries of
the working matrix agree with the corresponding bordered-minor determinants of
the source matrix, and the previous pivot agrees with the determinant of the
leading prefix of size `k`. As an immediate corollary, when all leading-prefix
determinants are nonzero (`NonzeroBareissPivots`), the loop never takes the
singular branch.

The invariant proof composes the bordered-minor `stepMatrix` update bridge
(`Hex.Matrix.stepMatrix_borderedMinor_update`) with the bordered-minor
specialization of Desnanot-Jacobi (`desnanot_jacobi_borderedMinor` in the
parent module) and the exact-division bridge
(`bareissExactDiv_borderedMinor_of_mul_eq`).
-/

namespace HexMatrixMathlib

universe u

variable {n : Nat}

private theorem borderedMinor_corner_eq_leadingPrefix {R : Type u}
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
      -- Bridge: BareissData.det = sign * (k, k) entry = 1 * det M = det M.
      show (Hex.Matrix.bareissNoPivotData M).det = Matrix.det (matrixEquiv M)
      rw [Hex.Matrix.BareissData.det_succ_eq _ hdata_sing, hdata_sign, one_mul,
        show (Hex.Matrix.bareissNoPivotData M).matrix[(⟨k, hk⟩ : Fin (k + 1))][
            (⟨k, hk⟩ : Fin (k + 1))] = Hex.Matrix.det M from hentry]
      exact det_eq M

end HexMatrixMathlib
