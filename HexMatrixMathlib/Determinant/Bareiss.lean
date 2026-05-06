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

end HexMatrixMathlib
