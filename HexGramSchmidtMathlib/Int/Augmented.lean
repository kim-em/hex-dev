module

public import HexGramSchmidtMathlib.Int.GramDet
import all HexGramSchmidtMathlib.Int.GramDet

public section

namespace Hex
namespace GramSchmidt
namespace Int
/-- Cramer's-rule identity for the scaled Gram-Schmidt coefficient determinant:
the Leibniz determinant of `scaledCoeffMatrix` equals
`gramDet b (j + 1) * coeffs[i,j]` after casting to `Rat`. -/
private theorem scaledCoeffMatrix_det_eq_gramDet_mul_coeffs
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    ((Matrix.det
        (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj) :
          Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ := by
  have hjlt : j < n := Nat.lt_trans hj hi
  have hjsuc : j + 1 ≤ n := Nat.succ_le_of_lt hjlt
  -- Cast LHS via det_intCast.
  rw [det_intCast]
  -- Step 1: express `castIntDetMatrix M` as a `colReplace` of `castIntDetMatrix G`.
  have hM_colReplace :
      castIntDetMatrix
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj) =
        Matrix.setCol
          (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
          (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
          (fun p : Fin (j + 1) =>
            Vector.dotProduct
              (castIntRow b ⟨p.val, Nat.lt_of_lt_of_le p.isLt hjsuc⟩)
              (castIntRow b ⟨i, hi⟩)) := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    let pp : Fin (j + 1) := ⟨r, hr⟩
    let cc : Fin (j + 1) := ⟨c, hc⟩
    change
      (castIntDetMatrix
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj))[pp][cc] =
        (Matrix.setCol _ _ _)[pp][cc]
    rw [Matrix.setCol_getElem, castIntDetMatrix_get]
    by_cases hc_eq : cc = (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
    · rw [if_pos hc_eq]
      have hc_val : cc.val = j := congrArg Fin.val hc_eq
      have hsc :
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj)[pp][cc] =
            Vector.dotProduct
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨i, hi⟩) := by
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn,
          GramSchmidt.liftFinLE, hc_val]
      rw [hsc, ← dot_castIntRow_eq_cast_dot]
    · rw [if_neg hc_eq, castIntDetMatrix_get]
      have hc_ne : cc.val ≠ j := fun h => hc_eq (Fin.ext h)
      have hsc :
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj)[pp][cc] =
            Vector.dotProduct
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt hjsuc⟩) := by
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn,
          GramSchmidt.liftFinLE, hc_ne]
      have hG :
          (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc)[pp][cc] =
            Vector.dotProduct
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt hjsuc⟩) := by
        simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn,
          GramSchmidt.liftFinLE]
      rw [hsc, hG]
  rw [hM_colReplace]
  -- Step 2: rewrite the replacement column as `castG * originalProjectionCoords`.
  have hcol_lin_comb :
      (fun p : Fin (j + 1) =>
        Vector.dotProduct
          (castIntRow b ⟨p.val, Nat.lt_of_lt_of_le p.isLt hjsuc⟩)
          (castIntRow b ⟨i, hi⟩)) =
      (fun p : Fin (j + 1) =>
        (List.finRange (j + 1)).foldl
          (fun (acc : Rat) (q : Fin (j + 1)) =>
            acc + (originalProjectionCoords b i j hi hjlt)[q] *
              (castIntDetMatrix
                (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[p][q]) 0) := by
    funext p
    -- dot castIntRow b p castIntRow b i = dot castIntRow b p basisPrefixProjection
    rw [dot_castIntRow_castIntRow_eq b i j p.val hi hj
      (Nat.le_of_lt_succ p.isLt) (Nat.lt_of_lt_of_le p.isLt hjsuc)]
    -- = (castG * originalProjectionCoords)[p]
    rw [← scaledCoeffMatrix_replacementColumn_solve b i j hi hj p]
    -- Now: (castG * origProjCoords)[p] = foldl over Fin (j+1) of castG[p][q] * origProjCoords[q].
    -- Reorder to origProjCoords[q] * castG[p][q] using Rat.mul_comm.
    change
      (Matrix.mulVec
          (castIntDetMatrix
            (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
          (originalProjectionCoords b i j hi hjlt))[p] = _
    unfold Matrix.mulVec Matrix.row
    have hleft :
        (Vector.ofFn fun i' : Fin (j + 1) =>
            Vector.dotProduct
              (castIntDetMatrix
                (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[i']
              (originalProjectionCoords b i j hi hjlt))[p] =
          Vector.dotProduct
            (castIntDetMatrix
              (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[p]
            (originalProjectionCoords b i j hi hjlt) := by
      simp [Vector.getElem_ofFn]
    rw [hleft]
    unfold Vector.dotProduct
    apply foldl_sum_congr_simple
    intro q _hq
    grind
  rw [hcol_lin_comb]
  -- Step 3: apply det_setCol_sum_finRange.
  rw [Matrix.det_setCol_sum_finRange]
  -- Step 4: isolate the q = ⟨j, _⟩ term.
  rw [foldl_finRange_succ_isolate_last j _ ?_]
  · -- Last term: origProjCoords[⟨j, _⟩] * det castG.
    have hlast_self :
        Matrix.setCol
            (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
            (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
            (fun p : Fin (j + 1) =>
              (castIntDetMatrix
                (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[p][Fin.last j]) =
          castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc) :=
      Matrix.setCol_self _ _
    rw [hlast_self]
    -- det castG = (gramDet (j+1) : Rat).
    have hdetG :
        Matrix.det
            (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc)) =
          (gramDet b (j + 1) hjsuc : Rat) := by
      rw [← det_intCast]
      have hdet_int :
          Matrix.det (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc) =
            Int.ofNat (gramDet b (j + 1) hjsuc) := by
        rw [gramDet, HexMatrixMathlib.bareiss_eq_mathlib_det, ← HexMatrixMathlib.det_eq]
        exact (Int.toNat_of_nonneg
          (leadingGramMatrixInt_det_nonneg b (j + 1) hjsuc)).symm
      rw [hdet_int]
      rfl
    rw [hdetG]
    -- Cancellation: origProjCoords[Fin.last j] * gramDet = gramDet * coeffs[i][j].
    have hcancel_normSq :
        Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            (originalProjectionCoords b i j hi hjlt)[Fin.last j] =
          Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ := by
      have hH2 := dot_basis_basisPrefixProjection_eq_coeff_mul_normSq b i j hi hj
      have hH3 := dot_basis_basisPrefixProjection_eq_origProjCoords_mul_normSq b i j hi hj
      have heq := hH3.symm.trans hH2
      -- heq : (originalProjectionCoords ...)[Fin.last j] * normSq = entry coeffs ... * normSq
      grind
    have hgd_succ := gramDet_succ_rat b j hjsuc
    -- Combine: gramDet(j+1) * coeffs[i][j] = gnp(j) * normSq * coeffs[i][j] = gnp(j) * normSq * origProjCoords = gramDet(j+1) * origProjCoords.
    rw [hgd_succ]
    have hgnp_ne_or_zero :
        gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            (originalProjectionCoords b i j hi hjlt)[Fin.last j] =
          gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ := by
      have h1 :
          gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            (originalProjectionCoords b i j hi hjlt)[Fin.last j] =
            gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              (Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
                (originalProjectionCoords b i j hi hjlt)[Fin.last j]) := by
        grind
      have h2 :
          gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ =
            gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              (Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
                GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩) := by
        grind
      rw [h1, h2, hcancel_normSq]
    rw [Rat.mul_comm (originalProjectionCoords b i j hi hjlt)[Fin.last j] _]
    exact hgnp_ne_or_zero
  · -- For q < j: det (colReplace castG ⟨j, _⟩ (col q of castG)) = 0 (existing col).
    intro q hqval
    have hq_ne :
        q ≠ (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) := by
      intro h
      exact Nat.ne_of_lt hqval (congrArg Fin.val h)
    rw [Matrix.det_setCol_existing_col_eq_zero _ _ _ hq_ne]
    grind

/-- Substitution helper for the diagonal `(i, i)` matrix entry under a Fin
equality. Folded out of `subst`/`rfl` so callers can rewrite the index without
dragging the dependent proof component through the motive. -/
private theorem matrix_diag_at_fin_eq {n : Nat} (M : Matrix Int n n)
    {i j : Fin n} (h : i = j) :
    M[i][i] = M[j][j] := by
  subst h; rfl

/-- If the `s`-fueled no-pivot Bareiss prefix already recorded a singular step,
that step persists into any longer pass. The longer pass's recorded singular
index therefore matches the earlier one. -/
private theorem noPivotLoop_extends_singularStep
    {n : Nat} (state : Matrix.BareissState n) (a b : Nat) (k : Fin n)
    (h_sing_a : (Matrix.noPivotLoop a state).singularStep = some k.val)
    (h_step_a : (Matrix.noPivotLoop a state).step = k.val)
    (h_zero_a :
      (Matrix.noPivotLoop a state).matrix[k][k] = 0)
    (hk : k.val + 1 < n) :
    Matrix.noPivotLoop (a + b) state = Matrix.noPivotLoop a state := by
  rw [Matrix.noPivotLoop_add a b state]
  set S := Matrix.noPivotLoop a state with hS_def
  have hDone : S.step + 1 < n := by rw [h_step_a]; exact hk
  have hp_zero :
      S.matrix[(⟨S.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨S.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
    have h_fin :
        (⟨S.step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step_a
    exact (matrix_diag_at_fin_eq S.matrix h_fin).trans h_zero_a
  have h_sing_step : S.singularStep = some S.step := by
    rw [h_sing_a, h_step_a]
  exact Matrix.noPivotLoop_id_at_singular_fixedpoint (n := n) b S hDone hp_zero h_sing_step

/-! ### Augmented Gram matrix for determinantal identification of
`bareissGramCanonicalCoeff`

The canonical row-coefficient vector of the initial no-pivot Bareiss trajectory
on `gramMatrix b` is identified with a trailing-column entry of the no-pivot
Bareiss pass on an `(n + 1) × (n + 1)` augmented matrix.  The upper `n × n`
block of the augmented matrix is `gramMatrix b`; the trailing column at upper
rows carries the standard basis vector `δ_a` at the chosen coefficient slot
`a`; the trailing row is structurally zero.

Because the trailing row is zero and the no-pivot Bareiss update at slot
`(i, j)` with `i, j < n` only consults the upper block, the upper-block
trajectory on the augmented matrix exactly mirrors the trajectory on
`gramMatrix b`.  Because the trailing-column update at row `i < n` and step
`k < i.val` mirrors the canonical-coefficient Bareiss step, the trailing
column at upper rows tracks `bareissGramCanonicalCoeff b fuel i` at slot `a`.
-/

/-- Augmented `(n + 1) × (n + 1)` matrix used to identify
`bareissGramCanonicalCoeff b fuel i [a]` with a trailing-column entry of the
no-pivot Bareiss pass.  Upper block is `gramMatrix b`; trailing column at
upper rows is the standard basis vector `δ_a`; trailing row is zero. -/
@[expose]
def augmentedGram (b : Matrix Int n m) (a : Fin n) :
    Hex.Matrix Int (n + 1) (n + 1) :=
  Matrix.ofFn fun i j : Fin (n + 1) =>
    if hi : i.val < n then
      if hj : j.val < n then
        (Matrix.gramMatrix b)[(⟨i.val, hi⟩ : Fin n)][(⟨j.val, hj⟩ : Fin n)]
      else
        if i.val = a.val then (1 : Int) else 0
    else
      0

/-- Upper-block entry of `augmentedGram b a` agrees with `gramMatrix b`. -/
theorem augmentedGram_upper_block
    (b : Matrix Int n m) (a : Fin n) (i j : Fin n) :
    (augmentedGram b a)[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
        (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1))] =
      (Matrix.gramMatrix b)[i][j] := by
  unfold augmentedGram
  rw [Matrix.getElem_ofFn]
  simp [i.isLt, j.isLt]

/-- Trailing-column entry of `augmentedGram b a` at an upper row `i : Fin n`
is `1` when `i = a` and `0` otherwise. -/
theorem augmentedGram_trailing_col
    (b : Matrix Int n m) (a : Fin n) (i : Fin n) :
    (augmentedGram b a)[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
        Fin.last n] =
      (if i = a then (1 : Int) else 0) := by
  unfold augmentedGram
  rw [Matrix.getElem_ofFn]
  have h_iff : (i.val = a.val) ↔ (i = a) := ⟨Fin.ext, fun h => by rw [h]⟩
  simp [i.isLt, h_iff]

/-- Trailing-row entries of `augmentedGram b a` are all zero. -/
theorem augmentedGram_trailing_row
    (b : Matrix Int n m) (a : Fin n) (j : Fin (n + 1)) :
    (augmentedGram b a)[Fin.last n][j] = 0 := by
  unfold augmentedGram
  rw [Matrix.getElem_ofFn]
  have hn : ¬ (Fin.last n).val < n := by show ¬ n < n; omega
  rw [dif_neg hn]

/-- Substitution helper: matrix entries agree when Fin indices are equal.
Used to reindex matrix-entry equalities across propositionally-equal Fin
indices without provoking motive issues from `rw`. -/
private theorem matrix_entry_eq_of_eq {n m : Nat} (M : Hex.Matrix Int n m)
    {i i' : Fin n} {j j' : Fin m} (hi : i = i') (hj : j = j') :
    M[i][j] = M[i'][j'] := by
  subst hi; subst hj; rfl

/-- Local copy of `HexMatrixMathlib.trailing_eq_at_step` (private there):
re-state `BareissNoPivotInvariant.trailing_eq` with the step value supplied
externally so the dependent bordered-minor type matches the desired
`s = state.step` substitution cleanly. -/
theorem trailing_eq_at_step_local
    {n' : Nat} {M : Hex.Matrix Int n' n'} {state : Matrix.BareissState n'}
    (hinv : HexMatrixMathlib.BareissNoPivotInvariant M state)
    (s : Nat) (hs : s < n') (hstep : s = state.step)
    (a c : Fin n') (hsa : s ≤ a.val) (hsc : s ≤ c.val) :
    state.matrix[a][c] =
      Hex.Matrix.det (Hex.Matrix.borderedMinor M s hs a c) := by
  subst hstep
  exact hinv.trailing_eq hs a c hsa hsc

/-- Auxiliary monotonicity: if a no-pivot Bareiss state reaches
`fuel + 1` iterations from `noPivotInitialState M` without recording a singular
step, then the prefix at `fuel` iterations is also non-singular.  Singular
states are fixed points of further iteration, so a non-singular outcome at
`fuel + 1` forces a non-singular prefix. -/
private theorem noPivotLoop_singularStep_none_of_succ
    {n : Nat} (M : Matrix Int n n) (fuel : Nat)
    (h_no_sing :
      (Matrix.noPivotLoop (fuel + 1)
          (Matrix.noPivotInitialState M)).singularStep = none) :
    (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).singularStep = none := by
  set init := Matrix.noPivotInitialState M with hinit
  have h_init : init.singularStep = none := rfl
  rcases noPivotLoop_singular_inv (n := n) fuel init h_init with hnone | ⟨k, hsing, hstep, hzero, hklt⟩
  · exact hnone
  · -- Singular at fuel persists to fuel + 1, contradicting h_no_sing.
    exfalso
    have hpersist : Matrix.noPivotLoop (fuel + 1) init = Matrix.noPivotLoop fuel init :=
      noPivotLoop_extends_singularStep init fuel 1 k hsing hstep hzero hklt
    rw [hpersist, hsing] at h_no_sing
    nomatch h_no_sing

/-- Combined invariant relating the no-pivot Bareiss trajectory on the
augmented matrix to the trajectory on `gramMatrix b`.  Under `fuel + 1 ≤ n`
and a non-singular prefix on the Gram side, the augmented loop tracks the
Gram loop on (i) `step`, (ii) `prevPivot`, (iii) the upper `n × n` block,
and (iv) carries the canonical row coefficient in its trailing column. -/
theorem noPivotLoop_augmentedGram_invariant
    (b : Matrix Int n m) (a : Fin n) (fuel : Nat) :
    fuel + 1 ≤ n →
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none →
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (augmentedGram b a))).step =
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ∧
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (augmentedGram b a))).prevPivot =
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).prevPivot ∧
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (augmentedGram b a))).singularStep = none ∧
      (∀ i j : Fin n,
        (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (augmentedGram b a))).matrix[
          (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
          (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1))] =
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j]) ∧
      (∀ i : Fin n,
        (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (augmentedGram b a))).matrix[
          (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][Fin.last n] =
          (bareissGramCanonicalCoeff b fuel i)[a]) := by
  induction fuel with
  | zero =>
      intro _ _
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · intro i j
        change (augmentedGram b a)[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
            (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1))] =
          (Matrix.gramMatrix b)[i][j]
        exact augmentedGram_upper_block b a i j
      · intro i
        change (augmentedGram b a)[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
            Fin.last n] =
          (Vector.ofFn fun k : Fin n => if i = k then (1 : Int) else 0)[a]
        rw [augmentedGram_trailing_col]
        simp
  | succ fuel ih =>
      intro hfuel h_no_sing
      -- Pull the previous-fuel invariant out of the inductive hypothesis.
      have hfuel_prev : fuel + 1 ≤ n := by omega
      have h_no_sing_prev :
          (Matrix.noPivotLoop fuel
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none :=
        noPivotLoop_singularStep_none_of_succ (Matrix.gramMatrix b) fuel h_no_sing
      obtain ⟨h_step_prev, h_prev_prev, h_sing_aug_prev, h_block_prev, h_trail_prev⟩ :=
        ih hfuel_prev h_no_sing_prev
      -- Set up shorthand for the previous-fuel states.
      set stateG := Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) with hstateG
      set stateA := Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (augmentedGram b a)) with hstateA
      -- Gram side has not finished and pivot is nonzero (else singular at fuel + 1).
      have h_step_G_fuel : stateG.step = fuel := by
        have h := Matrix.noPivotLoop_step_eq_add_of_singularStep_none fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl (by
            show 0 + fuel + 1 ≤ n; omega) h_no_sing_prev
        simpa [Matrix.noPivotInitialState] using h
      have hDone_G : stateG.step + 1 < n := by rw [h_step_G_fuel]; omega
      have hk_G_lt : stateG.step < n := Nat.lt_of_succ_lt hDone_G
      -- Pivot non-zero on the Gram side.
      have h_pivot_G_ne :
          stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
              (⟨stateG.step, hk_G_lt⟩ : Fin n)] ≠ 0 := by
        intro hzero
        -- Singular branch at fuel + 1 would record a singular step,
        -- contradicting `h_no_sing`.
        have h_sing_branch : Matrix.noPivotLoop 1 stateG
            = { stateG with singularStep := some stateG.step } :=
          Matrix.noPivotLoop_singular_branch 0 stateG hDone_G hzero
        have h_succ_eq :
            Matrix.noPivotLoop (fuel + 1)
              (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
            Matrix.noPivotLoop 1 stateG := by
          rw [Matrix.noPivotLoop_add fuel 1]
        rw [h_succ_eq, h_sing_branch] at h_no_sing
        simp at h_no_sing
      -- Augmented side: step matches, so it has not finished either.
      have h_step_A_fuel : stateA.step = fuel := h_step_prev.trans h_step_G_fuel
      have hDone_A : stateA.step + 1 < n + 1 := by rw [h_step_A_fuel]; omega
      have hk_A_lt : stateA.step < n + 1 := Nat.lt_of_succ_lt hDone_A
      -- Pivot at the lifted index on the augmented side equals the Gram pivot.
      have h_pivot_A_eq :
          stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
              (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))] =
            stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
              (⟨stateG.step, hk_G_lt⟩ : Fin n)] := by
        have h_idx :
            (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1)) =
              (⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                  Fin (n + 1)) := Fin.ext h_step_prev
        calc stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
              (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))]
            = stateA.matrix[(⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                  Fin (n + 1))][(⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                  Fin (n + 1))] := matrix_entry_eq_of_eq _ h_idx h_idx
          _ = stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
                (⟨stateG.step, hk_G_lt⟩ : Fin n)] :=
              h_block_prev ⟨stateG.step, hk_G_lt⟩ ⟨stateG.step, hk_G_lt⟩
      have h_pivot_A_ne :
          stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
              (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))] ≠ 0 := by
        rw [h_pivot_A_eq]; exact h_pivot_G_ne
      -- Peel off the last iteration on both sides.
      have h_G_succ :
          Matrix.noPivotLoop (fuel + 1)
              (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
            Matrix.noPivotLoop 0
              { step := stateG.step + 1
                matrix := Matrix.stepMatrix stateG.matrix stateG.step
                  stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
                    (⟨stateG.step, hk_G_lt⟩ : Fin n)] stateG.prevPivot
                prevPivot := stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
                  (⟨stateG.step, hk_G_lt⟩ : Fin n)]
                rowSwaps := stateG.rowSwaps
                singularStep := none } := by
        rw [Matrix.noPivotLoop_add fuel 1]
        exact Matrix.noPivotLoop_regular_branch 0 stateG hDone_G h_pivot_G_ne
      have h_A_succ :
          Matrix.noPivotLoop (fuel + 1)
              (Matrix.noPivotInitialState (augmentedGram b a)) =
            Matrix.noPivotLoop 0
              { step := stateA.step + 1
                matrix := Matrix.stepMatrix stateA.matrix stateA.step
                  stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
                    (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))] stateA.prevPivot
                prevPivot := stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
                  (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))]
                rowSwaps := stateA.rowSwaps
                singularStep := none } := by
        rw [Matrix.noPivotLoop_add fuel 1]
        exact Matrix.noPivotLoop_regular_branch 0 stateA hDone_A h_pivot_A_ne
      -- Both peeled states are zero-fuel, so the loop returns them unchanged.
      rw [h_G_succ, h_A_succ, Matrix.noPivotLoop_zero_fuel, Matrix.noPivotLoop_zero_fuel]
      -- Now project each component of the invariant.
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- Step equality.
        show stateA.step + 1 = stateG.step + 1
        exact congrArg (· + 1) h_step_prev
      · -- prevPivot equality.
        show stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
              (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))] =
            stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
              (⟨stateG.step, hk_G_lt⟩ : Fin n)]
        exact h_pivot_A_eq
      · -- singularStep = none.
        rfl
      · -- Upper-block invariant.
        intro i j
        -- Set up the lifted indices and `k` index used in `stepMatrix`.
        set iA : Fin (n + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with hiA
        set jA : Fin (n + 1) := ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ with hjA
        -- Case-split on whether step `fuel = stateG.step` updates this entry.
        by_cases hi_lt : stateG.step < i.val
        · by_cases hj_lt : stateG.step < j.val
          · -- Trailing block: Bareiss update fires on both sides.
            have hi_lt_A : stateA.step < iA.val := by
              show stateA.step < i.val
              rw [h_step_prev]; exact hi_lt
            have hj_lt_A : stateA.step < jA.val := by
              show stateA.step < j.val
              rw [h_step_prev]; exact hj_lt
            rw [Matrix.stepMatrix_update_eq stateA.matrix stateA.step _ _ iA jA
              hi_lt_A hj_lt_A]
            rw [Matrix.stepMatrix_update_eq stateG.matrix stateG.step _ _ i j
              hi_lt hj_lt]
            dsimp only []
            -- Rewrite the four matrix entries on the LHS using the block IH.
            have h_ij_A : stateA.matrix[iA][jA] = stateG.matrix[i][j] :=
              h_block_prev i j
            -- (colK : Fin (n+1)) for aug, (colK_G : Fin n) for gram.
            -- These have step.val = stateG.step (by h_step_prev) and we use
            -- the IH at row=i, col=⟨stateG.step, hk_G_lt⟩, and so on.
            have h_step_lift_eq :
                (⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ : Fin (n + 1)) =
                  (⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                    Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                      Fin (n + 1)) := by
              apply Fin.ext
              show stateA.step = stateG.step
              exact h_step_prev
            have h_iL_A :
                stateA.matrix[iA][(⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ :
                    Fin (n + 1))] =
                  stateG.matrix[i][(⟨stateG.step, hk_G_lt⟩ : Fin n)] := by
              calc stateA.matrix[iA][(⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ :
                      Fin (n + 1))]
                  = stateA.matrix[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
                      (⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                        Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                          Fin (n + 1))] := matrix_entry_eq_of_eq _ rfl h_step_lift_eq
                _ = stateG.matrix[i][(⟨stateG.step, hk_G_lt⟩ : Fin n)] :=
                    h_block_prev i ⟨stateG.step, hk_G_lt⟩
            have h_kJ_A :
                stateA.matrix[(⟨stateA.step, Nat.lt_trans hj_lt_A jA.isLt⟩ :
                    Fin (n + 1))][jA] =
                  stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][j] := by
              calc stateA.matrix[(⟨stateA.step, Nat.lt_trans hj_lt_A jA.isLt⟩ :
                      Fin (n + 1))][jA]
                  = stateA.matrix[(⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                      Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                        Fin (n + 1))][(⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1))] :=
                    matrix_entry_eq_of_eq _ h_step_lift_eq rfl
                _ = stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][j] :=
                    h_block_prev ⟨stateG.step, hk_G_lt⟩ j
            rw [h_ij_A, h_iL_A, h_kJ_A, h_pivot_A_eq, h_prev_prev]
          · -- Trailing row, but column ≤ step. Then both sides preserve the entry.
            -- On aug, the `stepMatrix` update condition `k < i ∧ k < j` fails because `j ≤ k`.
            -- Could be `j.val < k` (no update) or `j.val = k` (clear pivot col below;
            -- value 0, which matches Gram side since both are 0 below pivot).
            by_cases hj_eq : j.val = stateG.step
            · -- Clear pivot column below: both sides set to 0.
              have hj_eq_A : jA.val = stateA.step := by
                show j.val = stateA.step
                rw [h_step_prev]; exact hj_eq
              have hi_lt_A : stateA.step < iA.val := by
                show stateA.step < i.val
                rw [h_step_prev]; exact hi_lt
              rw [Matrix.stepMatrix_pivot_col_below stateA.matrix stateA.step _ _ iA jA
                hi_lt_A hj_eq_A]
              rw [Matrix.stepMatrix_pivot_col_below stateG.matrix stateG.step _ _ i j
                hi_lt hj_eq]
            · -- Column strictly below pivot: both sides preserve their value.
              have hj_lt_step : j.val < stateG.step := by omega
              have hj_lt_step_A : jA.val < stateA.step := by
                show j.val < stateA.step
                rw [h_step_prev]; exact hj_lt_step
              have h_not_update_A : ¬ (stateA.step < iA.val ∧ stateA.step < jA.val) := by
                intro ⟨_, h⟩; omega
              have h_not_col_A : ¬ (stateA.step < iA.val ∧ jA.val = stateA.step) := by
                intro ⟨_, h⟩; omega
              have h_not_update_G : ¬ (stateG.step < i.val ∧ stateG.step < j.val) := by
                intro ⟨_, h⟩; omega
              have h_not_col_G : ¬ (stateG.step < i.val ∧ j.val = stateG.step) := by
                intro ⟨_, h⟩; omega
              rw [Matrix.stepMatrix_eq_of_not_update stateA.matrix stateA.step _ _ iA jA
                h_not_update_A h_not_col_A]
              rw [Matrix.stepMatrix_eq_of_not_update stateG.matrix stateG.step _ _ i j
                h_not_update_G h_not_col_G]
              exact h_block_prev i j
        · -- Row ≤ step: no update on either side.
          have hi_le_step : i.val ≤ stateG.step := Nat.le_of_not_lt hi_lt
          have hi_le_step_A : iA.val ≤ stateA.step := by
            show i.val ≤ stateA.step
            rw [h_step_prev]; exact hi_le_step
          have h_not_update_A : ¬ (stateA.step < iA.val ∧ stateA.step < jA.val) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step_A h
          have h_not_col_A : ¬ (stateA.step < iA.val ∧ jA.val = stateA.step) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step_A h
          have h_not_update_G : ¬ (stateG.step < i.val ∧ stateG.step < j.val) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step h
          have h_not_col_G : ¬ (stateG.step < i.val ∧ j.val = stateG.step) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step h
          rw [Matrix.stepMatrix_eq_of_not_update stateA.matrix stateA.step _ _ iA jA
            h_not_update_A h_not_col_A]
          rw [Matrix.stepMatrix_eq_of_not_update stateG.matrix stateG.step _ _ i j
            h_not_update_G h_not_col_G]
          exact h_block_prev i j
      · -- Trailing-column invariant.
        intro i
        set iA : Fin (n + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with hiA
        set L : Fin (n + 1) := Fin.last n with hL
        have hL_lt : stateA.step < L.val := by
          show stateA.step < n
          rw [h_step_prev]; exact hk_G_lt
        by_cases hi_lt : stateG.step < i.val
        · -- Active row: both sides apply the Bareiss update.
          have hi_lt_A : stateA.step < iA.val := by
            show stateA.step < i.val
            rw [h_step_prev]; exact hi_lt
          rw [Matrix.stepMatrix_update_eq stateA.matrix stateA.step _ _ iA L
            hi_lt_A hL_lt]
          dsimp only []
          -- Match the four entries on the LHS via the IH:
          -- - the trailing-column entry at row i: by trailing IH.
          -- - the entry (i, step↑): by block IH after reindexing.
          -- - the entry (step↑, last n): by trailing IH at row k.
          -- The pivot at (step↑, step↑) is `h_pivot_A_eq`.
          have h_iL_A : stateA.matrix[iA][L] = (bareissGramCanonicalCoeff b fuel i)[a] :=
            h_trail_prev i
          have h_step_lift_eq :
              (⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ : Fin (n + 1)) =
                (⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                  Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                    Fin (n + 1)) := by
            apply Fin.ext
            show stateA.step = stateG.step
            exact h_step_prev
          have h_iK_A :
              stateA.matrix[iA][(⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ :
                  Fin (n + 1))] =
                stateG.matrix[i][(⟨stateG.step, hk_G_lt⟩ : Fin n)] := by
            calc stateA.matrix[iA][(⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ :
                    Fin (n + 1))]
                = stateA.matrix[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
                    (⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                      Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                        Fin (n + 1))] := matrix_entry_eq_of_eq _ rfl h_step_lift_eq
              _ = stateG.matrix[i][(⟨stateG.step, hk_G_lt⟩ : Fin n)] :=
                  h_block_prev i ⟨stateG.step, hk_G_lt⟩
          have h_kL_A :
              stateA.matrix[(⟨stateA.step, Nat.lt_trans hL_lt L.isLt⟩ : Fin (n + 1))][L] =
                (bareissGramCanonicalCoeff b fuel ⟨stateG.step, hk_G_lt⟩)[a] := by
            calc stateA.matrix[(⟨stateA.step, Nat.lt_trans hL_lt L.isLt⟩ :
                    Fin (n + 1))][L]
                = stateA.matrix[(⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                    Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                      Fin (n + 1))][Fin.last n] :=
                  matrix_entry_eq_of_eq _ h_step_lift_eq rfl
              _ = (bareissGramCanonicalCoeff b fuel
                    (⟨stateG.step, hk_G_lt⟩ : Fin n))[a] :=
                  h_trail_prev ⟨stateG.step, hk_G_lt⟩
          rw [h_iL_A, h_iK_A, h_kL_A, h_pivot_A_eq, h_prev_prev]
          -- The RHS is the canonical-coefficient recursion at active row.
          have hp_canon :
              (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
                (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
                (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0 := by
            show stateG.matrix[stateG.step][stateG.step] ≠ 0
            -- Lower the Fin index proof.
            intro hzero
            apply h_pivot_G_ne
            exact hzero
          have hnext_canon :
              (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n := by
            show stateG.step + 1 < n; exact hDone_G
          have hi_lt_canon :
              (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val := by
            show stateG.step + 1 ≤ i.val; exact hi_lt
          rw [bareissGramCanonicalCoeff_succ_regular b fuel i hnext_canon hp_canon hi_lt_canon]
          conv_rhs => rw [show ∀ f : Fin n → Int, (Vector.ofFn f)[a] = f a from
            fun f => by simp]
        · -- Processed row (i.val ≤ step): both sides preserve the value.
          have hi_le_step : i.val ≤ stateG.step := Nat.le_of_not_lt hi_lt
          have hi_le_step_A : iA.val ≤ stateA.step := by
            show i.val ≤ stateA.step
            rw [h_step_prev]; exact hi_le_step
          have h_not_update_A : ¬ (stateA.step < iA.val ∧ stateA.step < L.val) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step_A h
          have h_not_col_A : ¬ (stateA.step < iA.val ∧ L.val = stateA.step) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step_A h
          rw [Matrix.stepMatrix_eq_of_not_update stateA.matrix stateA.step _ _ iA L
            h_not_update_A h_not_col_A]
          -- Canon in processed-row case: stays at fuel-value.
          have hnext_canon :
              (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n := by
            show stateG.step + 1 < n; exact hDone_G
          have hp_canon :
              (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
                (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
                (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0 := by
            show stateG.matrix[stateG.step][stateG.step] ≠ 0
            intro hzero
            apply h_pivot_G_ne; exact hzero
          have h_not_active :
              ¬ (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val := by
            show ¬ stateG.step + 1 ≤ i.val; omega
          rw [bareissGramCanonicalCoeff_succ_processed b fuel i hnext_canon hp_canon
            h_not_active]
          exact h_trail_prev i

/-- Determinantal identification of the canonical row-coefficient vector
`bareissGramCanonicalCoeff b fuel i` at slot `a` as the trailing-column entry
of the no-pivot Bareiss pass on the augmented `(n + 1) × (n + 1)` matrix
`augmentedGram b a`.  The hypothesis `fuel ≤ i.val` ensures the comparison
covers both the active-row and processed-row branches of the canonical
recursion. -/
theorem bareissGramCanonicalCoeff_eq_augmentedGram_entry
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n) (a : Fin n)
    (hfuel : fuel ≤ i.val)
    (h_no_sing :
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (bareissGramCanonicalCoeff b fuel i)[a] =
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (augmentedGram b a))).matrix[
        (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][Fin.last n] := by
  have hfuel_n : fuel + 1 ≤ n := by
    have : i.val < n := i.isLt
    omega
  obtain ⟨_, _, _, _, h_trail⟩ :=
    noPivotLoop_augmentedGram_invariant b a fuel hfuel_n h_no_sing
  exact (h_trail i).symm

/-- Direct bordered-minor form: the canonical row-coefficient vector at slot
`a` equals the determinant of the `(fuel + 1) × (fuel + 1)` bordered minor of
the augmented Gram matrix.  Composes
`bareissGramCanonicalCoeff_eq_augmentedGram_entry` with the Bareiss
no-pivot invariant `trailing_eq`. -/
theorem bareissGramCanonicalCoeff_eq_borderedMinor_aug
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n) (a : Fin n)
    (hfuel : fuel ≤ i.val)
    (h_no_sing :
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (bareissGramCanonicalCoeff b fuel i)[a] =
      Matrix.det (Matrix.borderedMinor (augmentedGram b a) fuel
        (by have : i.val < n := i.isLt; omega : fuel < n + 1)
        (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) (Fin.last n)) := by
  rw [bareissGramCanonicalCoeff_eq_augmentedGram_entry b fuel i a hfuel h_no_sing]
  -- Set up the Bareiss invariant on the augmented loop.
  have hfuel_n : fuel + 1 ≤ n := by
    have : i.val < n := i.isLt; omega
  obtain ⟨_, _, h_sing_aug, _, _⟩ :=
    noPivotLoop_augmentedGram_invariant b a fuel hfuel_n h_no_sing
  have h_step_aug_eq_fuel :
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (augmentedGram b a))).step = fuel := by
    have h := Matrix.noPivotLoop_step_eq_add_of_singularStep_none fuel
      (Matrix.noPivotInitialState (augmentedGram b a)) rfl (by
        show 0 + fuel + 1 ≤ n + 1; omega) h_sing_aug
    simpa [Matrix.noPivotInitialState] using h
  have h_inv : HexMatrixMathlib.BareissNoPivotInvariant (augmentedGram b a)
      (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState (augmentedGram b a))) :=
    HexMatrixMathlib.noPivotLoop_invariant_of_singularStep_eq_none
      (augmentedGram b a) fuel
      (Matrix.noPivotInitialState (augmentedGram b a))
      (HexMatrixMathlib.bareissNoPivotInvariant_initial (augmentedGram b a)) h_sing_aug
  -- Apply trailing_eq_at_step with `s := fuel` and `hstep := h_step_aug_eq_fuel.symm`.
  have h_step_lt : fuel < n + 1 := by omega
  have h_step_le_i : fuel ≤ (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)).val := hfuel
  have h_step_le_last : fuel ≤ (Fin.last n).val := by show fuel ≤ n; omega
  exact trailing_eq_at_step_local h_inv fuel h_step_lt h_step_aug_eq_fuel.symm
    (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) (Fin.last n)
    h_step_le_i h_step_le_last

/-- Under a non-singular no-pivot Bareiss prefix that has not yet reached the
terminal step, the loop on the initial state of `M` consumed exactly `fuel`
regular iterations: the resulting step equals `fuel`, and `fuel + 1 ≤ n'`. -/
theorem noPivotLoop_initial_step_eq_and_fuel_succ_le
    {n' : Nat} (M : Hex.Matrix Int n' n') (fuel : Nat)
    (h_no_sing :
      (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).singularStep = none)
    (hnext :
      (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).step + 1 < n') :
    (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).step = fuel ∧
      fuel + 1 ≤ n' := by
  induction fuel with
  | zero =>
    have h_init_step : (Matrix.noPivotInitialState M).step = 0 := rfl
    refine ⟨rfl, ?_⟩
    have h0 := hnext
    rw [Matrix.noPivotLoop_zero_fuel, h_init_step] at h0
    omega
  | succ fuel ih =>
    have h_no_sing_prev := noPivotLoop_singularStep_none_of_succ M fuel h_no_sing
    set state' := Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) with hstate'
    by_cases hDone : state'.step + 1 < n'
    · by_cases hp : state'.matrix[state'.step][state'.step] = 0
      · exfalso
        rw [Matrix.noPivotLoop_add fuel 1, ← hstate',
            Matrix.noPivotLoop_singular_branch 0 state' hDone hp] at h_no_sing
        simp at h_no_sing
      · -- Regular branch: peel the last iteration.
        obtain ⟨h_step_prev, h_fuel_prev⟩ := ih h_no_sing_prev hDone
        refine ⟨?_, by omega⟩
        rw [Matrix.noPivotLoop_add fuel 1, ← hstate',
            Matrix.noPivotLoop_regular_branch 0 state' hDone hp,
            Matrix.noPivotLoop_zero_fuel]
        show state'.step + 1 = fuel + 1
        rw [h_step_prev]
    · exfalso
      rw [Matrix.noPivotLoop_add fuel 1, ← hstate',
          Matrix.noPivotLoop_done 0 state' hDone] at hnext
      exact hDone hnext

/-- Companion to `trailing_eq_at_step_local`: rewrite
`BareissNoPivotInvariant.prevPivot_eq` with the step value supplied externally
so the dependent `leadingPrefix` type matches the desired `s = state.step`
substitution cleanly. -/
theorem prevPivot_eq_at_step_local
    {n' : Nat} {M : Hex.Matrix Int n' n'} {state : Matrix.BareissState n'}
    (hinv : HexMatrixMathlib.BareissNoPivotInvariant M state)
    (s : Nat) (hs : s ≤ n') (hstep : s = state.step) :
    state.prevPivot = Hex.Matrix.det (Hex.Matrix.leadingPrefix M s hs) := by
  subst hstep
  exact hinv.prevPivot_eq

/-- Concrete bridge-side instance of `StepWitness` for any integer basis.

The witness quotient at slot `a` is the next iteration's canonical row
coefficient `(bareissGramCanonicalCoeff b (fuel + 1) i)[a]`.  Integrality of
this quotient comes from the Bareiss-Desnanot identity applied to the
augmented `(n + 1) × (n + 1)` matrix `augmentedGram b a`: the canonical
coefficients identify with trailing-column entries of the augmented no-pivot
Bareiss pass (`bareissGramCanonicalCoeff_eq_borderedMinor_aug`), and the
Bareiss step recurrence on the augmented matrix supplies the exact-division
multiplicative identity. -/
@[expose]
def StepWitness.ofGram (b : Matrix Int n m) :
    Hex.GramSchmidt.Int.StepWitness b := by
  intro fuel hinv h_canon h_prefix_none hnext hp i hi
  -- Prepare bound facts and the step equality before refining.
  set state := Matrix.noPivotLoop fuel
    (Matrix.noPivotInitialState (Matrix.gramMatrix b)) with hstate
  obtain ⟨h_step_eq_fuel, hfuel_n_le⟩ :=
    noPivotLoop_initial_step_eq_and_fuel_succ_le (Matrix.gramMatrix b)
      fuel h_prefix_none hnext
  have hfuel_lt_n : fuel < n := by omega
  have hfuel_lt_naug : fuel < n + 1 := by omega
  have hfuel_succ_lt_naug : fuel + 1 < n + 1 := by omega
  have hfuel_le_naug : fuel ≤ n + 1 := by omega
  -- The prefix at `fuel + 1` is also non-singular (one more regular step).
  have h_prefix_none_succ :
      (Matrix.noPivotLoop (fuel + 1)
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
    rw [Matrix.noPivotLoop_add fuel 1, ← hstate,
        Matrix.noPivotLoop_regular_branch 0 state hnext hp,
        Matrix.noPivotLoop_zero_fuel]
  have h_fuel_succ_le_i : fuel + 1 ≤ i.val := by rw [← h_step_eq_fuel]; exact hi
  refine ⟨fun a => (Hex.GramSchmidt.Int.bareissGramCanonicalCoeff b (fuel + 1) i)[a], ?_⟩
  -- The structure field has an outer `let k := ⟨state.step, _⟩` binder before
  -- the `∀ a`, so two intros are needed.
  intro k_let a
  -- Augmented invariants at fuel and fuel + 1, both at slot `a`.
  obtain ⟨h_step_A, h_prev_A, h_sing_A, h_block_A, h_trail_A⟩ :=
    noPivotLoop_augmentedGram_invariant b a fuel hfuel_n_le h_prefix_none
  set stateA := Matrix.noPivotLoop fuel
    (Matrix.noPivotInitialState (augmentedGram b a)) with hstateA
  -- The lifted Fin (n + 1) indices used throughout.
  set iA : Fin (n + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with hiA_def
  set kA : Fin (n + 1) := ⟨k_let.val, Nat.lt_succ_of_lt k_let.isLt⟩ with hkA_def
  set L : Fin (n + 1) := Fin.last n with hL_def
  -- `k_let.val = state.step = fuel`, so `kA.val = fuel`.
  have h_kA_val : kA.val = fuel := h_step_eq_fuel
  have h_fuel_le_kA : fuel ≤ kA.val := Nat.le_of_eq h_kA_val.symm
  have h_fuel_lt_iA : fuel < iA.val := by show fuel < i.val; omega
  have h_fuel_lt_L : fuel < L.val := by show fuel < n; omega
  have h_fuel_le_iA : fuel ≤ iA.val := Nat.le_of_lt h_fuel_lt_iA
  have h_fuel_le_L : fuel ≤ L.val := Nat.le_of_lt h_fuel_lt_L
  -- Substitute the row-invariant's coefficients by canonical via h_canon.
  rw [h_canon i, h_canon k_let]
  -- Bridge state.matrix entries to stateA entries via the upper-block bridge.
  rw [show state.matrix[k_let][k_let] = stateA.matrix[kA][kA] from
      (h_block_A k_let k_let).symm]
  rw [show state.matrix[i][k_let] = stateA.matrix[iA][kA] from
      (h_block_A i k_let).symm]
  -- Bridge canonical coefficients to stateA trailing-column entries.
  rw [show (bareissGramCanonicalCoeff b fuel i)[a] = stateA.matrix[iA][L] from
      (h_trail_A i).symm]
  rw [show (bareissGramCanonicalCoeff b fuel k_let)[a] = stateA.matrix[kA][L] from
      (h_trail_A k_let).symm]
  -- Bridge state.prevPivot to stateA.prevPivot (h_prev_A goes the other way).
  rw [← h_prev_A]
  -- Bareiss invariant on the augmented loop at fuel.
  have h_inv : HexMatrixMathlib.BareissNoPivotInvariant (augmentedGram b a) stateA :=
    HexMatrixMathlib.noPivotLoop_invariant_of_singularStep_eq_none
      (augmentedGram b a) fuel _
      (HexMatrixMathlib.bareissNoPivotInvariant_initial (augmentedGram b a))
      h_sing_A
  have h_stateA_step : stateA.step = fuel := h_step_A.trans h_step_eq_fuel
  -- Rewrite each stateA entry and the prevPivot as bordered-minor determinants.
  rw [trailing_eq_at_step_local h_inv fuel hfuel_lt_naug h_stateA_step.symm kA kA
        h_fuel_le_kA h_fuel_le_kA]
  rw [trailing_eq_at_step_local h_inv fuel hfuel_lt_naug h_stateA_step.symm iA L
        h_fuel_le_iA h_fuel_le_L]
  rw [trailing_eq_at_step_local h_inv fuel hfuel_lt_naug h_stateA_step.symm iA kA
        h_fuel_le_iA h_fuel_le_kA]
  rw [trailing_eq_at_step_local h_inv fuel hfuel_lt_naug h_stateA_step.symm kA L
        h_fuel_le_kA h_fuel_le_L]
  rw [prevPivot_eq_at_step_local h_inv fuel hfuel_le_naug h_stateA_step.symm]
  -- Beta-reduce the explicit `q a` on the RHS so the next rewrite matches.
  show ((augmentedGram b a).borderedMinor fuel hfuel_lt_naug kA kA).det *
        ((augmentedGram b a).borderedMinor fuel hfuel_lt_naug iA L).det -
      ((augmentedGram b a).borderedMinor fuel hfuel_lt_naug iA kA).det *
        ((augmentedGram b a).borderedMinor fuel hfuel_lt_naug kA L).det =
    (bareissGramCanonicalCoeff b (fuel + 1) i)[a] *
      ((augmentedGram b a).leadingPrefix fuel hfuel_le_naug).det
  rw [bareissGramCanonicalCoeff_eq_borderedMinor_aug b (fuel + 1) i a
        h_fuel_succ_le_i h_prefix_none_succ]
  -- Desnanot-Jacobi on the augmented matrix at level `fuel`.
  have hdj :=
    HexMatrixMathlib.desnanot_jacobi_borderedMinor (augmentedGram b a) fuel
      hfuel_lt_naug hfuel_succ_lt_naug iA L h_fuel_lt_iA h_fuel_lt_L
  -- The K positions in hdj are `⟨fuel, _⟩ : Fin (n + 1)`; via Fin.ext they
  -- equal `kA` (whose value is `state.step = fuel`).
  have hK : ∀ (h : fuel < n + 1), (⟨fuel, h⟩ : Fin (n + 1)) = kA := fun _ =>
    Fin.ext h_kA_val.symm
  simp_rw [hK] at hdj
  exact hdj.symm

/-- Cramer's rule identity under singularity. When the no-pivot Bareiss pass over
the Gram matrix records an early singular step before reaching column `j`, the
Leibniz determinant of the Cramer minor `scaledCoeffMatrix b i j hji` is zero.
Internally lifts the partial-pass singularity to the full `bareissNoPivotData`
pass, traverses `gramDetVecEntry` to conclude `gramDet b (j+1) = 0`, and
finishes via the Cramer determinant identity
`scaledCoeffMatrix_det_eq_gramDet_mul_coeffs`. -/
theorem scaledCoeffMatrix_det_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) (s : Nat)
    (h_sing : (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) = 0 := by
  -- Step A: derive `s < j.val` from the partial-pass singularity.
  have hsj : s < j.val := by
    have h := noPivotLoop_singularStep_lt j.val
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
    -- h : s < (noPivotInitialState ...).step + j.val. The init step is 0.
    change s < 0 + j.val at h
    omega
  -- Step B: lift to the full `bareissNoPivotData` pass.
  have hjn : j.val < n := Nat.lt_trans hji i.isLt
  have hsucc : j.val + 1 ≤ n := Nat.succ_le_of_lt hjn
  have hjle : j.val ≤ n := Nat.le_of_lt hjn
  have h_init :
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)).singularStep = none := rfl
  have h_full_sing :
      (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).singularStep = some s := by
    -- Apply singular_inv to the j.val-fueled pass.
    rcases noPivotLoop_singular_inv j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_init
      with h_none | ⟨k, hsk, hstk, hpk, hk⟩
    · rw [h_none] at h_sing; nomatch h_sing
    · -- The full pass equals the j.val pass via fixedpoint.
      have hks : k.val = s := by
        rw [hsk] at h_sing
        exact Option.some.inj h_sing
      -- Use noPivotLoop_add and noPivotLoop_id_at_singular_fixedpoint to lift.
      have h_add : Matrix.noPivotLoop (j.val + (n - j.val))
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
        Matrix.noPivotLoop (n - j.val)
          (Matrix.noPivotLoop j.val
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))) :=
        Matrix.noPivotLoop_add j.val (n - j.val) _
      have hn_eq : j.val + (n - j.val) = n := Nat.add_sub_cancel' hjle
      -- The post-`j.val` state already has singularStep = some k.val, step = k.val,
      -- and a zero pivot at column k. Extra fuel is a fixedpoint.
      have h_step_lt : (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n := by
        rw [hstk]; exact hk
      have h_pivot_zero :
          (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
              (⟨(Matrix.noPivotLoop j.val
                  (Matrix.noPivotInitialState
                    (Matrix.gramMatrix b))).step,
                Nat.lt_of_succ_lt h_step_lt⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop j.val
                  (Matrix.noPivotInitialState
                    (Matrix.gramMatrix b))).step,
                Nat.lt_of_succ_lt h_step_lt⟩ : Fin n)] = 0 := by
        have h_fin :
            (⟨(Matrix.noPivotLoop j.val
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step,
              Nat.lt_of_succ_lt h_step_lt⟩ : Fin n) = k :=
          Fin.ext hstk
        simp only [h_fin]
        exact hpk
      have h_sing_step :
          (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep =
            some (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step := by
        rw [hsk, hstk]
      have h_fixed :
          Matrix.noPivotLoop (n - j.val)
            (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))) =
            Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState (Matrix.gramMatrix b)) :=
        Matrix.noPivotLoop_id_at_singular_fixedpoint (n := n) (n - j.val) _
          h_step_lt h_pivot_zero h_sing_step
      have h_full_eq :
          Matrix.noPivotLoop n
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
          Matrix.noPivotLoop j.val
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := by
        calc Matrix.noPivotLoop n
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))
            = Matrix.noPivotLoop (j.val + (n - j.val))
                (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := by
                  rw [hn_eq]
          _ = Matrix.noPivotLoop (n - j.val)
                (Matrix.noPivotLoop j.val
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))) := h_add
          _ = Matrix.noPivotLoop j.val
                (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := h_fixed
      show (Matrix.finish (Matrix.noPivotLoop n
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)))).singularStep = some s
      change (Matrix.noPivotLoop n
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s
      rw [h_full_eq, hsk, hks]
  -- Step C: gramDet b (j+1) = 0 via gramDetVecEntry chain.
  have h_gd_zero : gramDet b (j.val + 1) hsucc = 0 := by
    have h_vec_gd :=
      gramDetVecEntry_eq_gramDet (b := b) (StepWitness.ofGram b) (j.val + 1) hsucc
    have h_vec_zero :=
      gramDetVecEntry_noPivot_eq_zero_of_singularStep_lt b s j.val hjn h_full_sing
        (by omega)
    rw [← h_vec_gd, h_vec_zero]
  -- Step D: Cramer's identity collapses to zero.
  have h_cramer :=
    scaledCoeffMatrix_det_eq_gramDet_mul_coeffs (b := b) i.val j.val i.isLt hji
  rw [h_gd_zero] at h_cramer
  simp at h_cramer
  exact_mod_cast h_cramer

/-- Unconditional rational closed form for the strictly lower entries of
`scaledCoeffs`: the executable integer scaled coefficient agrees with the
Leibniz determinant of the Cramer minor `scaledCoeffMatrix b i j hji`,
regardless of whether the no-pivot Bareiss pass over `gramMatrix b` reaches
column `j` without recording a singular step. The non-singular branch
composes the Mathlib-free correspondence
`scaledCoeffs_lower_eq_noPivotLoop_scaledCoeffMatrix` (via
`noPivotLoop_full_eq_borderedMinor_at_trailing` + `scaledCoeffMatrix_eq_borderedMinor`)
with `bareiss_eq_noPivotLoop_last_of_no_singular` and the `bareiss_eq_mathlib_det`
/ `det_eq` cross-bridge; the singular branch sends both sides to `0` via the
singular cascade. All Mathlib-side bridge theorems for strictly lower entries
route through this unconditional identity. -/
theorem scaledCoeffs_lower_eq_det_scaledCoeffMatrix
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) =
      ((Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) : Int) : Rat) := by
  have hjn : j.val < n := Nat.lt_trans hji i.isLt
  cases h_sing : (Matrix.noPivotLoop j.val
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep with
  | none =>
      have h_lhs : GramSchmidt.entry (scaledCoeffs b) i j =
          Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
        rw [scaledCoeffs_lower_eq_noPivotLoop_scaledCoeffMatrix b (StepWitness.ofGram b)
          i j hji h_sing]
        have h_sync :=
          noPivotLoop_full_eq_borderedMinor_at_trailing (Matrix.gramMatrix b) j.val hjn
            ⟨j.val, hjn⟩ i (Nat.le_refl j.val) (Nat.le_of_lt hji)
        have h_bm_nonsing :
            (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState
                (Matrix.borderedMinor (Matrix.gramMatrix b) j.val hjn
                  ⟨j.val, hjn⟩ i))).singularStep = none := by
          rw [← h_sync.2]; exact h_sing
        have h_sc_nonsing :
            (Matrix.noPivotLoop j.val
              (Matrix.noPivotInitialState
                (GramSchmidt.scaledCoeffMatrix b i j hji))).singularStep = none := by
          rw [scaledCoeffMatrix_eq_borderedMinor]; exact h_bm_nonsing
        exact (Matrix.bareiss_eq_noPivotLoop_last_of_no_singular
          (GramSchmidt.scaledCoeffMatrix b i j hji) h_sc_nonsing).symm
      rw [h_lhs]
      exact_mod_cast (HexMatrixMathlib.bareiss_eq_mathlib_det
          (GramSchmidt.scaledCoeffMatrix b i j hji)).trans
        (HexMatrixMathlib.det_eq (GramSchmidt.scaledCoeffMatrix b i j hji)).symm
  | some s =>
      have hsj : s < j.val := by
        have h := noPivotLoop_singularStep_lt j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
        change s < 0 + j.val at h
        omega
      have h_lhs : GramSchmidt.entry (scaledCoeffs b) i j = 0 := by
        rw [scaledCoeffs_entry_eq_getArrayEntry]
        exact getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
          b (StepWitness.ofGram b) i.val j.val i.isLt (Nat.le_of_lt hji) s hsj h_sing
      have h_det : Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) = 0 :=
        scaledCoeffMatrix_det_eq_zero_of_singularStep_lt b i j hji s h_sing
      rw [h_lhs, h_det]

/-- Non-singular branch of the Cramer/Bareiss identity: when the no-pivot
Bareiss pass over the Gram matrix reaches column `j` without recording a
singular step, the executable scaled coefficient agrees with the public
row-pivoted Bareiss determinant of the Cramer minor. Derived from the
unconditional `scaledCoeffs_lower_eq_det_scaledCoeffMatrix` by casting back
to `Int` and translating `Matrix.det` to `Matrix.bareiss` via the
`det_eq` / `bareiss_eq_mathlib_det` cross-bridge. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss_of_no_singular
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (_h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  have h_det : GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) := by
    exact_mod_cast scaledCoeffs_lower_eq_det_scaledCoeffMatrix b i j hji
  rw [h_det]
  exact ((HexMatrixMathlib.bareiss_eq_mathlib_det
        (GramSchmidt.scaledCoeffMatrix b i j hji)).trans
      (HexMatrixMathlib.det_eq (GramSchmidt.scaledCoeffMatrix b i j hji)).symm).symm

/-- Cramer/Bareiss identity: below the diagonal, the integral scaled
Gram-Schmidt coefficient is exactly the public Bareiss determinant of the
Cramer minor `scaledCoeffMatrix`. Derived from the unconditional
`scaledCoeffs_lower_eq_det_scaledCoeffMatrix` by casting back to `Int` and
translating `Matrix.det` to `Matrix.bareiss` via `det_eq` /
`bareiss_eq_mathlib_det`. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  have h_det : GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) := by
    exact_mod_cast scaledCoeffs_lower_eq_det_scaledCoeffMatrix b i j hji
  rw [h_det]
  exact ((HexMatrixMathlib.bareiss_eq_mathlib_det
        (GramSchmidt.scaledCoeffMatrix b i j hji)).trans
      (HexMatrixMathlib.det_eq (GramSchmidt.scaledCoeffMatrix b i j hji)).symm).symm

/-- The fraction-free scaled-coefficient loop computes the Cramer/Bareiss
integer equal to `d[j+1] * μ[i,j]` below the diagonal. Derived from the
unconditional `scaledCoeffs_lower_eq_det_scaledCoeffMatrix` and
`scaledCoeffMatrix_det_eq_gramDet_mul_coeffs`. -/
private theorem scaledCoeffRows_lower_eq_coeffs
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    ((getArrayEntry (scaledCoeffRows b) i j : Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ := by
  have hjlt : j < n := Nat.lt_trans hj hi
  have h_array :
      getArrayEntry (scaledCoeffRows b) i j =
        GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ := by
    rw [scaledCoeffs_entry_eq_getArrayEntry,
      getArrayEntry_scaledCoeffRowsSchur_eq b (StepWitness.ofGram b)]
  rw [h_array, scaledCoeffs_lower_eq_det_scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj]
  exact scaledCoeffMatrix_det_eq_gramDet_mul_coeffs b i j hi hj

/-- Below the diagonal, the rational image of the integer scaled
Gram-Schmidt coefficient factors as `gramDet b (j+1) * coeffs[i,j]`. Derived
from the unconditional `scaledCoeffs_lower_eq_det_scaledCoeffMatrix` and
`scaledCoeffMatrix_det_eq_gramDet_mul_coeffs`. -/
theorem scaledCoeffs_eq (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < i) :
    ((GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ : Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ := by
  rw [scaledCoeffs_lower_eq_det_scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj]
  exact scaledCoeffMatrix_det_eq_gramDet_mul_coeffs b i j hi hj

end Int
end GramSchmidt
end Hex
