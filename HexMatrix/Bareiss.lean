import HexMatrix.Determinant

/-!
Executable Bareiss determinant algorithm for `hex-matrix`.

This module implements fraction-free Bareiss elimination over `Int` in two
layers: a no-pivot recurrence that follows the standard exact-division update,
and a public row-pivoting wrapper that swaps in a nonzero pivot when needed and
tracks the resulting determinant sign. The root library also exposes the
theorem surface relating this executable path to the generic determinant.
-/

namespace Hex

universe u

namespace Matrix

variable {n : Nat}

/-- Output of an executable Bareiss elimination pass. -/
structure BareissData (n : Nat) where
  matrix : Matrix Int n n
  rowSwaps : Nat
  singularStep : Option Nat

namespace BareissData

/-- The determinant sign contributed by the recorded row swaps. -/
def sign (data : BareissData n) : Int :=
  if data.rowSwaps % 2 = 0 then 1 else -1

private def lastDiag? (M : Matrix Int n n) : Option Int :=
  match n with
  | 0 => none
  | k + 1 =>
      let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      some M[i][i]

/-- The determinant encoded by a Bareiss elimination result. -/
def det (data : BareissData n) : Int :=
  match data.singularStep with
  | some _ => 0
  | none =>
      match lastDiag? data.matrix with
      | some d => data.sign * d
      | none => data.sign

/-- For a non-singular Bareiss elimination of a positive-size matrix, the
encoded determinant is `sign * (last diagonal entry)`. -/
theorem det_succ_eq {k : Nat} (data : BareissData (k + 1))
    (h : data.singularStep = none) :
    data.det = data.sign *
      data.matrix[(⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))][
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))] := by
  unfold det
  rw [h]
  rfl

/-- For a non-singular Bareiss elimination of an empty matrix, the encoded
determinant is the sign. -/
theorem det_zero_eq (data : BareissData 0)
    (h : data.singularStep = none) :
    data.det = data.sign := by
  unfold det
  rw [h]
  rfl

end BareissData

/-- Internal state of the no-pivot Bareiss recurrence, exposed read-only for
the Mathlib-side determinant proof. -/
structure BareissState (n : Nat) where
  step : Nat
  matrix : Matrix Int n n
  prevPivot : Int
  rowSwaps : Nat
  singularStep : Option Nat

/-- Exact division used by the Bareiss recurrence. The `else` branch is
defensive; for matrices produced by the Bareiss update, divisibility should
always hold. -/
def exactDiv (num denom : Int) : Int :=
  if h : denom ∣ num then
    Int.divExact num denom h
  else
    0

/-- When divisibility is known, `exactDiv` is the GMP-backed exact quotient. -/
theorem exactDiv_eq_divExact {num denom : Int} (h : denom ∣ num) :
    exactDiv num denom = Int.divExact num denom h := by
  simp [exactDiv, h]

/-- Search column `col` for a nonzero pivot at or below `start`. -/
def findPivotAux (M : Matrix Int n n) (col : Fin n) (start fuel : Nat) :
    Option (Fin n) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < n then
        let i : Fin n := ⟨start, h⟩
        if M[i][col] = 0 then
          findPivotAux M col (start + 1) fuel
        else
          some i
      else
        none

/-- Search column `col` for a nonzero pivot at or below `start`. -/
def findPivot? (M : Matrix Int n n) (col : Fin n) (start : Nat) :
    Option (Fin n) :=
  findPivotAux M col start (n - start)

/-- A pivot returned by `findPivotAux` is always at or below its starting row. -/
theorem findPivotAux_ge_start (M : Matrix Int n n) (col : Fin n)
    (start fuel : Nat) {pivot : Fin n}
    (hfind : findPivotAux M col start fuel = some pivot) :
    start ≤ pivot.val := by
  induction fuel generalizing start with
  | zero =>
      simp [findPivotAux] at hfind
  | succ fuel ih =>
      by_cases hstart : start < n
      · simp [findPivotAux, hstart] at hfind
        split at hfind
        · exact Nat.le_trans (Nat.le_succ start) (ih (start + 1) hfind)
        · cases hfind
          exact Nat.le_refl _
      · simp [findPivotAux, hstart] at hfind

/-- A pivot returned by `findPivot?` is always at or below its starting row. -/
theorem findPivot?_ge_start (M : Matrix Int n n) (col : Fin n)
    (start : Nat) {pivot : Fin n}
    (hfind : findPivot? M col start = some pivot) :
    start ≤ pivot.val :=
  findPivotAux_ge_start M col start (n - start) hfind

/-- If bounded pivot search fails, every checked entry in the pivot column is
zero. -/
theorem findPivotAux_eq_zero_of_none (M : Matrix Int n n) (col : Fin n)
    (start fuel : Nat) (hfind : findPivotAux M col start fuel = none)
    (i : Fin n) (hstart : start ≤ i.val) (hfuel : i.val < start + fuel) :
    M[i][col] = 0 := by
  induction fuel generalizing start with
  | zero =>
      omega
  | succ fuel ih =>
      by_cases hlt : start < n
      · by_cases hi : i.val = start
        · have hentry : M[(⟨start, hlt⟩ : Fin n)][col] = 0 := by
            by_cases hzero : M[(⟨start, hlt⟩ : Fin n)][col] = 0
            · exact hzero
            · have hzeroNat : ¬ M[start][col.val] = 0 := by
                simpa using hzero
              simp [findPivotAux, hlt, hzeroNat] at hfind
          have hiFin : i = (⟨start, hlt⟩ : Fin n) := Fin.ext hi
          rw [hiFin]
          exact hentry
        · have hentry : M[(⟨start, hlt⟩ : Fin n)][col] = 0 := by
            by_cases hzero : M[(⟨start, hlt⟩ : Fin n)][col] = 0
            · exact hzero
            · have hzeroNat : ¬ M[start][col.val] = 0 := by
                simpa using hzero
              simp [findPivotAux, hlt, hzeroNat] at hfind
          have hnext : findPivotAux M col (start + 1) fuel = none := by
            have hentryNat : M[start][col.val] = 0 := by
              simpa using hentry
            simp [findPivotAux, hlt, hentryNat] at hfind
            exact hfind
          have hstart' : start + 1 ≤ i.val := by omega
          have hfuel' : i.val < start + 1 + fuel := by omega
          exact ih (start + 1) hnext hstart' hfuel'
      · omega

/-- If pivot search fails, every entry in the searched suffix of the pivot
column is zero. -/
theorem findPivot?_eq_zero_of_none (M : Matrix Int n n) (col : Fin n)
    (start : Nat) (hfind : findPivot? M col start = none)
    (i : Fin n) (hstart : start ≤ i.val) :
    M[i][col] = 0 := by
  apply findPivotAux_eq_zero_of_none M col start (n - start) hfind i hstart
  omega

/-- Apply one Bareiss update step to the trailing submatrix strictly below and
to the right of the current pivot. -/
def stepMatrix (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) :
    Matrix Int n n :=
  Matrix.ofFn fun i j =>
    if hkij : k < i.val ∧ k < j.val then
      let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
      let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
      exactDiv (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot
    else if hBelow : k < i.val ∧ j.val = k then
      0
    else
      M[i][j]

/-- Outside the trailing update region and pivot column below the pivot,
`stepMatrix` leaves entries unchanged. -/
theorem stepMatrix_eq_of_not_update
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i j : Fin n)
    (htrail : ¬ (k < i.val ∧ k < j.val))
    (hcol : ¬ (k < i.val ∧ j.val = k)) :
    (stepMatrix M k pivot prevPivot)[i][j] = M[i][j] := by
  simp [stepMatrix, Matrix.ofFn, htrail, hcol]

/-- `stepMatrix` preserves diagonal entries whose index is at or before the
current pivot step. -/
theorem stepMatrix_diag_of_le
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i : Fin n)
    (hi : i.val ≤ k) :
    (stepMatrix M k pivot prevPivot)[i][i] = M[i][i] := by
  apply stepMatrix_eq_of_not_update
  · intro htrail
    exact Nat.not_lt_of_ge hi htrail.1
  · intro hcol
    exact Nat.not_lt_of_ge hi hcol.1

/-- `stepMatrix` clears the pivot column below the current pivot. -/
theorem stepMatrix_pivot_col_below
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i colK : Fin n)
    (hi : k < i.val) (hcolK : colK.val = k) :
    (stepMatrix M k pivot prevPivot)[i][colK] = 0 := by
  simp [stepMatrix, Matrix.ofFn, hi, hcolK]

/-- Entry formula for the trailing block updated by one Bareiss step. -/
theorem stepMatrix_update_eq
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i j : Fin n)
    (hi : k < i.val) (hj : k < j.val) :
    (stepMatrix M k pivot prevPivot)[i][j] =
      (let colK : Fin n := ⟨k, Nat.lt_trans hi i.isLt⟩
       let rowK : Fin n := ⟨k, Nat.lt_trans hj j.isLt⟩
       exactDiv (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot) := by
  simp [stepMatrix, Matrix.ofFn, hi, hj]

/-- If the current matrix entries already match bordered minors and exact
division evaluates to the next bordered minor, then one `stepMatrix` update
preserves the bordered-minor invariant at the updated entry. -/
theorem stepMatrix_borderedMinor_update
    (source current : Matrix Int n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (pivot prevPivot : Int)
    (hpivot :
      pivot =
        det (borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
          (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)))
    (hentry :
      current[i][j] = det (borderedMinor source k hk i j))
    (hleft :
      current[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] =
        det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)))
    (htop :
      current[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j] =
        det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
    (hexact :
      exactDiv
        (det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot =
          det (borderedMinor source (k + 1) hnext i j)) :
    (stepMatrix current k pivot prevPivot)[i][j] =
      det (borderedMinor source (k + 1) hnext i j) := by
  rw [stepMatrix_update_eq current k pivot prevPivot i j hi hj]
  change
    exactDiv
      (pivot * current[i][j] -
        current[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] *
        current[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j])
      prevPivot =
        det (borderedMinor source (k + 1) hnext i j)
  rw [hpivot, hentry, hleft, htop]
  exact hexact

private structure BareissArrayState where
  step : Nat
  matrix : Array (Array Int)
  prevPivot : Int
  rowSwaps : Nat
  singularStep : Option Nat

@[inline] private def getEntry (rows : Array (Array Int)) (row col : Nat) : Int :=
  rows[row]![col]!

private def matrixToRows (M : Matrix Int n n) : Array (Array Int) :=
  (Array.range n).map fun row =>
    (Array.range n).map fun col =>
      if hrow : row < n then
        if hcol : col < n then
          let i : Fin n := ⟨row, hrow⟩
          let j : Fin n := ⟨col, hcol⟩
          M[i][j]
        else
          0
      else
        0

private def rowsToMatrix (rows : Array (Array Int)) (n : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j => getEntry rows i.val j.val

private theorem getEntry_matrixToRows (M : Matrix Int n n) (i j : Fin n) :
    getEntry (matrixToRows M) i.val j.val = M[i][j] := by
  simp [getEntry, matrixToRows]

private theorem rowsToMatrix_matrixToRows (M : Matrix Int n n) :
    rowsToMatrix (matrixToRows M) n = M := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simpa [rowsToMatrix, Matrix.ofFn] using getEntry_matrixToRows M ⟨i, hi⟩ ⟨j, hj⟩

private theorem array_getElem!_set!_same {α : Type} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.set! i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  simp [Array.getD, Array.set!_eq_setIfInBounds, hi]

private theorem array_getElem!_set!_ne {α : Type} [Inhabited α]
    (xs : Array α) {i j : Nat} (hij : j ≠ i) (v : α) :
    (xs.set! i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.set!
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hij.symm]
  · simp [hi]

private theorem array_getElem!_setIfInBounds_same {α : Type} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.setIfInBounds i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  simp [Array.setIfInBounds, hi]

private theorem array_getElem!_setIfInBounds_ne {α : Type} [Inhabited α]
    (xs : Array α) {i j : Nat} (hij : j ≠ i) (v : α) :
    (xs.setIfInBounds i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hij.symm]
  · simp [hi]

private def swapRowsArray (rows : Array (Array Int)) (rowA rowB : Nat) :
    Array (Array Int) :=
  if rowA = rowB then
    rows
  else
    (rows.set! rowA rows[rowB]!).set! rowB rows[rowA]!

private theorem rowSwap_get (M : Matrix Int n n) (rowA rowB i j : Fin n) :
    (rowSwap M rowA rowB)[i][j] =
      if i = rowB then M[rowA][j] else if i = rowA then M[rowB][j] else M[i][j] := by
  by_cases hiB : i = rowB
  · subst i
    simp [rowSwap]
  · by_cases hiA : i = rowA
    · subst i
      simp [rowSwap, hiB]
      have hval : rowB.val ≠ rowA.val := by
        intro hval
        exact hiB (Fin.ext hval.symm)
      have hrow : ((M.set rowA M[rowB]).set rowB M[rowA])[rowA] =
          (M.set rowA M[rowB])[rowA] := by
        exact Vector.getElem_set_ne (xs := M.set rowA M[rowB]) (x := M[rowA])
          rowB.isLt rowA.isLt hval
      simpa using congrArg (fun row => row[j]) hrow
    · simp [rowSwap, hiB, hiA]
      have hAi : rowA.val ≠ i.val := by
        intro hval
        exact hiA (Fin.ext hval.symm)
      have hBi : rowB.val ≠ i.val := by
        intro hval
        exact hiB (Fin.ext hval.symm)
      have hrow₁ : (M.set rowA M[rowB])[i] = M[i] := by
        exact Vector.getElem_set_ne (xs := M) (x := M[rowB]) rowA.isLt i.isLt hAi
      have hrow₂ : ((M.set rowA M[rowB]).set rowB M[rowA])[i] =
          (M.set rowA M[rowB])[i] := by
        exact Vector.getElem_set_ne (xs := M.set rowA M[rowB]) (x := M[rowA])
          rowB.isLt i.isLt hBi
      exact (congrArg (fun row => row[j]) hrow₂).trans
        (congrArg (fun row => row[j]) hrow₁)

private theorem getEntry_swapRowsArray_matrixToRows (M : Matrix Int n n)
    (rowA rowB i j : Fin n) :
    getEntry (swapRowsArray (matrixToRows M) rowA.val rowB.val) i.val j.val =
      (rowSwap M rowA rowB)[i][j] := by
  by_cases hsame : rowA.val = rowB.val
  · have hrows : rowA = rowB := Fin.ext hsame
    subst rowB
    simp [swapRowsArray, getEntry_matrixToRows, rowSwap]
  · have hrows_size : (matrixToRows M).size = n := by
      simp [matrixToRows]
    have hrowA : rowA.val < (matrixToRows M).size := by
      simp [hrows_size, rowA.isLt]
    have hrowB : rowB.val < (matrixToRows M).size := by
      simp [hrows_size, rowB.isLt]
    by_cases hiB : i = rowB
    · subst i
      have hBA : rowB.val ≠ rowA.val := by
        intro h
        exact hsame h.symm
      have hrowB_after :
          rowB.val <
            ((matrixToRows M).setIfInBounds rowA.val (matrixToRows M)[rowB.val]!).size := by
        simpa [Array.size_setIfInBounds] using hrowB
      calc
        getEntry (swapRowsArray (matrixToRows M) rowA.val rowB.val) rowB.val j.val =
            getEntry (matrixToRows M) rowA.val j.val := by
              simp [swapRowsArray, hsame, getEntry, Array.set!_eq_setIfInBounds]
              rw [array_getElem!_setIfInBounds_same
                (xs := (matrixToRows M).setIfInBounds rowA.val (matrixToRows M)[rowB.val]!)
                hrowB_after]
        _ = M[rowA][j] := getEntry_matrixToRows M rowA j
        _ = (rowSwap M rowA rowB)[rowB][j] := by
              rw [rowSwap_get]
              simp
    · by_cases hiA : i = rowA
      · subst i
        have hAB : rowA.val ≠ rowB.val := by
          intro h
          exact hsame h
        calc
          getEntry (swapRowsArray (matrixToRows M) rowA.val rowB.val) rowA.val j.val =
              getEntry (matrixToRows M) rowB.val j.val := by
                simp [swapRowsArray, hsame, getEntry, Array.set!_eq_setIfInBounds]
                rw [array_getElem!_setIfInBounds_ne
                  (xs := (matrixToRows M).setIfInBounds rowA.val
                    (matrixToRows M)[rowB.val]!) hAB]
                exact congrArg (fun row => row[j.val]!)
                  (array_getElem!_setIfInBounds_same
                    (xs := matrixToRows M) hrowA (matrixToRows M)[rowB.val]!)
          _ = M[rowB][j] := getEntry_matrixToRows M rowB j
          _ = (rowSwap M rowA rowB)[rowA][j] := by
                rw [rowSwap_get]
                simp [hiB]
      · have hiA_val : i.val ≠ rowA.val := by
          intro h
          exact hiA (Fin.ext h)
        have hiB_val : i.val ≠ rowB.val := by
          intro h
          exact hiB (Fin.ext h)
        calc
          getEntry (swapRowsArray (matrixToRows M) rowA.val rowB.val) i.val j.val =
              getEntry (matrixToRows M) i.val j.val := by
                simp [swapRowsArray, hsame, getEntry, Array.set!_eq_setIfInBounds]
                rw [array_getElem!_setIfInBounds_ne
                  (xs := (matrixToRows M).setIfInBounds rowA.val
                    (matrixToRows M)[rowB.val]!) hiB_val]
                exact congrArg (fun row => row[j.val]!)
                  (array_getElem!_setIfInBounds_ne
                    (xs := matrixToRows M) hiA_val (matrixToRows M)[rowB.val]!)
          _ = M[i][j] := getEntry_matrixToRows M i j
          _ = (rowSwap M rowA rowB)[i][j] := by
                rw [rowSwap_get]
                simp [hiA, hiB]

private theorem rowsToMatrix_swapRowsArray_matrixToRows (M : Matrix Int n n)
    (rowA rowB : Fin n) :
    rowsToMatrix (swapRowsArray (matrixToRows M) rowA.val rowB.val) n =
      rowSwap M rowA rowB := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simpa [rowsToMatrix, Matrix.ofFn] using
    getEntry_swapRowsArray_matrixToRows M rowA rowB ⟨i, hi⟩ ⟨j, hj⟩

private theorem getEntry_swapRowsArray_matches
    (rows : Array (Array Int)) (M : Matrix Int n n)
    (hsize : rows.size = n)
    (hentry : ∀ i j : Fin n, getEntry rows i.val j.val = M[i][j])
    (rowA rowB i j : Fin n) :
    getEntry (swapRowsArray rows rowA.val rowB.val) i.val j.val =
      (rowSwap M rowA rowB)[i][j] := by
  by_cases hsame : rowA.val = rowB.val
  · have hrows : rowA = rowB := Fin.ext hsame
    subst rowB
    simp [swapRowsArray, hentry, rowSwap]
  · have hrowA : rowA.val < rows.size := by
      simp [hsize]
    have hrowB : rowB.val < rows.size := by
      simp [hsize]
    by_cases hiB : i = rowB
    · subst i
      have hBA : rowB.val ≠ rowA.val := by
        intro h
        exact hsame h.symm
      have hrowB_after :
          rowB.val < (rows.setIfInBounds rowA.val rows[rowB.val]!).size := by
        simpa [Array.size_setIfInBounds] using hrowB
      calc
        getEntry (swapRowsArray rows rowA.val rowB.val) rowB.val j.val =
            getEntry rows rowA.val j.val := by
              simp [swapRowsArray, hsame, getEntry, Array.set!_eq_setIfInBounds]
              rw [array_getElem!_setIfInBounds_same
                (xs := rows.setIfInBounds rowA.val rows[rowB.val]!) hrowB_after]
        _ = M[rowA][j] := hentry rowA j
        _ = (rowSwap M rowA rowB)[rowB][j] := by
              rw [rowSwap_get]
              simp
    · by_cases hiA : i = rowA
      · subst i
        have hAB : rowA.val ≠ rowB.val := by
          intro h
          exact hsame h
        calc
          getEntry (swapRowsArray rows rowA.val rowB.val) rowA.val j.val =
              getEntry rows rowB.val j.val := by
                simp [swapRowsArray, hsame, getEntry, Array.set!_eq_setIfInBounds]
                rw [array_getElem!_setIfInBounds_ne
                  (xs := rows.setIfInBounds rowA.val rows[rowB.val]!) hAB]
                exact congrArg (fun row => row[j.val]!)
                  (array_getElem!_setIfInBounds_same
                    (xs := rows) hrowA rows[rowB.val]!)
          _ = M[rowB][j] := hentry rowB j
          _ = (rowSwap M rowA rowB)[rowA][j] := by
                rw [rowSwap_get]
                simp [hiB]
      · have hiA_val : i.val ≠ rowA.val := by
          intro h
          exact hiA (Fin.ext h)
        have hiB_val : i.val ≠ rowB.val := by
          intro h
          exact hiB (Fin.ext h)
        calc
          getEntry (swapRowsArray rows rowA.val rowB.val) i.val j.val =
              getEntry rows i.val j.val := by
                simp [swapRowsArray, hsame, getEntry, Array.set!_eq_setIfInBounds]
                rw [array_getElem!_setIfInBounds_ne
                  (xs := rows.setIfInBounds rowA.val rows[rowB.val]!) hiB_val]
                exact congrArg (fun row => row[j.val]!)
                  (array_getElem!_setIfInBounds_ne
                    (xs := rows) hiA_val rows[rowB.val]!)
          _ = M[i][j] := hentry i j
          _ = (rowSwap M rowA rowB)[i][j] := by
                rw [rowSwap_get]
                simp [hiA, hiB]

private def findPivotArrayAux
    (rows : Array (Array Int)) (n col start fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if start < n then
        if getEntry rows start col = 0 then
          findPivotArrayAux rows n col (start + 1) fuel
        else
          some start
      else
        none

private def findPivotArray? (rows : Array (Array Int)) (n col start : Nat) :
    Option Nat :=
  findPivotArrayAux rows n col start (n - start)

private theorem findPivotArrayAux_matrixToRows (M : Matrix Int n n)
    (col : Fin n) (start fuel : Nat) :
    findPivotArrayAux (matrixToRows M) n col.val start fuel =
      (findPivotAux M col start fuel).map Fin.val := by
  induction fuel generalizing start with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [findPivotArrayAux, findPivotAux]
      by_cases hstart : start < n
      · simp [hstart]
        have hentry :
            getEntry (matrixToRows M) start col.val =
              M[(⟨start, hstart⟩ : Fin n)][col] := by
          simpa [getEntry] using
            getEntry_matrixToRows M (⟨start, hstart⟩ : Fin n) col
        rw [hentry]
        by_cases hpivotNat : M[start][col.val] = 0
        · have hpivot : M[(⟨start, hstart⟩ : Fin n)][col] = 0 := by
            simpa using hpivotNat
          simp [hpivotNat, ih]
        · have hpivot : M[(⟨start, hstart⟩ : Fin n)][col] ≠ 0 := by
            simpa using hpivotNat
          simp [hpivotNat]
      · simp [hstart]

private theorem findPivotArray?_matrixToRows (M : Matrix Int n n)
    (col : Fin n) (start : Nat) :
    findPivotArray? (matrixToRows M) n col.val start =
      (findPivot? M col start).map Fin.val := by
  simp [findPivotArray?, findPivot?, findPivotArrayAux_matrixToRows]

private theorem findPivotArrayAux_matches (rows : Array (Array Int))
    (M : Matrix Int n n) (col : Fin n) (start fuel : Nat)
    (hentry : ∀ i : Fin n, getEntry rows i.val col.val = M[i][col]) :
    findPivotArrayAux rows n col.val start fuel =
      (findPivotAux M col start fuel).map Fin.val := by
  induction fuel generalizing start with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [findPivotArrayAux, findPivotAux]
      by_cases hstart : start < n
      · simp [hstart]
        have hentry_start :
            getEntry rows start col.val =
              M[(⟨start, hstart⟩ : Fin n)][col] :=
          hentry ⟨start, hstart⟩
        rw [hentry_start]
        by_cases hpivotNat : M[start][col.val] = 0
        · have hpivot : M[(⟨start, hstart⟩ : Fin n)][col] = 0 := by
            simpa using hpivotNat
          simp [hpivotNat, ih]
        · simp [hpivotNat]
      · simp [hstart]

private theorem findPivotArray?_matches (rows : Array (Array Int))
    (M : Matrix Int n n) (col : Fin n) (start : Nat)
    (hentry : ∀ i : Fin n, getEntry rows i.val col.val = M[i][col]) :
    findPivotArray? rows n col.val start =
      (findPivot? M col start).map Fin.val := by
  simp [findPivotArray?, findPivot?, findPivotArrayAux_matches rows M col start (n - start)
    hentry]

private def stepArray (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int) :
    Array (Array Int) :=
  (Array.range n).map fun i =>
    (Array.range n).map fun j =>
      if k < i ∧ k < j then
        exactDiv (pivot * getEntry rows i j - getEntry rows i k * getEntry rows k j)
          prevPivot
      else if k < i ∧ j = k then
        0
      else
        getEntry rows i j

private theorem getEntry_rangeMap₂ (f : Nat → Nat → Int) (i j : Fin n) :
    getEntry ((Array.range n).map fun row => (Array.range n).map fun col => f row col)
      i.val j.val = f i.val j.val := by
  simp [getEntry]

private theorem getEntry_stepArray_matches
    (rows : Array (Array Int)) (M : Matrix Int n n)
    (hentry : ∀ i j : Fin n, getEntry rows i.val j.val = M[i][j])
    (k : Nat) (pivot prevPivot : Int) (i j : Fin n) :
    getEntry (stepArray rows n k pivot prevPivot) i.val j.val =
      (stepMatrix M k pivot prevPivot)[i][j] := by
  unfold stepArray
  rw [getEntry_rangeMap₂]
  by_cases htrail : k < i.val ∧ k < j.val
  · have hcol₁ :
        getEntry rows i.val k =
          M[i][(⟨k, Nat.lt_trans htrail.1 i.isLt⟩ : Fin n)] := by
      simpa using hentry i (⟨k, Nat.lt_trans htrail.1 i.isLt⟩ : Fin n)
    have hrow₁ :
        getEntry rows k j.val =
          M[(⟨k, Nat.lt_trans htrail.2 j.isLt⟩ : Fin n)][j] := by
      simpa using hentry (⟨k, Nat.lt_trans htrail.2 j.isLt⟩ : Fin n) j
    have hij := hentry i j
    rw [if_pos htrail]
    rw [stepMatrix_update_eq M k pivot prevPivot i j htrail.1 htrail.2]
    rw [hij, hcol₁, hrow₁]
  · by_cases hcol : k < i.val ∧ j.val = k
    · rw [if_neg htrail, if_pos hcol]
      exact (stepMatrix_pivot_col_below M k pivot prevPivot i j hcol.1 hcol.2).symm
    · have hij := hentry i j
      rw [if_neg htrail, if_neg hcol]
      rw [stepMatrix_eq_of_not_update M k pivot prevPivot i j htrail hcol]
      exact hij

private theorem stepArray_size (rows : Array (Array Int)) (n k : Nat)
    (pivot prevPivot : Int) :
    (stepArray rows n k pivot prevPivot).size = n := by
  simp [stepArray]

private def pivotArrayLoop (n fuel : Nat) (state : BareissArrayState) :
    BareissArrayState :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if state.step + 1 < n then
        let k := state.step
        let (rows, swaps) :=
          if getEntry state.matrix k k = 0 then
            match findPivotArray? state.matrix n k (state.step + 1) with
            | some pivot => (swapRowsArray state.matrix k pivot, state.rowSwaps + 1)
            | none => (state.matrix, state.rowSwaps)
          else
            (state.matrix, state.rowSwaps)
        let pivot := getEntry rows k k
        if pivot = 0 then
          { state with matrix := rows, rowSwaps := swaps, singularStep := some state.step }
        else
          let next : BareissArrayState :=
            { step := state.step + 1
              matrix := stepArray rows n state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := swaps
              singularStep := none }
          pivotArrayLoop n fuel next
      else
        state

/-- Bareiss elimination with row pivoting. If a column has no nonzero pivot,
the elimination aborts and the determinant is zero. -/
def pivotLoop (fuel : Nat) (state : BareissState n) : BareissState n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let (M, swaps) :=
          if state.matrix[k][k] = 0 then
            match findPivot? state.matrix k (state.step + 1) with
            | some pivot => (rowSwap state.matrix k pivot, state.rowSwaps + 1)
            | none => (state.matrix, state.rowSwaps)
          else
            (state.matrix, state.rowSwaps)
        let pivot := M[k][k]
        if hp : pivot = 0 then
          { state with matrix := M, rowSwaps := swaps, singularStep := some state.step }
        else
          let next : BareissState n :=
            { step := state.step + 1
              matrix := stepMatrix M state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := swaps
              singularStep := none }
          pivotLoop fuel next
      else
        state

/-- With zero fuel, the row-pivoted Bareiss loop returns its input state. -/
theorem pivotLoop_zero_fuel (state : BareissState n) :
    pivotLoop 0 state = state := by
  rfl

/-- If the current step is already past the last update step, the row-pivoted
Bareiss loop returns its input state. -/
theorem pivotLoop_done (fuel : Nat) (state : BareissState n)
    (hDone : ¬ state.step + 1 < n) :
    pivotLoop (fuel + 1) state = state := by
  simp [pivotLoop, hDone]

/-- If the current row-pivoted Bareiss pivot is already nonzero, one loop
iteration applies `stepMatrix`, advances the step, and recurses without
changing the row-swap counter. -/
theorem pivotLoop_regular_branch_no_swap (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    pivotLoop (fuel + 1) state =
      pivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } := by
  simp [pivotLoop, hDone, hp]

/-- If the current pivot is zero and pivot search finds no replacement row,
the row-pivoted Bareiss loop records a singular step. -/
theorem pivotLoop_singular_branch_no_pivot (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0)
    (hfind :
      findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = none) :
    pivotLoop (fuel + 1) state =
      { state with singularStep := some state.step } := by
  simp [pivotLoop, hDone, hp0, hfind]

/-- If the current pivot is zero, pivot search finds a replacement row, and
the swapped pivot is nonzero, one loop iteration swaps rows, applies
`stepMatrix`, advances the step, increments the row-swap counter, and recurses. -/
theorem pivotLoop_regular_branch_swap (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp0 : state.matrix[state.step][state.step] = 0) {pivot : Fin n}
    (hfind :
      findPivot? state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        (state.step + 1) = some pivot)
    (hp :
      (rowSwap state.matrix
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
        pivot)[state.step][state.step] ≠ 0) :
    pivotLoop (fuel + 1) state =
      pivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix
            (rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)
            state.step
            ((rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)[state.step][state.step])
            state.prevPivot
          prevPivot :=
            (rowSwap state.matrix
              (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩ : Fin n)
              pivot)[state.step][state.step]
          rowSwaps := state.rowSwaps + 1
          singularStep := none } := by
  simp [pivotLoop, hDone, hp0, hfind, hp]

private def bareissArrayState (M : Matrix Int n n) : BareissArrayState :=
  let state := pivotLoop n
    { step := 0
      matrix := M
      prevPivot := 1
      rowSwaps := 0
      singularStep := none }
  { step := state.step
    matrix := matrixToRows state.matrix
    prevPivot := state.prevPivot
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

private def arraySign (rowSwaps : Nat) : Int :=
  if rowSwaps % 2 = 0 then 1 else -1

private def arrayLastDiag? (rows : Array (Array Int)) (n : Nat) : Option Int :=
  match n with
  | 0 => none
  | k + 1 => some (getEntry rows k k)

private def bareissArrayDet (state : BareissArrayState) (n : Nat) : Int :=
  match state.singularStep with
  | some _ => 0
  | none =>
      match arrayLastDiag? state.matrix n with
      | some d => arraySign state.rowSwaps * d
      | none => arraySign state.rowSwaps

/-- Package a Bareiss state as public elimination data. -/
def finish (state : BareissState n) : BareissData n :=
  { matrix := state.matrix
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- Bareiss elimination without pivoting. A zero pivot aborts and records the
singular step. -/
def noPivotLoop (fuel : Nat) (state : BareissState n) : BareissState n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let pivot := state.matrix[k][k]
        if hp : pivot = 0 then
          { state with singularStep := some state.step }
        else
          let next : BareissState n :=
            { step := state.step + 1
              matrix := stepMatrix state.matrix state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := state.rowSwaps
              singularStep := none }
          noPivotLoop fuel next
      else
        state

/-- With zero fuel, the no-pivot Bareiss loop returns its input state. -/
theorem noPivotLoop_zero_fuel (state : BareissState n) :
    noPivotLoop 0 state = state := by
  rfl

/-- If the current step is already past the last update step, the no-pivot loop
returns its input state. -/
theorem noPivotLoop_done (fuel : Nat) (state : BareissState n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoop (fuel + 1) state = state := by
  simp [noPivotLoop, hDone]

/-- If the no-pivot loop sees a zero pivot before completion, it records the
current step as singular. -/
theorem noPivotLoop_singular_branch (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] = 0) :
    noPivotLoop (fuel + 1) state = { state with singularStep := some state.step } := by
  simp [noPivotLoop, hDone, hp]

/-- If the current no-pivot Bareiss pivot is nonzero, one loop iteration applies
`stepMatrix`, advances the step, and recurses on the remaining fuel. -/
theorem noPivotLoop_regular_branch (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    noPivotLoop (fuel + 1) state =
      noPivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } := by
  simp [noPivotLoop, hDone, hp]

/-- Entries in rows already processed, or in columns strictly before the current
step, are unchanged by subsequent no-pivot loop iterations. -/
theorem noPivotLoop_matrix_entry_of_row_le_or_col_lt (fuel : Nat)
    (state : BareissState n) (i j : Fin n)
    (hfixed : i.val ≤ state.step ∨ j.val < state.step) :
    (noPivotLoop fuel state).matrix[i][j] = state.matrix[i][j] := by
  induction fuel generalizing state with
  | zero =>
      simp [noPivotLoop]
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · simp [noPivotLoop_singular_branch fuel state hDone hp]
        · rw [noPivotLoop_regular_branch fuel state hDone]
          · let next : BareissState n :=
              { step := state.step + 1
                matrix := stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }
            change (noPivotLoop fuel next).matrix[i][j] = state.matrix[i][j]
            have hnext : i.val ≤ next.step ∨ j.val < next.step := by
              cases hfixed with
              | inl hi =>
                  exact Or.inl (Nat.le_trans hi (Nat.le_succ state.step))
              | inr hj =>
                  exact Or.inr (Nat.lt_trans hj (Nat.lt_succ_self state.step))
            rw [ih next hnext]
            dsimp [next]
            apply stepMatrix_eq_of_not_update
            · intro htrail
              cases hfixed with
              | inl hi =>
                  exact Nat.not_lt_of_ge hi htrail.1
              | inr hj =>
                  exact Nat.not_lt_of_ge (Nat.le_of_lt hj) htrail.2
            · intro hcol
              cases hfixed with
              | inl hi =>
                  exact Nat.not_lt_of_ge hi hcol.1
              | inr hj =>
                  exact Nat.ne_of_lt hj hcol.2
          · simpa [k] using hp
      · simp [noPivotLoop_done fuel state hDone]

/-- Diagonal entries at or before the current step are unchanged by subsequent
no-pivot loop iterations. -/
theorem noPivotLoop_diag_of_le_step (fuel : Nat) (state : BareissState n)
    (i : Fin n) (hi : i.val ≤ state.step) :
    (noPivotLoop fuel state).matrix[i][i] = state.matrix[i][i] :=
  noPivotLoop_matrix_entry_of_row_le_or_col_lt fuel state i i (Or.inl hi)

/-- The no-pivot loop never changes the row-swap counter. -/
theorem noPivotLoop_rowSwaps (fuel : Nat) (state : BareissState n) :
    (noPivotLoop fuel state).rowSwaps = state.rowSwaps := by
  induction fuel generalizing state with
  | zero =>
      simp [noPivotLoop]
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · simp [noPivotLoop_singular_branch fuel state hDone hp]
        · rw [noPivotLoop_regular_branch fuel state hDone]
          · let next : BareissState n :=
              { step := state.step + 1
                matrix := stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }
            change (noPivotLoop fuel next).rowSwaps = state.rowSwaps
            rw [ih next]
          · simpa [k] using hp
      · simp [noPivotLoop_done fuel state hDone]

/-- Initial state used by the no-pivot Bareiss recurrence. -/
def noPivotInitialState (M : Matrix Int n n) : BareissState n :=
  { step := 0
    matrix := M
    prevPivot := 1
    rowSwaps := 0
    singularStep := none }

/-- Run the no-pivot Bareiss recurrence and return the final elimination data. -/
def bareissNoPivotData (M : Matrix Int n n) : BareissData n :=
  finish <| noPivotLoop n (noPivotInitialState M)

/-- Determinant computed by the no-pivot Bareiss recurrence. -/
def bareissNoPivot (M : Matrix Int n n) : Int :=
  (bareissNoPivotData M).det

/-- Run the row-pivoted Bareiss elimination and return the final elimination
data together with the swap/sign bookkeeping. -/
def bareissData (M : Matrix Int n n) : BareissData n :=
  let state := bareissArrayState M
  { matrix := rowsToMatrix state.matrix n
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- The packaged row-pivoted Bareiss data is exactly the structured pivot loop
state finished into public determinant data. This is the bridge consumed by the
Mathlib determinant proof; array storage is erased by `rowsToMatrix`. -/
theorem bareissData_eq_finish_pivotLoop (M : Matrix Int n n) :
    bareissData M = finish (pivotLoop n (noPivotInitialState M)) := by
  simp [bareissData, bareissArrayState, noPivotInitialState, finish,
    rowsToMatrix_matrixToRows]

/-- Determinant computed by the row-pivoted Bareiss algorithm. -/
def bareiss (M : Matrix Int n n) : Int :=
  let state := bareissArrayState M
  bareissArrayDet state n

/-- The public row-pivoted determinant agrees with the determinant encoded by
`bareissData`. This separates executable array evaluation from the packaged
elimination data used by correctness proofs. -/
theorem bareiss_eq_bareissData_det (M : Matrix Int n n) :
    bareiss M = (bareissData M).det := by
  cases n with
  | zero =>
      simp [bareiss, bareissData, bareissArrayDet, BareissData.det,
        arrayLastDiag?, BareissData.lastDiag?, arraySign, BareissData.sign]
      rfl
  | succ k =>
      simp [bareiss, bareissData, bareissArrayDet, BareissData.det,
        arrayLastDiag?, BareissData.lastDiag?, rowsToMatrix, Matrix.ofFn,
        arraySign, BareissData.sign]
      rfl

/-- The Bareiss determinant agrees with the generic determinant. -/
theorem bareiss_eq_det (M : Matrix Int n n) :
    bareiss M = det M := by
  sorry

end Matrix
end Hex
