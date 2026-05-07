import HexMatrix.RREF

/-!
Core Gram-Schmidt basis and coefficient definitions for `hex-gram-schmidt`.

This module provides executable Gram-Schmidt basis and coefficient
constructions over the dense `Hex.Matrix` representation. Integer inputs are
cast to rationals before applying Gram-Schmidt; rational inputs operate
directly on the ambient matrix. It also states the structural theorems used by
downstream lattice and reduction code, including the prefix-span invariance
surface consumed by later LLL work.
-/
namespace Hex

namespace GramSchmidt

/-- Coefficient of the orthogonal projection of `row` onto `basisRow`.
When the basis row has zero norm we use `0`, which matches the degenerate
case of Gram-Schmidt where the corresponding projection term vanishes. -/
private def projectionCoeff (row basisRow : Vector Rat m) : Rat :=
  let denom := Matrix.dot basisRow basisRow
  if denom = 0 then 0 else Matrix.dot row basisRow / denom

/-- Subtract the projection of `row` onto `basisRow`. -/
private def subtractProjection (row basisRow : Vector Rat m) : Vector Rat m :=
  row - projectionCoeff row basisRow • basisRow

private theorem dot_sub_smul_zero_of_dot_zero (row other basis : Vector Rat m) (c : Rat)
    (hrow : Matrix.dot row basis = 0) (hother : Matrix.dot other basis = 0) :
    Matrix.dot (row - c • other) basis = 0 := by
  rw [Matrix.dot_sub_smul_rat, hrow, hother]
  grind

private theorem dot_subtractProjection (row basisRow target : Vector Rat m) :
    Matrix.dot (subtractProjection row basisRow) target =
      Matrix.dot row target - projectionCoeff row basisRow * Matrix.dot basisRow target := by
  simp [subtractProjection, Matrix.dot_sub_smul_rat]

private theorem subtractProjection_add_projection (row basisRow : Vector Rat m) :
    row = subtractProjection row basisRow + projectionCoeff row basisRow • basisRow := by
  apply Vector.ext
  intro k hk
  change row[k] =
    (subtractProjection row basisRow + projectionCoeff row basisRow • basisRow)[k]
  rw [Vector.getElem_add, subtractProjection, Vector.getElem_sub, Vector.getElem_smul]
  grind

private theorem dot_subtractProjection_zero_of_dot_zero
    (row basisRow target : Vector Rat m)
    (hrow : Matrix.dot row target = 0) (hbasis : Matrix.dot basisRow target = 0) :
    Matrix.dot (subtractProjection row basisRow) target = 0 := by
  rw [dot_subtractProjection, hrow, hbasis]
  grind

private theorem dot_subtractProjection_self_zero (row basisRow : Vector Rat m)
    (hnorm : Matrix.dot basisRow basisRow ≠ 0) :
    Matrix.dot (subtractProjection row basisRow) basisRow = 0 := by
  rw [dot_subtractProjection]
  simp [projectionCoeff, hnorm]
  grind

private theorem projectionCoeff_sub_smul_self
    (row basisRow : Vector Rat m) (c : Rat)
    (hnorm : Matrix.dot basisRow basisRow ≠ 0) :
    projectionCoeff (row - c • basisRow) basisRow =
      projectionCoeff row basisRow - c := by
  simp [projectionCoeff, Matrix.dot_sub_smul_rat, hnorm]
  grind

private theorem projectionCoeff_sub_smul
    (row other basisRow : Vector Rat m) (c : Rat)
    (hnorm : Matrix.dot basisRow basisRow ≠ 0) :
    projectionCoeff (row - c • other) basisRow =
      projectionCoeff row basisRow - c * projectionCoeff other basisRow := by
  simp [projectionCoeff, Matrix.dot_sub_smul_rat, hnorm]
  grind

private theorem rat_mul_self_nonneg (x : Rat) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using (Lean.Grind.OrderedRing.sq_nonneg (a := x))

private theorem rat_mul_self_eq_zero_of_nonpos (x : Rat) (h : x * x ≤ 0) : x = 0 := by
  have hnonneg : 0 ≤ x * x := rat_mul_self_nonneg x
  have hsquare : x * x = 0 := by
    grind
  grind

private theorem foldl_dot_self_start_le (xs : List (Fin m)) (v : Vector Rat m)
    (acc : Rat) (hacc : 0 ≤ acc) :
    acc ≤ xs.foldl (fun sum i => sum + v[i] * v[i]) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hsq : 0 ≤ v[i] * v[i] := rat_mul_self_nonneg v[i]
      have hnext : 0 ≤ acc + v[i] * v[i] := by grind
      exact Rat.le_trans (by grind) (ih (acc := acc + v[i] * v[i]) hnext)

private theorem foldl_dot_self_eq_zero_of_mem (xs : List (Fin m)) (v : Vector Rat m)
    (acc : Rat) (hacc : 0 ≤ acc)
    (hzero : xs.foldl (fun sum i => sum + v[i] * v[i]) acc = 0) :
    ∀ i ∈ xs, v[i] = 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons head rest ih =>
      intro i hi
      simp only [List.mem_cons] at hi
      have hsq : 0 ≤ v[head] * v[head] := rat_mul_self_nonneg v[head]
      have hnext_nonneg : 0 ≤ acc + v[head] * v[head] := by grind
      have hnext_le_zero :
          acc + v[head] * v[head] ≤ 0 := by
        have hle :=
          foldl_dot_self_start_le (xs := rest) (v := v)
            (acc := acc + v[head] * v[head]) hnext_nonneg
        have hzero' :
            rest.foldl (fun sum i => sum + v[i] * v[i])
              (acc + v[head] * v[head]) = 0 := by
          simpa using hzero
        rw [hzero'] at hle
        exact hle
      have hnext_zero : acc + v[head] * v[head] = 0 := by grind
      have hhead_zero : v[head] = 0 := by
        apply rat_mul_self_eq_zero_of_nonpos
        grind
      cases hi with
      | inl h =>
          subst i
          exact hhead_zero
      | inr h =>
          exact ih (acc := acc + v[head] * v[head]) hnext_nonneg hzero i h

private theorem dot_self_eq_zero_get (v : Vector Rat m)
    (hzero : Matrix.dot v v = 0) (i : Fin m) :
    v[i] = 0 := by
  have hmem : i ∈ List.finRange m := by
    simp
  exact foldl_dot_self_eq_zero_of_mem (xs := List.finRange m) (v := v)
    (acc := 0) (by decide) (by simpa [Matrix.dot, Hex.Vector.dotProduct] using hzero) i hmem

private theorem dot_zero_of_dot_self_zero (row v : Vector Rat m)
    (hzero : Matrix.dot v v = 0) :
    Matrix.dot row v = 0 := by
  unfold Matrix.dot Hex.Vector.dotProduct
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [dot_self_eq_zero_get v hzero i]
      rw [show row[i] * (0 : Rat) = 0 by grind]
      rw [show (0 : Rat) + 0 = 0 by grind]
      change xs.foldl (fun acc i => acc + row[i] * v[i]) 0 = 0
      exact ih

private theorem dot_subtractProjection_self_zero_of_dot_self_zero
    (row basisRow : Vector Rat m)
    (hnorm : Matrix.dot basisRow basisRow = 0) :
    Matrix.dot (subtractProjection row basisRow) basisRow = 0 := by
  exact dot_zero_of_dot_self_zero (row := subtractProjection row basisRow)
    (v := basisRow) hnorm

private theorem foldl_dot_comm_rat (xs : List (Fin m)) (u v : Vector Rat m)
    (accU accV : Rat) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind

private theorem dot_comm_rat (u v : Vector Rat m) :
    Matrix.dot u v = Matrix.dot v u := by
  simpa [Matrix.dot, Hex.Vector.dotProduct] using
    foldl_dot_comm_rat (xs := List.finRange m) (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

private theorem projectionCoeff_subtractProjection_eq_of_dot_zero
    (row otherBasisRow basisRow : Vector Rat m)
    (horth : Matrix.dot otherBasisRow basisRow = 0) :
    projectionCoeff (subtractProjection row otherBasisRow) basisRow =
      projectionCoeff row basisRow := by
  by_cases hnorm : Matrix.dot basisRow basisRow = 0
  · simp [projectionCoeff, hnorm]
  · simp [projectionCoeff, dot_subtractProjection, horth, hnorm]
    grind

/-- Reduce a row against the previously constructed orthogonal basis rows. -/
private def reduceAgainstBasis (basisRev : List (Vector Rat m)) (row : Vector Rat m) :
    Vector Rat m :=
  basisRev.foldl subtractProjection row

private theorem dot_reduceAgainstBasis_zero_of_forall_dot_zero
    (basisRev : List (Vector Rat m)) (row target : Vector Rat m)
    (horth : ∀ basisRow ∈ basisRev, Matrix.dot basisRow target = 0) :
    Matrix.dot (reduceAgainstBasis basisRev row) target = Matrix.dot row target := by
  induction basisRev generalizing row with
  | nil =>
      simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      change Matrix.dot (reduceAgainstBasis rest (subtractProjection row basisRow)) target =
        Matrix.dot row target
      rw [ih]
      · rw [dot_subtractProjection, horth basisRow (by simp)]
        grind
      · intro laterBasisRow hlater
        exact horth laterBasisRow (by simp [hlater])

private theorem dot_reduceAgainstBasis_zero_of_dot_zero
    (basisRev : List (Vector Rat m)) (row target : Vector Rat m)
    (hrow : Matrix.dot row target = 0)
    (horth : ∀ basisRow ∈ basisRev, Matrix.dot basisRow target = 0) :
    Matrix.dot (reduceAgainstBasis basisRev row) target = 0 := by
  rw [dot_reduceAgainstBasis_zero_of_forall_dot_zero basisRev row target horth, hrow]

private theorem dot_reduceAgainstBasis_of_mem
    (basisRev : List (Vector Rat m)) (row basisRow : Vector Rat m)
    (hmem : basisRow ∈ basisRev)
    (horth : basisRev.Pairwise (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0)) :
    Matrix.dot (reduceAgainstBasis basisRev row) basisRow = 0 := by
  induction basisRev generalizing row with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      by_cases hhead : head = basisRow
      · subst basisRow
        apply dot_reduceAgainstBasis_zero_of_dot_zero
        · by_cases hnorm : Matrix.dot head head = 0
          · exact dot_subtractProjection_self_zero_of_dot_self_zero row head hnorm
          · exact dot_subtractProjection_self_zero row head hnorm
        · intro later hlater
          exact (List.rel_of_pairwise_cons horth hlater).2
      · have htail : basisRow ∈ rest := by
          have hneq : basisRow ≠ head := by
            intro hb
            exact hhead hb.symm
          simp [hneq] at hmem
          exact hmem
        apply ih
        · exact htail
        · exact List.Pairwise.of_cons horth

private theorem projectionCoeff_reduceAgainstBasis_eq_of_forall_dot_zero
    (basisRev : List (Vector Rat m)) (row basisRow : Vector Rat m)
    (horth : ∀ otherBasisRow ∈ basisRev, Matrix.dot otherBasisRow basisRow = 0) :
    projectionCoeff (reduceAgainstBasis basisRev row) basisRow =
      projectionCoeff row basisRow := by
  induction basisRev generalizing row with
  | nil =>
      simp [reduceAgainstBasis]
  | cons otherBasisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      change
        projectionCoeff (reduceAgainstBasis rest (subtractProjection row otherBasisRow)) basisRow =
          projectionCoeff row basisRow
      rw [ih]
      · exact projectionCoeff_subtractProjection_eq_of_dot_zero
          (row := row) (otherBasisRow := otherBasisRow) (basisRow := basisRow)
          (horth otherBasisRow (by simp))
      · intro laterBasisRow hlater
        exact horth laterBasisRow (by simp [hlater])

private def projectionCombination (row : Vector Rat m) (basisRev : List (Vector Rat m))
    (acc : Vector Rat m) : Vector Rat m :=
  basisRev.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) acc

private theorem projectionCombination_congr
    (basisRev : List (Vector Rat m)) (row row' acc : Vector Rat m)
    (hcoeff :
      ∀ basisRow ∈ basisRev, projectionCoeff row basisRow = projectionCoeff row' basisRow) :
    projectionCombination row basisRev acc = projectionCombination row' basisRev acc := by
  induction basisRev generalizing acc with
  | nil =>
      simp [projectionCombination]
  | cons basisRow rest ih =>
      simp only [projectionCombination, List.foldl_cons]
      have hhead := hcoeff basisRow (by simp)
      rw [hhead]
      exact ih (acc := acc + projectionCoeff row' basisRow • basisRow)
        (by
          intro laterBasisRow hlater
          exact hcoeff laterBasisRow (by simp [hlater]))

private theorem subtractProjection_add_projection_with_acc
    (row basisRow acc : Vector Rat m) :
    subtractProjection row basisRow +
        (acc + projectionCoeff row basisRow • basisRow) =
      row + acc := by
  apply Vector.ext
  intro k hk
  have hrow := subtractProjection_add_projection (row := row) (basisRow := basisRow)
  have hrowk := congrArg (fun v : Vector Rat m => v[k]) hrow
  simp only [Vector.getElem_add, Vector.getElem_smul] at hrowk ⊢
  grind

private theorem reduceAgainstBasis_reconstruction_acc
    (basisRev : List (Vector Rat m)) (row acc : Vector Rat m)
    (horth : basisRev.Pairwise (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0)) :
    reduceAgainstBasis basisRev row + projectionCombination row basisRev acc =
      row + acc := by
  induction basisRev generalizing row acc with
  | nil =>
      simp [reduceAgainstBasis, projectionCombination]
  | cons basisRow rest ih =>
      simp only [reduceAgainstBasis, List.foldl_cons, projectionCombination]
      change
        reduceAgainstBasis rest (subtractProjection row basisRow) +
            projectionCombination row rest
              (acc + projectionCoeff row basisRow • basisRow) =
          row + acc
      rw [← projectionCombination_congr
        (basisRev := rest)
        (row := subtractProjection row basisRow)
        (row' := row)
        (acc := acc + projectionCoeff row basisRow • basisRow)]
      · rw [ih (row := subtractProjection row basisRow)
          (acc := acc + projectionCoeff row basisRow • basisRow)
          (horth := List.Pairwise.of_cons horth)]
        exact subtractProjection_add_projection_with_acc row basisRow acc
      · intro laterBasisRow hlater
        exact projectionCoeff_subtractProjection_eq_of_dot_zero
          (row := row) (otherBasisRow := basisRow) (basisRow := laterBasisRow)
          (List.rel_of_pairwise_cons horth hlater).1

private theorem reduceAgainstBasis_reconstruction
    (basisRev : List (Vector Rat m)) (row : Vector Rat m)
    (horth : basisRev.Pairwise (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0)) :
    row =
      reduceAgainstBasis basisRev row +
        projectionCombination row basisRev 0 := by
  have h :=
    reduceAgainstBasis_reconstruction_acc (basisRev := basisRev) (row := row)
      (acc := 0) horth
  have hzero : row + (0 : Vector Rat m) = row := by
    apply Vector.ext
    intro k hk
    simp
    grind
  rw [hzero] at h
  exact h.symm

/-- Left-to-right Gram-Schmidt orthogonalization on a list of rows. -/
private def basisRowsAux (basisRev pending : List (Vector Rat m)) : List (Vector Rat m) :=
  match pending with
  | [] => basisRev.reverse
  | row :: rows =>
      let next := reduceAgainstBasis basisRev row
      basisRowsAux (next :: basisRev) rows

/-- Left-to-right Gram-Schmidt orthogonalization on a matrix's rows. -/
private def basisRows (rows : List (Vector Rat m)) : List (Vector Rat m) :=
  basisRowsAux [] rows

/-- Rebuild a matrix from its row list after Gram-Schmidt orthogonalization. -/
private def basisMatrix (b : Matrix Rat n m) : Matrix Rat n m :=
  let rows := basisRows b.toList
  Vector.ofFn fun i => rows[i.val]!

private theorem basisRowsAux_reverse_prefix (basisRev pending : List (Vector Rat m)) :
    ∃ suffix, basisRowsAux basisRev pending = basisRev.reverse ++ suffix := by
  induction pending generalizing basisRev with
  | nil =>
      exact ⟨[], by simp [basisRowsAux]⟩
  | cons row rows ih =>
      obtain ⟨suffix, hsuffix⟩ :=
        ih (GramSchmidt.reduceAgainstBasis basisRev row :: basisRev)
      refine ⟨GramSchmidt.reduceAgainstBasis basisRev row :: suffix, ?_⟩
      simp [basisRowsAux, hsuffix, List.reverse_cons, List.append_assoc]

private theorem basisRowsAux_singleton_head (row : Vector Rat m) (rows : List (Vector Rat m)) :
    (basisRowsAux [row] rows)[0]! = row := by
  obtain ⟨suffix, hsuffix⟩ := basisRowsAux_reverse_prefix [row] rows
  simp [hsuffix]

private theorem basisRowsAux_length (basisRev pending : List (Vector Rat m)) :
    (basisRowsAux basisRev pending).length = basisRev.length + pending.length := by
  induction pending generalizing basisRev with
  | nil =>
      simp [basisRowsAux]
  | cons row rows ih =>
      simpa [basisRowsAux, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (GramSchmidt.reduceAgainstBasis basisRev row :: basisRev)

private theorem basisRows_length (rows : List (Vector Rat m)) :
    (basisRows rows).length = rows.length := by
  simpa [basisRows] using basisRowsAux_length ([] : List (Vector Rat m)) rows

private theorem orthPairwise_reverse (rows : List (Vector Rat m))
    (horth : rows.Pairwise (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0)) :
    rows.reverse.Pairwise (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0) := by
  rw [List.pairwise_iff_getElem] at horth ⊢
  intro i j hirev hjrev hij
  simp [List.length_reverse] at hirev hjrev
  have hji : rows.length - 1 - j < rows.length - 1 - i := by omega
  have hxj : rows.length - 1 - j < rows.length := by omega
  have hxi : rows.length - 1 - i < rows.length := by omega
  have hrel := horth (rows.length - 1 - j) (rows.length - 1 - i) hxj hxi hji
  rw [List.getElem_reverse, List.getElem_reverse]
  exact ⟨hrel.2, hrel.1⟩

private theorem basisRowsAux_pairwise
    (basisRev pending : List (Vector Rat m))
    (horth : basisRev.Pairwise (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0)) :
    (basisRowsAux basisRev pending).Pairwise
      (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0) := by
  induction pending generalizing basisRev with
  | nil =>
      simpa [basisRowsAux] using orthPairwise_reverse basisRev horth
  | cons row rows ih =>
      apply ih
      apply List.Pairwise.cons
      · intro basisRow hmem
        constructor
        · exact dot_reduceAgainstBasis_of_mem basisRev row basisRow hmem horth
        · rw [dot_comm_rat]
          exact dot_reduceAgainstBasis_of_mem basisRev row basisRow hmem horth
      · exact horth

private theorem basisRows_pairwise (rows : List (Vector Rat m)) :
    (basisRows rows).Pairwise (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0) := by
  simpa [basisRows] using
    basisRowsAux_pairwise ([] : List (Vector Rat m)) rows (by simp)

private theorem basisMatrix_row_eq_basisRows_get!
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    (basisMatrix b).row ⟨i, hi⟩ = (basisRows b.toList)[i]! := by
  simp [basisMatrix, Matrix.row]

private theorem basisRows_get!_dot_eq_zero
    (b : Matrix Rat n m) (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Matrix.dot (basisRows b.toList)[i]! (basisRows b.toList)[j]! = 0 := by
  let rows := basisRows b.toList
  have hlen : rows.length = n := by
    simp [rows, basisRows_length]
  have hirows : i < rows.length := by simpa [hlen] using hi
  have hjrows : j < rows.length := by simpa [hlen] using hj
  have hpair : rows.Pairwise (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0) := by
    simpa [rows] using basisRows_pairwise (rows := b.toList)
  have hget_i : rows.get ⟨i, hirows⟩ = rows[i]! := by
    simp [hirows]
  have hget_j : rows.get ⟨j, hjrows⟩ = rows[j]! := by
    simp [hjrows]
  by_cases hlt : i < j
  · have hrel :=
      (List.pairwise_iff_get.1 hpair) ⟨i, hirows⟩ ⟨j, hjrows⟩ (by simpa using hlt)
    rw [← hget_i, ← hget_j]
    exact hrel.1
  · have hji : j < i := by
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hij h.symm)
    have hrel :=
      (List.pairwise_iff_get.1 hpair) ⟨j, hjrows⟩ ⟨i, hirows⟩ (by simpa using hji)
    rw [← hget_i, ← hget_j]
    exact hrel.2

private theorem basisRows_head (b : Matrix Rat n m) (hn : 0 < n) :
    (basisRows b.toList)[0]! = b[0] := by
  have hlen : b.toList.length = n := by simp
  cases hrows : b.toList with
  | nil =>
      simp [hrows] at hlen
      omega
  | cons row rows =>
      have hrow : row = b[0] := by
        have hget := Vector.getElem_toList (xs := b) (i := 0) (h := by simpa [hlen] using hn)
        simpa [hrows] using hget
      simpa [basisRows, basisRowsAux, reduceAgainstBasis, hrows, hrow] using
        basisRowsAux_singleton_head (row := b[0]) (rows := rows)

/-- Gram-Schmidt coefficient matrix for an already-cast rational input. -/
private def coeffMatrix (rows basis : Matrix Rat n m) : Matrix Rat n n :=
  Matrix.ofFn fun i j =>
    if hlt : j.val < i.val then
      projectionCoeff rows[i] basis[j]
    else if i = j then
      1
    else
      0

/-- Access a dense matrix entry by row and column indices. -/
def entry (M : Matrix R n m) (i : Fin n) (j : Fin m) : R :=
  (M.row i)[j]

/-- Cast an integer matrix into the rational matrix space used by
Gram-Schmidt. -/
private def castIntMatrix (b : Matrix Int n m) : Matrix Rat n m :=
  Vector.map (fun row => Vector.map (fun x : Int => (x : Rat)) row) b

/-- The prefix combination term used in the decomposition theorem shape. -/
def prefixCombination (coeffs : Matrix Rat n n) (basis : Matrix Rat n m) (i : Nat) (hi : i < n) :
    Vector Rat m :=
  (List.finRange i).foldl
    (fun acc j =>
      let jn : Fin n := ⟨j.val, Nat.lt_trans j.isLt hi⟩
      acc + GramSchmidt.entry coeffs ⟨i, hi⟩ jn • basis.row jn)
    0

/-- The row-prefix matrix containing rows `0` through `i`. -/
def prefixRows (M : Matrix R n m) (i : Nat) (hi : i < n) : Matrix R (i + 1) m :=
  Vector.ofFn fun j => M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hi)⟩

/-- Executable row-span membership in the first `i + 1` rows of a matrix. -/
def prefixSpan (M : Matrix Rat n m) (i : Nat) (hi : i < n) (v : Vector Rat m) : Prop :=
  ∃ c : Vector Rat (i + 1), Matrix.rowCombination (prefixRows M i hi) c = v

private theorem entry_ofFn (f : Fin n → Fin m → R) (i : Fin n) (j : Fin m) :
    entry (Matrix.ofFn f) i j = f i j := by
  simp [entry, Matrix.row, Matrix.ofFn, Vector.getElem_ofFn]

/-- Index bridge: the value at position `basisRev.length + k` of
`basisRowsAux basisRev pending` is the reduction of `pending[k]` against the
basis rows accumulated so far, which equals the reverse of the first
`basisRev.length + k` elements of the output. -/
private theorem basisRowsAux_get!_eq_reduceAgainstBasis_take
    (basisRev pending : List (Vector Rat m)) (k : Nat) (hk : k < pending.length) :
    (basisRowsAux basisRev pending)[basisRev.length + k]! =
      reduceAgainstBasis
        ((basisRowsAux basisRev pending).take (basisRev.length + k)).reverse
        pending[k]! := by
  induction pending generalizing basisRev k with
  | nil => simp at hk
  | cons row rest ih =>
    have hstep : basisRowsAux basisRev (row :: rest) =
        basisRowsAux (reduceAgainstBasis basisRev row :: basisRev) rest := rfl
    match k, hk with
    | 0, _ =>
      simp only [Nat.add_zero]
      obtain ⟨suffix, hsuffix⟩ :=
        basisRowsAux_reverse_prefix (reduceAgainstBasis basisRev row :: basisRev) rest
      rw [hstep, hsuffix]
      simp only [List.reverse_cons, List.append_assoc]
      have hlen : basisRev.length = basisRev.reverse.length := by simp
      have htake :
          (basisRev.reverse ++ ([reduceAgainstBasis basisRev row] ++ suffix)).take
              basisRev.length =
            basisRev.reverse := by
        rw [hlen]; exact List.take_append_length
      rw [htake, List.reverse_reverse]
      rw [List.getElem!_eq_getElem?_getD,
        List.getElem?_append_right (by simp)]
      simp
    | k + 1, hk =>
      have hk' : k < rest.length := by simpa using hk
      have ih' := ih (basisRev := reduceAgainstBasis basisRev row :: basisRev) (k := k) hk'
      have hidx : basisRev.length + (k + 1) =
          (reduceAgainstBasis basisRev row :: basisRev).length + k := by
        simp [List.length_cons]; omega
      rw [hstep, hidx]
      simpa [List.getElem!_cons_succ] using ih'

/-- Specialization to the public `basisRows` form. -/
private theorem basisRows_get!_eq_reduceAgainstBasis_take
    (rows : List (Vector Rat m)) (k : Nat) (hk : k < rows.length) :
    (basisRows rows)[k]! =
      reduceAgainstBasis ((basisRows rows).take k).reverse rows[k]! := by
  simpa [basisRows] using
    basisRowsAux_get!_eq_reduceAgainstBasis_take
      (basisRev := ([] : List (Vector Rat m))) (pending := rows) (k := k) hk

/-- The first `k` elements of `basisRows rows` are themselves pairwise
orthogonal — they form a Pairwise sublist. -/
private theorem basisRows_take_pairwise (rows : List (Vector Rat m)) (k : Nat) :
    ((basisRows rows).take k).Pairwise
      (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0) :=
  ((basisRows_pairwise rows).sublist (List.take_sublist k _))

/-- Pointwise foldl-with-accumulator-split for vector folds. -/
private theorem foldl_vec_acc_split_pointwise
    {α : Type _} (xs : List α) (f : α → Vector Rat m)
    (acc : Vector Rat m) (idx : Nat) (hidx : idx < m) :
    (xs.foldl (fun a x => a + f x) acc)[idx] =
      acc[idx] + (xs.foldl (fun a x => a + f x) 0)[idx] := by
  induction xs generalizing acc with
  | nil =>
      simp [Vector.getElem_zero]
      grind
  | cons x rest ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x), ih (acc := 0 + f x)]
      rw [Vector.getElem_add, Vector.getElem_add, Vector.getElem_zero]
      grind

/-- `projectionCombination` extracts the accumulator from the fold. -/
private theorem projectionCombination_acc_split
    (basisRev : List (Vector Rat m)) (row acc : Vector Rat m) :
    projectionCombination row basisRev acc =
      acc + projectionCombination row basisRev 0 := by
  apply Vector.ext
  intro idx hidx
  rw [Vector.getElem_add]
  exact foldl_vec_acc_split_pointwise basisRev (fun b => projectionCoeff row b • b) acc idx hidx

/-- `projectionCombination` of a concatenated list splits as a sum. -/
private theorem projectionCombination_append
    (l1 l2 : List (Vector Rat m)) (row : Vector Rat m) :
    projectionCombination row (l1 ++ l2) 0 =
      projectionCombination row l1 0 + projectionCombination row l2 0 := by
  show (l1 ++ l2).foldl
      (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) 0 =
    l1.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) 0 +
      l2.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) 0
  rw [List.foldl_append]
  exact projectionCombination_acc_split (basisRev := l2) (row := row)
    (acc := l1.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) 0)

/-- `projectionCombination` for a singleton list. -/
private theorem projectionCombination_singleton
    (b row : Vector Rat m) :
    projectionCombination row [b] 0 = projectionCoeff row b • b := by
  show List.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) 0 [b] =
    projectionCoeff row b • b
  simp only [List.foldl_cons, List.foldl_nil]
  apply Vector.ext
  intro idx hidx
  simp [Vector.getElem_add, Vector.getElem_zero]
  grind

/-- `projectionCombination` is invariant under list reversal. -/
private theorem projectionCombination_reverse
    (basisRev : List (Vector Rat m)) (row : Vector Rat m) :
    projectionCombination row basisRev.reverse 0 =
      projectionCombination row basisRev 0 := by
  induction basisRev with
  | nil => simp [projectionCombination]
  | cons b rest ih =>
      rw [List.reverse_cons, projectionCombination_append, ih,
        projectionCombination_singleton]
      have hsplit := projectionCombination_acc_split (basisRev := rest) (row := row)
        (acc := 0 + projectionCoeff row b • b)
      show projectionCombination row rest 0 + projectionCoeff row b • b =
        projectionCombination row (b :: rest) 0
      simp only [projectionCombination, List.foldl_cons] at hsplit ⊢
      rw [hsplit]
      apply Vector.ext
      intro idx hidx
      simp [Vector.getElem_add, Vector.getElem_zero]
      grind

/-- The k-th basis row obtained by the executable Gram-Schmidt iteration is
the input row k reduced against the previously generated basis rows in their
natural (forward) order. -/
private theorem basisRows_get!_eq_reduceAgainstBasis_forward
    (rows : List (Vector Rat m)) (k : Nat) (hk : k < rows.length) :
    rows[k]! =
      (basisRows rows)[k]! +
        projectionCombination rows[k]! ((basisRows rows).take k) 0 := by
  have hreduce :=
    basisRows_get!_eq_reduceAgainstBasis_take (rows := rows) (k := k) hk
  have hpair := basisRows_take_pairwise (rows := rows) (k := k)
  have horth := orthPairwise_reverse ((basisRows rows).take k) hpair
  have hrec :=
    reduceAgainstBasis_reconstruction
      (basisRev := ((basisRows rows).take k).reverse)
      (row := rows[k]!) horth
  rw [← hreduce] at hrec
  rw [projectionCombination_reverse] at hrec
  exact hrec

private theorem subtractProjection_zero_left (basisRow : Vector Rat m) :
    subtractProjection 0 basisRow = 0 := by
  have hdot : Matrix.dot (0 : Vector Rat m) basisRow = 0 := by
    unfold Matrix.dot Hex.Vector.dotProduct
    induction List.finRange m with
    | nil =>
        rfl
    | cons i rest ih =>
      simp only [List.foldl_cons]
      have hentry : (0 : Vector Rat m)[i] = 0 := by
        change (0 : Vector Rat m)[i.val] = 0
        rw [Vector.getElem_zero]
      rw [hentry]
      rw [show (0 : Rat) + 0 * basisRow[i] = 0 by grind]
      exact ih
  apply Vector.ext
  intro idx hidx
  by_cases hnorm : Matrix.dot basisRow basisRow = 0
  · have hcoeff : projectionCoeff 0 basisRow = 0 := by
      simp [projectionCoeff, hnorm]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_zero, Vector.getElem_smul,
      hcoeff]
    change (0 : Rat) - 0 * basisRow[idx] = 0
    grind
  · have hcoeff : projectionCoeff 0 basisRow = 0 := by
      have hzero_div : (0 : Rat) / Matrix.dot basisRow basisRow = 0 := by
        grind
      simp [projectionCoeff, hnorm, hdot, hzero_div]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_zero, Vector.getElem_smul,
      hcoeff]
    change (0 : Rat) - 0 * basisRow[idx] = 0
    grind

private theorem reduceAgainstBasis_zero_left (basisRev : List (Vector Rat m)) :
    reduceAgainstBasis basisRev 0 = 0 := by
  induction basisRev with
  | nil =>
      simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      rw [subtractProjection_zero_left]
      change reduceAgainstBasis rest 0 = 0
      exact ih

private theorem subtractProjection_eq_self_of_dot_zero
    (row basisRow : Vector Rat m) (h : Matrix.dot row basisRow = 0) :
    subtractProjection row basisRow = row := by
  apply Vector.ext
  intro idx hidx
  by_cases hnorm : Matrix.dot basisRow basisRow = 0
  · have hcoeff : projectionCoeff row basisRow = 0 := by
      simp [projectionCoeff, hnorm]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_smul, hcoeff]
    change row[idx] - 0 * basisRow[idx] = row[idx]
    grind
  · have hcoeff : projectionCoeff row basisRow = 0 := by
      have hzero_div : (0 : Rat) / Matrix.dot basisRow basisRow = 0 := by
        grind
      simp [projectionCoeff, h, hnorm, hzero_div]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_smul, hcoeff]
    change row[idx] - 0 * basisRow[idx] = row[idx]
    grind

private theorem reduceAgainstBasis_eq_self_of_forall_dot_zero
    (basisRev : List (Vector Rat m)) (row : Vector Rat m)
    (h : ∀ basisRow ∈ basisRev, Matrix.dot row basisRow = 0) :
    reduceAgainstBasis basisRev row = row := by
  induction basisRev generalizing row with
  | nil =>
      simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      have hhead : subtractProjection row basisRow = row :=
        subtractProjection_eq_self_of_dot_zero row basisRow (h basisRow (by simp))
      rw [hhead]
      exact ih row (by
        intro later hlater
        exact h later (by simp [hlater]))

private theorem subtractProjection_self_eq_zero (basisRow : Vector Rat m) :
    subtractProjection basisRow basisRow = 0 := by
  by_cases hnorm : Matrix.dot basisRow basisRow = 0
  · apply Vector.ext
    intro idx hidx
    have hzero : basisRow[idx] = 0 :=
      dot_self_eq_zero_get basisRow hnorm ⟨idx, hidx⟩
    have hcoeff : projectionCoeff basisRow basisRow = 0 := by
      simp [projectionCoeff, hnorm]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_zero, Vector.getElem_smul,
      hcoeff, hzero]
    change (0 : Rat) - 0 * 0 = 0
    grind
  · apply Vector.ext
    intro idx hidx
    have hdiv : Matrix.dot basisRow basisRow / Matrix.dot basisRow basisRow = 1 := by
      grind
    have hcoeff : projectionCoeff basisRow basisRow = 1 := by
      simp [projectionCoeff, hnorm, hdiv]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_zero, Vector.getElem_smul,
      hcoeff]
    change basisRow[idx] - 1 * basisRow[idx] = 0
    grind

private theorem reduceAgainstBasis_cons_self_eq_zero
    (basisRow : Vector Rat m) (rest : List (Vector Rat m)) :
    reduceAgainstBasis (basisRow :: rest) basisRow = 0 := by
  rw [reduceAgainstBasis]
  simp only [List.foldl_cons]
  rw [subtractProjection_self_eq_zero]
  change reduceAgainstBasis rest 0 = 0
  exact reduceAgainstBasis_zero_left rest

/-- Once a generated basis row has been included in the reduction prefix,
reducing that basis row against the prefix through its own index vanishes. -/
private theorem reduceAgainstBasis_basisRows_get!_succ_eq_zero
    (rows : List (Vector Rat m)) (j : Nat) (hj : j < rows.length) :
    reduceAgainstBasis ((basisRows rows).take (j + 1)).reverse
        (basisRows rows)[j]! = 0 := by
  have hlen : j < (basisRows rows).length := by
    simpa [basisRows_length] using hj
  have htake :
      (basisRows rows).take (j + 1) =
        (basisRows rows).take j ++ [(basisRows rows)[j]!] := by
    rw [List.take_succ_eq_append_getElem hlen]
    congr 1
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  rw [htake, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  exact reduceAgainstBasis_cons_self_eq_zero
    ((basisRows rows)[j]!) ((basisRows rows).take j).reverse

/-- The "by-row" prefix sum: a row-indexed variant of `prefixCombination` that
takes the projection row directly rather than reading it through a coefficient
matrix. Defined via `foldl` over `List.finRange i` so the conversion to
`prefixCombination` is a pointwise function-level rewrite. -/
private def prefixSumByRow (row : Vector Rat m) (basis : Matrix Rat n m)
    (i : Nat) (hi : i ≤ n) : Vector Rat m :=
  (List.finRange i).foldl
    (fun acc j =>
      let jn : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩
      acc + projectionCoeff row (basis.row jn) • basis.row jn)
    0

/-- The strict row prefix containing rows `0` through `k - 1`. This is the
matrix shape naturally paired with `prefixSumByRow`. -/
private def strictPrefixRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n) :
    Matrix R k m :=
  Vector.ofFn fun j => M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩

/-- Coefficients witnessing `prefixSumByRow` as a row combination of the strict
row prefix. -/
private def projectionCoeffVector (row : Vector Rat m) (basis : Matrix Rat n m)
    (k : Nat) (hk : k ≤ n) : Vector Rat k :=
  Vector.ofFn fun j =>
    projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)

private theorem foldl_projectionCoeff_rowCombination_comm
    (xs : List (Fin k)) (row : Vector Rat m) (basis : Matrix Rat n m)
    (hk : k ≤ n) (idx : Fin m) (acc : Rat) :
    xs.foldl
        (fun acc j =>
          acc +
            (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] *
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩))
        acc =
      xs.foldl
        (fun acc j =>
          acc +
            projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx])
        acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons j rest ih =>
      simp only [List.foldl_cons]
      have hcomm :
          (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] *
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) =
            projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] := by
        grind
      rw [hcomm]
      exact ih (acc := acc +
        projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
          (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx])

private theorem foldl_projectionCombination_getElem
    (xs : List (Fin k)) (row : Vector Rat m) (basis : Matrix Rat n m)
    (hk : k ≤ n) (idx : Fin m) (acc : Vector Rat m) :
    (xs.foldl
        (fun acc j =>
          acc + projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) •
            basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)
        acc)[idx] =
      xs.foldl
        (fun acc j =>
          acc +
            projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx])
        acc[idx] := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons j rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      have hstart :
          (acc +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) •
                basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] =
            acc[idx] +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
                (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] := by
        change
          (acc +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) •
                basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx.val] =
            acc[idx.val] +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
                (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx.val]
        rw [Vector.getElem_add, Vector.getElem_smul]
        rfl
      rw [hstart]

/-- `prefixSumByRow` is an executable row combination of the first `k` rows of
the basis matrix. -/
private theorem rowCombination_strictPrefixRows_projectionCoeffVector
    (row : Vector Rat m) (basis : Matrix Rat n m) (k : Nat) (hk : k ≤ n) :
    Matrix.rowCombination (strictPrefixRows basis k hk)
        (projectionCoeffVector row basis k hk) =
      prefixSumByRow row basis k hk := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change
    (Matrix.mulVec (Matrix.transpose (strictPrefixRows basis k hk))
        (projectionCoeffVector row basis k hk))[idxFin] =
      (prefixSumByRow row basis k hk)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose (strictPrefixRows basis k hk))
          (projectionCoeffVector row basis k hk))[idxFin] =
        (List.finRange k).foldl
          (fun acc j =>
            acc +
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idxFin] *
                projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩))
          0 by
        unfold Matrix.mulVec Matrix.transpose Matrix.col Matrix.row Matrix.dot
          Hex.Vector.dotProduct strictPrefixRows projectionCoeffVector
        simp [Matrix.row]]
  rw [show
      (prefixSumByRow row basis k hk)[idxFin] =
        (List.finRange k).foldl
          (fun acc j =>
            acc +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
                (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idxFin])
          0 by
        unfold prefixSumByRow
        simpa [Vector.getElem_zero] using
          foldl_projectionCombination_getElem
            (xs := List.finRange k) (row := row) (basis := basis) (hk := hk)
            (idx := idxFin) (acc := 0)]
  simpa [Matrix.row] using foldl_projectionCoeff_rowCombination_comm
    (xs := List.finRange k) (row := row) (basis := basis) (hk := hk)
    (idx := idxFin) (acc := 0)

/-- The recursive shape of `prefixSumByRow`: pulling off the last index. -/
private theorem prefixSumByRow_succ
    (row : Vector Rat m) (basis : Matrix Rat n m) (k : Nat) (hk : k + 1 ≤ n) :
    prefixSumByRow row basis (k + 1) hk =
      prefixSumByRow row basis k (Nat.le_of_succ_le hk) +
        projectionCoeff row (basis.row ⟨k, Nat.lt_of_succ_le hk⟩) •
          basis.row ⟨k, Nat.lt_of_succ_le hk⟩ := by
  unfold prefixSumByRow
  rw [List.finRange_succ_last]
  rw [List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  rfl

/-- `prefixCombination` over `coeffMatrix b (basisMatrix b)` agrees with
`prefixSumByRow` taking row `b.row ⟨i, hi⟩`. -/
private theorem prefixCombination_eq_prefixSumByRow
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    prefixCombination (coeffMatrix b (basisMatrix b)) (basisMatrix b) i hi =
      prefixSumByRow (b.row ⟨i, hi⟩) (basisMatrix b) i (Nat.le_of_lt hi) := by
  unfold prefixCombination prefixSumByRow
  congr 1
  funext acc j
  show acc + entry (coeffMatrix b (basisMatrix b)) ⟨i, hi⟩
        ⟨j.val, Nat.lt_trans j.isLt hi⟩ • (basisMatrix b).row ⟨j.val, _⟩ =
      acc + projectionCoeff (b.row ⟨i, hi⟩)
        ((basisMatrix b).row ⟨j.val, _⟩) • (basisMatrix b).row ⟨j.val, _⟩
  have hjlt : j.val < i := j.isLt
  have hentry : entry (coeffMatrix b (basisMatrix b)) ⟨i, hi⟩
        ⟨j.val, Nat.lt_trans j.isLt hi⟩ =
      projectionCoeff (b.row ⟨i, hi⟩)
        ((basisMatrix b).row ⟨j.val, Nat.lt_trans j.isLt hi⟩) := by
    simp [coeffMatrix, entry_ofFn, hjlt, Matrix.row]
  rw [hentry]

/-- `prefixSumByRow` with row free equals `projectionCombination` over the
first `i` rows of `basisRows b.toList`. -/
private theorem prefixSumByRow_eq_projectionCombination
    (b : Matrix Rat n m) (row : Vector Rat m) (i : Nat) (hi : i ≤ n) :
    prefixSumByRow row (basisMatrix b) i hi =
      projectionCombination row ((basisRows b.toList).take i) 0 := by
  have hlen : (basisRows b.toList).length = n := by simp [basisRows_length]
  induction i with
  | zero =>
      simp [prefixSumByRow, projectionCombination]
  | succ k ih =>
      have hk_lt : k < n := Nat.lt_of_succ_le hi
      have hkrows : k < (basisRows b.toList).length := by rw [hlen]; exact hk_lt
      rw [prefixSumByRow_succ]
      rw [ih (Nat.le_of_succ_le hi)]
      have htake : (basisRows b.toList).take (k + 1) =
          (basisRows b.toList).take k ++ [(basisRows b.toList)[k]!] := by
        rw [List.take_succ_eq_append_getElem hkrows]
        congr 1
        simp [List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem hkrows]
      rw [htake, projectionCombination_append, projectionCombination_singleton]
      have hbasisrow : (basisMatrix b).row ⟨k, hk_lt⟩ = (basisRows b.toList)[k]! := by
        rw [basisMatrix_row_eq_basisRows_get!]
      rw [hbasisrow]

/-- The projection combination over the first `i` generated basis rows is a
row combination of the strict prefix of the executable basis matrix. -/
private theorem projectionCombination_basisRows_take_eq_rowCombination
    (b : Matrix Rat n m) (row : Vector Rat m) (i : Nat) (hi : i ≤ n) :
    projectionCombination row ((basisRows b.toList).take i) 0 =
      Matrix.rowCombination (strictPrefixRows (basisMatrix b) i hi)
        (projectionCoeffVector row (basisMatrix b) i hi) := by
  rw [← prefixSumByRow_eq_projectionCombination (b := b) (row := row) (i := i) (hi := hi)]
  exact (rowCombination_strictPrefixRows_projectionCoeffVector
    (row := row) (basis := basisMatrix b) (k := i) (hk := hi)).symm

/-- The coefficient-matrix prefix term is an executable row combination of the
earlier generated basis rows. -/
private theorem prefixCombination_eq_strictPrefixRowCombination
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    prefixCombination (coeffMatrix b (basisMatrix b)) (basisMatrix b) i hi =
      Matrix.rowCombination (strictPrefixRows (basisMatrix b) i (Nat.le_of_lt hi))
        (projectionCoeffVector (b.row ⟨i, hi⟩) (basisMatrix b) i (Nat.le_of_lt hi)) := by
  rw [prefixCombination_eq_prefixSumByRow]
  exact (rowCombination_strictPrefixRows_projectionCoeffVector
    (row := b.row ⟨i, hi⟩) (basis := basisMatrix b) (k := i)
    (hk := Nat.le_of_lt hi)).symm

/-- Decomposition invariant: each input row equals its reduced basis row plus
the prefix combination of earlier basis rows weighted by `coeffMatrix`. -/
private theorem basisMatrix_reconstruction_invariant
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    b.row ⟨i, hi⟩ =
      (basisMatrix b).row ⟨i, hi⟩ +
        prefixCombination (coeffMatrix b (basisMatrix b)) (basisMatrix b) i hi := by
  have hilen : i < b.toList.length := by simpa using hi
  have htoList_get : b.toList[i]! = b.row ⟨i, hi⟩ := by
    simp [Matrix.row, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hilen, Vector.getElem_toList]
  have hreduce_forward :=
    basisRows_get!_eq_reduceAgainstBasis_forward
      (rows := b.toList) (k := i) hilen
  rw [htoList_get] at hreduce_forward
  rw [hreduce_forward, ← basisMatrix_row_eq_basisRows_get! b i hi]
  congr 1
  rw [prefixCombination_eq_prefixSumByRow,
    prefixSumByRow_eq_projectionCombination]

end GramSchmidt

namespace GramSchmidt.Rat

/-- The Gram-Schmidt orthogonal basis for a rational matrix. -/
noncomputable def basis (b : Matrix Rat n m) : Matrix Rat n m :=
  GramSchmidt.basisMatrix b

/-- The Gram-Schmidt coefficient matrix for a rational input matrix. -/
noncomputable def coeffs (b : Matrix Rat n m) : Matrix Rat n n :=
  GramSchmidt.coeffMatrix b (basis b)

theorem basis_zero (b : Matrix Rat n m) (hn : 0 < n) :
    (basis b).row ⟨0, hn⟩ = b.row ⟨0, hn⟩ := by
  simpa [basis, GramSchmidt.basisMatrix, Matrix.row] using
    GramSchmidt.basisRows_head (b := b) hn

theorem basis_orthogonal (b : Matrix Rat n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Matrix.dot ((basis b).row ⟨i, hi⟩) ((basis b).row ⟨j, hj⟩) = 0 := by
  rw [basis, GramSchmidt.basisMatrix_row_eq_basisRows_get!,
    GramSchmidt.basisMatrix_row_eq_basisRows_get!]
  exact GramSchmidt.basisRows_get!_dot_eq_zero b i j hi hj hij

theorem basis_decomposition (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    b.row ⟨i, hi⟩ =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  simpa [basis, coeffs] using
    GramSchmidt.basisMatrix_reconstruction_invariant (b := b) i hi

theorem coeffs_diag (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 1 := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn]

theorem coeffs_upper (b : Matrix Rat n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  have hnot_lt : ¬j < i := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hnot_lt, hne]

theorem basis_span (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    ∀ v : Vector Rat m,
      GramSchmidt.prefixSpan (basis b) i hi v ↔
        GramSchmidt.prefixSpan b i hi v := by
  sorry

end GramSchmidt.Rat

namespace GramSchmidt.Int

/-- The Gram-Schmidt orthogonal basis for an integer matrix, viewed in
`Rat` after coefficient divisions. -/
noncomputable def basis (b : Matrix Int n m) : Matrix Rat n m :=
  GramSchmidt.basisMatrix (GramSchmidt.castIntMatrix b)

/-- The Gram-Schmidt coefficient matrix for an integer input matrix. -/
noncomputable def coeffs (b : Matrix Int n m) : Matrix Rat n n :=
  GramSchmidt.coeffMatrix (GramSchmidt.castIntMatrix b) (basis b)

theorem basis_zero (b : Matrix Int n m) (hn : 0 < n) :
    (basis b).row ⟨0, hn⟩ =
      Vector.map (fun x : Int => (x : Rat)) (b.row ⟨0, hn⟩) := by
  simpa [basis, GramSchmidt.basisMatrix, GramSchmidt.castIntMatrix, Matrix.row] using
    GramSchmidt.basisRows_head (b := GramSchmidt.castIntMatrix b) hn

theorem basis_orthogonal (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Matrix.dot ((basis b).row ⟨i, hi⟩) ((basis b).row ⟨j, hj⟩) = 0 := by
  simpa [basis, GramSchmidt.Rat.basis] using
    GramSchmidt.Rat.basis_orthogonal (b := GramSchmidt.castIntMatrix b) i j hi hj hij

theorem basis_decomposition (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i, hi⟩) =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  simpa [basis, coeffs, GramSchmidt.castIntMatrix, GramSchmidt.Rat.basis,
    GramSchmidt.Rat.coeffs, Matrix.row] using
      GramSchmidt.Rat.basis_decomposition (b := GramSchmidt.castIntMatrix b) i hi

theorem coeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 1 := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn]

theorem coeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  have hnot_lt : ¬j < i := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hnot_lt, hne]

theorem basis_span (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    ∀ v : Vector Rat m,
      GramSchmidt.prefixSpan (basis b) i hi v ↔
        GramSchmidt.prefixSpan (GramSchmidt.castIntMatrix b) i hi v := by
  sorry

end GramSchmidt.Int
end Hex
