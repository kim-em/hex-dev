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

/-- `dot (subtractProjection row basisRow) target` expands as `dot row target`
minus the projection coefficient times `dot basisRow target`. -/
private theorem dot_subtractProjection (row basisRow target : Vector Rat m) :
    Matrix.dot (subtractProjection row basisRow) target =
      Matrix.dot row target - projectionCoeff row basisRow * Matrix.dot basisRow target := by
  simp [subtractProjection, Matrix.dot_sub_smul_rat]

/-- Reconstruction identity: `row` is the sum of its residual
`subtractProjection row basisRow` and its projection onto `basisRow`. -/
private theorem subtractProjection_add_projection (row basisRow : Vector Rat m) :
    row = subtractProjection row basisRow + projectionCoeff row basisRow • basisRow := by
  apply Vector.ext
  intro k hk
  change row[k] =
    (subtractProjection row basisRow + projectionCoeff row basisRow • basisRow)[k]
  rw [Vector.getElem_add, subtractProjection, Vector.getElem_sub, Vector.getElem_smul]
  grind

/-- The residual `subtractProjection row basisRow` is orthogonal to `basisRow`
whenever `basisRow` has nonzero norm. -/
private theorem dot_subtractProjection_self_zero (row basisRow : Vector Rat m)
    (hnorm : Matrix.dot basisRow basisRow ≠ 0) :
    Matrix.dot (subtractProjection row basisRow) basisRow = 0 := by
  rw [dot_subtractProjection]
  simp [projectionCoeff, hnorm]
  grind

/-- A rational multiplied by itself is nonnegative. -/
private theorem rat_mul_self_nonneg (x : Rat) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using (Lean.Grind.OrderedRing.sq_nonneg (a := x))

/-- A rational `x` with `x * x ≤ 0` is zero. -/
private theorem rat_mul_self_eq_zero_of_nonpos (x : Rat) (h : x * x ≤ 0) : x = 0 := by
  have hnonneg : 0 ≤ x * x := rat_mul_self_nonneg x
  have hsquare : x * x = 0 := by
    grind
  grind

/-- Folding the sum of squares `v[i] * v[i]` only increases the accumulator, so
the starting value is a lower bound for the result. -/
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

/-- If the folded sum of squares `v[i] * v[i]` is zero starting from a
nonnegative accumulator, then every entry `v[i]` over the folded list is zero. -/
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

/-- A vector with zero self-dot-product has every coordinate equal to zero. -/
private theorem dot_self_eq_zero_get (v : Vector Rat m)
    (hzero : Matrix.dot v v = 0) (i : Fin m) :
    v[i] = 0 := by
  have hmem : i ∈ List.finRange m := by
    simp
  exact foldl_dot_self_eq_zero_of_mem (xs := List.finRange m) (v := v)
    (acc := 0) (by decide) (by simpa [Matrix.dot, Hex.Vector.dotProduct] using hzero) i hmem

/-- Over `Rat`, a vector whose self-dot-product is zero is the zero vector, so
its dot product with any other row also vanishes. Used to discharge the
degenerate zero-norm basis row case when reasoning about orthogonality. -/
theorem dot_zero_of_dot_self_zero (row v : Vector Rat m)
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

/-- When `basisRow` has zero norm, `subtractProjection row basisRow` is still
orthogonal to `basisRow`. -/
private theorem dot_subtractProjection_self_zero_of_dot_self_zero
    (row basisRow : Vector Rat m)
    (hnorm : Matrix.dot basisRow basisRow = 0) :
    Matrix.dot (subtractProjection row basisRow) basisRow = 0 := by
  exact dot_zero_of_dot_self_zero (row := subtractProjection row basisRow)
    (v := basisRow) hnorm

/-- The folded dot product is symmetric in `u` and `v` when the two
accumulators start equal. -/
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

/-- The rational dot product is commutative. -/
private theorem dot_comm_rat (u v : Vector Rat m) :
    Matrix.dot u v = Matrix.dot v u := by
  simpa [Matrix.dot, Hex.Vector.dotProduct] using
    foldl_dot_comm_rat (xs := List.finRange m) (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

/-- Removing a component along `otherBasisRow` that is orthogonal to `basisRow`
leaves the projection coefficient onto `basisRow` unchanged. -/
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

/-- `reduceAgainstBasis basisRev row` has the same dot product with `target` as `row`
does, whenever `target` is orthogonal to every row in `basisRev`. -/
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

/-- The residual `reduceAgainstBasis basisRev row` stays orthogonal to `target` when both
`row` and every row in `basisRev` are orthogonal to `target`. -/
private theorem dot_reduceAgainstBasis_zero_of_dot_zero
    (basisRev : List (Vector Rat m)) (row target : Vector Rat m)
    (hrow : Matrix.dot row target = 0)
    (horth : ∀ basisRow ∈ basisRev, Matrix.dot basisRow target = 0) :
    Matrix.dot (reduceAgainstBasis basisRev row) target = 0 := by
  rw [dot_reduceAgainstBasis_zero_of_forall_dot_zero basisRev row target horth, hrow]

/-- `reduceAgainstBasis basisRev row` is orthogonal to every member of a pairwise-orthogonal
`basisRev`. -/
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

/-- `reduceAgainstBasis basisRev row` has the same projection coefficient onto `basisRow`
as `row`, when every row in `basisRev` is orthogonal to `basisRow`. -/
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

/-- `projectionCombination row basisRev acc` accumulates onto `acc` the sum of `row`'s
projections onto each row of `basisRev`. -/
private def projectionCombination (row : Vector Rat m) (basisRev : List (Vector Rat m))
    (acc : Vector Rat m) : Vector Rat m :=
  basisRev.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) acc

/-- `projectionCombination` is unchanged when `row` is replaced by `row'` sharing the same
projection coefficient on every row of `basisRev`. -/
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

/-- `subtractProjection row basisRow` plus the projection term and `acc` reassembles to
`row + acc`. -/
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

/-- For a pairwise-orthogonal `basisRev`, the residual plus the accumulated projection
combination reconstructs `row + acc`. -/
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

/-- For a pairwise-orthogonal `basisRev`, `row` equals its residual plus the sum of its
projections onto the basis rows. -/
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

/-- `basisRowsAux basisRev pending` begins with `basisRev.reverse` as a prefix. -/
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

/-- The first row produced by `basisRowsAux [row] rows` is `row` itself. -/
private theorem basisRowsAux_singleton_head (row : Vector Rat m) (rows : List (Vector Rat m)) :
    (basisRowsAux [row] rows)[0]! = row := by
  obtain ⟨suffix, hsuffix⟩ := basisRowsAux_reverse_prefix [row] rows
  simp [hsuffix]

/-- `basisRowsAux basisRev pending` has length `basisRev.length + pending.length`. -/
private theorem basisRowsAux_length (basisRev pending : List (Vector Rat m)) :
    (basisRowsAux basisRev pending).length = basisRev.length + pending.length := by
  induction pending generalizing basisRev with
  | nil =>
      simp [basisRowsAux]
  | cons row rows ih =>
      simpa [basisRowsAux, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (GramSchmidt.reduceAgainstBasis basisRev row :: basisRev)

/-- `basisRows rows` has the same length as `rows`. -/
private theorem basisRows_length (rows : List (Vector Rat m)) :
    (basisRows rows).length = rows.length := by
  simpa [basisRows] using basisRowsAux_length ([] : List (Vector Rat m)) rows

/-- `rows.reverse` is pairwise orthogonal whenever `rows` is. -/
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

/-- `basisRowsAux basisRev pending` is pairwise orthogonal whenever the accumulated basis
`basisRev` is. -/
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

/-- `basisRows rows` is a pairwise-orthogonal list of rows. -/
private theorem basisRows_pairwise (rows : List (Vector Rat m)) :
    (basisRows rows).Pairwise (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0) := by
  simpa [basisRows] using
    basisRowsAux_pairwise ([] : List (Vector Rat m)) rows (by simp)

/-- Row `i` of `basisMatrix b` is the `i`-th entry of `basisRows b.toList`. -/
private theorem basisMatrix_row_eq_basisRows_get!
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    (basisMatrix b).row ⟨i, hi⟩ = (basisRows b.toList)[i]! := by
  simp [basisMatrix, Matrix.row]

/-- Distinct rows of `basisRows b.toList` have dot product zero. -/
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

/-- Index equation: the value at position `basisRev.length + k` of
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

/-- Projecting the zero row out against any basis row leaves zero: the
projection coefficient of `0` vanishes, so `subtractProjection 0 b = 0`.
Base case for the vanishing facts the later `prefixSpan`/`projectionCoeff`
proofs invoke when a reduced row has already collapsed to zero. -/
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

/-- Reducing the zero row against an entire basis stays zero: each
`subtractProjection` step preserves `0` (by `subtractProjection_zero_left`),
so the whole fold leaves `reduceAgainstBasis basisRev 0 = 0`. Used to close
the tail of a reduction once a row has been driven to zero. -/
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

/-- A row already orthogonal to a basis row is unchanged by projecting that
basis row out: when `Matrix.dot row basisRow = 0` the projection coefficient
is `0`, so `subtractProjection row basisRow = row`. The single-step
orthogonality-invariance fact underpinning the list version below. -/
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

/-- A row orthogonal to *every* basis vector survives the whole reduction
unchanged: iterating `subtractProjection_eq_self_of_dot_zero` down the list
gives `reduceAgainstBasis basisRev row = row`. Lets later proofs conclude a
row lies outside the prefix span without recomputing the fold. -/
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

/-- Projecting a basis row out against itself annihilates it: the projection
coefficient is `1` (or the row is already zero), so
`subtractProjection basisRow basisRow = 0`. The self-cancellation fact that
makes a basis row vanish once it appears in its own reduction prefix. -/
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

/-- Reducing a basis row against a prefix that begins with it yields zero:
the head step cancels the row to `0` (by `subtractProjection_self_eq_zero`)
and the remaining steps preserve zero (by `reduceAgainstBasis_zero_left`).
The building block for `reduceAgainstBasis_basisRows_get!_succ_eq_zero`. -/
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

/-! Linearity-of-source helpers for `subtractProjection` and
`reduceAgainstBasis`. These let later proofs pull the reconstruction
sum across the reduction. -/

private theorem foldl_dot_add_left
    (xs : List (Fin m)) (a b c : Vector Rat m) (accA accB : Rat) :
    xs.foldl (fun acc i => acc + (a + b)[i] * c[i]) (accA + accB) =
      xs.foldl (fun acc i => acc + a[i] * c[i]) accA +
        xs.foldl (fun acc i => acc + b[i] * c[i]) accB := by
  induction xs generalizing accA accB with
  | nil => simp
  | cons i xs ih =>
      have hentry : (a + b)[i] = a[i] + b[i] := by
        change (a + b)[i.val] = a[i.val] + b[i.val]
        rw [Vector.getElem_add]
      simp only [List.foldl_cons]
      have hstart :
          accA + accB + (a + b)[i] * c[i] =
            (accA + a[i] * c[i]) + (accB + b[i] * c[i]) := by
        rw [hentry]
        grind
      rw [hstart]
      exact ih (accA := accA + a[i] * c[i]) (accB := accB + b[i] * c[i])

/-- `dot_add_left` states left-additivity of the dot product. -/
private theorem dot_add_left (a b c : Vector Rat m) :
    Matrix.dot (a + b) c = Matrix.dot a c + Matrix.dot b c := by
  unfold Matrix.dot Hex.Vector.dotProduct
  have hzero : (0 : Rat) + 0 = 0 := by grind
  simpa [hzero] using
    foldl_dot_add_left (xs := List.finRange m) (a := a) (b := b) (c := c)
      (accA := 0) (accB := 0)

/-- `foldl_dot_smul_left` states left-homogeneity of the dot-product fold. -/
private theorem foldl_dot_smul_left
    (xs : List (Fin m)) (s : Rat) (a c : Vector Rat m) (acc : Rat) :
    xs.foldl (fun acc i => acc + (s • a)[i] * c[i]) (s * acc) =
      s * xs.foldl (fun acc i => acc + a[i] * c[i]) acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons i xs ih =>
      have hentry : (s • a)[i] = s * a[i] := by
        change (s • a)[i.val] = s * a[i.val]
        rw [Vector.getElem_smul]; rfl
      simp only [List.foldl_cons]
      have hstart :
          s * acc + (s • a)[i] * c[i] =
            s * (acc + a[i] * c[i]) := by
        rw [hentry]; grind
      rw [hstart]
      exact ih (acc := acc + a[i] * c[i])

/-- `dot_smul_left` states left-homogeneity of the dot product. -/
private theorem dot_smul_left (s : Rat) (a c : Vector Rat m) :
    Matrix.dot (s • a) c = s * Matrix.dot a c := by
  unfold Matrix.dot Hex.Vector.dotProduct
  have hzero : s * (0 : Rat) = 0 := by grind
  simpa [hzero] using
    foldl_dot_smul_left (xs := List.finRange m) (s := s) (a := a) (c := c) (acc := 0)

/-- `projectionCoeff_add_left` states left-additivity of the projection coefficient. -/
private theorem projectionCoeff_add_left (a b c : Vector Rat m) :
    projectionCoeff (a + b) c = projectionCoeff a c + projectionCoeff b c := by
  unfold projectionCoeff
  by_cases hnorm : Matrix.dot c c = 0
  · simp [hnorm]
    grind
  · simp [hnorm]
    rw [dot_add_left]
    grind

/-- `projectionCoeff_smul_left` states left-homogeneity of the projection coefficient. -/
private theorem projectionCoeff_smul_left (s : Rat) (a c : Vector Rat m) :
    projectionCoeff (s • a) c = s * projectionCoeff a c := by
  unfold projectionCoeff
  by_cases hnorm : Matrix.dot c c = 0
  · simp [hnorm]
  · simp [hnorm]
    rw [dot_smul_left]
    grind

/-- `subtractProjection_add_left` states left-additivity of projection subtraction. -/
private theorem subtractProjection_add_left (a b c : Vector Rat m) :
    subtractProjection (a + b) c =
      subtractProjection a c + subtractProjection b c := by
  apply Vector.ext
  intro k hk
  unfold subtractProjection
  have hcoeff := projectionCoeff_add_left a b c
  have hentry_lhs :
      ((a + b) - projectionCoeff (a + b) c • c)[k] =
        a[k] + b[k] - projectionCoeff (a + b) c * c[k] := by
    rw [Vector.getElem_sub, Vector.getElem_add, Vector.getElem_smul]
    rfl
  have hentry_rhs :
      (a - projectionCoeff a c • c + (b - projectionCoeff b c • c))[k] =
        a[k] - projectionCoeff a c * c[k] +
          (b[k] - projectionCoeff b c * c[k]) := by
    rw [Vector.getElem_add, Vector.getElem_sub, Vector.getElem_sub,
      Vector.getElem_smul, Vector.getElem_smul]
    rfl
  rw [hentry_lhs, hentry_rhs, hcoeff]
  grind

/-- `subtractProjection_smul_left` states left-homogeneity of projection subtraction. -/
private theorem subtractProjection_smul_left (s : Rat) (a c : Vector Rat m) :
    subtractProjection (s • a) c = s • subtractProjection a c := by
  apply Vector.ext
  intro k hk
  unfold subtractProjection
  have hcoeff := projectionCoeff_smul_left s a c
  have hentry_lhs :
      (s • a - projectionCoeff (s • a) c • c)[k] =
        s * a[k] - projectionCoeff (s • a) c * c[k] := by
    rw [Vector.getElem_sub, Vector.getElem_smul, Vector.getElem_smul]
    rfl
  have hentry_rhs :
      (s • (a - projectionCoeff a c • c))[k] =
        s * (a[k] - projectionCoeff a c * c[k]) := by
    rw [Vector.getElem_smul, Vector.getElem_sub, Vector.getElem_smul]
    rfl
  rw [hentry_lhs, hentry_rhs, hcoeff]
  grind

/-- `reduceAgainstBasis_add_left` states left-additivity of basis reduction. -/
private theorem reduceAgainstBasis_add_left
    (basisRev : List (Vector Rat m)) (a b : Vector Rat m) :
    reduceAgainstBasis basisRev (a + b) =
      reduceAgainstBasis basisRev a + reduceAgainstBasis basisRev b := by
  induction basisRev generalizing a b with
  | nil => simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      rw [subtractProjection_add_left]
      change reduceAgainstBasis rest
          (subtractProjection a basisRow + subtractProjection b basisRow) =
        reduceAgainstBasis rest (subtractProjection a basisRow) +
          reduceAgainstBasis rest (subtractProjection b basisRow)
      exact ih (a := subtractProjection a basisRow) (b := subtractProjection b basisRow)

/-- `reduceAgainstBasis_smul_left` states left-homogeneity of basis reduction. -/
private theorem reduceAgainstBasis_smul_left
    (basisRev : List (Vector Rat m)) (s : Rat) (a : Vector Rat m) :
    reduceAgainstBasis basisRev (s • a) = s • reduceAgainstBasis basisRev a := by
  induction basisRev generalizing a with
  | nil => simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      rw [subtractProjection_smul_left]
      change reduceAgainstBasis rest (s • subtractProjection a basisRow) =
        s • reduceAgainstBasis rest (subtractProjection a basisRow)
      exact ih (a := subtractProjection a basisRow)

/-- `reduceAgainstBasis_append` states the append-decomposition of basis reduction. -/
private theorem reduceAgainstBasis_append
    (l₁ l₂ : List (Vector Rat m)) (row : Vector Rat m) :
    reduceAgainstBasis (l₁ ++ l₂) row =
      reduceAgainstBasis l₂ (reduceAgainstBasis l₁ row) := by
  unfold reduceAgainstBasis
  rw [List.foldl_append]

private theorem basisRows_get!_dot_eq_zero_of_list
    (rows : List (Vector Rat m)) (i j : Nat)
    (hi : i < rows.length) (hj : j < rows.length) (hij : i ≠ j) :
    Matrix.dot (basisRows rows)[i]! (basisRows rows)[j]! = 0 := by
  have hilen : i < (basisRows rows).length := by simpa [basisRows_length]
  have hjlen : j < (basisRows rows).length := by simpa [basisRows_length]
  have hpair : (basisRows rows).Pairwise
      (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0) :=
    basisRows_pairwise rows
  have hget_i : (basisRows rows).get ⟨i, hilen⟩ = (basisRows rows)[i]! := by
    simp [hilen]
  have hget_j : (basisRows rows).get ⟨j, hjlen⟩ = (basisRows rows)[j]! := by
    simp [hjlen]
  by_cases hlt : i < j
  · have hrel :=
      (List.pairwise_iff_get.1 hpair) ⟨i, hilen⟩ ⟨j, hjlen⟩ (by simpa using hlt)
    rw [← hget_i, ← hget_j]
    exact hrel.1
  · have hji : j < i :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hij h.symm)
    have hrel :=
      (List.pairwise_iff_get.1 hpair) ⟨j, hjlen⟩ ⟨i, hilen⟩ (by simpa using hji)
    rw [← hget_i, ← hget_j]
    exact hrel.2

private theorem zero_add_vec (v : Vector Rat m) : (0 : Vector Rat m) + v = v := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_add, Vector.getElem_zero]
  grind

private theorem smul_zero_vec (s : Rat) : s • (0 : Vector Rat m) = 0 := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_smul, Vector.getElem_zero]
  show s * (0 : Rat) = 0
  grind

/-- Reducing a generated basis row against any later prefix that contains it
returns 0. -/
private theorem reduceAgainstBasis_basisRows_take_get!_eq_zero
    (rows : List (Vector Rat m)) (ℓ k : Nat)
    (hℓk : ℓ < k) (hk : k ≤ rows.length) :
    reduceAgainstBasis ((basisRows rows).take k).reverse
        (basisRows rows)[ℓ]! = 0 := by
  have hℓlen : ℓ < rows.length := Nat.lt_of_lt_of_le hℓk hk
  have hℓbasis : ℓ < (basisRows rows).length := by simpa [basisRows_length]
  have hkbasis : k ≤ (basisRows rows).length := by simpa [basisRows_length]
  -- The first ℓ+1 elements of take k are exactly take (ℓ+1).
  have htake_take :
      ((basisRows rows).take k).take (ℓ + 1) = (basisRows rows).take (ℓ + 1) := by
    rw [List.take_take]
    congr 1
    omega
  have hsplit :
      (basisRows rows).take k =
        (basisRows rows).take (ℓ + 1) ++
          ((basisRows rows).take k).drop (ℓ + 1) := by
    rw [← htake_take]
    exact (List.take_append_drop (ℓ + 1) ((basisRows rows).take k)).symm
  rw [hsplit, List.reverse_append, reduceAgainstBasis_append]
  -- Inner reduction: (basisRows rows)[ℓ]! is orthogonal to all elements in
  -- the drop-take part (those are basis rows at indices > ℓ).
  have hinner :
      reduceAgainstBasis (((basisRows rows).take k).drop (ℓ + 1)).reverse
          (basisRows rows)[ℓ]! = (basisRows rows)[ℓ]! := by
    apply reduceAgainstBasis_eq_self_of_forall_dot_zero
    intro b hmem
    rw [List.mem_reverse] at hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hilen, hbget⟩ := hmem
    have hdroplen :
        (((basisRows rows).take k).drop (ℓ + 1)).length =
          ((basisRows rows).take k).length - (ℓ + 1) := by
      rw [List.length_drop]
    have htakelen : ((basisRows rows).take k).length = k := by
      rw [List.length_take]; omega
    rw [hdroplen, htakelen] at hilen
    have hidx_lt_basis : i + (ℓ + 1) < (basisRows rows).length := by
      have : k ≤ (basisRows rows).length := hkbasis
      omega
    have hidx_lt_take : i + (ℓ + 1) < ((basisRows rows).take k).length := by
      rw [htakelen]; omega
    -- Resolve b to (basisRows rows)[ℓ + 1 + i].
    have hidx_lt_basis' : ℓ + 1 + i < (basisRows rows).length := by
      have hcomm : ℓ + 1 + i = i + (ℓ + 1) := by omega
      rw [hcomm]; exact hidx_lt_basis
    have hbget' :
        b = (basisRows rows)[ℓ + 1 + i]'hidx_lt_basis' := by
      rw [← hbget]
      rw [List.getElem_drop, List.getElem_take]
    have hbget!_eq :
        b = (basisRows rows)[ℓ + 1 + i]! := by
      rw [hbget']
      simp [hidx_lt_basis']
    rw [hbget!_eq]
    apply basisRows_get!_dot_eq_zero_of_list rows ℓ (ℓ + 1 + i) hℓlen
    · -- ℓ + 1 + i < rows.length
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    · omega
  rw [hinner]
  exact reduceAgainstBasis_basisRows_get!_succ_eq_zero rows ℓ hℓlen

/-- A `projectionCombination` whose basis rows all reduce to 0 against
`basisRev'` (and whose accumulator does too) reduces to 0 against `basisRev'`. -/
private theorem reduceAgainstBasis_projectionCombination_eq_zero
    (basisRev basisRev' : List (Vector Rat m)) (row acc : Vector Rat m)
    (hzero : ∀ b ∈ basisRev, reduceAgainstBasis basisRev' b = 0)
    (haccZero : reduceAgainstBasis basisRev' acc = 0) :
    reduceAgainstBasis basisRev' (projectionCombination row basisRev acc) = 0 := by
  induction basisRev generalizing acc with
  | nil =>
      simp [projectionCombination]
      exact haccZero
  | cons b rest ih =>
      show reduceAgainstBasis basisRev'
          (projectionCombination row (b :: rest) acc) = 0
      simp only [projectionCombination, List.foldl_cons]
      change reduceAgainstBasis basisRev'
          (projectionCombination row rest
            (acc + projectionCoeff row b • b)) = 0
      apply ih
      · intro b' hb'
        exact hzero b' (by simp [hb'])
      · rw [reduceAgainstBasis_add_left, haccZero, reduceAgainstBasis_smul_left,
          hzero b (by simp), smul_zero_vec, zero_add_vec]

/-- Reducing the source row `rows[j]!` against any later prefix returns 0:
the source row's basis-prefix decomposition lies entirely in the reduction
prefix, and the basis component vanishes by index. -/
private theorem reduceAgainstBasis_basisRows_take_source_eq_zero
    (rows : List (Vector Rat m)) (j k : Nat)
    (hjk : j < k) (hk : k ≤ rows.length) :
    reduceAgainstBasis ((basisRows rows).take k).reverse rows[j]! = 0 := by
  have hjlen : j < rows.length := Nat.lt_of_lt_of_le hjk hk
  have hjbasis : j < (basisRows rows).length := by simpa [basisRows_length]
  -- Reconstruction theorem for the source row.
  have hrec :=
    basisRows_get!_eq_reduceAgainstBasis_forward (rows := rows) (k := j) hjlen
  rw [hrec]
  rw [reduceAgainstBasis_add_left]
  -- Basis-row component vanishes by Aux1 with ℓ = j.
  rw [reduceAgainstBasis_basisRows_take_get!_eq_zero rows j k hjk hk]
  rw [zero_add_vec]
  -- ProjectionCombination component vanishes: each contributing basis row is
  -- at index < j < k, so reducing it gives 0.
  apply reduceAgainstBasis_projectionCombination_eq_zero
  · intro b hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hilen, hbget⟩ := hmem
    have htakelen : ((basisRows rows).take j).length = j := by
      rw [List.length_take]; omega
    rw [htakelen] at hilen
    have hi_lt_basis : i < (basisRows rows).length := by
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    have hbget' : b = (basisRows rows)[i]'hi_lt_basis := by
      rw [← hbget, List.getElem_take]
    have hbget!_eq : b = (basisRows rows)[i]! := by
      rw [hbget']; simp [hi_lt_basis]
    rw [hbget!_eq]
    apply reduceAgainstBasis_basisRows_take_get!_eq_zero rows i k _ hk
    omega
  · exact reduceAgainstBasis_zero_left _

/-- The first `i` Gram-Schmidt output rows depend only on the first `i` input
rows. -/
private theorem basisRows_take_eq_of_prefix
    (rows rows' : List (Vector Rat m)) (i : Nat)
    (hlen : rows'.length = rows.length)
    (hprefix : ∀ t, t < i → rows'[t]! = rows[t]!)
    (hi : i ≤ rows.length) :
    (basisRows rows').take i = (basisRows rows).take i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ≤ rows.length := Nat.le_of_succ_le hi
    have ihtake := ih (by
      intro t ht
      exact hprefix t (Nat.lt_trans ht (Nat.lt_succ_self i))) hi'
    have hi_lt : i < rows.length := hi
    have hi_lt_rows' : i < rows'.length := by rw [hlen]; exact hi_lt
    have hb1_len : (basisRows rows').length = rows.length := by
      rw [basisRows_length, hlen]
    have hb2_len : (basisRows rows).length = rows.length := basisRows_length rows
    have hi_lt_b1 : i < (basisRows rows').length := by rw [hb1_len]; exact hi_lt
    have hi_lt_b2 : i < (basisRows rows).length := by rw [hb2_len]; exact hi_lt
    rw [List.take_succ_eq_append_getElem hi_lt_b1,
        List.take_succ_eq_append_getElem hi_lt_b2,
        ihtake]
    congr 1
    have hge1 : (basisRows rows')[i] = (basisRows rows')[i]! :=
      (getElem!_pos _ i hi_lt_b1).symm
    have hge2 : (basisRows rows)[i] = (basisRows rows)[i]! :=
      (getElem!_pos _ i hi_lt_b2).symm
    rw [hge1, hge2]
    congr 1
    rw [basisRows_get!_eq_reduceAgainstBasis_take rows' i hi_lt_rows',
        basisRows_get!_eq_reduceAgainstBasis_take rows i hi_lt,
        ihtake,
        hprefix i (Nat.lt_succ_self i)]

private theorem basisRows_get!_eq_of_prefix
    (rows rows' : List (Vector Rat m)) (i : Nat)
    (hlen : rows'.length = rows.length)
    (hprefix : ∀ t, t ≤ i → rows'[t]! = rows[t]!)
    (hi : i < rows.length) :
    (basisRows rows')[i]! = (basisRows rows)[i]! := by
  have htake :=
    basisRows_take_eq_of_prefix rows rows' (i + 1) hlen
      (by
        intro t ht
        exact hprefix t (Nat.le_of_lt_succ ht))
      (Nat.succ_le_of_lt hi)
  have hb1_len : (basisRows rows').length = rows.length := by
    rw [basisRows_length, hlen]
  have hb2_len : (basisRows rows).length = rows.length := basisRows_length rows
  have hi_b1 : i < (basisRows rows').length := by rw [hb1_len]; exact hi
  have hi_b2 : i < (basisRows rows).length := by rw [hb2_len]; exact hi
  have hget :=
    congrArg (fun xs : List (Vector Rat m) => xs[i]?) htake
  simp [hi_b1, hi_b2] at hget
  simp [hget, hi_b1, hi_b2]

/-- Reducing the next source row against the prefix before its predecessor
leaves the old next basis row plus the predecessor projection term. -/
private theorem reduceAgainstBasis_basisRows_take_source_adjacent
    (rows : List (Vector Rat m)) (km1 k : Nat)
    (hkm1 : km1 + 1 = k) (hk : k < rows.length) :
    reduceAgainstBasis ((basisRows rows).take km1).reverse rows[k]! =
      (basisRows rows)[k]! +
        projectionCoeff rows[k]! (basisRows rows)[km1]! • (basisRows rows)[km1]! := by
  have hkm1_lt_k : km1 < k := by omega
  have hkm1_lt_rows : km1 < rows.length := Nat.lt_trans hkm1_lt_k hk
  have hbasis_k_len : k < (basisRows rows).length := by simpa [basisRows_length]
  have hbasis_km1_len : km1 < (basisRows rows).length := by
    simpa [basisRows_length] using hkm1_lt_rows
  have hrec :=
    basisRows_get!_eq_reduceAgainstBasis_forward (rows := rows) (k := k) hk
  have htake :
      (basisRows rows).take k =
        (basisRows rows).take km1 ++ [(basisRows rows)[km1]!] := by
    rw [← hkm1]
    rw [List.take_succ_eq_append_getElem hbasis_km1_len]
    congr 1
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hbasis_km1_len]
  have hbasis_k :
      reduceAgainstBasis ((basisRows rows).take km1).reverse (basisRows rows)[k]! =
        (basisRows rows)[k]! := by
    apply reduceAgainstBasis_eq_self_of_forall_dot_zero
    intro b hmem
    rw [List.mem_reverse] at hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨idx, hidx, hbget⟩ := hmem
    have htake_len : ((basisRows rows).take km1).length = km1 := by
      rw [List.length_take]
      omega
    have hidx_km1 : idx < km1 := by
      rw [htake_len] at hidx
      exact hidx
    have hidx_basis : idx < (basisRows rows).length := by
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    have hbget' : b = (basisRows rows)[idx]! := by
      rw [← hbget, List.getElem_take]
      simp [hidx_basis]
    rw [hbget']
    exact basisRows_get!_dot_eq_zero_of_list rows k idx hk
      (by omega) (by omega)
  have hproj_prefix :
      reduceAgainstBasis ((basisRows rows).take km1).reverse
        (projectionCombination rows[k]! ((basisRows rows).take km1) 0) = 0 := by
    apply reduceAgainstBasis_projectionCombination_eq_zero
    · intro b hmem
      rw [List.mem_iff_getElem] at hmem
      obtain ⟨idx, hidx, hbget⟩ := hmem
      have htake_len : ((basisRows rows).take km1).length = km1 := by
        rw [List.length_take]
        omega
      have hidx_km1 : idx < km1 := by
        rw [htake_len] at hidx
        exact hidx
      have hidx_basis : idx < (basisRows rows).length := by
        have : (basisRows rows).length = rows.length := basisRows_length rows
        omega
      have hbget' : b = (basisRows rows)[idx]! := by
        rw [← hbget, List.getElem_take]
        simp [hidx_basis]
      rw [hbget']
      apply reduceAgainstBasis_basisRows_take_get!_eq_zero rows idx km1 hidx_km1
      omega
    · exact reduceAgainstBasis_zero_left _
  have hbasis_km1 :
      reduceAgainstBasis ((basisRows rows).take km1).reverse (basisRows rows)[km1]! =
      (basisRows rows)[km1]! := by
    apply reduceAgainstBasis_eq_self_of_forall_dot_zero
    intro b hmem
    rw [List.mem_reverse] at hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨idx, hidx, hbget⟩ := hmem
    have htake_len : ((basisRows rows).take km1).length = km1 := by
      rw [List.length_take]
      omega
    have hidx_km1 : idx < km1 := by
      rw [htake_len] at hidx
      exact hidx
    have hidx_basis : idx < (basisRows rows).length := by
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    have hbget' : b = (basisRows rows)[idx]! := by
      rw [← hbget, List.getElem_take]
      simp [hidx_basis]
    rw [hbget']
    exact basisRows_get!_dot_eq_zero_of_list rows km1 idx hkm1_lt_rows
      (by omega) (by omega)
  conv => lhs; rw [hrec]
  rw [htake, projectionCombination_append, projectionCombination_singleton]
  repeat rw [reduceAgainstBasis_add_left]
  rw [hbasis_k, hproj_prefix, reduceAgainstBasis_smul_left, hbasis_km1]
  apply Vector.ext
  intro idx hidx
  rw [Vector.getElem_add, Vector.getElem_add, Vector.getElem_zero]
  grind

/-- For `j < k < rows.length`, the first `i` basis rows produced by Gram-Schmidt
on `rows.set k (rows[k]! + c • rows[j]!)` agree with the first `i` basis rows
produced on `rows`. Proved jointly with the pointwise equality at index `i` by
ordinary induction: the inductive step rewrites `(basisRows _)[i]!` via
`basisRows_get!_eq_reduceAgainstBasis_take` against the equal prefix from the
inductive hypothesis, then either uses the unchanged-row case (`i ≠ k`) or
linearity plus `reduceAgainstBasis_basisRows_take_source_eq_zero` (`i = k`). -/
private theorem basisRows_take_set_rowAdd
    (rows : List (Vector Rat m)) (j k : Nat) (c : Rat)
    (hjk : j < k) (hk : k < rows.length) (i : Nat) (hi : i ≤ rows.length) :
    (basisRows (rows.set k (rows[k]! + c • rows[j]!))).take i =
      (basisRows rows).take i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ≤ rows.length := Nat.le_of_succ_le hi
    have ihtake := ih hi'
    have hi_lt : i < rows.length := hi
    have hrows'_len :
        (rows.set k (rows[k]! + c • rows[j]!)).length = rows.length := by simp
    have hi_lt_rows' : i < (rows.set k (rows[k]! + c • rows[j]!)).length := by
      rw [hrows'_len]; exact hi_lt
    have hb1_len :
        (basisRows (rows.set k (rows[k]! + c • rows[j]!))).length = rows.length := by
      rw [basisRows_length, hrows'_len]
    have hb2_len : (basisRows rows).length = rows.length := basisRows_length rows
    have hi_lt_b1 :
        i < (basisRows (rows.set k (rows[k]! + c • rows[j]!))).length := by
      rw [hb1_len]; exact hi_lt
    have hi_lt_b2 : i < (basisRows rows).length := by rw [hb2_len]; exact hi_lt
    rw [List.take_succ_eq_append_getElem hi_lt_b1,
        List.take_succ_eq_append_getElem hi_lt_b2,
        ihtake]
    congr 1
    -- Reduce `[(basisRows rows')[i]] = [(basisRows rows)[i]]` to `[i]!`-form.
    have hge1 :
        (basisRows (rows.set k (rows[k]! + c • rows[j]!)))[i] =
          (basisRows (rows.set k (rows[k]! + c • rows[j]!)))[i]! :=
      (getElem!_pos _ i hi_lt_b1).symm
    have hge2 : (basisRows rows)[i] = (basisRows rows)[i]! :=
      (getElem!_pos _ i hi_lt_b2).symm
    rw [hge1, hge2]
    congr 1
    rw [basisRows_get!_eq_reduceAgainstBasis_take
          (rows.set k (rows[k]! + c • rows[j]!)) i hi_lt_rows',
        basisRows_get!_eq_reduceAgainstBasis_take rows i hi_lt,
        ihtake]
    by_cases hik : i = k
    · -- Modified row: i = k.
      have hrows'_get_eq :
          (rows.set k (rows[k]! + c • rows[j]!))[i]! = rows[k]! + c • rows[j]! := by
        rw [hik]
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_self hk]
      rw [hrows'_get_eq, reduceAgainstBasis_add_left,
          reduceAgainstBasis_smul_left]
      have hsrc :
          reduceAgainstBasis ((basisRows rows).take i).reverse rows[j]! = 0 := by
        rw [hik]
        exact reduceAgainstBasis_basisRows_take_source_eq_zero rows j k hjk
            (Nat.le_of_lt hk)
      rw [hsrc]
      have hrhs_get :
          reduceAgainstBasis ((basisRows rows).take i).reverse rows[i]! =
            reduceAgainstBasis ((basisRows rows).take i).reverse rows[k]! := by
        rw [hik]
      rw [hrhs_get, smul_zero_vec]
      apply Vector.ext
      intro idx hidx
      rw [Vector.getElem_add, Vector.getElem_zero]
      grind
    · -- Unchanged row: i ≠ k.
      have hne : k ≠ i := Ne.symm hik
      have hrows'_get_eq :
          (rows.set k (rows[k]! + c • rows[j]!))[i]! = rows[i]! := by
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]
      rw [hrows'_get_eq]

/-- `basisRows` is invariant under replacing input row `k` by
`rows[k]! + c • rows[j]!` for `j < k < rows.length`. -/
private theorem basisRows_set_rowAdd
    (rows : List (Vector Rat m)) (j k : Nat) (c : Rat)
    (hjk : j < k) (hk : k < rows.length) :
    basisRows (rows.set k (rows[k]! + c • rows[j]!)) = basisRows rows := by
  have h :=
    basisRows_take_set_rowAdd rows j k c hjk hk rows.length (Nat.le_refl _)
  have hlen1 :
      (basisRows (rows.set k (rows[k]! + c • rows[j]!))).length = rows.length := by
    rw [basisRows_length, List.length_set]
  have hlen2 : (basisRows rows).length = rows.length := basisRows_length rows
  rw [List.take_of_length_le (Nat.le_of_eq hlen1),
      List.take_of_length_le (Nat.le_of_eq hlen2)] at h
  exact h

/-- `basisMatrix` is invariant under the executable row-add operation
`Matrix.rowAdd b src dst c` whenever `src.val < dst.val`. Wraps
`basisRows_set_rowAdd` through the `toList` representation. -/
private theorem basisMatrix_rowAdd
    (b : Matrix Rat n m) (src dst : Fin n) (c : Rat) (h : src.val < dst.val) :
    basisMatrix (Matrix.rowAdd b src dst c) = basisMatrix b := by
  unfold basisMatrix
  have hsrc_toList : b.toList[src.val]! = b[src] := by simp
  have hdst_toList : b.toList[dst.val]! = b[dst] := by simp
  have htoList :
      (Matrix.rowAdd b src dst c).toList =
        b.toList.set dst.val
          (b.toList[dst.val]! + c • b.toList[src.val]!) := by
    show (b.set dst (Vector.ofFn fun k => b[dst][k] + c * b[src][k])).toList = _
    rw [Vector.toList_set]
    congr 1
    rw [hsrc_toList, hdst_toList]
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_ofFn, Vector.getElem_add, Vector.getElem_smul]
    rfl
  rw [htoList, basisRows_set_rowAdd b.toList src.val dst.val c h
    (by rw [Vector.length_toList]; exact dst.isLt)]

/-- `rowSwap_toList_get!_of_lt`: reading `toList`/`get!` at an index `t` strictly
below both swapped positions `km1 < k` returns the same row as before the swap. -/
private theorem rowSwap_toList_get!_of_lt
    (b : Matrix Rat n m) (km1 k : Fin n) (t : Nat)
    (hkm1k : km1.val < k.val) (ht : t < km1.val) :
    (Matrix.rowSwap b km1 k).toList[t]! = b.toList[t]! := by
  have ht_n : t < n := Nat.lt_trans ht km1.isLt
  let r : Fin n := ⟨t, ht_n⟩
  have hrk : r ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    change t = k.val at hval
    omega
  have hrkm1 : r ≠ km1 := by
    intro h
    have hval := congrArg Fin.val h
    change t = km1.val at hval
    omega
  have hleft :
      (Matrix.rowSwap b km1 k).toList[t]! = (Matrix.rowSwap b km1 k).row r := by
    have hget :
        (Matrix.rowSwap b km1 k).toList[t]! =
          (Matrix.rowSwap b km1 k).toList[t]'(by simp [ht_n]) :=
      getElem!_pos _ t (by simp [ht_n])
    simpa [Matrix.row, Vector.getElem_toList, r] using hget
  have hright : b.toList[t]! = b.row r := by
    have hget : b.toList[t]! = b.toList[t]'(by simp [ht_n]) :=
      getElem!_pos _ t (by simp [ht_n])
    simpa [Matrix.row, Vector.getElem_toList, r] using hget
  rw [hleft, hright]
  apply Vector.ext
  intro idx hidx
  let cc : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b km1 k)[r][cc] = b[r][cc]
  rw [Matrix.rowSwap_getElem]
  simp [hrk, hrkm1]

/-- `rowSwap_toList_get!_left`: at the lower swapped index `km1`, the swapped matrix
reads back the original row stored at the upper index `k`. -/
private theorem rowSwap_toList_get!_left
    (b : Matrix Rat n m) (km1 k : Fin n) (hkm1k : km1.val ≠ k.val) :
    (Matrix.rowSwap b km1 k).toList[km1.val]! = b.toList[k.val]! := by
  have hleft :
      (Matrix.rowSwap b km1 k).toList[km1.val]! =
        (Matrix.rowSwap b km1 k).row km1 := by
    simp [Matrix.row]
  have hright : b.toList[k.val]! = b.row k := by
    simp [Matrix.row]
  rw [hleft, hright]
  have hne : km1 ≠ k := by
    intro h
    exact hkm1k (congrArg Fin.val h)
  apply Vector.ext
  intro idx hidx
  let cc : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b km1 k)[km1][cc] = b[k][cc]
  rw [Matrix.rowSwap_getElem]
  simp [hne]

/-- `rowSwap_toList_get!_right`: at the upper swapped index `k`, the swapped matrix
reads back the original row stored at the lower index `km1`. -/
private theorem rowSwap_toList_get!_right
    (b : Matrix Rat n m) (km1 k : Fin n) :
    (Matrix.rowSwap b km1 k).toList[k.val]! = b.toList[km1.val]! := by
  have hleft :
      (Matrix.rowSwap b km1 k).toList[k.val]! =
        (Matrix.rowSwap b km1 k).row k := by
    simp [Matrix.row]
  have hright : b.toList[km1.val]! = b.row km1 := by
    simp [Matrix.row]
  rw [hleft, hright]
  apply Vector.ext
  intro idx hidx
  let cc : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b km1 k)[k][cc] = b[km1][cc]
  rw [Matrix.rowSwap_getElem]
  simp

/-- `rowSwap_toList_get!_of_gt`: reading `toList`/`get!` at an index `t` strictly
above both swapped positions `km1 < k` returns the same row as before the swap. -/
private theorem rowSwap_toList_get!_of_gt
    (b : Matrix Rat n m) (km1 k : Fin n) (t : Nat)
    (hkm1k : km1.val < k.val) (ht_lt_n : t < n) (ht : k.val < t) :
    (Matrix.rowSwap b km1 k).toList[t]! = b.toList[t]! := by
  let r : Fin n := ⟨t, ht_lt_n⟩
  have hrk : r ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    change t = k.val at hval
    omega
  have hrkm1 : r ≠ km1 := by
    intro h
    have hval := congrArg Fin.val h
    change t = km1.val at hval
    omega
  have hleft :
      (Matrix.rowSwap b km1 k).toList[t]! = (Matrix.rowSwap b km1 k).row r := by
    have hget :
        (Matrix.rowSwap b km1 k).toList[t]! =
          (Matrix.rowSwap b km1 k).toList[t]'(by simp [ht_lt_n]) :=
      getElem!_pos _ t (by simp [ht_lt_n])
    simpa [Matrix.row, Vector.getElem_toList, r] using hget
  have hright : b.toList[t]! = b.row r := by
    have hget : b.toList[t]! = b.toList[t]'(by simp [ht_lt_n]) :=
      getElem!_pos _ t (by simp [ht_lt_n])
    simpa [Matrix.row, Vector.getElem_toList, r] using hget
  rw [hleft, hright]
  apply Vector.ext
  intro idx hidx
  let cc : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b km1 k)[r][cc] = b[r][cc]
  rw [Matrix.rowSwap_getElem]
  simp [hrk, hrkm1]

/-- `basisMatrix_rowSwap_of_before`: swapping rows `km1` and `k` leaves the
`basisMatrix` row at any index `i` lying before `km1` unchanged. -/
private theorem basisMatrix_rowSwap_of_before
    (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1k : km1.val < k.val) (hi : i.val < km1.val) :
    (basisMatrix (Matrix.rowSwap b km1 k)).row i = (basisMatrix b).row i := by
  rw [basisMatrix_row_eq_basisRows_get!, basisMatrix_row_eq_basisRows_get!]
  apply basisRows_get!_eq_of_prefix
  · simp
  · intro t ht
    exact rowSwap_toList_get!_of_lt b km1 k t hkm1k (Nat.lt_of_le_of_lt ht hi)
  · simp

/-- `basisMatrix_rowSwap_adjacent_prev`: after an adjacent swap (`km1 + 1 = k`),
the new `basisMatrix` row at `km1` is the original row `k` plus its projection
onto the original orthogonal row at `km1`. -/
private theorem basisMatrix_rowSwap_adjacent_prev
    (b : Matrix Rat n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    (basisMatrix (Matrix.rowSwap b km1 k)).row km1 =
      (basisMatrix b).row k +
        projectionCoeff (b.row k) ((basisMatrix b).row km1) • (basisMatrix b).row km1 := by
  rw [basisMatrix_row_eq_basisRows_get!, basisMatrix_row_eq_basisRows_get!,
    basisMatrix_row_eq_basisRows_get!]
  have hswap_row :
      (Matrix.rowSwap b km1 k).toList[km1.val]! = b.toList[k.val]! := by
    apply rowSwap_toList_get!_left
    omega
  have hprefix :
      ((basisRows (Matrix.rowSwap b km1 k).toList).take km1.val) =
        ((basisRows b.toList).take km1.val) := by
    apply basisRows_take_eq_of_prefix
    · simp
    · intro t ht
      exact rowSwap_toList_get!_of_lt b km1 k t (by omega) ht
    · simp
  have hlen_swap : (Matrix.rowSwap b km1 k).toList.length = b.toList.length := by simp
  have hkm1_lt_len : km1.val < b.toList.length := by simp [km1.isLt]
  have hkm1_lt_swap : km1.val < (Matrix.rowSwap b km1 k).toList.length := by
    rw [hlen_swap]; exact hkm1_lt_len
  rw [basisRows_get!_eq_reduceAgainstBasis_take
        (Matrix.rowSwap b km1 k).toList km1.val hkm1_lt_swap,
      hprefix, hswap_row]
  have hreduce :=
    reduceAgainstBasis_basisRows_take_source_adjacent
      (rows := b.toList) (km1 := km1.val) (k := k.val) hkm1 (by simp [k.isLt])
  simpa [Matrix.row] using hreduce

/-- `basisMatrix_rowSwap_adjacent_curr`: after an adjacent swap (`km1 + 1 = k`),
the new `basisMatrix` row at `k` is the original orthogonal row at `km1` minus
its projection onto the new orthogonal row produced at `km1`. -/
private theorem basisMatrix_rowSwap_adjacent_curr
    (b : Matrix Rat n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    (basisMatrix (Matrix.rowSwap b km1 k)).row k =
      (basisMatrix b).row km1 -
        projectionCoeff (b.row km1)
          ((basisMatrix b).row k +
            projectionCoeff (b.row k) ((basisMatrix b).row km1) •
              (basisMatrix b).row km1) •
          ((basisMatrix b).row k +
            projectionCoeff (b.row k) ((basisMatrix b).row km1) •
              (basisMatrix b).row km1) := by
  let prev := (basisMatrix b).row km1
  let curr := (basisMatrix b).row k
  let mu := projectionCoeff (b.row k) prev
  let swappedPrev := curr + mu • prev
  change (basisMatrix (Matrix.rowSwap b km1 k)).row k =
    prev - projectionCoeff (b.row km1) swappedPrev • swappedPrev
  rw [basisMatrix_row_eq_basisRows_get!]
  have hkm1k : km1.val < k.val := by omega
  have hk_lt_swap_len : k.val < (Matrix.rowSwap b km1 k).toList.length := by
    simp [k.isLt]
  have hkm1_lt_b_len : km1.val < b.toList.length := by simp [km1.isLt]
  rw [basisRows_get!_eq_reduceAgainstBasis_take
        (Matrix.rowSwap b km1 k).toList k.val hk_lt_swap_len]
  -- Replace the swapped source row at index k with the original row at km1.
  have hswap_row :
      (Matrix.rowSwap b km1 k).toList[k.val]! = b.toList[km1.val]! :=
    rowSwap_toList_get!_right b km1 k
  -- Decompose the prefix of length k = km1 + 1.
  have hkm1_lt_swap_basis :
      km1.val < (basisRows (Matrix.rowSwap b km1 k).toList).length := by
    simp [basisRows_length, km1.isLt]
  have htake_succ :
      (basisRows (Matrix.rowSwap b km1 k).toList).take k.val =
        (basisRows (Matrix.rowSwap b km1 k).toList).take km1.val ++
          [(basisRows (Matrix.rowSwap b km1 k).toList)[km1.val]!] := by
    rw [show k.val = km1.val + 1 from hkm1.symm]
    rw [List.take_succ_eq_append_getElem hkm1_lt_swap_basis]
    congr 1
    simp [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hkm1_lt_swap_basis]
  -- The first km1 entries of `basisRows` agree before and after the swap.
  have hprefix :
      (basisRows (Matrix.rowSwap b km1 k).toList).take km1.val =
        (basisRows b.toList).take km1.val := by
    apply basisRows_take_eq_of_prefix
    · simp
    · intro t ht
      exact rowSwap_toList_get!_of_lt b km1 k t hkm1k ht
    · simp
  -- The km1-th entry of `basisRows` after the swap is `swappedPrev`.
  have hkm1_entry :
      (basisRows (Matrix.rowSwap b km1 k).toList)[km1.val]! = swappedPrev := by
    have hraw :=
      basisMatrix_rowSwap_adjacent_prev (b := b) (km1 := km1) (k := k) hkm1
    have hlhs :
        (basisRows (Matrix.rowSwap b km1 k).toList)[km1.val]! =
          (basisMatrix (Matrix.rowSwap b km1 k)).row km1 := by
      simp [basisMatrix, Matrix.row]
    rw [hlhs, hraw]
  rw [hswap_row, htake_succ, hprefix, hkm1_entry]
  -- Now apply `reduceAgainstBasis_append` to split off `swappedPrev`.
  have hreduce_split :
      reduceAgainstBasis (((basisRows b.toList).take km1.val ++ [swappedPrev]).reverse)
          b.toList[km1.val]! =
        reduceAgainstBasis ((basisRows b.toList).take km1.val).reverse
          (subtractProjection b.toList[km1.val]! swappedPrev) := by
    rw [List.reverse_append, reduceAgainstBasis_append]
    rfl
  rw [hreduce_split]
  -- Expand `subtractProjection` into row + (-proj) • swappedPrev and use linearity.
  have hsource_row : b.toList[km1.val]! = b.row km1 := by simp [Matrix.row]
  rw [hsource_row]
  have hsubP : ∀ u : Vector Rat m, subtractProjection (b.row km1) u =
      (b.row km1) + (- projectionCoeff (b.row km1) u) • u := by
    intro u
    apply Vector.ext
    intro idx hidx
    change ((b.row km1) - projectionCoeff (b.row km1) u • u)[idx] =
      ((b.row km1) + (- projectionCoeff (b.row km1) u) • u)[idx]
    rw [Vector.getElem_sub, Vector.getElem_smul, Vector.getElem_add, Vector.getElem_smul]
    change (b.row km1)[idx] - projectionCoeff (b.row km1) u * u[idx] =
      (b.row km1)[idx] + (- projectionCoeff (b.row km1) u) * u[idx]
    grind
  rw [hsubP swappedPrev, reduceAgainstBasis_add_left, reduceAgainstBasis_smul_left]
  -- Compute the (b.row km1) reduction → `prev`.
  have hreduce_row :
      reduceAgainstBasis ((basisRows b.toList).take km1.val).reverse (b.row km1) =
        prev := by
    have hrec :=
      basisRows_get!_eq_reduceAgainstBasis_take b.toList km1.val hkm1_lt_b_len
    have hbasis_km1 :
        (basisRows b.toList)[km1.val]! = (basisMatrix b).row km1 := by
      exact (basisMatrix_row_eq_basisRows_get! (b := b) km1.val km1.isLt).symm
    have hsrc_row : b.toList[km1.val]! = b.row km1 := by simp [Matrix.row]
    change reduceAgainstBasis _ (b.row km1) = (basisMatrix b).row km1
    rw [← hbasis_km1, hrec, hsrc_row]
  -- Show that `swappedPrev` is orthogonal to every row of `basisRows.take km1`,
  -- so the reduction is the identity on it.
  have hreduce_sP :
      reduceAgainstBasis ((basisRows b.toList).take km1.val).reverse swappedPrev =
        swappedPrev := by
    apply reduceAgainstBasis_eq_self_of_forall_dot_zero
    intro other hother
    rw [List.mem_reverse] at hother
    rw [List.mem_iff_getElem] at hother
    obtain ⟨idx, hidx, hget⟩ := hother
    have htake_len :
        ((basisRows b.toList).take km1.val).length = km1.val := by
      rw [List.length_take]
      simp [basisRows_length]
    have hidx_km1 : idx < km1.val := by
      rw [htake_len] at hidx
      exact hidx
    have hidx_basis_len : idx < (basisRows b.toList).length := by
      simp only [basisRows_length, Vector.length_toList]
      omega
    have hother_get :
        other = (basisRows b.toList)[idx]! := by
      rw [← hget, List.getElem_take]
      simp [hidx_basis_len]
    rw [hother_get]
    -- dot swappedPrev (basisRows[idx]) = dot curr (basisRows[idx]) + mu * dot prev (basisRows[idx])
    -- Both inner products vanish by pairwise orthogonality.
    have hcurr_orth :
        Matrix.dot curr (basisRows b.toList)[idx]! = 0 := by
      change Matrix.dot ((basisMatrix b).row k) _ = 0
      rw [basisMatrix_row_eq_basisRows_get!]
      exact basisRows_get!_dot_eq_zero_of_list b.toList k.val idx
        (by simp [k.isLt])
        (by simp only [Vector.length_toList]; omega)
        (by omega)
    have hprev_orth :
        Matrix.dot prev (basisRows b.toList)[idx]! = 0 := by
      change Matrix.dot ((basisMatrix b).row km1) _ = 0
      rw [basisMatrix_row_eq_basisRows_get!]
      exact basisRows_get!_dot_eq_zero_of_list b.toList km1.val idx
        (by simp [km1.isLt])
        (by simp only [Vector.length_toList]; omega)
        (by omega)
    show Matrix.dot (curr + mu • prev) _ = 0
    rw [dot_add_left, dot_smul_left, hcurr_orth, hprev_orth]
    grind
  rw [hreduce_row, hreduce_sP]
  -- Combine: prev + (-proj) • swappedPrev = prev - proj • swappedPrev
  have hfinal : ∀ p : Vector Rat m, ∀ u : Vector Rat m, ∀ s : Rat,
      p + (- s) • u = p - s • u := by
    intro p u s
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_add, Vector.getElem_sub, Vector.getElem_smul, Vector.getElem_smul]
    change p[idx] + (- s) * u[idx] = p[idx] - s * u[idx]
    grind
  exact hfinal prev swappedPrev (projectionCoeff (b.row km1) swappedPrev)

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

/-- Extend coefficients on a strict prefix by a zero coefficient on the new
last row of the inclusive prefix. -/
private def extendStrictPrefixCoeff (c : Vector Rat k) : Vector Rat (k + 1) :=
  Vector.ofFn fun j =>
    if h : j.val < k then
      let jj : Fin k := ⟨j.val, h⟩
      c[jj]
    else
      0

/-- Coefficients witnessing `prefixSumByRow` as a row combination of the strict
row prefix. -/
private def projectionCoeffVector (row : Vector Rat m) (basis : Matrix Rat n m)
    (k : Nat) (hk : k ≤ n) : Vector Rat k :=
  Vector.ofFn fun j =>
    projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)

private theorem rowCombination_prefixRows_extendStrictPrefixCoeff
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat i) :
    Matrix.rowCombination (prefixRows M i hi) (extendStrictPrefixCoeff c) =
      Matrix.rowCombination (strictPrefixRows M i (Nat.le_of_lt hi)) c := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change
    (Matrix.mulVec (Matrix.transpose (prefixRows M i hi))
        (extendStrictPrefixCoeff c))[idxFin] =
      (Matrix.mulVec (Matrix.transpose (strictPrefixRows M i (Nat.le_of_lt hi)))
        c)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose (prefixRows M i hi))
          (extendStrictPrefixCoeff c))[idxFin] =
        (List.finRange (i + 1)).foldl
          (fun acc j =>
            acc +
              (M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hi)⟩)[idxFin] *
                (extendStrictPrefixCoeff c)[j])
          0 by
        unfold Matrix.mulVec Matrix.transpose Matrix.col Matrix.row Matrix.dot
          Hex.Vector.dotProduct prefixRows
        simp [Matrix.row]]
  rw [show
      (Matrix.mulVec (Matrix.transpose (strictPrefixRows M i (Nat.le_of_lt hi)))
          c)[idxFin] =
        (List.finRange i).foldl
          (fun acc j =>
            acc +
              (M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt hi)⟩)[idxFin] *
                c[j])
          0 by
        unfold Matrix.mulVec Matrix.transpose Matrix.col Matrix.row Matrix.dot
          Hex.Vector.dotProduct strictPrefixRows
        simp [Matrix.row]]
  rw [List.finRange_succ_last]
  rw [List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  have hlast_not_lt : ¬i < i := Nat.lt_irrefl i
  simp [extendStrictPrefixCoeff, hlast_not_lt]
  grind

private theorem rowCombination_add_rat
    (M : Matrix Rat n m) (c d : Vector Rat n) :
    Matrix.rowCombination M (c + d) =
      Matrix.rowCombination M c + Matrix.rowCombination M d := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) (c + d))[idxFin] =
    (Matrix.rowCombination M c + Matrix.rowCombination M d)[idxFin]
  simp [Matrix.rowCombination, HMul.hMul, Matrix.mulVec, Matrix.transpose, Matrix.col,
    Matrix.row, Matrix.dot, Hex.Vector.dotProduct, Vector.getElem_add]
  have hfold :
      ∀ xs : List (Fin n), ∀ accC accD : Rat,
        xs.foldl
            (fun acc row =>
              acc + M[row.val][idxFin.val] * (c[row.val] + d[row.val]))
            (accC + accD) =
          xs.foldl (fun acc row => acc + M[row.val][idxFin.val] * c[row.val]) accC +
            xs.foldl (fun acc row => acc + M[row.val][idxFin.val] * d[row.val]) accD := by
    intro xs
    induction xs with
    | nil =>
        intro accC accD
        simp
    | cons row rows ih =>
        intro accC accD
        simp only [List.foldl_cons]
        have hstep :
            accC + accD + M[row.val][idxFin.val] * (c[row.val] + d[row.val]) =
              (accC + M[row.val][idxFin.val] * c[row.val]) +
                (accD + M[row.val][idxFin.val] * d[row.val]) := by
          grind
        rw [hstep]
        exact ih (accC + M[row.val][idxFin.val] * c[row.val])
          (accD + M[row.val][idxFin.val] * d[row.val])
  have h := hfold (List.finRange n) 0 0
  rw [show (0 : Rat) + 0 = 0 by grind] at h
  exact h

private theorem rowCombination_smul_rat
    (M : Matrix Rat n m) (a : Rat) (c : Vector Rat n) :
    Matrix.rowCombination M (a • c) =
      a • Matrix.rowCombination M c := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) (a • c))[idxFin] =
    (a • Matrix.rowCombination M c)[idxFin]
  simp [Matrix.rowCombination, HMul.hMul, Matrix.mulVec, Matrix.transpose, Matrix.col,
    Matrix.row, Matrix.dot, Hex.Vector.dotProduct, Vector.getElem_smul]
  have hfold :
      ∀ xs : List (Fin n), ∀ acc : Rat,
        xs.foldl
            (fun acc row => acc + M[row.val][idxFin.val] * (a * c[row.val]))
            (a * acc) =
          a * xs.foldl (fun acc row => acc + M[row.val][idxFin.val] * c[row.val]) acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp
    | cons row rows ih =>
        intro acc
        simp only [List.foldl_cons]
        have hstep :
            a * acc + M[row.val][idxFin.val] * (a * c[row.val]) =
              a * (acc + M[row.val][idxFin.val] * c[row.val]) := by
          grind
        rw [hstep]
        exact ih (acc + M[row.val][idxFin.val] * c[row.val])
  simpa using hfold (List.finRange n) 0

/-- `prefixSpan_add` says the rational prefix row-span is closed under vector addition. -/
private theorem prefixSpan_add
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) {u v : Vector Rat m}
    (hu : prefixSpan M i hi u) (hv : prefixSpan M i hi v) :
    prefixSpan M i hi (u + v) := by
  rcases hu with ⟨cu, hcu⟩
  rcases hv with ⟨cv, hcv⟩
  refine ⟨cu + cv, ?_⟩
  rw [rowCombination_add_rat, hcu, hcv]

/-- `prefixSpan_smul` says the rational prefix row-span is closed under scalar multiplication. -/
private theorem prefixSpan_smul
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (a : Rat) {u : Vector Rat m}
    (hu : prefixSpan M i hi u) :
    prefixSpan M i hi (a • u) := by
  rcases hu with ⟨cu, hcu⟩
  refine ⟨a • cu, ?_⟩
  rw [rowCombination_smul_rat, hcu]

/-- `prefixSpan_sub` says the rational prefix row-span is closed under vector subtraction. -/
private theorem prefixSpan_sub
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) {u v : Vector Rat m}
    (hu : prefixSpan M i hi u) (hv : prefixSpan M i hi v) :
    prefixSpan M i hi (u - v) := by
  have hneg : prefixSpan M i hi ((-1 : Rat) • v) :=
    prefixSpan_smul M i hi (-1) hv
  have hadd := prefixSpan_add M i hi hu hneg
  have hsub : u + (-1 : Rat) • v = u - v := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_add, Vector.getElem_smul, Vector.getElem_sub]
    change u[idx] + (-1 : Rat) * v[idx] = u[idx] - v[idx]
    grind
  simpa [← hsub] using hadd

/-- `dot_add_right` gives additivity of the rational dot product in its right argument. -/
private theorem dot_add_right (a b c : Vector Rat m) :
    Matrix.dot a (b + c) = Matrix.dot a b + Matrix.dot a c := by
  rw [dot_comm_rat, dot_add_left, dot_comm_rat b a, dot_comm_rat c a]

/-- `dot_smul_right` pulls a rational scalar out of the right argument of the dot product. -/
private theorem dot_smul_right (s : Rat) (a b : Vector Rat m) :
    Matrix.dot a (s • b) = s * Matrix.dot a b := by
  rw [dot_comm_rat, dot_smul_left, dot_comm_rat b a]

/-- `dot_sub_right` gives subtractivity of the rational dot product in its right argument. -/
private theorem dot_sub_right (a b c : Vector Rat m) :
    Matrix.dot a (b - c) = Matrix.dot a b - Matrix.dot a c := by
  have hsub : b - c = b + (-1 : Rat) • c := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_sub, Vector.getElem_add, Vector.getElem_smul]
    change b[idx] - c[idx] = b[idx] + (-1 : Rat) * c[idx]
    grind
  rw [hsub, dot_add_right, dot_smul_right]
  grind

/-- `dot_zero_right` says the rational dot product with a zero right argument is zero. -/
private theorem dot_zero_right (a : Vector Rat m) :
    Matrix.dot a 0 = 0 := by
  unfold Matrix.dot Hex.Vector.dotProduct
  change (List.finRange m).foldl
      (fun acc i => acc + a[i] * (0 : Vector Rat m)[i]) 0 = 0
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hterm : a[i] * (0 : Vector Rat m)[i] = 0 := by
        change a[i] * (0 : Vector Rat m)[i.val] = 0
        rw [Vector.getElem_zero]
        grind
      rw [hterm]
      rw [show (0 : Rat) + 0 = 0 by grind]
      exact ih

private def unitCoeff (j : Fin n) : Vector Rat n :=
  Vector.ofFn fun k => if k = j then 1 else 0

private theorem foldl_add_eq_acc_rat
    {α : Type} (xs : List α) (f : α → Rat) (acc : Rat)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hacc : acc + (0 : Rat) = acc := by grind
      rw [hacc]
      exact ih acc hxs

private theorem foldl_indicator_mul_unique_rat
    (xs : List (Fin n)) (i : Fin n) (f : Fin n → Rat)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : Rat) :
    xs.foldl (fun acc l => acc + f l * (if l = i then (1 : Rat) else 0)) acc =
      acc + f i := by
  induction xs generalizing acc with
  | nil =>
      exact absurd hi List.not_mem_nil
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hix | hitail
      · subst i
        rw [if_pos rfl]
        have hxs_zero :
            ∀ y ∈ xs, f y * (if y = x then (1 : Rat) else 0) = 0 := by
          intro y hy
          have hyx : y ≠ x := by
            intro heq
            exact (List.nodup_cons.mp hnodup).1 (heq ▸ hy)
          rw [if_neg hyx]
          grind
        have hfold :=
          foldl_add_eq_acc_rat xs
            (fun l => f l * (if l = x then (1 : Rat) else 0))
            (acc + f x * 1) hxs_zero
        have hfold' :
            xs.foldl (fun acc l => acc + f l * (if l = x then (1 : Rat) else 0))
                (acc + f x * 1) =
              acc + f x * 1 := hfold
        rw [hfold']
        grind
      · have hxi : x ≠ i := by
          intro h
          subst i
          exact (List.nodup_cons.mp hnodup).1 hitail
        rw [if_neg hxi]
        have hzero : f x * (0 : Rat) = 0 := by grind
        rw [hzero]
        have hacc : acc + (0 : Rat) = acc := by grind
        rw [hacc]
        exact ih hitail (List.nodup_cons.mp hnodup).2 acc

private theorem rowCombination_prefixRows_unitCoeff
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (j : Fin (i + 1)) :
    Matrix.rowCombination (prefixRows M i hi) (unitCoeff j) =
      (prefixRows M i hi).row j := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change
    (Matrix.mulVec (Matrix.transpose (prefixRows M i hi)) (unitCoeff j))[idxFin] =
      ((prefixRows M i hi).row j)[idxFin]
  simp [HMul.hMul, Matrix.mulVec, Matrix.transpose, Matrix.col,
    Matrix.row, Matrix.dot, Hex.Vector.dotProduct, unitCoeff]
  have h :=
    foldl_indicator_mul_unique_rat
      (xs := List.finRange (i + 1)) (i := j)
      (f := fun row : Fin (i + 1) => (prefixRows M i hi)[row.val][idxFin.val])
      (hi := List.mem_finRange j) (hnodup := List.nodup_finRange (i + 1)) (acc := 0)
  rw [show (0 : Rat) + (prefixRows M i hi)[j.val][idxFin.val] =
      (prefixRows M i hi)[j.val][idxFin.val] by grind] at h
  exact h

private theorem prefixSpan_row
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (j : Fin (i + 1)) :
    prefixSpan M i hi ((prefixRows M i hi).row j) := by
  exact ⟨unitCoeff j, rowCombination_prefixRows_unitCoeff M i hi j⟩

private theorem rowCombination_eq_foldl_rows
    (M : Matrix Rat n m) (c : Vector Rat n) :
    Matrix.rowCombination M c =
      (List.finRange n).foldl (fun acc j => acc + c[j] • M.row j) 0 := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) c)[idxFin] =
    ((List.finRange n).foldl (fun acc j => acc + c[j] • M.row j) 0)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose M) c)[idxFin] =
        (List.finRange n).foldl
          (fun acc j => acc + M[j.val][idxFin.val] * c[j])
          0 by
        unfold Matrix.mulVec Matrix.transpose Matrix.col Matrix.row Matrix.dot
          Hex.Vector.dotProduct
        simp]
  have hfold :
      ∀ xs : List (Fin n), ∀ accL : Rat, ∀ accR : Vector Rat m,
        accL = accR[idxFin] →
        xs.foldl (fun acc j => acc + M[j.val][idxFin.val] * c[j]) accL =
          (xs.foldl (fun acc j => acc + c[j] • M.row j) accR)[idxFin] := by
    intro xs
    induction xs with
    | nil =>
        intro accL accR hacc
        simp [hacc]
    | cons j rest ih =>
        intro accL accR hacc
        simp only [List.foldl_cons]
        apply ih
        change accL + M[j.val][idxFin.val] * c[j] =
          (accR + c[j] • M.row j)[idxFin.val]
        rw [Vector.getElem_add, Vector.getElem_smul]
        rw [hacc]
        change accR[idx] + M[j.val][idx] * c[j] =
          accR[idx] + c[j] * M[j.val][idx]
        grind
  exact hfold (List.finRange n) 0 0 (by simp [Vector.getElem_zero])

private theorem dot_eq_zero_of_prefixSpan
    (M : Matrix Rat n m) (i : Nat) (hi : i < n)
    (u v : Vector Rat m)
    (hspan : prefixSpan M i hi v)
    (horth : ∀ j : Fin (i + 1), Matrix.dot u ((prefixRows M i hi).row j) = 0) :
    Matrix.dot u v = 0 := by
  rcases hspan with ⟨c, hc⟩
  rw [← hc, rowCombination_eq_foldl_rows]
  have hfold :
      ∀ xs : List (Fin (i + 1)), ∀ acc : Vector Rat m,
        Matrix.dot u acc = 0 →
          Matrix.dot u
            (xs.foldl
              (fun acc j => acc + c[j] • (prefixRows M i hi).row j) acc) = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons j rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        rw [dot_add_right, dot_smul_right, hacc, horth j]
        grind
  exact hfold (List.finRange (i + 1)) 0 (dot_zero_right u)

/-- `Vector.normSq v` is nonnegative for a rational vector, since it is the
self-dot-product, a sum of squares (via `foldl_dot_self_start_le`). -/
private theorem rat_normSq_nonneg (v : Vector Rat m) :
    0 ≤ Vector.normSq v := by
  simpa [Vector.normSq, Matrix.dot, Hex.Vector.dotProduct] using
    foldl_dot_self_start_le (xs := List.finRange m) (v := v)
      (acc := 0) (by decide)

/-- Pythagorean split: when `acc` is orthogonal to `row`, the squared norm of
`acc + c • row` expands to `Vector.normSq acc + c * c * Vector.normSq row`. -/
private theorem normSq_add_smul_of_orthogonal
    (acc row : Vector Rat m) (c : Rat)
    (horth : Matrix.dot acc row = 0) :
    Vector.normSq (acc + c • row) =
      Vector.normSq acc + c * c * Vector.normSq row := by
  change Matrix.dot (acc + c • row) (acc + c • row) =
    Matrix.dot acc acc + c * c * Matrix.dot row row
  rw [dot_add_left]
  rw [dot_add_right acc acc (c • row)]
  rw [dot_smul_right]
  rw [dot_smul_left]
  rw [dot_add_right row acc (c • row)]
  rw [dot_smul_right]
  rw [horth]
  have horth' : Matrix.dot row acc = 0 := by
    rw [dot_comm_rat]
    exact horth
  rw [horth']
  grind

/-- A left fold summing `f` over `xs` factors its starting accumulator out:
`xs.foldl (· + f ·) acc = acc + xs.foldl (· + f ·) 0`. -/
private theorem foldl_rat_sum_start {α : Type v}
    (xs : List α) (f : α → Rat) (acc : Rat) :
    xs.foldl (fun total x => total + f x) acc =
      acc + xs.foldl (fun total x => total + f x) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
      grind
  | cons x xs ih =>
    simp only [List.foldl_cons]
    calc
      xs.foldl (fun total x => total + f x) (acc + f x) =
          (acc + f x) + xs.foldl (fun total x => total + f x) 0 := ih (acc + f x)
      _ = acc + ((0 + f x) + xs.foldl (fun total x => total + f x) 0) := by grind
      _ = acc + xs.foldl (fun total x => total + f x) (0 + f x) := by
          rw [ih (0 + f x)]

/-- Orthogonal-expansion of a folded row combination: when the listed rows are
pairwise orthogonal and `acc` is orthogonal to each, the squared norm of the
fold splits as `Vector.normSq acc` plus the fold of weighted squared norms
`coeffs[i] * coeffs[i] * Vector.normSq (rows.row i)`. -/
private theorem foldl_orthogonal_expansion_normSq
    (xs : List (Fin n)) (rows : Matrix Rat n m) (coeffs : Vector Rat n)
    (acc : Vector Rat m)
    (hnodup : xs.Nodup)
    (hacc : ∀ i ∈ xs, Matrix.dot acc (rows.row i) = 0)
    (horth : ∀ i ∈ xs, ∀ j ∈ xs, i ≠ j →
      Matrix.dot (rows.row i) (rows.row j) = 0) :
    Vector.normSq
        (xs.foldl (fun acc i => acc + coeffs[i] • rows.row i) acc) =
      Vector.normSq acc +
        xs.foldl
          (fun total i => total + coeffs[i] * coeffs[i] * Vector.normSq (rows.row i)) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
      grind
  | cons i rest ih =>
    simp only [List.foldl_cons]
    have hnodup_tail : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hi_not_mem : i ∉ rest := (List.nodup_cons.mp hnodup).1
    let acc' := acc + coeffs[i] • rows.row i
    have hacc' : ∀ j ∈ rest, Matrix.dot acc' (rows.row j) = 0 := by
      intro j hj
      have hij : i ≠ j := by
        intro h
        subst h
        exact hi_not_mem hj
      have hrow : Matrix.dot (rows.row i) (rows.row j) = 0 :=
        horth i (by simp) j (by simp [hj]) hij
      simp only [acc']
      rw [dot_add_left, dot_smul_left, hacc j (by simp [hj]), hrow]
      grind
    have horth' : ∀ a ∈ rest, ∀ b ∈ rest, a ≠ b →
        Matrix.dot (rows.row a) (rows.row b) = 0 := by
      intro a ha b hb hab
      exact horth a (by simp [ha]) b (by simp [hb]) hab
    rw [ih (acc := acc') hnodup_tail hacc' horth']
    rw [normSq_add_smul_of_orthogonal acc (rows.row i) coeffs[i] (hacc i (by simp))]
    rw [foldl_rat_sum_start rest
      (fun j => coeffs[j] * coeffs[j] * Vector.normSq (rows.row j))
      (0 + coeffs[i] * coeffs[i] * Vector.normSq (rows.row i))]
    grind

/-- The `acc = 0` case of `foldl_orthogonal_expansion_normSq`: for pairwise
orthogonal rows the squared norm of the full row combination equals the fold of
`coeffs[i] * coeffs[i] * Vector.normSq (rows.row i)` over `List.finRange n`. -/
private theorem foldl_orthogonal_expansion_normSq_zero
    (rows : Matrix Rat n m) (coeffs : Vector Rat n)
    (horth : ∀ i j : Fin n, i ≠ j →
      Matrix.dot (rows.row i) (rows.row j) = 0) :
    Vector.normSq
        ((List.finRange n).foldl (fun acc i => acc + coeffs[i] • rows.row i) 0) =
      (List.finRange n).foldl
        (fun total i => total + coeffs[i] * coeffs[i] * Vector.normSq (rows.row i)) 0 := by
  have hacc : ∀ i ∈ List.finRange n, Matrix.dot (0 : Vector Rat m) (rows.row i) = 0 := by
    intro i _hi
    rw [dot_comm_rat]
    exact dot_zero_right (rows.row i)
  have horth' : ∀ i ∈ List.finRange n, ∀ j ∈ List.finRange n, i ≠ j →
      Matrix.dot (rows.row i) (rows.row j) = 0 := by
    intro i _hi j _hj hij
    exact horth i j hij
  have h :=
    foldl_orthogonal_expansion_normSq (xs := List.finRange n)
      (rows := rows) (coeffs := coeffs) (acc := (0 : Vector Rat m))
      (List.nodup_finRange n) hacc horth'
  have hzero : Vector.normSq (0 : Vector Rat m) = 0 := by
    have hfold :
        ∀ xs : List (Fin m), ∀ acc : Rat,
          xs.foldl (fun acc _ => acc + 0) acc = acc := by
      intro xs
      induction xs with
      | nil =>
          intro acc
          simp
      | cons _ rest ih =>
          intro acc
          simp only [List.foldl_cons]
          have hacc : acc + 0 = acc := by grind
          rw [hacc]
          exact ih acc
    simpa [Vector.normSq, Hex.Vector.dotProduct] using
      hfold (List.finRange m) 0
  rw [hzero] at h
  have hzero_add :
      (0 : Rat) +
          (List.finRange n).foldl
            (fun total i => total + coeffs[i] * coeffs[i] * Vector.normSq (rows.row i)) 0 =
        (List.finRange n).foldl
            (fun total i => total + coeffs[i] * coeffs[i] * Vector.normSq (rows.row i)) 0 := by
    grind
  rw [hzero_add] at h
  exact h

/-- The weighted-squared-norm fold `xs.foldl (· + coeffs[i] * coeffs[i] *
Vector.normSq (rows.row i)) 0` is nonnegative, being a sum of nonnegative
terms. -/
private theorem foldl_orthogonal_weighted_nonneg
    (xs : List (Fin n)) (rows : Matrix Rat n m) (coeffs : Vector Rat n) :
    0 ≤ xs.foldl
      (fun total i => total + coeffs[i] * coeffs[i] * Vector.normSq (rows.row i)) 0 := by
  induction xs with
  | nil =>
      simp
  | cons i rest ih =>
      simp only [List.foldl_cons]
      rw [foldl_rat_sum_start rest
        (fun j => coeffs[j] * coeffs[j] * Vector.normSq (rows.row j))
        (0 + coeffs[i] * coeffs[i] * Vector.normSq (rows.row i))]
      have hterm : 0 ≤ coeffs[i] * coeffs[i] * Vector.normSq (rows.row i) :=
        Rat.mul_nonneg (rat_mul_self_nonneg coeffs[i]) (rat_normSq_nonneg (rows.row i))
      exact Rat.add_nonneg (by grind) ih

/-- If `k ∈ xs` and its coefficient square is at least `1`, the
weighted-squared-norm fold over `xs` is at least `Vector.normSq (rows.row k)`,
the single term contributed by `k`. -/
private theorem foldl_orthogonal_weighted_normSq_ge
    (xs : List (Fin n)) (rows : Matrix Rat n m) (coeffs : Vector Rat n)
    (k : Fin n) (hk : k ∈ xs)
    (hcoeff : 1 ≤ coeffs[k] * coeffs[k]) :
    Vector.normSq (rows.row k) ≤
      xs.foldl
        (fun total i => total + coeffs[i] * coeffs[i] * Vector.normSq (rows.row i)) 0 := by
  induction xs with
  | nil =>
      cases hk
  | cons i rest ih =>
      simp only [List.foldl_cons]
      simp only [List.mem_cons] at hk
      have hterm_nonneg :
          0 ≤ coeffs[i] * coeffs[i] * Vector.normSq (rows.row i) := by
        exact Rat.mul_nonneg (rat_mul_self_nonneg coeffs[i]) (rat_normSq_nonneg (rows.row i))
      cases hk with
      | inl hik =>
          subst hik
          rw [foldl_rat_sum_start rest
            (fun j => coeffs[j] * coeffs[j] * Vector.normSq (rows.row j))
            (0 + coeffs[k] * coeffs[k] * Vector.normSq (rows.row k))]
          have hrow_nonneg : 0 ≤ Vector.normSq (rows.row k) :=
            rat_normSq_nonneg (rows.row k)
          have hfirst :
              Vector.normSq (rows.row k) ≤
                coeffs[k] * coeffs[k] * Vector.normSq (rows.row k) := by
            have hdelta_nonneg : 0 ≤ (coeffs[k] * coeffs[k] - 1) *
                Vector.normSq (rows.row k) :=
              Rat.mul_nonneg (by grind) hrow_nonneg
            have hsplit :
                coeffs[k] * coeffs[k] * Vector.normSq (rows.row k) =
                  Vector.normSq (rows.row k) +
                    (coeffs[k] * coeffs[k] - 1) * Vector.normSq (rows.row k) := by
              grind
            calc
              Vector.normSq (rows.row k) ≤
                  Vector.normSq (rows.row k) +
                    (coeffs[k] * coeffs[k] - 1) * Vector.normSq (rows.row k) := by
                    grind
              _ = coeffs[k] * coeffs[k] * Vector.normSq (rows.row k) := hsplit.symm
          have htail_nonneg :
              0 ≤ rest.foldl
                (fun total j => total + coeffs[j] * coeffs[j] * Vector.normSq (rows.row j)) 0 := by
            exact foldl_orthogonal_weighted_nonneg rest rows coeffs
          exact Rat.le_trans hfirst (by grind)
      | inr htail =>
          have htail_le := ih htail
          rw [foldl_rat_sum_start rest
            (fun j => coeffs[j] * coeffs[j] * Vector.normSq (rows.row j))
            (0 + coeffs[i] * coeffs[i] * Vector.normSq (rows.row i))]
          exact Rat.le_trans htail_le (by grind)

/-- Orthogonal row-combination lower bound. If the rows of `rows` are pairwise
orthogonal and the coefficient at `k` has square at least `1`, then the squared
norm of the whole row combination is at least the squared norm of row `k`. -/
theorem rowCombination_normSq_ge_of_orthogonal_coeff_sq_ge_one
    (rows : Matrix Rat n m) (coeffs : Vector Rat n) (k : Fin n)
    (horth : ∀ i j : Fin n, i ≠ j →
      Matrix.dot (rows.row i) (rows.row j) = 0)
    (hcoeff : 1 ≤ coeffs[k] * coeffs[k]) :
    Vector.normSq (rows.row k) ≤ Vector.normSq (Matrix.rowCombination rows coeffs) := by
  rw [rowCombination_eq_foldl_rows]
  rw [foldl_orthogonal_expansion_normSq_zero rows coeffs horth]
  exact foldl_orthogonal_weighted_normSq_ge (xs := List.finRange n)
    (rows := rows) (coeffs := coeffs) k (by simp) hcoeff

/-- A nonzero integer coefficient has rational square at least `1`. -/
theorem one_le_intCast_mul_self_of_ne_zero (z : Int) (hz : z ≠ 0) :
    (1 : Rat) ≤ ((z : Rat) * (z : Rat)) := by
  cases z with
  | ofNat n =>
      cases n with
      | zero =>
          exact False.elim (hz rfl)
      | succ n =>
          let a : Rat := ((Nat.succ n : Nat) : Rat)
          have hge : (1 : Rat) ≤ a := by
            have hnat : 1 ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
            dsimp [a]
            exact_mod_cast hnat
          have hnonneg : (0 : Rat) ≤ a := by
            exact Rat.le_trans (by decide) hge
          have hsum_nonneg : 0 ≤ a + 1 := by grind
          have hprod_nonneg : 0 ≤ (a - 1) * (a + 1) :=
            Rat.mul_nonneg (by grind) hsum_nonneg
          have hsplit : a * a = 1 + (a - 1) * (a + 1) := by grind
          change (1 : Rat) ≤ a * a
          rw [hsplit]
          grind
  | negSucc n =>
      have hpos :
          (1 : Rat) ≤ (((Nat.succ n : Nat) : Rat) * ((Nat.succ n : Nat) : Rat)) := by
        let a : Rat := ((Nat.succ n : Nat) : Rat)
        have hge : (1 : Rat) ≤ a := by
          have hnat : 1 ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
          dsimp [a]
          exact_mod_cast hnat
        have hnonneg : (0 : Rat) ≤ a := by
          exact Rat.le_trans (by decide) hge
        have hsum_nonneg : 0 ≤ a + 1 := by grind
        have hprod_nonneg : 0 ≤ (a - 1) * (a + 1) :=
          Rat.mul_nonneg (by grind) hsum_nonneg
        have hsplit : a * a = 1 + (a - 1) * (a + 1) := by grind
        change (1 : Rat) ≤ a * a
        rw [hsplit]
        grind
      change (1 : Rat) ≤ (-(↑(Nat.succ n) : Rat)) * (-(↑(Nat.succ n) : Rat))
      have hsq :
          (-(↑(Nat.succ n) : Rat)) * (-(↑(Nat.succ n) : Rat)) =
            (↑(Nat.succ n) : Rat) * (↑(Nat.succ n) : Rat) := by
        grind
      rw [hsq]
      exact hpos

private theorem eq_zero_of_prefixSpan_of_forall_dot_zero
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (v : Vector Rat m)
    (hspan : prefixSpan M i hi v)
    (horth : ∀ j : Fin (i + 1), Matrix.dot v ((prefixRows M i hi).row j) = 0) :
    v = 0 := by
  have hself : Matrix.dot v v = 0 :=
    dot_eq_zero_of_prefixSpan M i hi v v hspan horth
  apply Vector.ext
  intro idx hidx
  rw [Vector.getElem_zero]
  exact dot_self_eq_zero_get v hself ⟨idx, hidx⟩

/-- If two residuals reconstruct the same source row modulo the same prefix
span and are both orthogonal to that prefix, they are equal. This is the
local uniqueness principle used by suffix row-swap proofs after translating
equal generated prefixes into equal `prefixSpan` predicates. -/
private theorem residual_eq_of_same_prefixSpan
    (M : Matrix Rat n m) (i : Nat) (hi : i < n)
    (row r s : Vector Rat m)
    (hrspan : prefixSpan M i hi (row - r))
    (hsspan : prefixSpan M i hi (row - s))
    (hrorth : ∀ j : Fin (i + 1), Matrix.dot r ((prefixRows M i hi).row j) = 0)
    (hsorth : ∀ j : Fin (i + 1), Matrix.dot s ((prefixRows M i hi).row j) = 0) :
    r = s := by
  have hspanDiff :
      prefixSpan M i hi ((row - s) - (row - r)) :=
    prefixSpan_sub M i hi hsspan hrspan
  have hdiff_eq : (row - s) - (row - r) = r - s := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_sub, Vector.getElem_sub, Vector.getElem_sub]
    grind
  have hspan : prefixSpan M i hi (r - s) := by
    simpa [hdiff_eq] using hspanDiff
  have horth : ∀ j : Fin (i + 1),
      Matrix.dot (r - s) ((prefixRows M i hi).row j) = 0 := by
    intro j
    rw [dot_comm_rat (r - s) ((prefixRows M i hi).row j)]
    rw [dot_sub_right]
    rw [dot_comm_rat ((prefixRows M i hi).row j) r,
      dot_comm_rat ((prefixRows M i hi).row j) s, hrorth j, hsorth j]
    grind
  have hzero := eq_zero_of_prefixSpan_of_forall_dot_zero M i hi (r - s) hspan horth
  apply Vector.ext
  intro idx hidx
  have hz := congrArg (fun v : Vector Rat m => v[(⟨idx, hidx⟩ : Fin m)]) hzero
  change (r - s)[idx] = (0 : Vector Rat m)[idx] at hz
  rw [Vector.getElem_sub, Vector.getElem_zero] at hz
  grind

/-- Residual uniqueness across two prefix bases with the same span. The
second residual only needs to reconstruct modulo `B`; the span equality and
orthogonality transport move it to `A`, where `residual_eq_of_same_prefixSpan`
applies. -/
private theorem residual_eq_of_equiv_prefixSpan
    (A B : Matrix Rat n m) (i : Nat) (hi : i < n)
    (row r s : Vector Rat m)
    (hrspan : prefixSpan A i hi (row - r))
    (hsspan : prefixSpan B i hi (row - s))
    (hB_to_A : ∀ v : Vector Rat m, prefixSpan B i hi v → prefixSpan A i hi v)
    (hA_rows_to_B :
      ∀ j : Fin (i + 1), prefixSpan B i hi ((prefixRows A i hi).row j))
    (hrorth : ∀ j : Fin (i + 1), Matrix.dot r ((prefixRows A i hi).row j) = 0)
    (hsorth : ∀ j : Fin (i + 1), Matrix.dot s ((prefixRows B i hi).row j) = 0) :
    r = s := by
  apply residual_eq_of_same_prefixSpan A i hi row r s hrspan (hB_to_A _ hsspan) hrorth
  intro j
  exact dot_eq_zero_of_prefixSpan B i hi s ((prefixRows A i hi).row j)
    (hA_rows_to_B j) hsorth

/-- `prefixSpan_zero` states that the zero vector is contained in every prefix span, providing the base case for prefix-span closure arguments. -/
private theorem prefixSpan_zero
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) :
    prefixSpan M i hi 0 := by
  let j : Fin (i + 1) := ⟨0, Nat.succ_pos i⟩
  have hz := prefixSpan_smul M i hi 0 (prefixSpan_row M i hi j)
  have hzero : (0 : Rat) • (prefixRows M i hi).row j = 0 := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_smul, Vector.getElem_zero]
    change (0 : Rat) * ((prefixRows M i hi).row j)[idx] = 0
    grind
  simpa [hzero] using hz

/-- `prefixSpan_rowCombination_of_rows` states that any row combination of prefix rows already in another prefix span remains in that prefix span. -/
private theorem prefixSpan_rowCombination_of_rows
    (A B : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat (i + 1))
    (hrows : ∀ j : Fin (i + 1), prefixSpan B i hi ((prefixRows A i hi).row j)) :
    prefixSpan B i hi (Matrix.rowCombination (prefixRows A i hi) c) := by
  rw [rowCombination_eq_foldl_rows]
  have hfold :
      ∀ xs : List (Fin (i + 1)), ∀ acc : Vector Rat m,
        prefixSpan B i hi acc →
          prefixSpan B i hi
            (xs.foldl
              (fun acc j => acc + c[j] • (prefixRows A i hi).row j) acc) := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons j rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        exact prefixSpan_add B i hi hacc
          (prefixSpan_smul B i hi c[j] (hrows j))
  exact hfold (List.finRange (i + 1)) 0 (prefixSpan_zero B i hi)

/-- `strictPrefixRows_succ_eq_prefixRows` identifies the strict prefix of length `i + 1` with the inclusive prefix through row `i`. -/
private theorem strictPrefixRows_succ_eq_prefixRows
    (M : Matrix Rat n m) (i : Nat) (hi : i + 1 < n) :
    strictPrefixRows M (i + 1) (Nat.le_of_lt hi) =
      prefixRows M i (Nat.lt_of_succ_lt hi) := by
  apply Vector.ext
  intro row hrow
  apply Vector.ext
  intro col hcol
  rfl

/-- `prefixSpan_mono_succ` lifts prefix-span membership across one successor step in the prefix length. -/
private theorem prefixSpan_mono_succ
    (M : Matrix Rat n m) (i : Nat) (hi : i + 1 < n) {v : Vector Rat m}
    (hv : prefixSpan M i (Nat.lt_of_succ_lt hi) v) :
    prefixSpan M (i + 1) hi v := by
  rcases hv with ⟨c, hc⟩
  refine ⟨extendStrictPrefixCoeff c, ?_⟩
  rw [rowCombination_prefixRows_extendStrictPrefixCoeff]
  rw [strictPrefixRows_succ_eq_prefixRows (hi := hi)]
  exact hc

/-- `prefixSpan_mono_le` lifts prefix-span membership along any ordered pair of prefix indices. -/
private theorem prefixSpan_mono_le
    (M : Matrix Rat n m) {j i : Nat} (hj : j < n) (hi : i < n) (hji : j ≤ i)
    {v : Vector Rat m} (hv : prefixSpan M j hj v) :
    prefixSpan M i hi v := by
  induction hji with
  | refl =>
      exact hv
  | step hji ih =>
      exact prefixSpan_mono_succ M _ hi (ih (Nat.lt_of_succ_lt hi))

/-- `prefixSpan_matrix_row` records that each matrix row belongs to the prefix span ending at that row. -/
private theorem prefixSpan_matrix_row
    (M : Matrix Rat n m) (j : Fin n) :
    prefixSpan M j.val j.isLt (M.row j) := by
  let last : Fin (j.val + 1) := ⟨j.val, Nat.lt_succ_self j.val⟩
  simpa [prefixRows, Matrix.row] using prefixSpan_row M j.val j.isLt last

private theorem prefixRows_rowSwap_row_mem_prefixSpan
    (b : Matrix Rat n m) (km1 k : Fin n) (i : Nat) (hi : i < n)
    (hkm1k : km1.val < k.val) (hki : k.val ≤ i) (j : Fin (i + 1)) :
    prefixSpan b i hi ((prefixRows (Matrix.rowSwap b km1 k) i hi).row j) := by
  let r : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hi)⟩
  have hkm1_ne_k : km1 ≠ k := by
    intro h
    exact Nat.ne_of_lt hkm1k (congrArg Fin.val h)
  by_cases hjkm1 : r = km1
  · have hrow :
        (prefixRows (Matrix.rowSwap b km1 k) i hi).row j = b.row k := by
      apply Vector.ext
      intro col hcol
      let c : Fin m := ⟨col, hcol⟩
      simp [prefixRows, Matrix.row]
      change (Matrix.rowSwap b km1 k)[r][c] = b[k][c]
      rw [Matrix.rowSwap_getElem]
      simp [hjkm1, hkm1_ne_k]
    rw [hrow]
    exact prefixSpan_mono_le b k.isLt hi hki (prefixSpan_matrix_row b k)
  · by_cases hjk : r = k
    · have hkm1_le_i : km1.val ≤ i := by
        omega
      have hrow :
          (prefixRows (Matrix.rowSwap b km1 k) i hi).row j = b.row km1 := by
        apply Vector.ext
        intro col hcol
        let c : Fin m := ⟨col, hcol⟩
        simp [prefixRows, Matrix.row]
        change (Matrix.rowSwap b km1 k)[r][c] = b[km1][c]
        rw [Matrix.rowSwap_getElem]
        simp [hjk]
      rw [hrow]
      exact prefixSpan_mono_le b km1.isLt hi hkm1_le_i (prefixSpan_matrix_row b km1)
    · have hrle : r.val ≤ i := Nat.le_of_lt_succ j.isLt
      have hrow :
          (prefixRows (Matrix.rowSwap b km1 k) i hi).row j = b.row r := by
        apply Vector.ext
        intro col hcol
        let c : Fin m := ⟨col, hcol⟩
        simp [prefixRows, Matrix.row, r]
        change (Matrix.rowSwap b km1 k)[r][c] = b[r][c]
        rw [Matrix.rowSwap_getElem]
        simp [hjk, hjkm1]
      rw [hrow]
      exact prefixSpan_mono_le b r.isLt hi hrle (prefixSpan_matrix_row b r)

private theorem prefixSpan_rowSwap_adjacent_at_or_after
    (b : Matrix Rat n m) (km1 k : Fin n) (i : Nat) (hi : i < n)
    (hkm1 : km1.val + 1 = k.val) (hki : k.val ≤ i) (v : Vector Rat m) :
    prefixSpan (Matrix.rowSwap b km1 k) i hi v ↔ prefixSpan b i hi v := by
  constructor
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      prefixSpan_rowCombination_of_rows
        (A := Matrix.rowSwap b km1 k) (B := b) (i := i) (hi := hi) c
        (by
          intro j
          exact prefixRows_rowSwap_row_mem_prefixSpan
            (b := b) (km1 := km1) (k := k) (i := i) (hi := hi)
            (by omega) hki j)
    rwa [hc] at hspan
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      prefixSpan_rowCombination_of_rows
        (A := b) (B := Matrix.rowSwap b km1 k) (i := i) (hi := hi) c
        (by
          intro j
          have hrowspan :=
            prefixRows_rowSwap_row_mem_prefixSpan
              (b := Matrix.rowSwap b km1 k) (km1 := km1) (k := k)
              (i := i) (hi := hi) (by omega) hki j
          have hswap_swap : Matrix.rowSwap (Matrix.rowSwap b km1 k) km1 k = b := by
            exact Matrix.rowSwap_rowSwap b km1 k
          simpa [hswap_swap] using hrowspan)
    rwa [hc] at hspan

private theorem prefixSpan_strictPrefix_rowCombination
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat i) :
    prefixSpan M i hi
      (Matrix.rowCombination (strictPrefixRows M i (Nat.le_of_lt hi)) c) := by
  cases i with
  | zero =>
      have hcomb :
          Matrix.rowCombination (strictPrefixRows M 0 (Nat.le_of_lt hi)) c = 0 := by
        rw [rowCombination_eq_foldl_rows]
        simp
      simpa [hcomb] using prefixSpan_zero M 0 hi
  | succ k =>
      have hk : k < n := Nat.lt_of_succ_lt hi
      rw [strictPrefixRows_succ_eq_prefixRows (M := M) (i := k) (hi := hi)]
      have hspan :
          prefixSpan M k hk
            (Matrix.rowCombination (prefixRows M k hk) c) := by
        apply prefixSpan_rowCombination_of_rows
        intro row
        have hself :=
          prefixSpan_matrix_row M (⟨row.val, Nat.lt_trans row.isLt hi⟩ : Fin n)
        have hmono :=
          prefixSpan_mono_le M (Nat.lt_trans row.isLt hi) hk
            (Nat.le_of_lt_succ row.isLt) hself
        have htarget :
            M.row (⟨row.val, Nat.lt_trans row.isLt hi⟩ : Fin n) =
              (prefixRows M k hk).row row := by
          apply Vector.ext
          intro col hcol
          simp [prefixRows, Matrix.row]
        rw [htarget] at hmono
        exact hmono
      exact prefixSpan_mono_succ M k hi hspan

private theorem prefixSpan_strictRowCombination_of_rows
    (A B : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat i)
    (hrows : ∀ j : Fin i,
      prefixSpan B i hi ((strictPrefixRows A i (Nat.le_of_lt hi)).row j)) :
    prefixSpan B i hi
      (Matrix.rowCombination (strictPrefixRows A i (Nat.le_of_lt hi)) c) := by
  rw [rowCombination_eq_foldl_rows]
  have hfold :
      ∀ xs : List (Fin i), ∀ acc : Vector Rat m,
        prefixSpan B i hi acc →
          prefixSpan B i hi
            (xs.foldl
              (fun acc j => acc + c[j] • (strictPrefixRows A i (Nat.le_of_lt hi)).row j)
              acc) := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons j rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        exact prefixSpan_add B i hi hacc
          (prefixSpan_smul B i hi c[j] (hrows j))
  exact hfold (List.finRange i) 0 (prefixSpan_zero B i hi)

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

/-- Gram-Schmidt leaves the first row untouched: the leading basis row of a
rational matrix is its leading input row. -/
@[simp, grind =]
theorem basis_zero (b : Matrix Rat n m) (hn : 0 < n) :
    (basis b).row ⟨0, hn⟩ = b.row ⟨0, hn⟩ := by
  simpa [basis, GramSchmidt.basisMatrix, Matrix.row] using
    GramSchmidt.basisRows_head (b := b) hn

/-- The defining guarantee of the construction: distinct rational Gram-Schmidt
basis rows are mutually orthogonal (their dot product is zero). -/
@[grind =]
theorem basis_orthogonal (b : Matrix Rat n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Matrix.dot ((basis b).row ⟨i, hi⟩) ((basis b).row ⟨j, hj⟩) = 0 := by
  rw [basis, GramSchmidt.basisMatrix_row_eq_basisRows_get!,
    GramSchmidt.basisMatrix_row_eq_basisRows_get!]
  exact GramSchmidt.basisRows_get!_dot_eq_zero b i j hi hj hij

/-- The triangular factorization `b = coeffs · basis`, stated row by row: each
rational input row equals its orthogonalized basis row plus the
coefficient-weighted combination of the earlier basis rows. -/
theorem basis_decomposition (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    b.row ⟨i, hi⟩ =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  simpa [basis, coeffs] using
    GramSchmidt.basisMatrix_reconstruction_invariant (b := b) i hi

/-- The rational coefficient matrix has unit diagonal: each input row enters its
own decomposition with weight `1`. -/
@[simp, grind =]
theorem coeffs_diag (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 1 := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn]

/-- The rational coefficient matrix is lower triangular: entries strictly above
the diagonal vanish, since a row only combines basis rows with smaller index. -/
@[grind =]
theorem coeffs_upper (b : Matrix Rat n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  have hnot_lt : ¬j < i := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hnot_lt, hne]

/-- Strictly lower-triangular coefficient entries are the rational projection
coefficient of the input row onto the earlier generated basis row. -/
theorem coeffs_lower_projection (b : Matrix Rat n m) {i j : Fin n}
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs b) i j =
      (if Matrix.dot ((basis b).row j) ((basis b).row j) = 0 then 0
       else
        Matrix.dot (b.row i) ((basis b).row j) /
          Matrix.dot ((basis b).row j) ((basis b).row j)) := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn,
    GramSchmidt.projectionCoeff, Matrix.row, hji]

/-- Lower coefficient entries, with the dot product oriented to match
Mathlib's projection coefficient numerator. -/
theorem coeffs_lower_projection_comm (b : Matrix Rat n m) {i j : Fin n}
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs b) i j =
      (if Matrix.dot ((basis b).row j) ((basis b).row j) = 0 then 0
       else
        Matrix.dot ((basis b).row j) (b.row i) /
          Matrix.dot ((basis b).row j) ((basis b).row j)) := by
  rw [coeffs_lower_projection (b := b) hji]
  by_cases hnorm : Matrix.dot ((basis b).row j) ((basis b).row j) = 0
  · simp [hnorm]
  · simp [hnorm, GramSchmidt.dot_comm_rat]

/-- The Gram-Schmidt basis is invariant under adding a scalar multiple of an
earlier row to a later row. This is the rational size-reduction update used by
the integer wrappers. -/
@[grind =]
theorem basis_rowAdd (b : Matrix Rat n m) (src dst : Fin n) (c : Rat)
    (hsrcdst : src.val < dst.val) :
    basis (Matrix.rowAdd b src dst c) = basis b := by
  simpa [basis] using
    GramSchmidt.basisMatrix_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst

/-- Swapping rows `km1` and `k` leaves every basis row before the pair
unchanged, since each Gram-Schmidt output row depends only on the input prefix
up to its own index. -/
@[grind =]
theorem basis_rowSwap_of_before (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1k : km1.val < k.val) (hi : i.val < km1.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  simpa [basis] using
    GramSchmidt.basisMatrix_rowSwap_of_before (b := b) (km1 := km1) (k := k)
      (i := i) hkm1k hi

/-- After swapping the adjacent rows `km1, k`, the basis row at the lower index
`km1` becomes the old basis row `k` plus its projection coefficient times the
old basis row `km1`. The explicit re-orthogonalization formula for the first
vector of the swapped pair. -/
@[grind =]
theorem basis_rowSwap_adjacent_prev (b : Matrix Rat n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val) :
    (basis (Matrix.rowSwap b km1 k)).row km1 =
      (basis b).row k +
        GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1 := by
  have hraw :=
    GramSchmidt.basisMatrix_rowSwap_adjacent_prev (b := b) (km1 := km1) (k := k) hkm1
  have hlt : km1.val < k.val := by omega
  have hcoeff :
      GramSchmidt.projectionCoeff (b.row k) ((GramSchmidt.basisMatrix b).row km1) =
        GramSchmidt.entry (coeffs b) k km1 := by
    simp [coeffs, basis, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn,
      GramSchmidt.projectionCoeff, Matrix.row, hlt]
  simpa [basis, hcoeff] using hraw

private theorem projectionCoeff_row_later_basis_eq_zero
    (b : Matrix Rat n m) (src col : Fin n) (hsrccol : src.val < col.val) :
    GramSchmidt.projectionCoeff (b.row src) ((basis b).row col) = 0 := by
  have hsrc_toList : b.toList[src.val]! = b.row src := by simp [Matrix.row]
  have hbasis_col :
      (basis b).row col = (GramSchmidt.basisRows b.toList)[col.val]! := by
    simpa [basis] using
      GramSchmidt.basisMatrix_row_eq_basisRows_get! (b := b) col.val col.isLt
  have hreduce :
      GramSchmidt.reduceAgainstBasis
          ((GramSchmidt.basisRows b.toList).take col.val).reverse (b.row src) = 0 := by
    simpa [hsrc_toList] using
      GramSchmidt.reduceAgainstBasis_basisRows_take_source_eq_zero
        (rows := b.toList) (j := src.val) (k := col.val) hsrccol
        (by simp [Vector.length_toList, Nat.le_of_lt col.isLt])
  have hproj :=
    GramSchmidt.projectionCoeff_reduceAgainstBasis_eq_of_forall_dot_zero
      (basisRev := ((GramSchmidt.basisRows b.toList).take col.val).reverse)
      (row := b.row src) (basisRow := (basis b).row col)
      (by
        intro other hother
        rw [List.mem_reverse] at hother
        rw [List.mem_iff_getElem] at hother
        obtain ⟨idx, hidx, hget⟩ := hother
        have htake_len : ((GramSchmidt.basisRows b.toList).take col.val).length = col.val := by
          rw [List.length_take]
          have hbasis_len : (GramSchmidt.basisRows b.toList).length = n := by
            simp [GramSchmidt.basisRows_length]
          omega
        have hidx_col : idx < col.val := by
          rw [htake_len] at hidx
          exact hidx
        have hbasis_len : (GramSchmidt.basisRows b.toList).length = n := by
          simp [GramSchmidt.basisRows_length]
        have hidx_basis : idx < (GramSchmidt.basisRows b.toList).length := by
          rw [hbasis_len]
          exact Nat.lt_trans hidx_col col.isLt
        have hother_get :
            other = (GramSchmidt.basisRows b.toList)[idx]! := by
          rw [← hget, List.getElem_take]
          simp [hidx_basis]
        rw [hother_get, hbasis_col]
        exact GramSchmidt.basisRows_get!_dot_eq_zero
          (b := b) idx col.val (Nat.lt_trans hidx_col col.isLt) col.isLt
          (Nat.ne_of_lt hidx_col))
  rw [hreduce] at hproj
  have hzero : GramSchmidt.projectionCoeff (0 : Vector Rat m) ((basis b).row col) = 0 := by
    by_cases hnorm : Matrix.dot ((basis b).row col) ((basis b).row col) = 0
    · simp [GramSchmidt.projectionCoeff, hnorm]
    · have hdot : Matrix.dot (0 : Vector Rat m) ((basis b).row col) = 0 := by
        unfold Matrix.dot Hex.Vector.dotProduct
        induction List.finRange m with
        | nil => rfl
        | cons idx rest ih =>
            simp only [List.foldl_cons]
            have hentry : (0 : Vector Rat m)[idx] = 0 := by
              change (0 : Vector Rat m)[idx.val] = 0
              rw [Vector.getElem_zero]
            rw [hentry]
            rw [show (0 : Rat) + 0 * ((basis b).row col)[idx] = 0 by grind]
            exact ih
      have hzero_div : (0 : Rat) / Matrix.dot ((basis b).row col) ((basis b).row col) = 0 := by
        grind
      simp [GramSchmidt.projectionCoeff, hnorm, hdot, hzero_div]
  simpa [hzero] using hproj.symm

private theorem projectionCoeff_row_basis_self_eq_one
    (b : Matrix Rat n m) (src : Fin n)
    (hnorm : Matrix.dot ((basis b).row src) ((basis b).row src) ≠ 0) :
    GramSchmidt.projectionCoeff (b.row src) ((basis b).row src) = 1 := by
  have hsrc_toList : b.toList[src.val]! = b.row src := by simp [Matrix.row]
  have hbasis_src :
      (basis b).row src = (GramSchmidt.basisRows b.toList)[src.val]! := by
    simpa [basis] using
      GramSchmidt.basisMatrix_row_eq_basisRows_get! (b := b) src.val src.isLt
  have hreduce :
      GramSchmidt.reduceAgainstBasis
          ((GramSchmidt.basisRows b.toList).take src.val).reverse (b.row src) =
        (basis b).row src := by
    have hbasis :=
      GramSchmidt.basisRows_get!_eq_reduceAgainstBasis_take
        (rows := b.toList) (k := src.val) (by
          simp [Vector.length_toList])
    simpa [hsrc_toList, hbasis_src] using hbasis.symm
  have hproj :=
    GramSchmidt.projectionCoeff_reduceAgainstBasis_eq_of_forall_dot_zero
      (basisRev := ((GramSchmidt.basisRows b.toList).take src.val).reverse)
      (row := b.row src) (basisRow := (basis b).row src)
      (by
        intro other hother
        rw [List.mem_reverse] at hother
        rw [List.mem_iff_getElem] at hother
        obtain ⟨idx, hidx, hget⟩ := hother
        have htake_len : ((GramSchmidt.basisRows b.toList).take src.val).length = src.val := by
          rw [List.length_take]
          have hbasis_len : (GramSchmidt.basisRows b.toList).length = n := by
            simp [GramSchmidt.basisRows_length]
          omega
        have hidx_src : idx < src.val := by
          rw [htake_len] at hidx
          exact hidx
        have hbasis_len : (GramSchmidt.basisRows b.toList).length = n := by
          simp [GramSchmidt.basisRows_length]
        have hidx_basis : idx < (GramSchmidt.basisRows b.toList).length := by
          rw [hbasis_len]
          exact Nat.lt_trans hidx_src src.isLt
        have hother_get :
            other = (GramSchmidt.basisRows b.toList)[idx]! := by
          rw [← hget, List.getElem_take]
          simp [hidx_basis]
        rw [hother_get, hbasis_src]
        exact GramSchmidt.basisRows_get!_dot_eq_zero
          (b := b) idx src.val (Nat.lt_trans hidx_src src.isLt) src.isLt
          (Nat.ne_of_lt hidx_src))
  rw [hreduce] at hproj
  have hself :
      GramSchmidt.projectionCoeff ((basis b).row src) ((basis b).row src) = 1 := by
    have hdiv :
        Matrix.dot ((basis b).row src) ((basis b).row src) /
            Matrix.dot ((basis b).row src) ((basis b).row src) = 1 := by
      grind
    simp [GramSchmidt.projectionCoeff, hnorm, hdiv]
  simpa [hself] using hproj.symm

/-- After swapping the adjacent rows `km1, k` (assuming the swapped pivot is
nonzero), the basis row at index `k` is the explicit two-term combination of the
old basis rows `km1, k`. The companion of `basis_rowSwap_adjacent_prev` tracking
how a swap rewrites the second vector of the pair. -/
theorem basis_rowSwap_adjacent_curr (b : Matrix Rat n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val)
    (hnorm :
      Matrix.dot
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1)
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1) ≠ 0) :
    let prev := (basis b).row km1
    let curr := (basis b).row k
    let mu := GramSchmidt.entry (coeffs b) k km1
    let swappedPrev := curr + mu • prev
    (basis (Matrix.rowSwap b km1 k)).row k =
      (Matrix.dot curr curr / Matrix.dot swappedPrev swappedPrev) • prev -
        (mu * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev) • curr := by
  let prev := (basis b).row km1
  let curr := (basis b).row k
  let mu := GramSchmidt.entry (coeffs b) k km1
  let swappedPrev := curr + mu • prev
  have hraw :=
    GramSchmidt.basisMatrix_rowSwap_adjacent_curr (b := b) (km1 := km1) (k := k) hkm1
  have hlt : km1.val < k.val := by omega
  have hmu :
      GramSchmidt.projectionCoeff (b.row k) ((basis b).row km1) = mu := by
    simp [mu, coeffs, basis, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn,
      GramSchmidt.projectionCoeff, Matrix.row, hlt]
  have hmu_raw :
      GramSchmidt.projectionCoeff (b.row k) ((GramSchmidt.basisMatrix b).row km1) = mu := by
    simpa [basis] using hmu
  have hraw' :
      (basis (Matrix.rowSwap b km1 k)).row k =
        prev - GramSchmidt.projectionCoeff (b.row km1) swappedPrev • swappedPrev := by
    simpa [basis, prev, curr, mu, swappedPrev, hmu_raw] using hraw
  have horth_curr_prev : Matrix.dot curr prev = 0 := by
    simpa [curr, prev] using
      basis_orthogonal (b := b) k.val km1.val k.isLt km1.isLt (by omega)
  have horth_prev_curr : Matrix.dot prev curr = 0 := by
    simpa [prev, curr, GramSchmidt.dot_comm_rat] using horth_curr_prev
  have hrow_curr : Matrix.dot (b.row km1) curr = 0 := by
    have hpc :=
      projectionCoeff_row_later_basis_eq_zero (b := b) (src := km1) (col := k) hlt
    by_cases hcurr : Matrix.dot curr curr = 0
    · exact GramSchmidt.dot_zero_of_dot_self_zero (row := b.row km1) (v := curr) hcurr
    · have hdiv :
        Matrix.dot (b.row km1) curr / Matrix.dot curr curr = 0 := by
          simpa [curr, GramSchmidt.projectionCoeff, hcurr] using hpc
      grind
  have hrow_prev : Matrix.dot (b.row km1) prev = Matrix.dot prev prev := by
    by_cases hprev : Matrix.dot prev prev = 0
    · have hzero := GramSchmidt.dot_zero_of_dot_self_zero (row := b.row km1) (v := prev) hprev
      simp [hzero, hprev]
    · have hpc := projectionCoeff_row_basis_self_eq_one (b := b) (src := km1) (by
        simpa [prev] using hprev)
      have hdiv :
        Matrix.dot (b.row km1) prev / Matrix.dot prev prev = 1 := by
          simpa [prev, GramSchmidt.projectionCoeff, hprev] using hpc
      grind
  have hrow_swapped :
      Matrix.dot (b.row km1) swappedPrev = mu * Matrix.dot prev prev := by
    rw [GramSchmidt.dot_comm_rat]
    change Matrix.dot (curr + mu • prev) (b.row km1) = mu * Matrix.dot prev prev
    rw [GramSchmidt.dot_add_left, GramSchmidt.dot_smul_left]
    have hcurr_row : Matrix.dot curr (b.row km1) = 0 := by
      simpa [GramSchmidt.dot_comm_rat] using hrow_curr
    have hprev_row : Matrix.dot prev (b.row km1) = Matrix.dot prev prev := by
      simpa [GramSchmidt.dot_comm_rat] using hrow_prev
    rw [hcurr_row, hprev_row]
    grind
  have hproj :
      GramSchmidt.projectionCoeff (b.row km1) swappedPrev =
        mu * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev := by
    have hnorm' : Matrix.dot swappedPrev swappedPrev ≠ 0 := by
      simpa [prev, curr, mu, swappedPrev] using hnorm
    simp [GramSchmidt.projectionCoeff, hnorm', hrow_swapped]
  have hcurr_swapped : Matrix.dot curr swappedPrev = Matrix.dot curr curr := by
    rw [GramSchmidt.dot_comm_rat]
    change Matrix.dot (curr + mu • prev) curr = Matrix.dot curr curr
    rw [GramSchmidt.dot_add_left, GramSchmidt.dot_smul_left, horth_prev_curr]
    grind
  have hprev_swapped : Matrix.dot prev swappedPrev = mu * Matrix.dot prev prev := by
    rw [GramSchmidt.dot_comm_rat]
    change Matrix.dot (curr + mu • prev) prev = mu * Matrix.dot prev prev
    rw [GramSchmidt.dot_add_left, GramSchmidt.dot_smul_left, horth_curr_prev]
    grind
  have hdenom :
      Matrix.dot swappedPrev swappedPrev =
        Matrix.dot curr curr + mu * mu * Matrix.dot prev prev := by
    change Matrix.dot (curr + mu • prev) swappedPrev =
      Matrix.dot curr curr + mu * mu * Matrix.dot prev prev
    rw [GramSchmidt.dot_add_left, GramSchmidt.dot_smul_left, hcurr_swapped, hprev_swapped]
    grind
  rw [hraw', hproj]
  change
    prev - (mu * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev) • swappedPrev =
      (Matrix.dot curr curr / Matrix.dot swappedPrev swappedPrev) • prev -
        (mu * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev) • curr
  apply Vector.ext
  intro idx hidx
  simp only [Vector.getElem_sub, Vector.getElem_smul]
  have hswapped_idx : swappedPrev[idx] = curr[idx] + mu * prev[idx] := by
    simp only [swappedPrev, Vector.getElem_add, Vector.getElem_smul]
    change curr[idx] + mu * prev[idx] = curr[idx] + mu * prev[idx]
    rfl
  rw [hswapped_idx]
  change
    prev[idx] -
        (mu * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev) *
          (curr[idx] + mu * prev[idx]) =
      (Matrix.dot curr curr / Matrix.dot swappedPrev swappedPrev) * prev[idx] -
        (mu * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev) * curr[idx]
  have hdenom_ne : Matrix.dot swappedPrev swappedPrev ≠ 0 := by
    simpa [prev, curr, mu, swappedPrev] using hnorm
  rw [hdenom]
  grind

private theorem rowSwap_row_left (b : Matrix Rat n m) (i j : Fin n) :
    (Matrix.rowSwap b i j).row i = b.row j := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[i][c] = b[j][c]
  rw [Matrix.rowSwap_getElem (M := b) (i := i) (j := j) (r := i) (k := c)]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

private theorem rowSwap_row_right (b : Matrix Rat n m) (i j : Fin n) :
    (Matrix.rowSwap b i j).row j = b.row i := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[j][c] = b[i][c]
  rw [Matrix.rowSwap_getElem (M := b) (i := i) (j := j) (r := j) (k := c)]
  simp

private theorem rowSwap_row_eq_of_ne (b : Matrix Rat n m) (i j r : Fin n)
    (hri : r ≠ i) (hrj : r ≠ j) :
    (Matrix.rowSwap b i j).row r = b.row r := by
  apply Vector.ext
  intro idx hidx
  let c : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b i j)[r][c] = b[r][c]
  rw [Matrix.rowSwap_getElem (M := b) (i := i) (j := j) (r := r) (k := c)]
  simp [hri, hrj]

/-- After an adjacent swap, the coefficient at the lower row `km1` against an
earlier column `j` equals the old coefficient at row `k` against `j`: the
swapped rows carry their lower coefficients with them. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_prev (b : Matrix Rat n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) km1 j =
      GramSchmidt.entry (coeffs b) k j := by
  have hkm1k : km1.val < k.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row km1 = b.row k :=
    rowSwap_row_left b km1 k
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := km1) (j := j) hj]
  rw [coeffs_lower_projection (b := b) (i := k) (j := j) (Nat.lt_trans hj hkm1k)]
  rw [hrow, hbasis]

/-- Dual of `coeffs_rowSwap_adjacent_lower_prev`: after an adjacent swap, the
coefficient at row `k` against an earlier column `j` equals the old coefficient
at row `km1` against `j`. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_curr (b : Matrix Rat n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) k j =
      GramSchmidt.entry (coeffs b) km1 j := by
  have hkm1k : km1.val < k.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row k = b.row km1 :=
    rowSwap_row_right b km1 k
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := k) (j := j)
    (by omega)]
  rw [coeffs_lower_projection (b := b) (i := km1) (j := j) hj]
  rw [hrow, hbasis]

/-- The explicit value of the new pivot coefficient (row `k`, column `km1`)
after an adjacent swap, in terms of the old projection coefficient and basis-row
norms. -/
theorem coeffs_rowSwap_adjacent_pivot (b : Matrix Rat n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val)
    (hnorm :
      Matrix.dot
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1)
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1) ≠ 0) :
    let mu := GramSchmidt.entry (coeffs b) k km1
    let prev := (basis b).row km1
    let curr := (basis b).row k
    let swappedPrev := curr + mu • prev
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) k km1 =
      mu * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev := by
  let mu := GramSchmidt.entry (coeffs b) k km1
  let prev := (basis b).row km1
  let curr := (basis b).row k
  let swappedPrev := curr + mu • prev
  have hkm1k : km1.val < k.val := by omega
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := k) (j := km1) hkm1k]
  have hrow : (Matrix.rowSwap b km1 k).row k = b.row km1 :=
    rowSwap_row_right b km1 k
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row km1 = swappedPrev := by
    simpa [swappedPrev, curr, prev, mu] using
      basis_rowSwap_adjacent_prev (b := b) (km1 := km1) (k := k) hkm1
  rw [hrow, hbasis]
  have horth_curr_prev : Matrix.dot curr prev = 0 := by
    simpa [curr, prev] using
      basis_orthogonal (b := b) k.val km1.val k.isLt km1.isLt (by omega)
  have hrow_curr : Matrix.dot (b.row km1) curr = 0 := by
    have hpc :=
      projectionCoeff_row_later_basis_eq_zero (b := b) (src := km1) (col := k) hkm1k
    by_cases hcurr : Matrix.dot curr curr = 0
    · exact GramSchmidt.dot_zero_of_dot_self_zero (row := b.row km1) (v := curr) hcurr
    · have hdiv :
        Matrix.dot (b.row km1) curr / Matrix.dot curr curr = 0 := by
          simpa [curr, GramSchmidt.projectionCoeff, hcurr] using hpc
      grind
  have hrow_prev : Matrix.dot (b.row km1) prev = Matrix.dot prev prev := by
    by_cases hprev : Matrix.dot prev prev = 0
    · have hzero := GramSchmidt.dot_zero_of_dot_self_zero (row := b.row km1) (v := prev) hprev
      simp [hzero, hprev]
    · have hpc := projectionCoeff_row_basis_self_eq_one (b := b) (src := km1) (by
        simpa [prev] using hprev)
      have hdiv :
        Matrix.dot (b.row km1) prev / Matrix.dot prev prev = 1 := by
          simpa [prev, GramSchmidt.projectionCoeff, hprev] using hpc
      grind
  have hrow_swapped :
      Matrix.dot (b.row km1) swappedPrev = mu * Matrix.dot prev prev := by
    rw [GramSchmidt.dot_comm_rat]
    change Matrix.dot (curr + mu • prev) (b.row km1) = mu * Matrix.dot prev prev
    rw [GramSchmidt.dot_add_left, GramSchmidt.dot_smul_left]
    have hcurr_row : Matrix.dot curr (b.row km1) = 0 := by
      simpa [GramSchmidt.dot_comm_rat] using hrow_curr
    have hprev_row : Matrix.dot prev (b.row km1) = Matrix.dot prev prev := by
      simpa [GramSchmidt.dot_comm_rat] using hrow_prev
    rw [hcurr_row, hprev_row]
    grind
  have hnorm' : Matrix.dot swappedPrev swappedPrev ≠ 0 := by
    simpa [swappedPrev, curr, prev, mu] using hnorm
  simp [hnorm', hrow_swapped, swappedPrev, curr, prev, mu]

/-- Under `rowAdd b src dst c` with `src < dst`, lower coefficients in the
destination row update linearly below the pivot source column. -/
@[grind =]
theorem coeffs_rowAdd_lower (b : Matrix Rat n m) (col src dst : Fin n)
    (hcolsrc : col.val < src.val) (hsrcdst : src.val < dst.val) (c : Rat) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col +
        c * GramSchmidt.entry (coeffs b) src col := by
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn,
    hcolsrc, Nat.lt_trans hcolsrc hsrcdst]
  rw [hbasis]
  unfold Matrix.rowAdd
  simp [Vector.getElem_set_self]
  have hvec :
      (Vector.ofFn fun k : Fin m => b[dst.val][k.val] + c * b[src.val][k.val]) =
        b[dst.val] + c • b[src.val] := by
    apply Vector.ext
    intro idx hidx
    simp [Vector.getElem_add, Vector.getElem_smul]
    rfl
  rw [hvec]
  rw [GramSchmidt.projectionCoeff_add_left, GramSchmidt.projectionCoeff_smul_left]

/-- Under `rowAdd b src dst c` with `src < dst`, the pivot coefficient in the
destination row increases by `c` when the source basis row has nonzero norm. -/
@[grind =]
theorem coeffs_rowAdd_pivot (b : Matrix Rat n m) (src dst : Fin n)
    (hsrcdst : src.val < dst.val) (c : Rat)
    (hnorm : Matrix.dot ((basis b).row src) ((basis b).row src) ≠ 0) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst src =
      GramSchmidt.entry (coeffs b) dst src + c := by
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  have hself :
      GramSchmidt.projectionCoeff (b.row src) ((basis b).row src) = 1 := by
    exact projectionCoeff_row_basis_self_eq_one (b := b) (src := src) hnorm
  have hself_get :
      GramSchmidt.projectionCoeff b[src.val] (basis b)[src.val] = 1 := by
    simpa [Matrix.row] using hself
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hsrcdst]
  rw [hbasis]
  unfold Matrix.rowAdd
  simp [Vector.getElem_set_self]
  have hvec :
      (Vector.ofFn fun k : Fin m => b[dst.val][k.val] + c * b[src.val][k.val]) =
        b[dst.val] + c • b[src.val] := by
    apply Vector.ext
    intro idx hidx
    simp [Vector.getElem_add, Vector.getElem_smul]
    rfl
  rw [hvec]
  rw [GramSchmidt.projectionCoeff_add_left, GramSchmidt.projectionCoeff_smul_left,
    hself_get]
  grind

/-- Under `rowAdd b src dst c` with `src < col < dst`, destination-row
coefficients above the pivot source column are preserved. -/
@[grind =]
theorem coeffs_rowAdd_above_pivot (b : Matrix Rat n m) (src col dst : Fin n)
    (hsrccol : src.val < col.val) (hcoldst : col.val < dst.val) (c : Rat) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col := by
  have hsrcdst : src.val < dst.val := Nat.lt_trans hsrccol hcoldst
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  have hzero := projectionCoeff_row_later_basis_eq_zero (b := b) (src := src) (col := col)
    hsrccol
  have hzero_get :
      GramSchmidt.projectionCoeff b[src.val] (basis b)[col.val] = 0 := by
    simpa [Matrix.row] using hzero
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hcoldst]
  rw [hbasis]
  unfold Matrix.rowAdd
  simp [Vector.getElem_set_self]
  have hvec :
      (Vector.ofFn fun k : Fin m => b[dst.val][k.val] + c * b[src.val][k.val]) =
        b[dst.val] + c • b[src.val] := by
    apply Vector.ext
    intro idx hidx
    simp [Vector.getElem_add, Vector.getElem_smul]
    rfl
  rw [hvec]
  rw [GramSchmidt.projectionCoeff_add_left, GramSchmidt.projectionCoeff_smul_left,
    hzero_get]
  grind

/-- A row add only changes the destination row of the coefficient matrix. -/
@[grind =]
theorem coeffs_rowAdd_other_row (b : Matrix Rat n m) (src dst : Fin n) (c : Rat)
    (hsrcdst : src.val < dst.val) (row : Fin n) (hrow : row ≠ dst) :
    (coeffs (Matrix.rowAdd b src dst c)).row row = (coeffs b).row row := by
  have hbasis := basis_rowAdd (b := b) (src := src) (dst := dst) (c := c) hsrcdst
  apply Vector.ext
  intro col hcol
  let colFin : Fin n := ⟨col, hcol⟩
  change GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) row colFin =
    GramSchmidt.entry (coeffs b) row colFin
  by_cases hlt : colFin.val < row.val
  · simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hlt]
    rw [hbasis]
    unfold Matrix.rowAdd
    have hval : dst.val ≠ row.val := by
      intro h
      exact hrow (Fin.ext h.symm)
    change
      GramSchmidt.projectionCoeff
          ((Vector.set b dst.val (Vector.ofFn fun k => b[dst][k] + c * b[src][k])
            dst.isLt)[row.val])
          (basis b)[colFin.val] =
        GramSchmidt.projectionCoeff b[row.val] (basis b)[colFin.val]
    rw [Vector.getElem_set_ne dst.isLt row.isLt hval]
  · simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hlt]

/-- Orthogonalization preserves the row space of each prefix: the first `i + 1`
rational basis rows span exactly the vectors spanned by the first `i + 1` input
rows. -/
theorem basis_span (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    ∀ v : Vector Rat m,
      GramSchmidt.prefixSpan (basis b) i hi v ↔
        GramSchmidt.prefixSpan b i hi v := by
  have hmembersAll :
      ∀ (i : Nat) (hi : i < n),
        (∀ j : Fin (i + 1),
          GramSchmidt.prefixSpan b i hi ((GramSchmidt.prefixRows (basis b) i hi).row j)) ∧
        (∀ j : Fin (i + 1),
          GramSchmidt.prefixSpan (basis b) i hi ((GramSchmidt.prefixRows b i hi).row j)) := by
    intro i
    induction i with
    | zero =>
        intro hi
        constructor
        · intro j
          have hrow :
              (GramSchmidt.prefixRows (basis b) 0 hi).row j =
                (GramSchmidt.prefixRows b 0 hi).row j := by
            apply Vector.ext
            intro col hcol
            have hj : j.val = 0 := by omega
            have hb0 := congrArg (fun v : Vector Rat m => v[col]) (basis_zero b hi)
            simpa [GramSchmidt.prefixRows, Matrix.row, hj] using hb0
          rw [hrow]
          exact GramSchmidt.prefixSpan_row b 0 hi j
        · intro j
          have hrow :
              (GramSchmidt.prefixRows b 0 hi).row j =
                (GramSchmidt.prefixRows (basis b) 0 hi).row j := by
            apply Vector.ext
            intro col hcol
            have hj : j.val = 0 := by omega
            have hb0 := congrArg (fun v : Vector Rat m => v[col]) (basis_zero b hi)
            simpa [GramSchmidt.prefixRows, Matrix.row, hj] using hb0.symm
          rw [hrow]
          exact GramSchmidt.prefixSpan_row (basis b) 0 hi j
    | succ k ih =>
        intro hi
        have hk : k < n := Nat.lt_of_succ_lt hi
        have ihk := ih hk
        constructor
        · intro j
          by_cases hlt : j.val < k + 1
          · let jp : Fin (k + 1) := ⟨j.val, hlt⟩
            have hprev := ihk.1 jp
            have hmono := GramSchmidt.prefixSpan_mono_succ b k hi hprev
            have hrow :
                (GramSchmidt.prefixRows (basis b) (k + 1) hi).row j =
                  (GramSchmidt.prefixRows (basis b) k hk).row jp := by
              apply Vector.ext
              intro col hcol
              simp [GramSchmidt.prefixRows, Matrix.row, jp]
            rwa [hrow]
          · have hjlast : j.val = k + 1 := by omega
            let last : Fin n := ⟨k + 1, hi⟩
            let pc :=
              GramSchmidt.prefixCombination (coeffs b) (basis b) (k + 1) hi
            have hpc : GramSchmidt.prefixSpan b (k + 1) hi pc := by
              have hraw :=
                GramSchmidt.prefixSpan_strictRowCombination_of_rows
                  (A := basis b) (B := b) (i := k + 1) (hi := hi)
                  (c := GramSchmidt.projectionCoeffVector (b.row last) (basis b)
                    (k + 1) (Nat.le_of_lt hi))
                  (by
                    intro row
                    let jp : Fin (k + 1) := row
                    have hprev := ihk.1 jp
                    have hmono := GramSchmidt.prefixSpan_mono_succ b k hi hprev
                    have hrow :
                        (GramSchmidt.strictPrefixRows (basis b) (k + 1)
                            (Nat.le_of_lt hi)).row row =
                          (GramSchmidt.prefixRows (basis b) k hk).row jp := by
                      apply Vector.ext
                      intro col hcol
                      simp [GramSchmidt.strictPrefixRows, GramSchmidt.prefixRows,
                        Matrix.row, jp]
                    rwa [hrow])
              simpa [pc, basis, coeffs,
                GramSchmidt.prefixCombination_eq_strictPrefixRowCombination] using hraw
            have hbrow : GramSchmidt.prefixSpan b (k + 1) hi (b.row last) := by
              simpa [GramSchmidt.prefixRows, Matrix.row, last, hjlast] using
                GramSchmidt.prefixSpan_row b (k + 1) hi j
            have hbasis_eq :
                ((GramSchmidt.prefixRows (basis b) (k + 1) hi).row j) =
                  b.row last + (-1 : Rat) • pc := by
              have hdec := basis_decomposition b (k + 1) hi
              apply Vector.ext
              intro col hcol
              have hdec_col := congrArg (fun v : Vector Rat m => v[col]) hdec
              simp [Vector.getElem_add, Vector.getElem_smul, pc, last, hjlast,
                GramSchmidt.prefixRows, Matrix.row] at hdec_col ⊢
              change (basis b)[k + 1][col] =
                b[k + 1][col] +
                  (-1 : Rat) * (prefixCombination (coeffs b) (basis b) (k + 1) hi)[col]
              rw [hdec_col]
              grind
            rw [hbasis_eq]
            exact GramSchmidt.prefixSpan_add b (k + 1) hi hbrow
              (GramSchmidt.prefixSpan_smul b (k + 1) hi (-1) hpc)
        · intro j
          by_cases hlt : j.val < k + 1
          · let jp : Fin (k + 1) := ⟨j.val, hlt⟩
            have hprev := ihk.2 jp
            have hmono := GramSchmidt.prefixSpan_mono_succ (basis b) k hi hprev
            have hrow :
                (GramSchmidt.prefixRows b (k + 1) hi).row j =
                  (GramSchmidt.prefixRows b k hk).row jp := by
              apply Vector.ext
              intro col hcol
              simp [GramSchmidt.prefixRows, Matrix.row, jp]
            rwa [hrow]
          · have hjlast : j.val = k + 1 := by omega
            let last : Fin n := ⟨k + 1, hi⟩
            let pc :=
              GramSchmidt.prefixCombination (coeffs b) (basis b) (k + 1) hi
            have hpc : GramSchmidt.prefixSpan (basis b) (k + 1) hi pc := by
              have hraw :=
                GramSchmidt.prefixSpan_strictPrefix_rowCombination
                  (M := basis b) (i := k + 1) (hi := hi)
                  (c := GramSchmidt.projectionCoeffVector (b.row last) (basis b)
                    (k + 1) (Nat.le_of_lt hi))
              simpa [pc, basis, coeffs,
                GramSchmidt.prefixCombination_eq_strictPrefixRowCombination] using hraw
            have hbasisrow :
                GramSchmidt.prefixSpan (basis b) (k + 1) hi ((basis b).row last) := by
              have hself := GramSchmidt.prefixSpan_row (basis b) (k + 1) hi j
              simpa [GramSchmidt.prefixRows, Matrix.row, last, hjlast] using hself
            have hb_eq :
                ((GramSchmidt.prefixRows b (k + 1) hi).row j) =
                  (basis b).row last + pc := by
              have hdec := basis_decomposition b (k + 1) hi
              apply Vector.ext
              intro col hcol
              have hdec_col := congrArg (fun v : Vector Rat m => v[col]) hdec
              simpa [pc, last, hjlast, GramSchmidt.prefixRows, Matrix.row] using hdec_col
            rw [hb_eq]
            exact GramSchmidt.prefixSpan_add (basis b) (k + 1) hi hbasisrow hpc
  intro v
  constructor
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      GramSchmidt.prefixSpan_rowCombination_of_rows (A := basis b) (B := b)
        (i := i) (hi := hi) c (hmembersAll i hi).1
    rwa [hc] at hspan
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      GramSchmidt.prefixSpan_rowCombination_of_rows (A := b) (B := basis b)
        (i := i) (hi := hi) c (hmembersAll i hi).2
    rwa [hc] at hspan

private theorem basis_row_sub_basis_row_prefixSpan_pred
    (b : Matrix Rat n m) (i p : Nat) (hi : i < n) (hp : p < n)
    (hsucc : p + 1 = i) :
    GramSchmidt.prefixSpan (basis b) p hp
      (b.row ⟨i, hi⟩ - (basis b).row ⟨i, hi⟩) := by
  subst i
  refine ⟨GramSchmidt.projectionCoeffVector (b.row ⟨p + 1, hi⟩) (basis b)
      (p + 1) (Nat.le_of_lt hi), ?_⟩
  change
    Matrix.rowCombination (GramSchmidt.prefixRows (basis b) p hp)
        (GramSchmidt.projectionCoeffVector (b.row ⟨p + 1, hi⟩) (basis b)
          (p + 1) (Nat.le_of_lt hi)) =
      b.row ⟨p + 1, hi⟩ - (basis b).row ⟨p + 1, hi⟩
  rw [← GramSchmidt.strictPrefixRows_succ_eq_prefixRows
    (M := basis b) (i := p) (hi := hi)]
  have hpc :
      GramSchmidt.prefixCombination (coeffs b) (basis b) (p + 1) hi =
        Matrix.rowCombination (GramSchmidt.strictPrefixRows (basis b) (p + 1)
            (Nat.le_of_lt hi))
          (GramSchmidt.projectionCoeffVector (b.row ⟨p + 1, hi⟩) (basis b)
            (p + 1) (Nat.le_of_lt hi)) := by
    simpa [basis, coeffs] using
      GramSchmidt.prefixCombination_eq_strictPrefixRowCombination
        (b := b) (i := p + 1) (hi := hi)
  rw [← hpc]
  have hdec := basis_decomposition b (p + 1) hi
  apply Vector.ext
  intro col hcol
  have hdec_col := congrArg (fun v : Vector Rat m => v[col]) hdec
  rw [Vector.getElem_sub]
  simp only [Vector.getElem_add] at hdec_col
  grind

private theorem basis_row_orthogonal_prefix_pred
    (b : Matrix Rat n m) (i p : Nat) (hi : i < n) (hp : p < n)
    (hsucc : p + 1 = i) :
    ∀ j : Fin (p + 1),
      Matrix.dot ((basis b).row ⟨i, hi⟩)
        ((GramSchmidt.prefixRows (basis b) p hp).row j) = 0 := by
  subst i
  intro j
  have hjn : j.val < n := Nat.lt_trans j.isLt hi
  have hrow :
      (GramSchmidt.prefixRows (basis b) p hp).row j =
        (basis b).row ⟨j.val, hjn⟩ := by
    apply Vector.ext
    intro col hcol
    simp [GramSchmidt.prefixRows, Matrix.row]
  rw [hrow]
  exact basis_orthogonal b (p + 1) j.val hi hjn (by omega)

private theorem basis_rowSwap_of_after_private (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  let p := i.val - 1
  have hp : p < n := by
    dsimp [p]
    exact Nat.lt_of_le_of_lt (Nat.pred_le i.val) i.isLt
  have hsucc : p + 1 = i.val := by
    dsimp [p]
    omega
  have hkp : k.val ≤ p := by
    dsimp [p]
    omega
  have hsource :
      (Matrix.rowSwap b km1 k).row i = b.row i := by
    apply Vector.ext
    intro col hcol
    let c : Fin m := ⟨col, hcol⟩
    change (Matrix.rowSwap b km1 k)[i][c] = b[i][c]
    rw [Matrix.rowSwap_getElem]
    have hik : i ≠ k := by
      intro h
      exact Nat.ne_of_gt hi (congrArg Fin.val h)
    have hikm1 : i ≠ km1 := by
      intro h
      have hval := congrArg Fin.val h
      omega
    simp [hik, hikm1]
  have horig_span :
      GramSchmidt.prefixSpan (basis b) p hp
        (b.row i - (basis b).row i) :=
    basis_row_sub_basis_row_prefixSpan_pred (b := b) (i := i.val) (p := p)
      (hi := i.isLt) (hp := hp) hsucc
  have hswap_span :
      GramSchmidt.prefixSpan (basis (Matrix.rowSwap b km1 k)) p hp
        (b.row i - (basis (Matrix.rowSwap b km1 k)).row i) := by
    have hraw :=
      basis_row_sub_basis_row_prefixSpan_pred (b := Matrix.rowSwap b km1 k)
        (i := i.val) (p := p) (hi := i.isLt) (hp := hp) hsucc
    simpa [hsource] using hraw
  have hswap_to_orig :
      ∀ v : Vector Rat m,
        GramSchmidt.prefixSpan (basis (Matrix.rowSwap b km1 k)) p hp v →
          GramSchmidt.prefixSpan (basis b) p hp v := by
    intro v hv
    have hswap_input := (basis_span (Matrix.rowSwap b km1 k) p hp v).1 hv
    have hinput :=
      (GramSchmidt.prefixSpan_rowSwap_adjacent_at_or_after
        (b := b) (km1 := km1) (k := k) (i := p) (hi := hp)
        hkm1 hkp v).1 hswap_input
    exact (basis_span b p hp v).2 hinput
  have horig_rows_to_swap :
      ∀ j : Fin (p + 1),
        GramSchmidt.prefixSpan (basis (Matrix.rowSwap b km1 k)) p hp
          ((GramSchmidt.prefixRows (basis b) p hp).row j) := by
    intro j
    have horig_basis :
        GramSchmidt.prefixSpan (basis b) p hp
          ((GramSchmidt.prefixRows (basis b) p hp).row j) :=
      GramSchmidt.prefixSpan_row (basis b) p hp j
    have horig_input :=
      (basis_span b p hp ((GramSchmidt.prefixRows (basis b) p hp).row j)).1 horig_basis
    have hswap_input :=
      (GramSchmidt.prefixSpan_rowSwap_adjacent_at_or_after
        (b := b) (km1 := km1) (k := k) (i := p) (hi := hp)
        hkm1 hkp ((GramSchmidt.prefixRows (basis b) p hp).row j)).2 horig_input
    exact
      (basis_span (Matrix.rowSwap b km1 k) p hp
        ((GramSchmidt.prefixRows (basis b) p hp).row j)).2 hswap_input
  have horig_orth :=
    basis_row_orthogonal_prefix_pred (b := b) (i := i.val) (p := p)
      (hi := i.isLt) (hp := hp) hsucc
  have hswap_orth :=
    basis_row_orthogonal_prefix_pred (b := Matrix.rowSwap b km1 k)
      (i := i.val) (p := p) (hi := i.isLt) (hp := hp) hsucc
  have hres :=
    GramSchmidt.residual_eq_of_equiv_prefixSpan
      (A := basis b) (B := basis (Matrix.rowSwap b km1 k)) (i := p) (hi := hp)
      (row := b.row i) (r := (basis b).row i)
      (s := (basis (Matrix.rowSwap b km1 k)).row i)
      horig_span hswap_span hswap_to_orig horig_rows_to_swap horig_orth hswap_orth
  exact hres.symm

/-- Swapping the adjacent rows `km1, k` leaves every basis row after the pair
unchanged: the orthogonalized prefix beyond index `k` is recomputed from the
same set of input rows. -/
@[grind =]
theorem basis_rowSwap_of_after (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i :=
  basis_rowSwap_of_after_private b km1 k i hkm1 hi

/-- Coefficient entries for a row and column both lying before the swapped pair
are unaffected by an adjacent swap. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_before (b : Matrix Rat n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : i.val < km1.val) (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  have hkm1k : km1.val < k.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row i = b.row i := by
    apply rowSwap_row_eq_of_ne
    · intro h
      have : i.val = km1.val := congrArg Fin.val h
      omega
    · intro h
      have : i.val = k.val := congrArg Fin.val h
      omega
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k
      (Nat.lt_trans hji hi)
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := i) (j := j) hji]
  rw [coeffs_lower_projection (b := b) (i := i) (j := j) hji]
  rw [hrow, hbasis]

/-- Coefficient entries for a row after the swapped pair against a column before
it are unaffected by an adjacent swap. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_after_low (b : Matrix Rat n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  have hkm1k : km1.val < k.val := by omega
  have hji : j.val < i.val := by omega
  have hrow : (Matrix.rowSwap b km1 k).row i = b.row i := by
    apply rowSwap_row_eq_of_ne
    · intro h
      have : i.val = km1.val := congrArg Fin.val h
      omega
    · intro h
      have : i.val = k.val := congrArg Fin.val h
      omega
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_before (b := b) (km1 := km1) (k := k) (i := j) hkm1k hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := i) (j := j) hji]
  rw [coeffs_lower_projection (b := b) (i := i) (j := j) hji]
  rw [hrow, hbasis]

/-- Coefficient entries for a row and column both lying after the swapped pair
are unaffected by an adjacent swap. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_after_high (b : Matrix Rat n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : k.val < j.val)
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  have hrow : (Matrix.rowSwap b km1 k).row i = b.row i := by
    apply rowSwap_row_eq_of_ne
    · intro h
      have : i.val = km1.val := congrArg Fin.val h
      omega
    · intro h
      have : i.val = k.val := congrArg Fin.val h
      omega
  have hbasis :
      (basis (Matrix.rowSwap b km1 k)).row j = (basis b).row j := by
    exact basis_rowSwap_of_after (b := b) (km1 := km1) (k := k) (i := j) hkm1 hj
  rw [coeffs_lower_projection (b := Matrix.rowSwap b km1 k) (i := i) (j := j) hji]
  rw [coeffs_lower_projection (b := b) (i := i) (j := j) hji]
  rw [hrow, hbasis]

end GramSchmidt.Rat

namespace GramSchmidt.Int

/-- The Gram-Schmidt orthogonal basis for an integer matrix, viewed in
`Rat` after coefficient divisions. -/
noncomputable def basis (b : Matrix Int n m) : Matrix Rat n m :=
  GramSchmidt.basisMatrix (GramSchmidt.castIntMatrix b)

/-- The Gram-Schmidt coefficient matrix for an integer input matrix. -/
noncomputable def coeffs (b : Matrix Int n m) : Matrix Rat n n :=
  GramSchmidt.coeffMatrix (GramSchmidt.castIntMatrix b) (basis b)

/-- Gram-Schmidt leaves the first row untouched: the leading basis row of an
integer matrix is its leading input row cast into `Rat`. -/
@[simp, grind =]
theorem basis_zero (b : Matrix Int n m) (hn : 0 < n) :
    (basis b).row ⟨0, hn⟩ =
      Vector.map (fun x : Int => (x : Rat)) (b.row ⟨0, hn⟩) := by
  simpa [basis, GramSchmidt.basisMatrix, GramSchmidt.castIntMatrix, Matrix.row] using
    GramSchmidt.basisRows_head (b := GramSchmidt.castIntMatrix b) hn

/-- Distinct Gram-Schmidt basis rows of an integer matrix (taken in `Rat`) are
mutually orthogonal. -/
@[grind =]
theorem basis_orthogonal (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Matrix.dot ((basis b).row ⟨i, hi⟩) ((basis b).row ⟨j, hj⟩) = 0 := by
  simpa [basis, GramSchmidt.Rat.basis] using
    GramSchmidt.Rat.basis_orthogonal (b := GramSchmidt.castIntMatrix b) i j hi hj hij

/-- The triangular factorization for an integer matrix: each input row, cast
into `Rat`, equals its orthogonalized basis row plus the coefficient-weighted
combination of the earlier basis rows. -/
theorem basis_decomposition (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i, hi⟩) =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  simpa [basis, coeffs, GramSchmidt.castIntMatrix, GramSchmidt.Rat.basis,
    GramSchmidt.Rat.coeffs, Matrix.row] using
      GramSchmidt.Rat.basis_decomposition (b := GramSchmidt.castIntMatrix b) i hi

/-- The coefficient matrix of an integer input has unit diagonal: each row
enters its own decomposition with weight `1`. -/
@[simp, grind =]
theorem coeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 1 := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn]

/-- The coefficient matrix of an integer input is lower triangular: entries
strictly above the diagonal vanish. -/
@[grind =]
theorem coeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  have hnot_lt : ¬j < i := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hnot_lt, hne]

private theorem castIntMatrix_rowAdd (b : Matrix Int n m) (src dst : Fin n) (c : Int) :
    GramSchmidt.castIntMatrix (Matrix.rowAdd b src dst c) =
      Matrix.rowAdd (GramSchmidt.castIntMatrix b) src dst (c : Rat) := by
  apply Vector.ext
  intro row hrow
  apply Vector.ext
  intro col hcol
  by_cases hdst : row = dst.val
  · subst row
    simp [GramSchmidt.castIntMatrix, Matrix.rowAdd, Vector.getElem_set_self]
  · have hne : dst.val ≠ row := by
      intro h
      exact hdst h.symm
    simp [GramSchmidt.castIntMatrix, Matrix.rowAdd, Vector.getElem_set_ne, hne]

private theorem castIntMatrix_rowSwap (b : Matrix Int n m) (i j : Fin n) :
    GramSchmidt.castIntMatrix (Matrix.rowSwap b i j) =
      Matrix.rowSwap (GramSchmidt.castIntMatrix b) i j := by
  apply Vector.ext
  intro row hrow
  apply Vector.ext
  intro col hcol
  let r : Fin n := ⟨row, hrow⟩
  let c : Fin m := ⟨col, hcol⟩
  calc
    (GramSchmidt.castIntMatrix (Matrix.rowSwap b i j))[r][c]
        = ((Matrix.rowSwap b i j)[r][c] : Rat) := by
          simp [GramSchmidt.castIntMatrix]
    _ = (Matrix.rowSwap (GramSchmidt.castIntMatrix b) i j)[r][c] := by
          rw [Matrix.rowSwap_getElem (M := b) (i := i) (j := j) (r := r) (k := c)]
          rw [Matrix.rowSwap_getElem (M := GramSchmidt.castIntMatrix b)
            (i := i) (j := j) (r := r) (k := c)]
          by_cases hrj : r = j
          · simp [hrj, GramSchmidt.castIntMatrix]
          · by_cases hri : r = i
            · by_cases hij : i = j
              · simp [hri, hij, GramSchmidt.castIntMatrix]
              · simp [hri, hij, GramSchmidt.castIntMatrix]
            · simp [hrj, hri, GramSchmidt.castIntMatrix]

/-- The integer Gram-Schmidt basis is invariant under adding an integer
multiple of an earlier row to a later row. -/
@[grind =]
theorem basis_rowAdd (b : Matrix Int n m) (src dst : Fin n) (c : Int)
    (hsrcdst : src.val < dst.val) :
    basis (Matrix.rowAdd b src dst c) = basis b := by
  simpa [basis, GramSchmidt.Rat.basis, castIntMatrix_rowAdd] using
    GramSchmidt.Rat.basis_rowAdd
      (b := GramSchmidt.castIntMatrix b) (src := src) (dst := dst) (c := (c : Rat))
      hsrcdst

/-- Swapping rows `km1` and `k` of an integer matrix leaves every basis row
before the pair unchanged. -/
@[grind =]
theorem basis_rowSwap_of_before (b : Matrix Int n m) (km1 k i : Fin n)
    (hkm1k : km1.val < k.val) (hi : i.val < km1.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  simpa [basis, GramSchmidt.Rat.basis, castIntMatrix_rowSwap] using
    GramSchmidt.Rat.basis_rowSwap_of_before
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) hkm1k hi

/-- After swapping adjacent rows `km1, k` of an integer matrix, the basis row at
the lower index `km1` becomes the old basis row `k` plus its projection
coefficient times the old basis row `km1`. -/
@[grind =]
theorem basis_rowSwap_adjacent_prev (b : Matrix Int n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val) :
    (basis (Matrix.rowSwap b km1 k)).row km1 =
      (basis b).row k +
        GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1 := by
  simpa [basis, coeffs, GramSchmidt.Rat.basis, GramSchmidt.Rat.coeffs,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.basis_rowSwap_adjacent_prev
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) hkm1

/-- Swapping the adjacent rows `km1, k` of an integer matrix leaves every basis
row after the pair unchanged. -/
@[grind =]
theorem basis_rowSwap_of_after (b : Matrix Int n m) (km1 k i : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) :
    (basis (Matrix.rowSwap b km1 k)).row i = (basis b).row i := by
  simpa [basis, GramSchmidt.Rat.basis, castIntMatrix_rowSwap] using
    GramSchmidt.Rat.basis_rowSwap_of_after
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) hkm1 hi

/-- After swapping adjacent rows `km1, k` of an integer matrix (assuming the
swapped pivot is nonzero), the basis row at index `k` is the explicit two-term
combination of the old basis rows `km1, k`. -/
theorem basis_rowSwap_adjacent_curr (b : Matrix Int n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val)
    (hnorm :
      Matrix.dot
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1)
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1) ≠ 0) :
    let prev := (basis b).row km1
    let curr := (basis b).row k
    let mu := GramSchmidt.entry (coeffs b) k km1
    let swappedPrev := curr + mu • prev
    (basis (Matrix.rowSwap b km1 k)).row k =
      (Matrix.dot curr curr / Matrix.dot swappedPrev swappedPrev) • prev -
        (mu * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev) • curr := by
  have hnormRat :
      Matrix.dot
        ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row k +
          GramSchmidt.entry (GramSchmidt.Rat.coeffs (GramSchmidt.castIntMatrix b)) k km1 •
            (GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row km1)
        ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row k +
          GramSchmidt.entry (GramSchmidt.Rat.coeffs (GramSchmidt.castIntMatrix b)) k km1 •
            (GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row km1) ≠ 0 := by
    simpa [basis, coeffs, GramSchmidt.Rat.basis, GramSchmidt.Rat.coeffs] using hnorm
  simpa [basis, coeffs, GramSchmidt.Rat.basis, GramSchmidt.Rat.coeffs,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.basis_rowSwap_adjacent_curr
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) hkm1 hnormRat

/-- After an adjacent swap of an integer matrix, the coefficient at the lower
row `km1` against an earlier column `j` equals the old coefficient at row `k`
against `j`. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_prev (b : Matrix Int n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) km1 j =
      GramSchmidt.entry (coeffs b) k j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_lower_prev
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (j := j) hkm1 hj

/-- Dual of `coeffs_rowSwap_adjacent_lower_prev` for an integer matrix: after an
adjacent swap, the coefficient at row `k` against an earlier column `j` equals
the old coefficient at row `km1` against `j`. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_lower_curr (b : Matrix Int n m) (km1 k j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) k j =
      GramSchmidt.entry (coeffs b) km1 j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_lower_curr
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (j := j) hkm1 hj

/-- The explicit value of the new pivot coefficient (row `k`, column `km1`)
after an adjacent swap of an integer matrix. -/
theorem coeffs_rowSwap_adjacent_pivot (b : Matrix Int n m) (km1 k : Fin n)
    (hkm1 : km1.val + 1 = k.val)
    (hnorm :
      Matrix.dot
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1)
        ((basis b).row k + GramSchmidt.entry (coeffs b) k km1 • (basis b).row km1) ≠ 0) :
    let mu := GramSchmidt.entry (coeffs b) k km1
    let prev := (basis b).row km1
    let curr := (basis b).row k
    let swappedPrev := curr + mu • prev
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) k km1 =
      mu * Matrix.dot prev prev / Matrix.dot swappedPrev swappedPrev := by
  have hnormRat :
      Matrix.dot
        ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row k +
          GramSchmidt.entry (GramSchmidt.Rat.coeffs (GramSchmidt.castIntMatrix b)) k km1 •
            (GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row km1)
        ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row k +
          GramSchmidt.entry (GramSchmidt.Rat.coeffs (GramSchmidt.castIntMatrix b)) k km1 •
            (GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row km1) ≠ 0 := by
    simpa [basis, coeffs, GramSchmidt.Rat.basis, GramSchmidt.Rat.coeffs] using hnorm
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_pivot
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) hkm1 hnormRat

/-- Coefficient entries for a row and column both lying before the swapped pair
are unaffected by an adjacent swap of an integer matrix. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_before (b : Matrix Int n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : i.val < km1.val) (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_before
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) (j := j)
      hkm1 hi hji

/-- Coefficient entries for a row after the swapped pair against a column before
it are unaffected by an adjacent swap of an integer matrix. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_after_low (b : Matrix Int n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : j.val < km1.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_after_low
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) (j := j)
      hkm1 hi hj

/-- Coefficient entries for a row and column both lying after the swapped pair
are unaffected by an adjacent swap of an integer matrix. -/
@[grind =]
theorem coeffs_rowSwap_adjacent_after_high (b : Matrix Int n m) (km1 k i j : Fin n)
    (hkm1 : km1.val + 1 = k.val) (hi : k.val < i.val) (hj : k.val < j.val)
    (hji : j.val < i.val) :
    GramSchmidt.entry (coeffs (Matrix.rowSwap b km1 k)) i j =
      GramSchmidt.entry (coeffs b) i j := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowSwap] using
    GramSchmidt.Rat.coeffs_rowSwap_adjacent_after_high
      (b := GramSchmidt.castIntMatrix b) (km1 := km1) (k := k) (i := i) (j := j)
      hkm1 hi hj hji

/-- Under integer row-add with `src < dst`, lower coefficients in the
destination row update linearly below the pivot source column. -/
@[grind =]
theorem coeffs_rowAdd_lower (b : Matrix Int n m) (col src dst : Fin n)
    (hcolsrc : col.val < src.val) (hsrcdst : src.val < dst.val) (c : Int) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col +
        (c : Rat) * GramSchmidt.entry (coeffs b) src col := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowAdd] using
    GramSchmidt.Rat.coeffs_rowAdd_lower
      (b := GramSchmidt.castIntMatrix b) (col := col) (src := src) (dst := dst)
      hcolsrc hsrcdst (c := (c : Rat))

/-- Under integer row-add with `src < dst`, the pivot coefficient in the
destination row increases by the added integer multiple. -/
@[grind =]
theorem coeffs_rowAdd_pivot (b : Matrix Int n m) (src dst : Fin n)
    (hsrcdst : src.val < dst.val) (c : Int)
    (hnorm : Matrix.dot ((basis b).row src) ((basis b).row src) ≠ 0) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst src =
      GramSchmidt.entry (coeffs b) dst src + (c : Rat) := by
  have hnormRat :
      Matrix.dot ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row src)
          ((GramSchmidt.Rat.basis (GramSchmidt.castIntMatrix b)).row src) ≠ 0 := by
    simpa [basis, GramSchmidt.Rat.basis] using hnorm
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowAdd] using
    GramSchmidt.Rat.coeffs_rowAdd_pivot
      (b := GramSchmidt.castIntMatrix b) (src := src) (dst := dst) hsrcdst
      (c := (c : Rat)) hnormRat

/-- Under integer row-add with `src < col < dst`, destination-row coefficients
above the pivot source column are preserved. -/
@[grind =]
theorem coeffs_rowAdd_above_pivot (b : Matrix Int n m) (src col dst : Fin n)
    (hsrccol : src.val < col.val) (hcoldst : col.val < dst.val) (c : Int) :
    GramSchmidt.entry (coeffs (Matrix.rowAdd b src dst c)) dst col =
      GramSchmidt.entry (coeffs b) dst col := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowAdd] using
    GramSchmidt.Rat.coeffs_rowAdd_above_pivot
      (b := GramSchmidt.castIntMatrix b) (src := src) (col := col) (dst := dst)
      hsrccol hcoldst (c := (c : Rat))

/-- An integer row-add only changes the destination row of the coefficient
matrix. -/
@[grind =]
theorem coeffs_rowAdd_other_row (b : Matrix Int n m) (src dst : Fin n) (c : Int)
    (hsrcdst : src.val < dst.val) (row : Fin n) (hrow : row ≠ dst) :
    (coeffs (Matrix.rowAdd b src dst c)).row row = (coeffs b).row row := by
  simpa [coeffs, basis, GramSchmidt.Rat.coeffs, GramSchmidt.Rat.basis,
    castIntMatrix_rowAdd] using
    GramSchmidt.Rat.coeffs_rowAdd_other_row
      (b := GramSchmidt.castIntMatrix b) (src := src) (dst := dst) (c := (c : Rat))
      hsrcdst row hrow

/-- Orthogonalization preserves the row space of each prefix for an integer
matrix: the first `i + 1` basis rows span exactly the vectors spanned by the
first `i + 1` input rows cast into `Rat`. -/
theorem basis_span (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    ∀ v : Vector Rat m,
      GramSchmidt.prefixSpan (basis b) i hi v ↔
        GramSchmidt.prefixSpan (GramSchmidt.castIntMatrix b) i hi v := by
  simpa [basis, GramSchmidt.Rat.basis] using
    GramSchmidt.Rat.basis_span (b := GramSchmidt.castIntMatrix b) i hi

end GramSchmidt.Int
end Hex
