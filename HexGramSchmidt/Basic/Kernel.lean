/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.RREF

public section

/-!
Executable Gram-Schmidt orthogonalization kernel for `hex-gram-schmidt`.

This module is the rational core that the rest of the library builds on. It
defines the projection primitives (`projectionCoeff`, `subtractProjection`),
the per-row reduction `reduceAgainstBasis`, the left-to-right orthogonalization
`basisRows`/`basisMatrix`, the coefficient matrix `coeffMatrix`, and the
supporting entry/prefix helpers (`entry`, `castIntMatrix`, `prefixCombination`,
`prefixRows`, `prefixSpan`). It also proves the foundational facts the
correspondence proofs consume: pairwise orthogonality of `basisRows`, the
residual/projection reconstruction identity, the leading-row equation, and the
zero-norm degeneracy lemmas (a `Rat` vector with zero self-dot-product is the
zero vector).
-/
namespace Hex
namespace GramSchmidt

/-- Coefficient of the orthogonal projection of `row` onto `basisRow`.
When the basis row has zero norm we use `0`, which matches the degenerate
case of Gram-Schmidt where the corresponding projection term vanishes. -/
@[expose]
def projectionCoeff (row basisRow : Vector Rat m) : Rat :=
  let denom := basisRow.dotProduct basisRow
  if denom = 0 then 0 else row.dotProduct basisRow / denom

/-- Subtract the projection of `row` onto `basisRow`. -/
@[expose]
def subtractProjection (row basisRow : Vector Rat m) : Vector Rat m :=
  row - projectionCoeff row basisRow • basisRow

/-- `dot (subtractProjection row basisRow) target` expands as `dot row target`
minus the projection coefficient times `dot basisRow target`. -/
private theorem dot_subtractProjection (row basisRow target : Vector Rat m) :
    (subtractProjection row basisRow).dotProduct target =
      row.dotProduct target - projectionCoeff row basisRow * basisRow.dotProduct target := by
  simp [subtractProjection, Vector.dotProduct_sub_smul_left]

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
    (hnorm : basisRow.dotProduct basisRow ≠ 0) :
    (subtractProjection row basisRow).dotProduct basisRow = 0 := by
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
    (hzero : v.dotProduct v = 0) (i : Fin m) :
    v[i] = 0 := by
  have hmem : i ∈ List.finRange m := by
    simp
  exact foldl_dot_self_eq_zero_of_mem (xs := List.finRange m) (v := v)
    (acc := 0) (by decide) (by simpa [Vector.dotProduct] using hzero) i hmem

/-- Over `Rat`, a vector whose self-dot-product is zero is the zero vector, so
its dot product with any other row also vanishes. Used to discharge the
degenerate zero-norm basis row case when reasoning about orthogonality. -/
theorem dot_zero_of_dot_self_zero (row v : Vector Rat m)
    (hzero : v.dotProduct v = 0) :
    row.dotProduct v = 0 := by
  unfold Vector.dotProduct
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [dot_self_eq_zero_get v hzero i, show row[i] * (0 : Rat) = 0 by grind,
        show (0 : Rat) + 0 = 0 by grind]
      change xs.foldl (fun acc i => acc + row[i] * v[i]) 0 = 0
      exact ih

/-- When `basisRow` has zero norm, `subtractProjection row basisRow` is still
orthogonal to `basisRow`. -/
private theorem dot_subtractProjection_self_zero_of_dot_self_zero
    (row basisRow : Vector Rat m)
    (hnorm : basisRow.dotProduct basisRow = 0) :
    (subtractProjection row basisRow).dotProduct basisRow = 0 := by
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
    u.dotProduct v = v.dotProduct u := by
  simpa [Vector.dotProduct] using
    foldl_dot_comm_rat (xs := List.finRange m) (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

/-- Removing a component along `otherBasisRow` that is orthogonal to `basisRow`
leaves the projection coefficient onto `basisRow` unchanged. -/
private theorem projectionCoeff_subtractProjection_eq
    (row otherBasisRow basisRow : Vector Rat m)
    (horth : otherBasisRow.dotProduct basisRow = 0) :
    projectionCoeff (subtractProjection row otherBasisRow) basisRow =
      projectionCoeff row basisRow := by
  by_cases hnorm : basisRow.dotProduct basisRow = 0
  · simp [projectionCoeff, hnorm]
  · simp [projectionCoeff, dot_subtractProjection, horth, hnorm]
    grind

/-- Reduce a row against the previously constructed orthogonal basis rows. -/
@[expose]
def reduceAgainstBasis (basisRev : List (Vector Rat m)) (row : Vector Rat m) :
    Vector Rat m :=
  basisRev.foldl subtractProjection row

/-- `reduceAgainstBasis basisRev row` has the same dot product with `target` as `row`
does, whenever `target` is orthogonal to every row in `basisRev`. -/
private theorem dot_reduceAgainstBasis_zero_of_forall_dot_zero
    (basisRev : List (Vector Rat m)) (row target : Vector Rat m)
    (horth : ∀ basisRow ∈ basisRev, basisRow.dotProduct target = 0) :
    (reduceAgainstBasis basisRev row).dotProduct target = row.dotProduct target := by
  induction basisRev generalizing row with
  | nil =>
      simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      change (reduceAgainstBasis rest (subtractProjection row basisRow)).dotProduct target =
        row.dotProduct target
      rw [ih]
      · rw [dot_subtractProjection, horth basisRow (by simp)]
        grind
      · intro laterBasisRow hlater
        exact horth laterBasisRow (by simp [hlater])

/-- The residual `reduceAgainstBasis basisRev row` stays orthogonal to `target` when both
`row` and every row in `basisRev` are orthogonal to `target`. -/
private theorem dot_reduceAgainstBasis_zero_of_dot_zero
    (basisRev : List (Vector Rat m)) (row target : Vector Rat m)
    (hrow : row.dotProduct target = 0)
    (horth : ∀ basisRow ∈ basisRev, basisRow.dotProduct target = 0) :
    (reduceAgainstBasis basisRev row).dotProduct target = 0 := by
  rw [dot_reduceAgainstBasis_zero_of_forall_dot_zero basisRev row target horth, hrow]

/-- `reduceAgainstBasis basisRev row` is orthogonal to every member of a pairwise-orthogonal
`basisRev`. -/
private theorem dot_reduceAgainstBasis_of_mem
    (basisRev : List (Vector Rat m)) (row basisRow : Vector Rat m)
    (hmem : basisRow ∈ basisRev)
    (horth : basisRev.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0)) :
    (reduceAgainstBasis basisRev row).dotProduct basisRow = 0 := by
  induction basisRev generalizing row with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      by_cases hhead : head = basisRow
      · subst basisRow
        apply dot_reduceAgainstBasis_zero_of_dot_zero
        · by_cases hnorm : head.dotProduct head = 0
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
private theorem projectionCoeff_reduceAgainstBasis_eq
    (basisRev : List (Vector Rat m)) (row basisRow : Vector Rat m)
    (horth : ∀ otherBasisRow ∈ basisRev, otherBasisRow.dotProduct basisRow = 0) :
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
      · exact projectionCoeff_subtractProjection_eq
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
    (horth : basisRev.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0)) :
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
        exact projectionCoeff_subtractProjection_eq
          (row := row) (otherBasisRow := basisRow) (basisRow := laterBasisRow)
          (List.rel_of_pairwise_cons horth hlater).1

/-- For a pairwise-orthogonal `basisRev`, `row` equals its residual plus the sum of its
projections onto the basis rows. -/
private theorem reduceAgainstBasis_reconstruction
    (basisRev : List (Vector Rat m)) (row : Vector Rat m)
    (horth : basisRev.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0)) :
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
@[expose]
def basisRowsAux (basisRev pending : List (Vector Rat m)) : List (Vector Rat m) :=
  match pending with
  | [] => basisRev.reverse
  | row :: rows =>
      let next := reduceAgainstBasis basisRev row
      basisRowsAux (next :: basisRev) rows

/-- Left-to-right Gram-Schmidt orthogonalization on a matrix's rows. -/
@[expose]
def basisRows (rows : List (Vector Rat m)) : List (Vector Rat m) :=
  basisRowsAux [] rows

/-- Rebuild a matrix from its row list after Gram-Schmidt orthogonalization. -/
@[expose]
def basisMatrix (b : Matrix Rat n m) : Matrix Rat n m :=
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
    (horth : rows.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0)) :
    rows.reverse.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) := by
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
    (horth : basisRev.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0)) :
    (basisRowsAux basisRev pending).Pairwise
      (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) := by
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
    (basisRows rows).Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) := by
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
    (basisRows b.toList)[i]!.dotProduct (basisRows b.toList)[j]! = 0 := by
  let rows := basisRows b.toList
  have hlen : rows.length = n := by
    simp [rows, basisRows_length]
  have hirows : i < rows.length := by simpa [hlen] using hi
  have hjrows : j < rows.length := by simpa [hlen] using hj
  have hpair : rows.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) := by
    simpa [rows] using basisRows_pairwise (rows := b.toList)
  have hget_i : rows[i]! = rows[i] := by simp [hirows]
  have hget_j : rows[j]! = rows[j] := by simp [hjrows]
  by_cases hlt : i < j
  · have hrel :=
      (List.pairwise_iff_getElem.1 hpair) i j hirows hjrows hlt
    rw [hget_i, hget_j]
    exact hrel.1
  · have hji : j < i := by
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hij h.symm)
    have hrel :=
      (List.pairwise_iff_getElem.1 hpair) j i hjrows hirows hji
    rw [hget_i, hget_j]
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
@[expose]
def coeffMatrix (rows basis : Matrix Rat n m) : Matrix Rat n n :=
  Matrix.ofFn fun i j =>
    if hlt : j.val < i.val then
      projectionCoeff rows[i] basis[j]
    else if i = j then
      1
    else
      0

/-- Access a dense matrix entry by row and column indices. -/
@[expose]
def entry (M : Matrix R n m) (i : Fin n) (j : Fin m) : R :=
  (M.row i)[j]

/-- Cast an integer matrix into the rational matrix space used by
Gram-Schmidt. -/
@[expose]
def castIntMatrix (b : Matrix Int n m) : Matrix Rat n m :=
  Vector.map (fun row => Vector.map (fun x : Int => (x : Rat)) row) b

/-- The prefix combination term used in the decomposition theorem shape. -/
@[expose]
def prefixCombination (coeffs : Matrix Rat n n) (basis : Matrix Rat n m) (i : Nat) (hi : i < n) :
    Vector Rat m :=
  (List.finRange i).foldl
    (fun acc j =>
      let jn : Fin n := ⟨j.val, Nat.lt_trans j.isLt hi⟩
      acc + GramSchmidt.entry coeffs ⟨i, hi⟩ jn • basis.row jn)
    0

/-- The row-prefix matrix containing rows `0` through `i`. -/
@[expose]
def prefixRows (M : Matrix R n m) (i : Nat) (hi : i < n) : Matrix R (i + 1) m :=
  Vector.ofFn fun j => M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hi)⟩

/-- Executable row-span membership in the first `i + 1` rows of a matrix. -/
@[expose]
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
      (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) :=
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
      rw [ih (acc := acc + f x), ih (acc := 0 + f x),
        Vector.getElem_add, Vector.getElem_add, Vector.getElem_zero]
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
  have hdot : (0 : Vector Rat m).dotProduct basisRow = 0 := by
    unfold Vector.dotProduct
    induction List.finRange m with
    | nil =>
        rfl
    | cons i rest ih =>
      simp only [List.foldl_cons]
      have hentry : (0 : Vector Rat m)[i] = 0 := by
        change (0 : Vector Rat m)[i.val] = 0
        rw [Vector.getElem_zero]
      rw [hentry, show (0 : Rat) + 0 * basisRow[i] = 0 by grind]
      exact ih
  apply Vector.ext
  intro idx hidx
  by_cases hnorm : basisRow.dotProduct basisRow = 0
  · have hcoeff : projectionCoeff 0 basisRow = 0 := by
      simp [projectionCoeff, hnorm]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_zero, Vector.getElem_smul,
      hcoeff]
    change (0 : Rat) - 0 * basisRow[idx] = 0
    grind
  · have hcoeff : projectionCoeff 0 basisRow = 0 := by
      have hzero_div : (0 : Rat) / basisRow.dotProduct basisRow = 0 := by
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
basis row out: when `row.dotProduct basisRow = 0` the projection coefficient
is `0`, so `subtractProjection row basisRow = row`. The single-step
orthogonality-invariance fact underpinning the list version below. -/
private theorem subtractProjection_eq_self
    (row basisRow : Vector Rat m) (h : row.dotProduct basisRow = 0) :
    subtractProjection row basisRow = row := by
  apply Vector.ext
  intro idx hidx
  by_cases hnorm : basisRow.dotProduct basisRow = 0
  · have hcoeff : projectionCoeff row basisRow = 0 := by
      simp [projectionCoeff, hnorm]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_smul, hcoeff]
    change row[idx] - 0 * basisRow[idx] = row[idx]
    grind
  · have hcoeff : projectionCoeff row basisRow = 0 := by
      have hzero_div : (0 : Rat) / basisRow.dotProduct basisRow = 0 := by
        grind
      simp [projectionCoeff, h, hnorm, hzero_div]
    rw [subtractProjection, Vector.getElem_sub, Vector.getElem_smul, hcoeff]
    change row[idx] - 0 * basisRow[idx] = row[idx]
    grind

/-- A row orthogonal to *every* basis vector survives the whole reduction
unchanged: iterating `subtractProjection_eq_self` down the list
gives `reduceAgainstBasis basisRev row = row`. Lets later proofs conclude a
row lies outside the prefix span without recomputing the fold. -/
private theorem reduceAgainstBasis_eq_self
    (basisRev : List (Vector Rat m)) (row : Vector Rat m)
    (h : ∀ basisRow ∈ basisRev, row.dotProduct basisRow = 0) :
    reduceAgainstBasis basisRev row = row := by
  induction basisRev generalizing row with
  | nil =>
      simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      have hhead : subtractProjection row basisRow = row :=
        subtractProjection_eq_self row basisRow (h basisRow (by simp))
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
  by_cases hnorm : basisRow.dotProduct basisRow = 0
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
    have hdiv : basisRow.dotProduct basisRow / basisRow.dotProduct basisRow = 1 := by
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

end GramSchmidt
end Hex
