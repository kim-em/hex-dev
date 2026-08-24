/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHermite.Unique

public section

/-! Executable row-lattice, kernel, pivot, and index APIs derived from HNF. -/

namespace Hex.Matrix

namespace Hermite

/-- Solve against the nonzero HNF rows by forward pivot substitution. -/
@[expose]
def solve (H : Matrix Int n m) (r : Nat) (piv : Vector (Fin m) r)
    (v : Vector Int m) : Option (Vector Int n) :=
  let initial : Vector Int m × Vector Int n := (v, 0)
  let result := (List.finRange n).foldlM (m := Option)
    (fun (state : Vector Int m × Vector Int n) (row : Fin n) =>
      if hr : row.val < r then
        let i : Fin r := ⟨row.val, hr⟩
        let col := piv.get i
        let p : Int := H[(row, col)]
        if p = 0 then
          none
        else
          let value := state.1.get col
          if value % p = 0 then
            let q := value / p
            let residual := Vector.ofFn fun j => state.1.get j - q * H[(row, j)]
            some (residual, state.2.set row.val q row.isLt)
          else
            none
      else
        some state) initial
  match result with
  | none => none
  | some (residual, coeffs) =>
      if residual = 0 then some coeffs else none

end Hermite

/-- Integer coefficients expressing `v` as a combination of the rows of
`A`, or `none` when the forward HNF solve does not verify. -/
@[expose]
def latticeCoeffs (A : Matrix Int n m) (v : Vector Int m) : Option (Vector Int n) :=
  let D := hnfData A
  match Hermite.solve D.echelon D.rank D.pivotCols v with
  | none => none
  | some d =>
      let c := Matrix.transpose D.transform * d
      if vecMul c A = v then some c else none

/-- Decide membership in the integer row lattice of `A`. -/
@[expose]
def latticeContains (A : Matrix Int n m) (v : Vector Int m) : Bool :=
  (latticeCoeffs A v).isSome

/-- The rows of the transform corresponding to zero HNF rows. -/
@[expose]
def kernelBasis (A : Matrix Int n m) : Matrix Int (n - hnfRank A) n :=
  let hr := Hermite.run_rank_le (Hermite.formAccumulator n) A
  Matrix.ofFn fun i j =>
    let row : Fin n := ⟨hnfRank A + i.val, by omega⟩
    (hnfData A).transform[(row, j)]

/-- Positive HNF pivot values in pivot-column order. -/
@[expose]
def pivots (A : Matrix Int n m) : Vector Nat (hnfRank A) :=
  let D := hnfData A
  let hrank := hnfRank_eq A
  let hr := Hermite.run_rank_le (Hermite.transformAccumulator n) A
  have hrD : D.rank ≤ n := by
    change (Hermite.run (Hermite.transformAccumulator n) A).pivots.length ≤ n
    exact hr
  Vector.ofFn fun i =>
    have hiD : i.val < D.rank := by
      rw [← hrank]
      exact i.isLt
    let pi : Fin D.rank := ⟨i.val, hiD⟩
    let row : Fin n := ⟨i.val, Nat.lt_of_lt_of_le hiD hrD⟩
    (D.echelon[(row, D.pivotCols.get pi)]).natAbs

/-- Index of the row lattice in `Int^m`, with `0` denoting infinite index. -/
@[expose]
def latticeIndex (A : Matrix Int n m) : Nat :=
  if hnfRank A = m then
    (pivots A).foldl (· * ·) 1
  else
    0

set_option maxHeartbeats 400000 in
private theorem recover_of_inverse {A : Matrix Int n m} {H : Matrix Int n m}
    {U W : Matrix Int n n} (hUA : U * A = H)
    (hWU : W * U = Matrix.identity (R := Int) n) : W * H = A := by
  calc
    W * H = W * (U * A) := by rw [hUA]
    _ = (W * U) * A := (Matrix.mul_assoc W U A).symm
    _ = Matrix.identity (R := Int) n * A := by rw [hWU]
    _ = A := Matrix.identity_mul A

set_option maxHeartbeats 400000 in
/-- Hermite reduction preserves the integer row lattice. -/
theorem hnf_memLattice_iff (A : Matrix Int n m) (v : Vector Int m) :
    A.memLattice v ↔ (hnf A).memLattice v := by
  let D := hnfWithInv A
  have hforward : D.rowData.transform * A = D.rowData.echelon :=
    hnfWithInv_transform_mul A
  have hback : D.inverse * D.rowData.echelon = A :=
    recover_of_inverse hforward (hnfWithInv_inv_mul A)
  have hform : hnf A = D.rowData.echelon := by
    rw [hnf_eq_hnfData_echelon, ← hnfWithInv_data A]
  rw [hform]
  exact memLattice_iff_of_mul_eq hforward hback v

private theorem row_mul_eq_vecMul (M : Matrix Int n' n) (N : Matrix Int n m)
    (i : Fin n') : Matrix.row (M * N) i = vecMul (Matrix.row M i) N := by
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  change (M * N)[i][jj] = (Matrix.row M i * N)[jj]
  rw [Matrix.getElem_mul, Matrix.getElem_vecMul]
  exact Vector.dotProduct_comm _ _

private theorem basis_mul_form (A : Matrix Int n m) :
    let P : Matrix Int (hnfRank A) n := Matrix.ofFn fun i j =>
      if Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i = j
        then 1 else 0
    P * hnf A = hnfBasis A := by
  dsimp only
  let P : Matrix Int (hnfRank A) n := Matrix.ofFn fun i j =>
    if Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i = j
      then 1 else 0
  apply Matrix.ext_getElem
  intro i j
  have hrow : Matrix.row P i = Vector.ofFn fun k : Fin n =>
      if Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i = k
        then 1 else 0 := by
    apply Vector.ext
    intro k hk
    let kk : Fin n := ⟨k, hk⟩
    have hp : (Matrix.row P i)[kk] =
        (if Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i = kk
          then 1 else 0) := by
      rw [Matrix.getElem_row]
      simp only [P, Matrix.getElem_ofFn]
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using hp
  have hmul := row_mul_eq_vecMul P (hnf A) i
  rw [hrow, IsRowReduced.vecMul_single] at hmul
  have hentry := congrArg (fun row : Vector Int m => row.get j) hmul
  calc
    (P * hnf A)[i][j] =
        (hnf A)[Fin.castLE
          (Hermite.run_rank_le (Hermite.formAccumulator n) A) i][j] := hentry
    _ = (hnfBasis A)[i][j] := by
      simp only [hnfBasis, Matrix.getElem_ofFn,
        Matrix.getElem_pair_eq_nested]

private theorem form_mul_basis (A : Matrix Int n m) :
    let Q : Matrix Int n (hnfRank A) := Matrix.ofFn fun i j =>
      if i.val = j.val then 1 else 0
    Q * hnfBasis A = hnf A := by
  dsimp only
  let Q : Matrix Int n (hnfRank A) := Matrix.ofFn fun i j =>
    if i.val = j.val then 1 else 0
  have hform := hnfData_isHNF A
  have hrank := hnfRank_eq A
  apply Matrix.ext_getElem
  intro i j
  by_cases hir : i.val < hnfRank A
  · let ii : Fin (hnfRank A) := ⟨i.val, hir⟩
    have hrow : Matrix.row Q i = Vector.ofFn fun k : Fin (hnfRank A) =>
        if ii = k then 1 else 0 := by
      apply Vector.ext
      intro k hk
      let kk : Fin (hnfRank A) := ⟨k, hk⟩
      have hq : (Matrix.row Q i)[kk] =
          (if ii = kk then 1 else 0) := by
        rw [Matrix.getElem_row]
        simp only [Q, Matrix.getElem_ofFn]
        congr 1
        exact propext ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using hq
    have hmul := row_mul_eq_vecMul Q (hnfBasis A) i
    rw [hrow, IsRowReduced.vecMul_single] at hmul
    have hentry := congrArg (fun row : Vector Int m => row.get j) hmul
    calc
      (Q * hnfBasis A)[i][j] = (hnfBasis A)[ii][j] := hentry
      _ = (hnf A)[i][j] := by
        simp only [hnfBasis, Matrix.getElem_ofFn,
          Matrix.getElem_pair_eq_nested]
        congr 2
  · have hrow : Matrix.row Q i = 0 := by
      apply Vector.ext
      intro k hk
      let kk : Fin (hnfRank A) := ⟨k, hk⟩
      have hq : (Matrix.row Q i)[kk] = 0 := by
        rw [Matrix.getElem_row]
        simp only [Q, Matrix.getElem_ofFn]
        rw [if_neg]
        omega
      have hz : (0 : Vector Int (hnfRank A))[kk.val] = 0 :=
        Vector.getElem_zero kk.val kk.isLt
      calc
        (Matrix.row Q i)[k] = 0 := by
          simpa only [Fin.getElem_fin] using hq
        _ = (0 : Vector Int (hnfRank A))[k] := hz.symm
    have hmul := row_mul_eq_vecMul Q (hnfBasis A) i
    have hzero : vecMul (0 : Vector Int (hnfRank A)) (hnfBasis A) = 0 :=
      Matrix.mulVec_zero (Matrix.transpose (hnfBasis A))
    rw [hrow, hzero] at hmul
    have hentry := congrArg (fun row : Vector Int m => row.get j) hmul
    have hiD : (hnfData A).rank ≤ i.val := by omega
    have hz := hform.toIsEchelonForm.zero_row i hiD
    have hzentry := congrArg (fun row : Vector Int m => row.get j) hz
    rw [← hnf_eq_hnfData_echelon A] at hzentry
    calc
      (Q * hnfBasis A)[i][j] = (0 : Vector Int m)[j] := hentry
      _ = (hnf A)[i][j] := hzentry.symm

/-- Discarding the trailing zero rows of HNF does not change its integer row
lattice. -/
theorem hnfBasis_memLattice_iff (A : Matrix Int n m) (v : Vector Int m) :
    (hnfBasis A).memLattice v ↔ A.memLattice v := by
  let P : Matrix Int (hnfRank A) n := Matrix.ofFn fun i j =>
    if Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i = j
      then 1 else 0
  let Q : Matrix Int n (hnfRank A) := Matrix.ofFn fun i j =>
    if i.val = j.val then 1 else 0
  have hP : P * hnf A = hnfBasis A := basis_mul_form A
  have hQ : Q * hnfBasis A = hnf A := form_mul_basis A
  constructor
  · intro hv
    exact (hnf_memLattice_iff A v).2 (memLattice_of_mul_eq hP hv)
  · intro hv
    exact memLattice_of_mul_eq hQ ((hnf_memLattice_iff A v).1 hv)

/-- Every returned lattice coefficient vector satisfies its advertised
row-combination equation. -/
theorem latticeCoeffs_sound {A : Matrix Int n m} {v : Vector Int m}
    {c : Vector Int n} :
    latticeCoeffs A v = some c → vecMul c A = v := by
  intro h
  unfold latticeCoeffs at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · rename_i d hverify
      injection h with hc
      subst c
      exact hverify
    · contradiction

private theorem take_append_drop {R : Type} (v : Vector R n) (r : Nat)
    (hr : r ≤ n) :
    (((v.take r).cast (Nat.min_eq_left hr)) ++ v.drop r).cast
      (Nat.add_sub_of_le hr) = v := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_cast]
  by_cases hir : i < r
  · rw [Vector.getElem_append_left hir, Vector.getElem_cast,
      Vector.getElem_take]
  · have hri : r ≤ i := Nat.le_of_not_gt hir
    rw [Vector.getElem_append_right]
    · rw [Vector.getElem_drop]
      congr 1
      omega
    · simpa [Nat.min_eq_left hr] using hri

private theorem dotProduct_cast {R : Type} [Mul R] [Add R] [OfNat R 0]
    (u v : Vector R n) (h : n = n') :
    (u.cast h).dotProduct (v.cast h) = u.dotProduct v := by
  subst n'
  rfl

private theorem dotProduct_drop_of_head_zero {R : Type} [Lean.Grind.Ring R]
    (u v : Vector R n) (r : Nat) (hr : r ≤ n)
    (hz : ∀ i : Fin r, u[Fin.castLE hr i] = 0) :
    (u.drop r).dotProduct (v.drop r) = u.dotProduct v := by
  let hu : Vector R r := (u.take r).cast (Nat.min_eq_left hr)
  let hv : Vector R r := (v.take r).cast (Nat.min_eq_left hr)
  have huz : hu = 0 := by
    apply Vector.ext
    intro i hi
    simp only [hu, Vector.getElem_cast, Vector.getElem_take,
      Vector.getElem_zero]
    exact hz ⟨i, hi⟩
  have husplit := take_append_drop u r hr
  have hvsplit := take_append_drop v r hr
  calc
    (u.drop r).dotProduct (v.drop r) =
        hu.dotProduct hv + (u.drop r).dotProduct (v.drop r) := by
          have hdot : (0 : Vector R r).dotProduct hv = 0 := by
            unfold Vector.dotProduct
            apply List.foldl_add_eq_self
            intro i _hi
            rw [show (0 : Vector R r)[i] = 0 by
              exact Vector.getElem_zero i.val i.isLt]
            grind
          rw [huz, hdot]
          grind
    _ = (hu ++ u.drop r).dotProduct (hv ++ v.drop r) :=
      (Vector.dotProduct_append hu (u.drop r) hv (v.drop r)).symm
    _ = (((hu ++ u.drop r).cast (Nat.add_sub_of_le hr)).dotProduct
        ((hv ++ v.drop r).cast (Nat.add_sub_of_le hr))) := by
          exact (dotProduct_cast (hu ++ u.drop r) (hv ++ v.drop r)
            (Nat.add_sub_of_le hr)).symm
    _ = u.dotProduct v := by rw [husplit, hvsplit]

private theorem vecMul_kernelBasis (A : Matrix Int n m) (d : Vector Int n)
    (hz : ∀ i : Fin (hnfRank A),
      d[Fin.castLE (Hermite.run_rank_le (Hermite.formAccumulator n) A) i] = 0) :
    vecMul (d.drop (hnfRank A)) (kernelBasis A) =
      vecMul d (hnfData A).transform := by
  let r := hnfRank A
  have hr : r ≤ n := Hermite.run_rank_le (Hermite.formAccumulator n) A
  apply Vector.ext
  intro j hj
  let col : Fin n := ⟨j, hj⟩
  change ((d.drop r) * kernelBasis A)[col] =
    (d * (hnfData A).transform)[col]
  rw [getElem_vecMul, getElem_vecMul]
  have hcol : Matrix.col (kernelBasis A) col =
      (Matrix.col (hnfData A).transform col).drop r := by
    apply Vector.ext
    intro i hi
    unfold Matrix.col
    rw [Vector.getElem_ofFn]
    rw [Vector.getElem_drop, Vector.getElem_ofFn]
    simp only [kernelBasis, Matrix.getElem_ofFn,
      Matrix.getElem_pair_eq_nested, r]
  rw [hcol]
  calc
    ((Matrix.col (hnfData A).transform col).drop r).dotProduct (d.drop r) =
        (d.drop r).dotProduct
          ((Matrix.col (hnfData A).transform col).drop r) :=
      Vector.dotProduct_comm _ _
    _ = d.dotProduct (Matrix.col (hnfData A).transform col) :=
      dotProduct_drop_of_head_zero d
        (Matrix.col (hnfData A).transform col) r hr hz
    _ = (Matrix.col (hnfData A).transform col).dotProduct d :=
      Vector.dotProduct_comm _ _

/-- The returned kernel rows are annihilated by the input matrix. -/
theorem kernelBasis_mul (A : Matrix Int n m) : kernelBasis A * A = 0 := by
  let D := hnfData A
  have hform := hnfData_isHNF A
  have hrank : hnfRank A = D.rank := hnfRank_eq A
  apply Matrix.ext_getElem
  intro i j
  let row : Fin n := ⟨hnfRank A + i.val, by
    have hr := hform.toIsEchelonForm.rank_le_n
    omega⟩
  have hrow : D.rank ≤ row.val := by simp only [row]; omega
  have hzero : D.echelon[row] = 0 := hform.toIsEchelonForm.zero_row row hrow
  calc
    (kernelBasis A * A)[i][j] = (D.transform * A)[row][j] := by
      simp only [D, row, Matrix.getElem_mul, kernelBasis, Matrix.getElem_ofFn,
        Matrix.getElem_row, Matrix.getElem_col, Matrix.getElem_pair_eq_nested,
        Vector.dotProduct]
    _ = D.echelon[row][j] := by rw [hnfData_transform_mul A]
    _ = 0 := by rw [hzero]; simp
    _ = (0 : Matrix Int (n - hnfRank A) m)[i][j] :=
      (Matrix.getElem_zero i j).symm

set_option maxHeartbeats 400000 in
/-- Every integer left-kernel vector is an integer combination of the returned
kernel rows. -/
theorem kernelBasis_complete {A : Matrix Int n m} {x : Vector Int n} :
    vecMul x A = 0 → ∃ c, vecMul c (kernelBasis A) = x := by
  intro hx
  let D := hnfData A
  let W := (hnfWithInv A).inverse
  let d : Vector Int n := Matrix.transpose W * x
  have hform : IsHNF A D := hnfData_isHNF A
  have hinv : W * D.transform = Matrix.identity (R := Int) n := by
    simp only [W, D]
    rw [← hnfWithInv_data A]
    exact hnfWithInv_inv_mul A
  have hd : vecMul d D.echelon = 0 := by
    calc
      vecMul d D.echelon = vecMul x A :=
        hform.toIsEchelonForm.vecMul_transformInv_transpose hinv x
      _ = 0 := hx
  have hr : hnfRank A ≤ n :=
    Hermite.run_rank_le (Hermite.formAccumulator n) A
  have hz : ∀ i : Fin (hnfRank A), d[Fin.castLE hr i] = 0 := by
    intro i
    have hi : i.val < D.rank := by
      rw [← hnfRank_eq A]
      exact i.isLt
    let ii : Fin D.rank := ⟨i.val, hi⟩
    have hcoeff := hform.coeff_eq_zero d hd ii
    have hrow : hform.toIsEchelonForm.pivotRow ii = Fin.castLE hr i := Fin.ext rfl
    change d.get (Fin.castLE hr i) = 0
    calc
      d.get (Fin.castLE hr i) =
          d.get (hform.toIsEchelonForm.pivotRow ii) :=
        congrArg d.get hrow.symm
      _ = 0 := hcoeff
  have hrecover : Matrix.transpose D.transform * d = x := by
    calc
      Matrix.transpose D.transform * d =
          Matrix.transpose D.transform * (Matrix.transpose W * x) := rfl
      _ = (Matrix.transpose D.transform * Matrix.transpose W) * x :=
        (Matrix.mul_assoc_vec D.transform.transpose W.transpose x).symm
      _ = Matrix.transpose (W * D.transform) * x := by
        rw [← Matrix.transpose_mul_of_mul_comm]
      _ = Matrix.transpose (Matrix.identity (R := Int) n) * x := by rw [hinv]
      _ = Matrix.identity (R := Int) n * x := by rw [Matrix.transpose_identity]
      _ = x := Matrix.identity_mulVec x
  refine ⟨d.drop (hnfRank A), ?_⟩
  calc
    vecMul (d.drop (hnfRank A)) (kernelBasis A) =
        vecMul d D.transform := vecMul_kernelBasis A d hz
    _ = x := hrecover

set_option maxHeartbeats 400000 in
/-- The returned kernel rows are linearly independent over the integers. -/
theorem kernelBasis_independent {A : Matrix Int n m}
    {c : Vector Int (n - hnfRank A)} :
    vecMul c (kernelBasis A) = 0 → c = 0 := by
  intro hc
  let r := hnfRank A
  have hr : r ≤ n := Hermite.run_rank_le (Hermite.formAccumulator n) A
  let d : Vector Int n := Vector.ofFn fun i =>
    if h : i.val < r then 0 else c[i.val - r]'(by omega)
  have hz : ∀ i : Fin r, d[Fin.castLE hr i] = 0 := by
    intro i
    simp [d, i.isLt]
  have hdrop : d.drop r = c := by
    apply Vector.ext
    intro i hi
    simp only [d, Vector.getElem_drop, Vector.getElem_ofFn]
    rw [dite_eq_right (by omega)]
    congr 1
    omega
  have hdU : vecMul d (hnfData A).transform = 0 := by
    rw [← vecMul_kernelBasis A d hz, hdrop, hc]
  let W := (hnfWithInv A).inverse
  have hinv : (hnfData A).transform * W = Matrix.identity (R := Int) n := by
    simp only [W]
    rw [← hnfWithInv_data A]
    exact hnfWithInv_mul_inv A
  have hd : d = 0 := by
    have hrecover : Matrix.transpose W *
        (Matrix.transpose (hnfData A).transform * d) = d := by
      calc
        Matrix.transpose W * (Matrix.transpose (hnfData A).transform * d) =
            (Matrix.transpose W * Matrix.transpose (hnfData A).transform) * d :=
          (Matrix.mul_assoc_vec W.transpose (hnfData A).transform.transpose d).symm
        _ = Matrix.transpose ((hnfData A).transform * W) * d := by
          rw [← Matrix.transpose_mul_of_mul_comm]
        _ = Matrix.transpose (Matrix.identity (R := Int) n) * d := by rw [hinv]
        _ = Matrix.identity (R := Int) n * d := by rw [Matrix.transpose_identity]
        _ = d := Matrix.identity_mulVec d
    have hzero : Matrix.transpose W *
        (Matrix.transpose (hnfData A).transform * d) = 0 := by
      change Matrix.transpose W * vecMul d (hnfData A).transform = 0
      rw [hdU]
      exact Matrix.mulVec_zero _
    exact hrecover.symm.trans hzero
  have hdropzero : (0 : Vector Int n).drop r = 0 := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_drop]
    calc
      (0 : Vector Int n)[r + i] = (0 : Int) :=
        Vector.getElem_zero (α := Int) (n := n) (r + i) (by
          simp only [r] at hi ⊢
          omega)
      _ = (0 : Vector Int (n - r))[i] :=
        (Vector.getElem_zero (α := Int) (n := n - r) i hi).symm
  calc
    c = d.drop r := hdrop.symm
    _ = (0 : Vector Int n).drop r := congrArg (fun v : Vector Int n => v.drop r) hd
    _ = 0 := hdropzero

@[simp] theorem latticeContains_eq_isSome (A : Matrix Int n m) (v : Vector Int m) :
    latticeContains A v = (latticeCoeffs A v).isSome := rfl

/-- The index definition is the pivot product in the full-rank case. -/
theorem latticeIndex_eq_prod_pivots (A : Matrix Int n m) (h : hnfRank A = m) :
    latticeIndex A = (pivots A).foldl (· * ·) 1 := by
  simp [latticeIndex, h]

end Hex.Matrix
