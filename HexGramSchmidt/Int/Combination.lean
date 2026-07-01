/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Int.Correspondence
import all HexGramSchmidt.Int.Correspondence

public section

namespace Hex
namespace GramSchmidt.Int
/-! ### Prefix coefficient vector for integer row combinations -/

/-- Cast the first `k.val + 1` entries of an integer coefficient vector into a
rational prefix coefficient vector. Used to package an integer row combination
whose later coefficients vanish as a prefix-span witness over the cast input
rows. -/
private def prefixCoeffsCast (c : Vector Int n) (k : Fin n) : Vector Rat (k.val + 1) :=
  Vector.ofFn fun j : Fin (k.val + 1) =>
    let jn : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
    (c[jn] : Rat)

/-- Integer cast distributes over an inner-product-style integer `foldl`. -/
private theorem foldl_int_dot_cast {n' : Nat}
    (xs : List (Fin n')) (g h : Fin n' → Int) (acc : Int) :
    ((xs.foldl (fun a i => a + g i * h i) acc : Int) : Rat) =
      xs.foldl
        (fun a i => a + ((g i : Rat)) * ((h i : Rat)))
        (acc : Rat) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hpush : ((acc + g i * h i : Int) : Rat) =
          (acc : Rat) + (g i : Rat) * (h i : Rat) := by
        push_cast
        rfl
      have := ih (acc := acc + g i * h i)
      rw [this, hpush]

/-- Entry expansion of an integer row combination at a fixed output column. -/
private theorem vecMul_int_getElem
    (b : Matrix Int n m) (c : Vector Int n) (col : Fin m) :
    (Matrix.vecMul c b)[col] =
      (List.finRange n).foldl
        (fun (acc : Int) (i : Fin n) => acc + b[i][col] * c[i]) 0 := by
  show (Matrix.transpose b * c)[col] = _
  rw [Matrix.getElem_mulVec]
  show ((Matrix.transpose b).row col).dotProduct c = _
  simp [Vector.dotProduct, Matrix.row, Matrix.transpose, Matrix.col, Hex.Matrix.getRow, Fin.getElem_fin]

/-- Entry expansion of the cast prefix row combination. The `(j + 1)`-row prefix
of `castIntMatrix b` combined with `prefixCoeffsCast c k` reads out as a sum of
the cast integer products through index `k`. -/
private theorem vecMul_prefix_castIntMatrix_getElem
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n) (col : Fin m) :
    (Matrix.vecMul (prefixCoeffsCast c k) (GramSchmidt.prefixRows (castIntMatrix b) k.val k.isLt))[col] =
      (List.finRange (k.val + 1)).foldl
        (fun (acc : Rat) (j : Fin (k.val + 1)) =>
          let jn : Fin n :=
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
          acc + (b[jn][col] : Rat) * (c[jn] : Rat)) 0 := by
  show (Matrix.transpose _ * _)[col] = _
  rw [Matrix.getElem_mulVec]
  show ((Matrix.transpose _).row col).dotProduct _ = _
  simp [Vector.dotProduct, GramSchmidt.prefixRows,
    castIntMatrix, prefixCoeffsCast, Matrix.row, Matrix.transpose, Matrix.col,
    Hex.Matrix.getRow, Fin.getElem_fin]

/-- Cast row-combination prefix-span truncation. If an integer coefficient
vector has all entries above index `k` equal to zero, the cast of the integer
row combination is the row combination of the first `k.val + 1` cast rows with
the prefix coefficient vector `prefixCoeffsCast c k`. -/
private theorem cast_vecMul_eq
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b) =
      Matrix.vecMul (prefixCoeffsCast c k) (GramSchmidt.prefixRows (castIntMatrix b) k.val k.isLt) := by
  apply Vector.ext
  intro col hcol
  let cf : Fin m := ⟨col, hcol⟩
  have hLHS :
      (Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b))[cf] =
        ((Matrix.vecMul c b)[cf] : Rat) :=
    Vector.getElem_map _ _
  change (Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b))[cf]
      = (Matrix.vecMul (prefixCoeffsCast c k) (GramSchmidt.prefixRows (castIntMatrix b) k.val k.isLt))[cf]
  rw [hLHS, vecMul_int_getElem b c cf, vecMul_prefix_castIntMatrix_getElem b c k cf]
  -- LHS: cast of an integer foldl; RHS: a rational foldl over `finRange (k+1)`.
  -- First, push the cast through the integer foldl, getting a rational foldl
  -- over `finRange n` whose later terms vanish; then truncate to `k + 1`.
  rw [foldl_int_dot_cast (List.finRange n)
    (fun i : Fin n => b[i][cf]) (fun i : Fin n => c[i]) 0]
  let f : Fin n → Rat := fun i => (b[i][cf] : Rat) * (c[i] : Rat)
  have hfzero : ∀ j : Fin n, k.val < j.val → f j = 0 := by
    intro j hj
    have hcj : (c[j] : Rat) = 0 := by
      have : c[j] = 0 := hzero j hj
      simp [this]
    show (b[j][cf] : Rat) * (c[j] : Rat) = 0
    rw [hcj]
    grind
  have htrunc :=
    foldl_finRange_eq_prefix_of_zero_above (n := n) k f hfzero
  show (List.finRange n).foldl (fun acc i => acc + f i) ((0 : Int) : Rat) =
    (List.finRange (k.val + 1)).foldl
      (fun (acc : Rat) (j : Fin (k.val + 1)) =>
        let jn : Fin n :=
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
        acc + (b[jn][cf] : Rat) * (c[jn] : Rat)) 0
  have hcast0 : ((0 : Int) : Rat) = 0 := by norm_cast
  rw [hcast0]
  exact htrunc

/-- Cast row-combination prefix-span witness over the cast input rows. Under
the zero-tail hypothesis, the cast of an integer row combination lies in the
prefix span of the first `k.val + 1` cast input rows, with `prefixCoeffsCast c k`
as the explicit witness. -/
private theorem prefixSpan_castIntMatrix
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    GramSchmidt.prefixSpan (castIntMatrix b) k.val k.isLt
      (Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b)) :=
  ⟨prefixCoeffsCast c k, (cast_vecMul_eq b c k hzero).symm⟩

/-- Transport of `prefixSpan_castIntMatrix` through
`basis_span`: the cast integer row combination also lies in the prefix span of
the first `k.val + 1` Gram-Schmidt basis rows. -/
theorem prefixSpan_basis_of_vecMul
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    GramSchmidt.prefixSpan (basis b) k.val k.isLt
      (Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b)) :=
  (basis_span b k.val k.isLt _).mpr
    (prefixSpan_castIntMatrix b c k hzero)

/-- Package the prefix-span witness together with the recovered top
Gram-Schmidt coordinate for a lattice row combination whose integer
coefficients vanish above `k`. -/
theorem prefixSpan_basis_and_coeffs_apply_eq_of_vecMul
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    GramSchmidt.prefixSpan (basis b) k.val k.isLt
        (Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b)) ∧
      (Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (coeffs b))[k] = (c[k] : Rat) :=
  ⟨prefixSpan_basis_of_vecMul b c k hzero,
    vecMul_coeffs_apply_eq_of_zero_above b c k hzero⟩

/-- The coefficient matrix reconstructs the cast integer input rows from the
Gram-Schmidt basis rows: `coeffs b * basis b` collapses to the cast input
`castIntMatrix b`. -/
@[simp, grind =] theorem coeffs_mul_basis_eq_castIntMatrix (b : Matrix Int n m) :
    coeffs b * basis b = castIntMatrix b := by
  apply Hex.Matrix.ext
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  have hdec := basis_decomposition b i hi
  have hentry :
      ((basis b).row ii)[jj] +
        (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] =
      ((castIntMatrix b).row ii)[jj] := by
    have hdecj := congrArg (fun v : Vector Rat m => v[jj]) hdec
    simpa [castIntMatrix, Matrix.row, Vector.getElem_add, Hex.Matrix.getRow, Fin.getElem_fin] using hdecj.symm
  show (coeffs b * basis b)[ii][jj] = (castIntMatrix b)[ii][jj]
  rw [Matrix.getElem_mul]
  unfold Vector.dotProduct
  let f : Fin n → Rat := fun k => ((coeffs b).row ii)[k] * ((basis b).col jj)[k]
  have hzero : ∀ k : Fin n, i < k.val → f k = 0 := by
    intro k hk
    have hcoeff :
        GramSchmidt.entry (coeffs b) ii k = 0 :=
      coeffs_upper b i k.val hi k.isLt hk
    change ((coeffs b).row ii)[k] * ((basis b).col jj)[k] = 0
    rw [show ((coeffs b).row ii)[k] = 0 from hcoeff]
    grind
  have htrunc := foldl_finRange_eq_prefix_of_zero_above ii f hzero
  change (List.finRange n).foldl (fun acc k => acc + f k) 0 =
    (castIntMatrix b)[ii][jj]
  rw [htrunc, List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  have hprefix :
      (List.finRange i).foldl
        (fun acc (x : Fin i) =>
          acc + f ⟨(Fin.castSucc x).val,
            Nat.lt_of_lt_of_le (Fin.castSucc x).isLt (Nat.succ_le_of_lt hi)⟩) 0 =
      (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] := by
    unfold GramSchmidt.prefixCombination GramSchmidt.entry
    let lift : Fin i → Fin n := fun x => ⟨x.val, Nat.lt_trans x.isLt hi⟩
    have hfold :
        ∀ xs : List (Fin i), ∀ accR : Rat, ∀ accV : Vector Rat m,
          accR = accV[jj] →
          xs.foldl
              (fun acc (x : Fin i) =>
                acc + f ⟨(Fin.castSucc x).val,
                  Nat.lt_of_lt_of_le (Fin.castSucc x).isLt (Nat.succ_le_of_lt hi)⟩)
              accR =
            (xs.foldl
              (fun acc (x : Fin i) =>
                acc + GramSchmidt.entry (coeffs b) ii (lift x) • (basis b).row (lift x))
              accV)[jj] := by
      intro xs
      induction xs with
      | nil =>
          intro accR accV hacc
          simp [hacc]
      | cons x xs ih =>
          intro accR accV hacc
          simp only [List.foldl_cons]
          apply ih
          have hstep :
              (accV + GramSchmidt.entry (coeffs b) ii (lift x) •
                  (basis b).row (lift x))[jj] =
                accV[jj] + GramSchmidt.entry (coeffs b) ii (lift x) *
                  ((basis b).row (lift x))[jj] := by
            change (accV + GramSchmidt.entry (coeffs b) ii (lift x) •
                (basis b).row (lift x))[jj.val]'jj.isLt =
              accV[jj.val]'jj.isLt + GramSchmidt.entry (coeffs b) ii (lift x) *
                ((basis b).row (lift x))[jj.val]'jj.isLt
            rw [Vector.getElem_add, Vector.getElem_smul]
            change accV[jj.val]'jj.isLt +
                GramSchmidt.entry (coeffs b) ii (lift x) *
                  ((basis b).row (lift x))[jj.val]'jj.isLt =
              accV[jj.val]'jj.isLt + GramSchmidt.entry (coeffs b) ii (lift x) *
                ((basis b).row (lift x))[jj.val]'jj.isLt
            rfl
          rw [hstep]
          simp [f, lift, GramSchmidt.entry, Matrix.row, Matrix.col, hacc, Hex.Matrix.getRow, Fin.getElem_fin]
    exact hfold (List.finRange i) 0 0 (by simp)
  rw [hprefix]
  have hdiag :
      ((coeffs b).row ii)[ii] = 1 := by
    exact coeffs_diag b i hi
  change (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] +
      ((coeffs b).row ii)[ii] * ((basis b).col jj)[ii] =
    (castIntMatrix b)[ii][jj]
  rw [hdiag]
  simp [Matrix.col]
  have hentry' :
      (basis b)[ii][jj] + (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] =
        (castIntMatrix b)[ii][jj] := by
    simpa [Matrix.row] using hentry
  change (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] +
      (basis b)[ii][jj] = (castIntMatrix b)[ii][jj]
  rw [← hentry']
  exact Lean.Grind.Semiring.add_comm _ _

/-- Integer row combinations reconstruct through the Gram-Schmidt basis after
first combining the Gram-Schmidt coefficient rows. -/
theorem vecMul_basis_coeffs_reconstruction
    (b : Matrix Int n m) (c : Vector Int n) :
    Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b) =
      Matrix.vecMul (Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (coeffs b)) (basis b) := by
  have hcoeff : coeffs b * basis b = castIntMatrix b :=
    coeffs_mul_basis_eq_castIntMatrix b
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  change (Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b))[jj] =
    (Matrix.vecMul (Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (coeffs b)) (basis b))[jj]
  have hmap :
      (Vector.map (fun x : Int => (x : Rat)) (Matrix.vecMul c b))[jj] =
        ((Matrix.vecMul c b)[jj] : Rat) :=
    Vector.getElem_map _ _
  rw [hmap, vecMul_int_getElem b c jj]
  rw [foldl_int_dot_cast (List.finRange n)
    (fun i : Fin n => b[i][jj]) (fun i : Fin n => c[i]) 0]
  have hleft :
      (List.finRange n).foldl
        (fun acc i => acc + ((b[i][jj] : Int) : Rat) *
          ((c[i] : Int) : Rat)) ((0 : Int) : Rat) =
      (Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (castIntMatrix b))[jj] := by
    rw [show ((0 : Int) : Rat) = 0 by norm_cast]
    show _ = (Matrix.transpose (castIntMatrix b) *
        Vector.map (fun x : Int => (x : Rat)) c)[jj]
    rw [Matrix.getElem_mulVec]
    simp [Vector.dotProduct, Matrix.row, Matrix.transpose,
      Matrix.col, castIntMatrix, Hex.Matrix.getRow, Fin.getElem_fin]
  rw [hleft, ← hcoeff]
  change ((Matrix.transpose (coeffs b * basis b)) *
      Vector.map (fun x : Int => (x : Rat)) c)[jj] =
    (Matrix.transpose (basis b) *
      (Matrix.transpose (coeffs b) *
        Vector.map (fun x : Int => (x : Rat)) c))[jj]
  rw [Matrix.transpose_mul_of_mul_comm, Matrix.mul_assoc_vec]

private theorem exists_highest_nonzero_coeff_in_list
    (c : Vector Int n) (xs : List (Fin n))
    (hne : ∃ i : Fin n, i ∈ xs ∧ c[i] ≠ 0) :
    ∃ k : Fin n, k ∈ xs ∧ c[k] ≠ 0 ∧
      ∀ j : Fin n, j ∈ xs → k.val < j.val → c[j] = 0 := by
  induction xs with
  | nil =>
      rcases hne with ⟨_, hi, _⟩
      cases hi
  | cons x xs ih =>
      by_cases htail : ∃ i : Fin n, i ∈ xs ∧ c[i] ≠ 0
      · rcases ih htail with ⟨k, hk_mem, hck, hmax⟩
        by_cases hx : c[x] ≠ 0
        · by_cases hkx : k.val < x.val
          · refine ⟨x, by simp, hx, ?_⟩
            intro j hj hxj
            simp at hj
            rcases hj with rfl | hjtail
            · omega
            · have hkj : k.val < j.val := by omega
              exact hmax j hjtail hkj
          · refine ⟨k, by simp [hk_mem], hck, ?_⟩
            intro j hj hkj
            simp at hj
            rcases hj with rfl | hjtail
            · exact False.elim (hkx hkj)
            · exact hmax j hjtail hkj
        · refine ⟨k, by simp [hk_mem], hck, ?_⟩
          intro j hj hkj
          simp at hj
          rcases hj with rfl | hjtail
          · by_cases hx0 : c[j] = 0
            · exact hx0
            · exact False.elim (hx hx0)
          · exact hmax j hjtail hkj
      · have hx : c[x] ≠ 0 := by
          rcases hne with ⟨i, hi, hci⟩
          simp at hi
          rcases hi with rfl | hitail
          · exact hci
          · exact False.elim (htail ⟨i, hitail, hci⟩)
        refine ⟨x, by simp, hx, ?_⟩
        intro j hj hxj
        simp at hj
        rcases hj with rfl | hjtail
        · omega
        · by_cases hj0 : c[j] = 0
          · exact hj0
          · exact False.elim (htail ⟨j, hjtail, hj0⟩)

private theorem exists_highest_nonzero_coeff
    (c : Vector Int n) (hne : ∃ i : Fin n, c[i] ≠ 0) :
    ∃ k : Fin n, c[k] ≠ 0 ∧ ∀ j : Fin n, k.val < j.val → c[j] = 0 := by
  have hmem : ∃ i : Fin n, i ∈ List.finRange n ∧ c[i] ≠ 0 := by
    rcases hne with ⟨i, hi⟩
    exact ⟨i, List.mem_finRange i, hi⟩
  rcases exists_highest_nonzero_coeff_in_list c (List.finRange n) hmem with
    ⟨k, _hk_mem, hck, hmax⟩
  exact ⟨k, hck, fun j hj => hmax j (List.mem_finRange j) hj⟩

/-- Casting commutes with the squared norm: the rational squared norm of an
integer vector mapped into `ℚ` equals its integer squared norm cast to `ℚ`. This
transfers norm facts proved over `ℤ` into the rational Gram-Schmidt setting. As
a `simp` rule it pushes the cast outward, putting the rational squared norm in
the normal form `((normSq v : Int) : Rat)`. -/
@[simp, grind =] theorem normSq_map_intCast (v : Vector Int m) :
    (Vector.map (fun x : Int => (x : Rat)) v).normSq =
      ((v.normSq : Int) : Rat) := by
  simpa [Vector.normSq, Vector.dotProduct]
    using (foldl_int_dot_cast (List.finRange m)
      (fun i : Fin m => v[i]) (fun i : Fin m => v[i]) 0).symm

/-- Every nonzero lattice vector is at least as long as some basis row: there is
an index `i` with `normSq ((basis b).row i) ≤ normSq v` (compared in `ℚ`). This
lower-bounds an arbitrary lattice vector by an explicit basis quantity, the
starting point for relating short lattice vectors to the input basis. -/
theorem normSq_latticeVec_ge_min_basis_normSq
    (b : Matrix Int n m) (_hli : independent b)
    (v : Vector Int m) (hv : memLattice b v) (hv' : v ≠ 0) :
    ∃ i : Fin n,
      ((basis b).row i).normSq ≤ ((v.normSq : Int) : Rat) := by
  rcases hv with ⟨c, hcv⟩
  have hc_nonzero : ∃ i : Fin n, c[i] ≠ 0 := by
    by_cases h : ∃ i : Fin n, c[i] ≠ 0
    · exact h
    · have hc_zero : c = 0 := by
        apply Vector.ext
        intro i hi
        let ii : Fin n := ⟨i, hi⟩
        by_cases hci : c[ii] = 0
        · simpa [ii] using hci
        · exact False.elim (h ⟨ii, hci⟩)
      have hv_zero : v = 0 := by
        rw [← hcv, hc_zero]
        simp [Matrix.vecMul]
      exact False.elim (hv' hv_zero)
  rcases exists_highest_nonzero_coeff c hc_nonzero with ⟨k, hck, hzero_above⟩
  let d : Vector Rat n :=
    Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (coeffs b)
  have hcoeff_sq : (1 : Rat) ≤ d[k] * d[k] := by
    have htop :
        d[k] = (c[k] : Rat) := by
      dsimp [d]
      exact vecMul_coeffs_apply_eq_of_zero_above b c k hzero_above
    rw [htop]
    exact GramSchmidt.one_le_intCast_mul_self_of_ne_zero c[k] hck
  refine ⟨k, ?_⟩
  have horth : ∀ i j : Fin n, i ≠ j →
      ((basis b).row i).dotProduct ((basis b).row j) = 0 := by
    intro i j hij
    exact basis_orthogonal b i.val j.val i.isLt j.isLt (by
      intro hval
      exact hij (Fin.ext hval))
  have hle :
      ((basis b).row k).normSq ≤
        (Matrix.vecMul d (basis b)).normSq :=
    GramSchmidt.vecMul_normSq_ge_of_orthogonal_coeff_sq_ge_one
      (rows := basis b) (coeffs := d) (k := k) horth hcoeff_sq
  have hrec :
      Vector.map (fun x : Int => (x : Rat)) v =
        Matrix.vecMul d (basis b) := by
    rw [← hcv]
    dsimp [d]
    exact vecMul_basis_coeffs_reconstruction b c
  have hnorm :
      (Matrix.vecMul d (basis b)).normSq =
        ((v.normSq : Int) : Rat) := by
    rw [← hrec, normSq_map_intCast]
  rw [← hnorm]
  exact hle

/-- Strengthening of `normSq_latticeVec_ge_min_basis_normSq` that exposes the
highest nonzero coefficient index `k` of a nonzero lattice vector together with
the integer coefficients that witness it, the fact that those coefficients
vanish above `k`, and the matching basis-row length bound `‖b*_k‖² ≤ ‖v‖²`.

This is the survivor-span entry point: the vanishing-above-`k` data localizes
`v` to the prefix `b_0 … b_k`, and the length bound feeds a Gram-Schmidt cut
test on the top index `k`. -/
theorem exists_top_index_normSq_le_of_memLattice
    (b : Matrix Int n m) (_hli : independent b)
    (v : Vector Int m) (hv : memLattice b v) (hv' : v ≠ 0) :
    ∃ (k : Fin n) (c : Vector Int n),
      Matrix.vecMul c b = v ∧
      c[k] ≠ 0 ∧
      (∀ j : Fin n, k.val < j.val → c[j] = 0) ∧
      ((basis b).row k).normSq ≤ ((v.normSq : Int) : Rat) := by
  rcases hv with ⟨c, hcv⟩
  have hc_nonzero : ∃ i : Fin n, c[i] ≠ 0 := by
    by_cases h : ∃ i : Fin n, c[i] ≠ 0
    · exact h
    · have hc_zero : c = 0 := by
        apply Vector.ext
        intro i hi
        let ii : Fin n := ⟨i, hi⟩
        by_cases hci : c[ii] = 0
        · simpa [ii] using hci
        · exact False.elim (h ⟨ii, hci⟩)
      have hv_zero : v = 0 := by
        rw [← hcv, hc_zero]
        simp [Matrix.vecMul]
      exact False.elim (hv' hv_zero)
  rcases exists_highest_nonzero_coeff c hc_nonzero with ⟨k, hck, hzero_above⟩
  refine ⟨k, c, hcv, hck, hzero_above, ?_⟩
  let d : Vector Rat n :=
    Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (coeffs b)
  have hcoeff_sq : (1 : Rat) ≤ d[k] * d[k] := by
    have htop : d[k] = (c[k] : Rat) := by
      dsimp [d]
      exact vecMul_coeffs_apply_eq_of_zero_above b c k hzero_above
    rw [htop]
    exact GramSchmidt.one_le_intCast_mul_self_of_ne_zero c[k] hck
  have horth : ∀ i j : Fin n, i ≠ j →
      ((basis b).row i).dotProduct ((basis b).row j) = 0 := by
    intro i j hij
    exact basis_orthogonal b i.val j.val i.isLt j.isLt (by
      intro hval
      exact hij (Fin.ext hval))
  have hle :
      ((basis b).row k).normSq ≤
        (Matrix.vecMul d (basis b)).normSq :=
    GramSchmidt.vecMul_normSq_ge_of_orthogonal_coeff_sq_ge_one
      (rows := basis b) (coeffs := d) (k := k) horth hcoeff_sq
  have hrec :
      Vector.map (fun x : Int => (x : Rat)) v =
        Matrix.vecMul d (basis b) := by
    rw [← hcv]
    dsimp [d]
    exact vecMul_basis_coeffs_reconstruction b c
  have hnorm :
      (Matrix.vecMul d (basis b)).normSq =
        ((v.normSq : Int) : Rat) := by
    rw [← hrec, normSq_map_intCast]
  rw [← hnorm]
  exact hle

/-! ### Dot-product symmetry support -/

private theorem foldl_dot_comm_int {n' : Nat} (xs : List (Fin n'))
    (u v : Vector Int n') (accU accV : Int) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind

/-- The dot product of integer vectors is commutative. -/
private theorem dot_comm_int {n' : Nat} (u v : Vector Int n') :
    u.dotProduct v = v.dotProduct u := by
  simpa [Vector.dotProduct] using
    foldl_dot_comm_int (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

/-- The integer Gram matrix is symmetric: each entry equals the entry at the
swapped index. Consumed by the no-pivot Bareiss symmetry/transpose argument for
bordered minors of `gramMatrix b`. -/
private theorem gramMatrix_symm (b : Matrix Int n m) (a c : Fin n) :
    (Matrix.gramMatrix b)[a][c] = (Matrix.gramMatrix b)[c][a] := by
  show (Matrix.ofFn fun i j => Vector.dotProduct
        (Matrix.row b i) (Matrix.row b j))[a][c]
    = (Matrix.ofFn fun i j => Vector.dotProduct
        (Matrix.row b i) (Matrix.row b j))[c][a]
  simp [Matrix.ofFn, Vector.getElem_ofFn]
  exact dot_comm_int _ _

/-- The Cramer determinant matrix for the scaled Gram-Schmidt coefficient
`(i, j)` (with `j < i`) is the bordered minor of `gramMatrix b` at level `j`
with the border row index taken to be `j` and the border column index taken
to be `i`. This is the definitional equation between
`GramSchmidt.scaledCoeffMatrix` and the bordered-minor machinery in
`HexBareiss.Bareiss`. -/
theorem scaledCoeffMatrix_eq_borderedMinor
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.scaledCoeffMatrix b i j hji =
      Matrix.borderedMinor (Matrix.gramMatrix b) j.val
        (Nat.lt_trans hji i.isLt)
        ⟨j.val, Nat.lt_trans hji i.isLt⟩ i := by
  apply Hex.Matrix.ext
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  let pp : Fin (j.val + 1) := ⟨r, hr⟩
  let cc : Fin (j.val + 1) := ⟨c, hc⟩
  show (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
    (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
        (Nat.lt_trans hji i.isLt)
        ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc]
  -- Case split on whether the column index is the border (= j.val) or interior.
  by_cases hcj : cc.val < j.val
  · -- Interior column: both sides are `gramMatrix[r'][c']` with the
    -- lifted-to-`Fin n` indices, since the bordered-minor `r` lookup falls into
    -- the lt branch when `pp.val < j.val` and into the border (= j) row when
    -- `pp.val = j.val`. Splitting on the row case mirrors the bordered minor.
    by_cases hrj : pp.val < j.val
    · have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Vector.dotProduct
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩) := by
        have hcc_ne : cc.val ≠ j.val := Nat.ne_of_lt hcj
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn, GramSchmidt.liftFinLE, hcc_ne,
          Hex.Matrix.getRow, Fin.getElem_fin]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[
            (⟨pp.val, Nat.lt_trans hrj (Nat.lt_trans hji i.isLt)⟩ : Fin n)][
            (⟨cc.val, Nat.lt_trans hcj (Nat.lt_trans hji i.isLt)⟩ : Fin n)] := by
        rw [Matrix.borderedMinor_entry_lt_lt (Matrix.gramMatrix b) j.val
          (Nat.lt_trans hji i.isLt) ⟨j.val, Nat.lt_trans hji i.isLt⟩ i pp cc hrj hcj]
        simp [Hex.Matrix.getElem_pair_eq_nested]
      rw [h_sc, h_bm]
      simp [Matrix.gramMatrix, Matrix.ofFn, Vector.getElem_ofFn, Vector.dotProduct,
        Hex.Matrix.getRow, Fin.getElem_fin]
    · -- pp.val = j.val (since not < j.val and bounded by j.val + 1).
      have hpr : pp.val = j.val :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp pp.isLt) (Nat.le_of_not_lt hrj)
      have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Vector.dotProduct
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩) := by
        have hcc_ne : cc.val ≠ j.val := Nat.ne_of_lt hcj
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn, GramSchmidt.liftFinLE, hcc_ne,
          Hex.Matrix.getRow, Fin.getElem_fin]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[(⟨j.val, Nat.lt_trans hji i.isLt⟩ : Fin n)][
            (⟨cc.val, Nat.lt_trans hcj (Nat.lt_trans hji i.isLt)⟩ : Fin n)] := by
        have hpr_not : ¬ pp.val < j.val := Nat.not_lt.mpr (Nat.le_of_eq hpr.symm)
        simp [Matrix.borderedMinor, Matrix.ofFn, Vector.getElem_ofFn, hpr_not, hcj]
      rw [h_sc, h_bm, Matrix.getElem_gramMatrix]
      have hrow : (⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
          (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩ : Fin n)
          = ⟨j.val, Nat.lt_trans hji i.isLt⟩ := Fin.ext hpr
      rw [hrow]
  · -- Border column: cc.val = j.val.
    have hcj_eq : cc.val = j.val :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp cc.isLt) (Nat.le_of_not_lt hcj)
    by_cases hrj : pp.val < j.val
    · have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Vector.dotProduct
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b i) := by
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn, GramSchmidt.liftFinLE, hcj_eq]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[
            (⟨pp.val, Nat.lt_trans hrj (Nat.lt_trans hji i.isLt)⟩ : Fin n)][i] := by
        simp [Matrix.borderedMinor, Matrix.ofFn, Vector.getElem_ofFn, hrj, hcj]
      rw [h_sc, h_bm]
      simp [Matrix.gramMatrix, Matrix.ofFn, Vector.getElem_ofFn, Vector.dotProduct,
        Hex.Matrix.getRow, Fin.getElem_fin]
    · -- pp.val = j.val and cc.val = j.val: corner case.
      have hpr_eq : pp.val = j.val :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp pp.isLt) (Nat.le_of_not_lt hrj)
      have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Vector.dotProduct
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b i) := by
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn, GramSchmidt.liftFinLE, hcj_eq]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[(⟨j.val, Nat.lt_trans hji i.isLt⟩ : Fin n)][i] := by
        have hpr_not : ¬ pp.val < j.val := hrj
        simp [Matrix.borderedMinor, Matrix.ofFn, Vector.getElem_ofFn, hpr_not, hcj]
      rw [h_sc, h_bm, Matrix.getElem_gramMatrix]
      have hrow : (⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
          (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩ : Fin n)
          = ⟨j.val, Nat.lt_trans hji i.isLt⟩ := Fin.ext hpr_eq
      rw [hrow]

/-- The no-pivot Bareiss-style trailing value on `scaledCoeffMatrix b i j hji`
agrees with the value on the bordered minor of `gramMatrix b` whose border
row/column are swapped. The proof composes the symmetry of `gramMatrix` (via
`noPivotLoop_borderedMinor_swap_at_trailing`) with the definitional identity
`scaledCoeffMatrix_eq_borderedMinor`. -/
private theorem noPivotLoop_scaledCoeffMatrix_eq
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (GramSchmidt.scaledCoeffMatrix b i j hji))).matrix[
          Fin.last j.val][Fin.last j.val] =
    (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt) i j))).matrix[
          Fin.last j.val][Fin.last j.val] := by
  rw [scaledCoeffMatrix_eq_borderedMinor b i j hji]
  exact noPivotLoop_borderedMinor_swap_at_trailing
    (Matrix.gramMatrix b) (gramMatrix_symm (b := b))
    j.val (Nat.lt_trans hji i.isLt)
    ⟨j.val, Nat.lt_trans hji i.isLt⟩ i
    (Nat.le_refl _) (Nat.le_of_lt hji)

/-- Non-singular top-level composite: when the no-pivot Bareiss pass over the
full Gram matrix has not recorded a singular step before reaching column `j`,
the executable scaled-coefficient array entry below the diagonal at `(i, j)`
matches the trailing entry of the no-pivot Bareiss-style loop on the
corresponding Cramer determinant matrix `scaledCoeffMatrix b i j hji`. This
composes `scaledCoeffArrayLoop_lower_matches_target_column` (from #4103),
`noPivotLoop_full_eq_borderedMinor_at_trailing` (from #4028), and the
symmetry/transpose equation `noPivotLoop_scaledCoeffMatrix_eq`. -/
theorem scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    getArrayEntry (scaledCoeffRows b) i.val j.val =
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (GramSchmidt.scaledCoeffMatrix b i j hji))).matrix[
        Fin.last j.val][Fin.last j.val] := by
  -- Step 1: top-level state-level invariant via the non-singular target-column lemma.
  have h_target_nonsing :
      (Matrix.noPivotLoop (j.val - 0)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
    simpa using h_nonsing
  have h_lower :=
    scaledCoeffArrayLoop_lower_matches_target_column
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (rowsToMatrix_gramRows b) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      n i j (Nat.zero_le _) hji
      (by have := i.isLt; omega) h_target_nonsing
  have h_state_level :
      getArrayEntry (scaledCoeffRows b) i.val j.val =
        (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] := by
    show getArrayEntry
        (scaledCoeffArrayLoop n n
            { step := 0, matrix := gramRows b, coeffs := zeroRows n,
              prevPivot := 1 }).coeffs i.val j.val = _
    have h_step_eq : (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step = 0 := rfl
    have h_sub : j.val - (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step = j.val := by
      rw [h_step_eq]; omega
    rw [h_lower, h_sub]
  rw [h_state_level]
  -- Step 2: bordered-minor sync at (row=i, col=j).
  have h_bm :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing (Matrix.gramMatrix b) j.val
      (Nat.lt_trans hji i.isLt) i j (Nat.le_of_lt hji) (Nat.le_refl _)).1
  rw [h_bm]
  -- Step 3: symmetry/transpose equation to `scaledCoeffMatrix`.
  exact
    (noPivotLoop_scaledCoeffMatrix_eq b i j hji).symm

/-- Singular dual of `scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix`,
phrased on the Bareiss-array path. When the no-pivot Bareiss pass over the
full Gram matrix records an early singular step before reaching column `j`,
the column-major array loop never writes the target column and the entry at
`(i, j)` below the diagonal is left at its initial zero. -/
private theorem scaledCoeffRows_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    getArrayEntry (scaledCoeffRows b) i.val j.val = 0 := by
  have h_target_sing :
      (Matrix.noPivotLoop (j.val - 0)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s := by
    simpa using h_sing
  have h_zero :=
    scaledCoeffArrayLoop_lower_zero
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (rowsToMatrix_gramRows b) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      (by
        intro r c _hsc _hcr
        exact getArrayEntry_zeroRows n r.val c.val)
      rfl
      n i j (Nat.zero_le _) hji
      (by have := i.isLt; omega) s h_target_sing
  show getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i.val j.val = 0
  exact h_zero

/-- Strict-lower non-singular Bareiss-side bridge: state-level form of
`scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix` extracted at the
`gramMatrix` matrix-level, before the bordered-minor/transpose closure. When
the no-pivot Bareiss pass over the full Gram matrix has not recorded a
singular step before reaching column `j`, the executable scaled-coefficient
array entry below the diagonal at `(i, j)` matches the matrix-level diagonal
of `noPivotLoop` at fuel `j` on `gramMatrix b`. -/
private theorem scaledCoeffRows_lower_eq
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    getArrayEntry (scaledCoeffRows b) i.val j.val =
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] := by
  have h_target_nonsing :
      (Matrix.noPivotLoop (j.val - 0)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
    simpa using h_nonsing
  have h_lower :=
    scaledCoeffArrayLoop_lower_matches_target_column
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (rowsToMatrix_gramRows b) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      n i j (Nat.zero_le _) hji
      (by have := i.isLt; omega) h_target_nonsing
  show getArrayEntry
      (scaledCoeffArrayLoop n n
          { step := 0, matrix := gramRows b, coeffs := zeroRows n,
            prevPivot := 1 }).coeffs i.val j.val = _
  have h_step_eq : (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step = 0 := rfl
  have h_sub :
      j.val - (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step = j.val := by
    rw [h_step_eq]; omega
  rw [h_lower, h_sub]

/-- Diagonal non-singular Bareiss-side bridge. When the no-pivot Bareiss pass
over the full Gram matrix has not recorded a singular step before reaching
column `j`, the executable scaled-coefficient array entry on the diagonal at
`(j, j)` matches the matrix-level diagonal of `noPivotLoop` at fuel `j` on
`gramMatrix b`. The proof composes `scaledCoeffArrayLoop_diag_matches` at
fuel `n` with `Matrix.noPivotLoop_diag_of_le_step` plus
`noPivotLoop_step_eq_add_of_singularStep_none` to bridge between the
full-trajectory diagonal at `j` and the truncated-trajectory diagonal at the
same row. -/
private theorem scaledCoeffRows_diag_eq_noPivotLoop_gramMatrix_of_no_singular
    (b : Matrix Int n m) (j : Fin n)
    (h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    getArrayEntry (scaledCoeffRows b) j.val j.val =
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[j][j] := by
  let init : Matrix.BareissState n :=
    Matrix.noPivotInitialState (Matrix.gramMatrix b)
  let prefAtJ : Matrix.BareissState n := Matrix.noPivotLoop j.val init
  have h_step_j : prefAtJ.step = j.val := by
    have h_room : init.step + j.val + 1 ≤ n := by
      have := j.isLt
      simp [init, Matrix.noPivotInitialState]
      omega
    have h := noPivotLoop_step_eq_add_of_singularStep_none j.val init rfl h_room h_nonsing
    simpa [prefAtJ, init, Matrix.noPivotInitialState] using h
  have h_factor :
      Matrix.noPivotLoop n init = Matrix.noPivotLoop (n - j.val) prefAtJ := by
    have h_add := Matrix.noPivotLoop_add j.val (n - j.val) init
    have h_split : j.val + (n - j.val) = n := by have := j.isLt; omega
    simpa [prefAtJ, h_split] using h_add
  have h_diag_bridge :
      (Matrix.noPivotLoop n init).matrix[j][j] = prefAtJ.matrix[j][j] := by
    rw [h_factor]
    have h_le : j.val ≤ prefAtJ.step := by rw [h_step_j]; exact Nat.le_refl _
    exact Matrix.noPivotLoop_diag_of_le_step (n - j.val) prefAtJ j h_le
  have hdiag :=
    scaledCoeffArrayLoop_diag_matches
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := init)
      (by rfl) (rowsToMatrix_gramRows b) (by rfl) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      (by
        intro k hks _hkn
        simp [init, Matrix.noPivotInitialState] at hks)
      (by
        intro k _hks _hkn
        exact getArrayEntry_zeroRows n k k)
      n j (by
        left
        show j.val < (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + n
        simp [Matrix.noPivotInitialState, j.isLt])
  show getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs j.val j.val =
    prefAtJ.matrix[j][j]
  rcases hdiag with ⟨_h_sing_n, h_eq⟩ | ⟨s, h_sing_n, h_cases⟩
  · -- Non-singular full trajectory: bridge directly.
    rw [h_eq]; exact h_diag_bridge
  · rcases h_cases with ⟨hsj, h_zero⟩ | ⟨hjs, h_eq⟩
    · -- Sub-case `s ≤ j.val`: by monotonicity `j.val ≤ s`, so `s = j.val`; then
      -- the singular_inv invariant gives `(noPivotLoop n init).matrix[j][j] = 0`,
      -- which combined with `h_diag_bridge` shows `prefAtJ.matrix[j][j] = 0`.
      have h_mono :
          prefAtJ.step ≤ (Matrix.noPivotLoop (n - j.val) prefAtJ).step :=
        noPivotLoop_step_monotone _ _
      have h_step_n_eq :
          (Matrix.noPivotLoop n init).step =
            (Matrix.noPivotLoop (n - j.val) prefAtJ).step :=
        congrArg Matrix.BareissState.step h_factor
      rcases noPivotLoop_singular_inv (n := n) n init rfl with h_none | ⟨k, h_k_sing, h_k_step, h_k_zero, _⟩
      · rw [h_sing_n] at h_none; nomatch h_none
      · have h_s_eq_k : s = k.val := by
          rw [h_k_sing] at h_sing_n
          injection h_sing_n with heq
          exact heq.symm
        have h_step_n_eq_s :
            (Matrix.noPivotLoop n init).step = s := by
          rw [h_k_step, h_s_eq_k]
        have h_j_le_s : j.val ≤ s := by
          have h_chain : prefAtJ.step ≤ (Matrix.noPivotLoop n init).step := by
            rw [h_step_n_eq]; exact h_mono
          rw [h_step_j, h_step_n_eq_s] at h_chain
          exact h_chain
        have h_s_eq_j : s = j.val := Nat.le_antisymm hsj h_j_le_s
        have h_idx_eq : k = j := by
          apply Fin.ext
          rw [← h_s_eq_k]; exact h_s_eq_j
        have h_matrix_n_jj :
            (Matrix.noPivotLoop n init).matrix[j][j] = 0 := by
          have h_lift := congrArg
            (fun (idx : Fin n) => (Matrix.noPivotLoop n init).matrix[idx][idx])
            h_idx_eq
          exact h_lift.symm.trans h_k_zero
        have h_prefAtJ_jj : prefAtJ.matrix[j][j] = 0 := by
          rw [← h_diag_bridge]; exact h_matrix_n_jj
        rw [h_zero, h_prefAtJ_jj]
    · -- Sub-case `j.val < s`: same bridge as the non-singular case.
      rw [h_eq]; exact h_diag_bridge

/-- Diagonal singular Bareiss-side bridge. When the no-pivot Bareiss pass
over the full Gram matrix records a singular step strictly before column `j`,
the executable scaled-coefficient array entry on the diagonal at `(j, j)` is
zero. The proof composes `scaledCoeffArrayLoop_diag_matches` at fuel `n` with
the persistence lemma `noPivotLoop_singularStep`. -/
private theorem scaledCoeffRows_diag_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (j : Fin n)
    (s : Nat) (hsj : s < j.val)
    (h_sing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    getArrayEntry (scaledCoeffRows b) j.val j.val = 0 := by
  let init : Matrix.BareissState n :=
    Matrix.noPivotInitialState (Matrix.gramMatrix b)
  -- Lift singularity from prefix `j` to full `n` via `prefix_singular`.
  have h_persist_split :
      Matrix.noPivotLoop (j.val + (n - j.val)) init =
        Matrix.noPivotLoop n init := by
    have h_split : j.val + (n - j.val) = n := by have := j.isLt; omega
    rw [h_split]
  have h_sing_full' :
      (Matrix.noPivotLoop (j.val + (n - j.val)) init).singularStep = some s :=
    noPivotLoop_singularStep j.val (n - j.val) init rfl h_sing
  have h_sing_full : (Matrix.noPivotLoop n init).singularStep = some s := by
    rw [← h_persist_split]; exact h_sing_full'
  have hdiag :=
    scaledCoeffArrayLoop_diag_matches
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := init)
      (by rfl) (rowsToMatrix_gramRows b) (by rfl) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      (by
        intro k hks _hkn
        simp [init, Matrix.noPivotInitialState] at hks)
      (by
        intro k _hks _hkn
        exact getArrayEntry_zeroRows n k k)
      n j (by
        left
        show j.val < (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + n
        simp [Matrix.noPivotInitialState, j.isLt])
  show getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs j.val j.val = 0
  rcases hdiag with ⟨h_none, _⟩ | ⟨s', h_sing_n, h_cases⟩
  · rw [h_sing_full] at h_none; nomatch h_none
  · have h_s_eq : s' = s := by
      rw [h_sing_full] at h_sing_n
      injection h_sing_n with heq
      exact heq.symm
    have h_s'_le_j : s' ≤ j.val := by rw [h_s_eq]; omega
    rcases h_cases with ⟨_hsj', h_zero⟩ | ⟨hjs', _h_eq⟩
    · exact h_zero
    · -- j.val < s' contradicts s' ≤ j.val
      omega

/-- On a non-singular initial Gram trajectory, the diagonal pivot at step `q`
is nonzero whenever `q + 1` iterations stay non-singular. The (`q + 1`)-th
iteration would otherwise record a singular step at `q`. -/
private theorem noPivotLoop_initial_gram_diag_ne_zero
    (b : Matrix Int n m) (p q : Nat) (hq : q < p) (hpn : p < n)
    (h_nonsing :
      (Matrix.noPivotLoop p
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.noPivotLoop q
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
      (⟨q, Nat.lt_trans hq hpn⟩ : Fin n)][
      (⟨q, Nat.lt_trans hq hpn⟩ : Fin n)] ≠ 0 := by
  intro h_zero
  -- The (q+1)-prefix is also non-singular: split p = (q+1) + (p - q - 1).
  let state₀ : Matrix.BareissState n := Matrix.noPivotInitialState (Matrix.gramMatrix b)
  have h_split : p = (q + 1) + (p - q - 1) := by omega
  have h_prefix_succ_none :
      (Matrix.noPivotLoop (q + 1) state₀).singularStep = none := by
    apply noPivotLoop_prefix_none_of_final_none (q + 1) (p - q - 1) state₀
      (by simp [state₀, Matrix.noPivotInitialState])
    rw [← h_split]; exact h_nonsing
  -- At step q (where step = q under non-singularity of q-prefix), the q-th
  -- diagonal is the pivot for the (q+1)-th iteration.
  have h_prefix_none :
      (Matrix.noPivotLoop q state₀).singularStep = none :=
    noPivotLoop_prefix_none_of_final_none q 1 state₀
      (by simp [state₀, Matrix.noPivotInitialState])
      (by rw [show q + 1 = q + 1 from rfl]; exact h_prefix_succ_none)
  have hqn : q < n := Nat.lt_trans hq hpn
  have h_step_q :
      (Matrix.noPivotLoop q state₀).step = q :=
    noPivotLoop_initial_gram_step_eq b q (by omega) h_prefix_none
  -- The (q+1)-th iteration: starting from state with step = q, matrix[q][q] = 0,
  -- it records singularStep := some q.
  have hDone : (Matrix.noPivotLoop q state₀).step + 1 < n := by
    rw [h_step_q]; omega
  have hp_at_step :
      (Matrix.noPivotLoop q state₀).matrix[
        (Matrix.noPivotLoop q state₀).step][
        (Matrix.noPivotLoop q state₀).step] = 0 := by
    have h_idx_eq :
        (⟨(Matrix.noPivotLoop q state₀).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)
          = ⟨q, hqn⟩ := Fin.ext h_step_q
    have h_lift := congrArg
      (fun (idx : Fin n) =>
        (Matrix.noPivotLoop q state₀).matrix[idx][idx])
      h_idx_eq
    -- h_lift : M[⟨step, _⟩][⟨step, _⟩] = M[⟨q, _⟩][⟨q, _⟩]
    change
      (Matrix.noPivotLoop q state₀).matrix[
        (⟨(Matrix.noPivotLoop q state₀).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨(Matrix.noPivotLoop q state₀).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0
    exact h_lift.trans h_zero
  -- Now noPivotLoop applied for 1 more fuel from the q-prefix records a singular
  -- step at q. But that contradicts the (q+1)-prefix non-singularity.
  have h_one_more :
      Matrix.noPivotLoop 1 (Matrix.noPivotLoop q state₀) =
        { (Matrix.noPivotLoop q state₀) with
          singularStep := some (Matrix.noPivotLoop q state₀).step } :=
    Matrix.noPivotLoop_singular_branch 0 _ hDone hp_at_step
  have h_q_plus_one :
      Matrix.noPivotLoop (q + 1) state₀ =
        Matrix.noPivotLoop 1 (Matrix.noPivotLoop q state₀) :=
    Matrix.noPivotLoop_add q 1 state₀
  rw [h_q_plus_one, h_one_more] at h_prefix_succ_none
  simp at h_prefix_succ_none

/-- Algebraic exact-division step used by the σ-chain correction successor:
if the Bareiss update numerator is divisible by the previous pivot, the σ-body
quotient subtracts the corresponding Bareiss quotient from `pivot * gram`. -/
private theorem exactDiv_bareissCorrection_succ_algebra
    (denom pivot gram entry row col : Int) (hdenom : denom ≠ 0)
    (hdiv : denom ∣ pivot * entry - row * col) :
    Matrix.exactDiv (pivot * (denom * gram - entry) + row * col) denom =
      pivot * gram - Matrix.exactDiv (pivot * entry - row * col) denom := by
  rcases hdiv with ⟨quot, hnum⟩
  have hquot :
      Matrix.exactDiv (pivot * entry - row * col) denom = quot := by
    refine exactDiv_eq_of_eq_mul_right hdenom ?_
    rw [hnum]
    grind
  rw [hquot]
  refine exactDiv_eq_of_eq_mul_right hdenom ?_
  have hrow : row * col = pivot * entry - denom * quot := by
    grind
  rw [hrow]
  grind

/-- Successor step for the σ-chain/Bareiss correction invariant.  Once the
row reads in the σ-chain body have already been rewritten to a Bareiss
trajectory, one body application advances the closed correction term from the
current step to the next one.  The caller supplies the one-step Bareiss quotient
for the next matrix entry. -/
private theorem schurSigma_noPivotCorrection_succ
    (denom pivot gram entry row col nextEntry : Int)
    (hdenom : denom ≠ 0)
    (h_step_dvd : denom ∣ pivot * entry - row * col)
    (h_next :
      nextEntry = Matrix.exactDiv (pivot * entry - row * col) denom) :
    Matrix.exactDiv (pivot * (denom * gram - entry) + row * col) denom =
      pivot * gram - nextEntry := by
  rw [h_next]
  exact exactDiv_bareissCorrection_succ_algebra
    denom pivot gram entry row col hdenom h_step_dvd

set_option maxHeartbeats 400000 in
/-- The σ-chain Bareiss correction invariant.  At step `q < p_out` of the
σ-update fold for position `(a, p_out)`, the cumulative fold value equals
the algebraic closed form `matrix_q[q][q] * gram - matrix_(q+1)[a][p_out]`.
Proved by induction on `q`. -/
private theorem schurSigma_foldl_eq
    {n m : Nat} (b : Matrix Int n m) (hquot : StepWitness b)
    (a p_out q : Nat) (hp_out_n : p_out < n) (han : a < n) (hpa : p_out ≤ a)
    (hq_lt_pout : q < p_out)
    (h_nonsing :
      (Matrix.noPivotLoop p_out
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (correspondence :
      ∀ l (hl : l ≤ q),
        getArrayEntry (scaledCoeffRowsSchur b) l l =
          (Matrix.noPivotLoop l
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
            (⟨l, Nat.lt_of_le_of_lt (Nat.le_trans hl (Nat.le_of_lt hq_lt_pout)) hp_out_n⟩
              : Fin n)][
            (⟨l, Nat.lt_of_le_of_lt (Nat.le_trans hl (Nat.le_of_lt hq_lt_pout)) hp_out_n⟩
              : Fin n)] ∧
        ∀ c (_hlc : l < c) (hcn : c < n),
          getArrayEntry (scaledCoeffRowsSchur b) c l =
            (Matrix.noPivotLoop l
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
              (⟨c, hcn⟩ : Fin n)][
              (⟨l, Nat.lt_of_le_of_lt (Nat.le_trans hl (Nat.le_of_lt hq_lt_pout)) hp_out_n⟩
                : Fin n)]) :
    (List.range' 1 q).foldl
        (fun σ p_iter =>
          Matrix.exactDiv
            (getArrayEntry (scaledCoeffRowsSchur b) p_iter p_iter * σ +
              getArrayEntry (scaledCoeffRowsSchur b) a p_iter *
              getArrayEntry (scaledCoeffRowsSchur b) p_out p_iter)
            (getArrayEntry (scaledCoeffRowsSchur b) (p_iter - 1) (p_iter - 1)))
        (getArrayEntry (scaledCoeffRowsSchur b) a 0 *
          getArrayEntry (scaledCoeffRowsSchur b) p_out 0) =
      (Matrix.noPivotLoop q
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
        (⟨q, Nat.lt_trans hq_lt_pout hp_out_n⟩ : Fin n)][
        (⟨q, Nat.lt_trans hq_lt_pout hp_out_n⟩ : Fin n)] *
        (Matrix.gramMatrix b)[(⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)] -
      (Matrix.noPivotLoop (q + 1)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
        (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)] := by
  induction q with
  | zero =>
    -- Empty fold; reduce to the q = 0 algebraic identity via the gramMatrix
    -- entries supplied by `correspondence` at `l = 0`.
    have hp_out_pos : 0 < p_out := hq_lt_pout
    have h0a : 0 < a := Nat.lt_of_lt_of_le hp_out_pos hpa
    have ih0 := correspondence 0 (Nat.le_refl 0)
    have h_rows_a0 :
        getArrayEntry (scaledCoeffRowsSchur b) a 0 =
          (Matrix.gramMatrix b)[(⟨a, han⟩ : Fin n)][
            (⟨0, Nat.lt_trans hp_out_pos hp_out_n⟩ : Fin n)] := by
      simpa [Matrix.noPivotLoop_zero_fuel, Matrix.noPivotInitialState] using
        ih0.2 a h0a han
    have h_rows_p0 :
        getArrayEntry (scaledCoeffRowsSchur b) p_out 0 =
          (Matrix.gramMatrix b)[(⟨p_out, hp_out_n⟩ : Fin n)][
            (⟨0, Nat.lt_trans hp_out_pos hp_out_n⟩ : Fin n)] := by
      simpa [Matrix.noPivotLoop_zero_fuel, Matrix.noPivotInitialState] using
        ih0.2 p_out hp_out_pos hp_out_n
    have h_sym_p0 :
        (Matrix.gramMatrix b)[(⟨p_out, hp_out_n⟩ : Fin n)][
            (⟨0, Nat.lt_trans hp_out_pos hp_out_n⟩ : Fin n)] =
          (Matrix.gramMatrix b)[(⟨0, Nat.lt_trans hp_out_pos hp_out_n⟩ : Fin n)][
            (⟨p_out, hp_out_n⟩ : Fin n)] :=
      gramMatrix_symm (b := b) _ _
    have hDone :
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + 1 < n := by
      simp [Matrix.noPivotInitialState]; omega
    have hpivot :
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step][
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step] ≠ 0 := by
      have key :=
        noPivotLoop_initial_gram_diag_ne_zero
          (b := b) p_out 0 hp_out_pos hp_out_n h_nonsing
      simp only [Matrix.noPivotInitialState]
      exact key
    rw [Matrix.noPivotLoop_regular_branch 0
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) hDone hpivot]
    simp [Matrix.noPivotLoop_zero_fuel, Matrix.noPivotInitialState]
    simp [Matrix.stepMatrix_eq_ofFn, Matrix.exactDiv, Matrix.ofFn, h0a, hp_out_pos,
      h_rows_a0, h_rows_p0]
    grind
  | succ q' ih =>
    -- Extend the fold by one iteration; rewrite the body via correspondence,
    -- apply the IH, then close via `schurSigma_noPivotCorrection_succ`.
    let state₀ : Matrix.BareissState n :=
      Matrix.noPivotInitialState (Matrix.gramMatrix b)
    have h_init_none : state₀.singularStep = none := by
      simp [state₀, Matrix.noPivotInitialState]
    have hq'_lt : q' < p_out := Nat.lt_of_succ_lt hq_lt_pout
    have hq'_succ_lt : q' + 1 < p_out := hq_lt_pout
    have hq'_n : q' < n := Nat.lt_trans hq'_lt hp_out_n
    have hq'_succ_n : q' + 1 < n := Nat.lt_trans hq'_succ_lt hp_out_n
    have hp_a_lt : q' + 1 < a := Nat.lt_of_lt_of_le hq'_succ_lt hpa
    -- (loop (q'+1)) and (loop q') are both non-singular prefixes of (loop p_out).
    have h_prefix_q'_succ_none :
        (Matrix.noPivotLoop (q' + 1) state₀).singularStep = none := by
      apply noPivotLoop_prefix_none_of_final_none (q' + 1) (p_out - (q' + 1)) state₀
        h_init_none
      have h_eq : (q' + 1) + (p_out - (q' + 1)) = p_out := by omega
      rw [h_eq]; exact h_nonsing
    have h_prefix_q'_none :
        (Matrix.noPivotLoop q' state₀).singularStep = none := by
      apply noPivotLoop_prefix_none_of_final_none q' (p_out - q') state₀ h_init_none
      have h_eq : q' + (p_out - q') = p_out := by omega
      rw [h_eq]; exact h_nonsing
    -- step matches fuel under non-singular prefix.
    have h_step_q' : (Matrix.noPivotLoop q' state₀).step = q' :=
      noPivotLoop_initial_gram_step_eq b q' (by omega) h_prefix_q'_none
    have h_step_q'_succ : (Matrix.noPivotLoop (q' + 1) state₀).step = q' + 1 :=
      noPivotLoop_initial_gram_step_eq b (q' + 1) (by omega)
        h_prefix_q'_succ_none
    -- Apply the inductive hypothesis at q'.
    have ih_eq :=
      ih hq'_lt (fun l hl => correspondence l (Nat.le_succ_of_le hl))
    -- Extract correspondence values needed for the new body at p_iter = q' + 1.
    have corr_q' := correspondence q' (Nat.le_succ q')
    have corr_q'_succ := correspondence (q' + 1) (Nat.le_refl (q' + 1))
    -- diagonal at q' (the denominator)
    have h_rows_q'_diag :
        getArrayEntry (scaledCoeffRowsSchur b) q' q' =
          (Matrix.noPivotLoop q' state₀).matrix[
            (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] := corr_q'.1
    -- diagonal at q'+1 (the pivot)
    have h_rows_q'_succ_diag :
        getArrayEntry (scaledCoeffRowsSchur b) (q' + 1) (q' + 1) =
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
            (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
            (⟨q' + 1, hq'_succ_n⟩ : Fin n)] := corr_q'_succ.1
    -- entries at row a and row p_out, column q' + 1
    have h_rows_a_q'_succ :
        getArrayEntry (scaledCoeffRowsSchur b) a (q' + 1) =
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
            (⟨a, han⟩ : Fin n)][
            (⟨q' + 1, hq'_succ_n⟩ : Fin n)] :=
      corr_q'_succ.2 a hp_a_lt han
    have h_rows_p_q'_succ :
        getArrayEntry (scaledCoeffRowsSchur b) p_out (q' + 1) =
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
            (⟨p_out, hp_out_n⟩ : Fin n)][
            (⟨q' + 1, hq'_succ_n⟩ : Fin n)] :=
      corr_q'_succ.2 p_out hq'_succ_lt hp_out_n
    -- prevPivot at fuel q'+1: this is matrix_q'[q'][q'].
    have h_prevPivot_q'_succ :
        (Matrix.noPivotLoop (q' + 1) state₀).prevPivot =
          (Matrix.noPivotLoop q' state₀).matrix[
            (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] := by
      have h_add : Matrix.noPivotLoop (q' + 1) state₀ =
          Matrix.noPivotLoop 1 (Matrix.noPivotLoop q' state₀) :=
        Matrix.noPivotLoop_add q' 1 state₀
      have hDone :
          (Matrix.noPivotLoop q' state₀).step + 1 < n := by
        rw [h_step_q']; exact hq'_succ_n
      have h_idx_eq :
          (⟨(Matrix.noPivotLoop q' state₀).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n) = (⟨q', hq'_n⟩ : Fin n) :=
        Fin.ext h_step_q'
      have h_diag_at_q' :=
        noPivotLoop_initial_gram_diag_ne_zero b (q' + 1) q'
          (Nat.lt_succ_self q') hq'_succ_n h_prefix_q'_succ_none
      have h_eq_diag :
          (Matrix.noPivotLoop q' state₀).matrix[
              (⟨(Matrix.noPivotLoop q' state₀).step,
                  Nat.lt_of_succ_lt hDone⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop q' state₀).step,
                  Nat.lt_of_succ_lt hDone⟩ : Fin n)] =
            (Matrix.noPivotLoop q' state₀).matrix[
              (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] :=
        congrArg
          (fun (i : Fin n) => (Matrix.noPivotLoop q' state₀).matrix[i][i]) h_idx_eq
      have h_diag_at_step :
          (Matrix.noPivotLoop q' state₀).matrix[
              (⟨(Matrix.noPivotLoop q' state₀).step,
                  Nat.lt_of_succ_lt hDone⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop q' state₀).step,
                  Nat.lt_of_succ_lt hDone⟩ : Fin n)] ≠ 0 :=
        h_eq_diag ▸ h_diag_at_q'
      rw [h_add, Matrix.noPivotLoop_regular_branch 0 _ hDone h_diag_at_step,
        Matrix.noPivotLoop_zero_fuel]
      -- The `noPivotLoop_regular_branch` rewrite makes the goal:
      --   matrix[⟨step, ⋯⟩][⟨step, ⋯⟩] = matrix[⟨q', hq'_n⟩][⟨q', hq'_n⟩]
      -- which we close by the index equality.
      exact congrArg
        (fun (i : Fin n) =>
          (Matrix.noPivotLoop q' state₀).matrix[i][i]) h_idx_eq
    -- Bareiss step at fuel q'+1: matrix_(q'+2)[a][p_out] = exactDiv of the
    -- standard Bareiss numerator by prevPivot.
    have h_step_a_p :
        (Matrix.noPivotLoop (q' + 1 + 1) state₀).matrix[
            (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)] =
          Matrix.exactDiv
            ((Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
                (⟨q' + 1, hq'_succ_n⟩ : Fin n)] *
              (Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)] -
              (Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨a, han⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)] *
              (Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨q' + 1, hq'_succ_n⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)])
            ((Matrix.noPivotLoop (q' + 1) state₀).prevPivot) := by
      have h_add : Matrix.noPivotLoop (q' + 1 + 1) state₀ =
          Matrix.noPivotLoop 1 (Matrix.noPivotLoop (q' + 1) state₀) :=
        Matrix.noPivotLoop_add (q' + 1) 1 state₀
      rw [h_add]
      have hDone : (Matrix.noPivotLoop (q' + 1) state₀).step + 1 < n := by
        rw [h_step_q'_succ]; omega
      have hp :
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                Nat.lt_of_succ_lt hDone⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                Nat.lt_of_succ_lt hDone⟩ : Fin n)] ≠ 0 := by
        have h_diag := noPivotLoop_initial_gram_diag_ne_zero b p_out (q' + 1)
          hq'_succ_lt hp_out_n h_nonsing
        have h_idx :
            (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)
              = (⟨q' + 1, hq'_succ_n⟩ : Fin n) := Fin.ext h_step_q'_succ
        have h_eq :
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                    Nat.lt_of_succ_lt hDone⟩ : Fin n)][
                (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                    Nat.lt_of_succ_lt hDone⟩ : Fin n)] =
              (Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
                (⟨q' + 1, hq'_succ_n⟩ : Fin n)] :=
          congrArg
            (fun (i : Fin n) =>
              (Matrix.noPivotLoop (q' + 1) state₀).matrix[i][i]) h_idx
        exact h_eq ▸ h_diag
      rw [Matrix.noPivotLoop_regular_branch 0 _ hDone hp,
        Matrix.noPivotLoop_zero_fuel]
      have ha : (Matrix.noPivotLoop (q' + 1) state₀).step < a := by
        rw [h_step_q'_succ]; exact hp_a_lt
      have hpo : (Matrix.noPivotLoop (q' + 1) state₀).step < p_out := by
        rw [h_step_q'_succ]; exact hq'_succ_lt
      rw [Matrix.stepMatrix_update_eq (Matrix.noPivotLoop (q' + 1) state₀).matrix
        (Matrix.noPivotLoop (q' + 1) state₀).step _
        (Matrix.noPivotLoop (q' + 1) state₀).prevPivot
        (⟨a, han⟩ : Fin n) (⟨p_out, hp_out_n⟩ : Fin n) ha hpo]
      -- The remaining goal is to identify the unfolded `colK = ⟨step, _⟩`
      -- (and similarly `rowK`) with `⟨q'+1, hq'_succ_n⟩`. Substitute via the
      -- step-equality, then close by reflexivity (Fin proofs are irrelevant).
      simp only [h_step_q'_succ]
      rfl
    -- Symmetry of matrix_(q'+1) at (q'+1, p_out).
    -- Built by application (not by re-elaborating the written-out nested-getElem
    -- type, which whnf-reduces the `noPivotLoop` term and is very slow).
    have h_sym_pivot_row :=
      noPivotLoop_matrix_symm_preserve (q' + 1) state₀
        (fun x y _ _ => by
          simp only [state₀, Matrix.noPivotInitialState]
          exact gramMatrix_symm (b := b) x y)
        (⟨q' + 1, hq'_succ_n⟩ : Fin n) (⟨p_out, hp_out_n⟩ : Fin n)
        (by rw [h_step_q'_succ]; exact Nat.le_refl _)
        (by rw [h_step_q'_succ]; exact Nat.le_of_lt hq'_succ_lt)
    -- Matrix-level Bareiss divisibility at fuel q'+1: prevPivot ∣ numerator.
    have hpivot_q'_succ :
        (Matrix.noPivotLoop (q' + 1) state₀).matrix[
          (Matrix.noPivotLoop (q' + 1) state₀).step][
          (Matrix.noPivotLoop (q' + 1) state₀).step] ≠ 0 := by
      have h_diag_ne :=
        noPivotLoop_initial_gram_diag_ne_zero b p_out (q' + 1)
          hq'_succ_lt hp_out_n h_nonsing
      have h_step_lt_n :
          (Matrix.noPivotLoop (q' + 1) state₀).step < n := by
        rw [h_step_q'_succ]; exact hq'_succ_n
      have h_idx :
          (⟨(Matrix.noPivotLoop (q' + 1) state₀).step, h_step_lt_n⟩ : Fin n)
            = (⟨q' + 1, hq'_succ_n⟩ : Fin n) := Fin.ext h_step_q'_succ
      have h_eq :
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                  h_step_lt_n⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                  h_step_lt_n⟩ : Fin n)] =
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)] :=
        congrArg
          (fun (i : Fin n) =>
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[i][i]) h_idx
      exact h_eq ▸ h_diag_ne
    have h_step_dvd_raw :=
      noPivotLoop_initial_gram_bareiss_step_dvd b hquot (q' + 1)
        h_prefix_q'_succ_none
        (by rw [h_step_q'_succ]; omega)
        hpivot_q'_succ
        (⟨a, han⟩ : Fin n) (⟨p_out, hp_out_n⟩ : Fin n)
        (by rw [h_step_q'_succ]; exact hp_a_lt)
    -- Identify the `k` index in `h_step_dvd_raw` with `q'+1`.
    have h_step_dvd :
        (Matrix.noPivotLoop q' state₀).matrix[
            (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] ∣
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)] *
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)] -
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨a, han⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)] *
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨p_out, hp_out_n⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)] := by
      rw [← h_prevPivot_q'_succ, ← h_sym_pivot_row]
      -- Unfold the `let state, let k` in h_step_dvd_raw to get a normalized form.
      simp only at h_step_dvd_raw
      -- Now apply congrArg to identify the matrix entries with `⟨step, _⟩` =
      -- `⟨q' + 1, hq'_succ_n⟩` indices.
      have h_kk :
          ∀ (h_lt : (Matrix.noPivotLoop (q' + 1) state₀).step < n),
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step, h_lt⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step, h_lt⟩ : Fin n)] =
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)] := fun _ =>
        congrArg
          (fun (i : Fin n) =>
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[i][i])
          (Fin.ext h_step_q'_succ)
      have h_ak :
          ∀ (h_lt : (Matrix.noPivotLoop (q' + 1) state₀).step < n),
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨a, han⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step, h_lt⟩ : Fin n)] =
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨a, han⟩ : Fin n)][
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)] := fun _ =>
        congrArg
          (fun (i : Fin n) =>
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨a, han⟩ : Fin n)][i])
          (Fin.ext h_step_q'_succ)
      have h_kp :
          ∀ (h_lt : (Matrix.noPivotLoop (q' + 1) state₀).step < n),
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step, h_lt⟩ : Fin n)][
              (⟨p_out, hp_out_n⟩ : Fin n)] =
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
              (⟨p_out, hp_out_n⟩ : Fin n)] := fun _ =>
        congrArg
          (fun (i : Fin n) =>
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[i][
              (⟨p_out, hp_out_n⟩ : Fin n)])
          (Fin.ext h_step_q'_succ)
      rw [h_kk _, h_ak _, h_kp _] at h_step_dvd_raw
      exact h_step_dvd_raw
    -- nonzero denom
    have hdenom_ne :
        (Matrix.noPivotLoop q' state₀).matrix[
          (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] ≠ 0 :=
      noPivotLoop_initial_gram_diag_ne_zero b (q' + 1) q'
        (Nat.lt_succ_self q') hq'_succ_n h_prefix_q'_succ_none
    -- Now expand the fold: range' 1 (q' + 1) = range' 1 q' ++ [q' + 1].
    have h_concat :
        List.range' 1 (q' + 1) = List.range' 1 q' ++ [q' + 1] := by
      have := List.range'_concat (s := 1) (n := q') (step := 1)
      simpa [Nat.add_comm 1 q'] using this
    rw [h_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.add_sub_cancel]
    rw [ih_eq, h_rows_q'_diag, h_rows_q'_succ_diag, h_rows_a_q'_succ,
      h_rows_p_q'_succ]
    -- Close via the succ algebraic helper.
    exact schurSigma_noPivotCorrection_succ
      ((Matrix.noPivotLoop q' state₀).matrix[
          (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)])
      ((Matrix.noPivotLoop (q' + 1) state₀).matrix[
          (⟨q' + 1, hq'_succ_n⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)])
      ((Matrix.gramMatrix b)[(⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)])
      ((Matrix.noPivotLoop (q' + 1) state₀).matrix[
          (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)])
      ((Matrix.noPivotLoop (q' + 1) state₀).matrix[
          (⟨a, han⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)])
      ((Matrix.noPivotLoop (q' + 1) state₀).matrix[
          (⟨p_out, hp_out_n⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)])
      ((Matrix.noPivotLoop (q' + 1 + 1) state₀).matrix[
          (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)])
      hdenom_ne h_step_dvd
      (by rw [h_step_a_p, h_prevPivot_q'_succ, h_sym_pivot_row])

/-- Mathlib-free non-singular Schur ≡ Bareiss correspondence at a single
column.  When the no-pivot Bareiss pass over the full Gram matrix reaches
column `q` without recording a singular step, the diagonal slot and every
below-column entry of the integral Schur kernel match the corresponding
`noPivotLoop`/Bareiss matrix at fuel `q`.

Proved by strong induction on `q`. The base case `q = 0` reduces to the
column-zero boundary of the Schur kernel together with `noPivotLoop` at
zero fuel returning the initial Gram state. The step case `q' + 1` rewrites
the Schur recurrence `rows[c][q' + 1] = rows[q'][q'] · gram[c][q' + 1] -
schurSigma rows c (q' + 1)` and discharges the σ-chain via
`schurSigma_foldl_eq` at `p_out = q' + 1`, fed with the
σ-fold correspondence assembled from the strong inductive hypothesis. -/
theorem getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing
    {n m : Nat} (b : Matrix Int n m) (hquot : StepWitness b)
    (q : Nat) (hqn : q < n)
    (h_nonsing :
      (Matrix.noPivotLoop q
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (getArrayEntry (scaledCoeffRowsSchur b) q q =
      (Matrix.noPivotLoop q
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
        (⟨q, hqn⟩ : Fin n)][(⟨q, hqn⟩ : Fin n)]) ∧
    (∀ c (_hqc : q < c) (hcn : c < n),
      getArrayEntry (scaledCoeffRowsSchur b) c q =
        (Matrix.noPivotLoop q
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (⟨c, hcn⟩ : Fin n)][(⟨q, hqn⟩ : Fin n)]) := by
  revert hqn h_nonsing
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro hqn h_nonsing
    match q, hqn, h_nonsing, ih with
    | 0, hqn, _, _ =>
      refine ⟨?_, ?_⟩
      · rw [getArrayEntry_scaledCoeffRowsSchur_col_zero,
          Matrix.noPivotLoop_zero_fuel]
        exact getArrayEntry_gramRows b ⟨0, hqn⟩ ⟨0, hqn⟩
      · intro c _hqc hcn
        rw [getArrayEntry_scaledCoeffRowsSchur_col_zero,
          Matrix.noPivotLoop_zero_fuel]
        exact getArrayEntry_gramRows b ⟨c, hcn⟩ ⟨0, hqn⟩
    | q' + 1, hqn, h_nonsing, ih =>
      have hq'_lt_succ : q' < q' + 1 := Nat.lt_succ_self q'
      have hq'_n : q' < n := Nat.lt_of_succ_lt hqn
      have prefix_none : ∀ (l : Nat), l ≤ q' + 1 →
          (Matrix.noPivotLoop l
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
        intro l hl
        apply noPivotLoop_prefix_none_of_final_none l (q' + 1 - l)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))
          (by simp [Matrix.noPivotInitialState])
        have h_eq : l + (q' + 1 - l) = q' + 1 := by omega
        rw [h_eq]
        exact h_nonsing
      have correspondence :
          ∀ (l : Nat) (hl : l ≤ q'),
            getArrayEntry (scaledCoeffRowsSchur b) l l =
              (Matrix.noPivotLoop l
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
                (⟨l, Nat.lt_of_le_of_lt
                      (Nat.le_trans hl (Nat.le_of_lt hq'_lt_succ)) hqn⟩
                  : Fin n)][
                (⟨l, Nat.lt_of_le_of_lt
                      (Nat.le_trans hl (Nat.le_of_lt hq'_lt_succ)) hqn⟩
                  : Fin n)] ∧
            ∀ c (_hlc : l < c) (hcn : c < n),
              getArrayEntry (scaledCoeffRowsSchur b) c l =
                (Matrix.noPivotLoop l
                    (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
                  (⟨c, hcn⟩ : Fin n)][
                  (⟨l, Nat.lt_of_le_of_lt
                        (Nat.le_trans hl (Nat.le_of_lt hq'_lt_succ)) hqn⟩
                    : Fin n)] := by
        intro l hl
        have hl_lt : l < q' + 1 := Nat.lt_succ_of_le hl
        have hl_n : l < n :=
          Nat.lt_of_le_of_lt (Nat.le_trans hl (Nat.le_of_lt hq'_lt_succ)) hqn
        have h_l_none := prefix_none l (Nat.le_of_lt hl_lt)
        exact ih l hl_lt hl_n h_l_none
      have ih_diag := (correspondence q' (Nat.le_refl q')).1
      have h_sigma_closed : ∀ (a : Nat) (han : a < n) (hpa : q' + 1 ≤ a),
          schurSigma (scaledCoeffRowsSchur b) a (q' + 1) =
            (Matrix.noPivotLoop q'
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
              (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] *
              (Matrix.gramMatrix b)[(⟨a, han⟩ : Fin n)][
                (⟨q' + 1, hqn⟩ : Fin n)] -
            (Matrix.noPivotLoop (q' + 1)
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
              (⟨a, han⟩ : Fin n)][(⟨q' + 1, hqn⟩ : Fin n)] := by
        intro a han hpa
        have h_fold := schurSigma_foldl_eq b hquot a (q' + 1) q'
          hqn han hpa hq'_lt_succ h_nonsing correspondence
        show (Id.run do
              let mut sigma :=
                getArrayEntry (scaledCoeffRowsSchur b) a 0 *
                getArrayEntry (scaledCoeffRowsSchur b) (q' + 1) 0
              for p in [1:q' + 1] do
                sigma :=
                  Matrix.exactDiv
                    (getArrayEntry (scaledCoeffRowsSchur b) p p * sigma +
                      getArrayEntry (scaledCoeffRowsSchur b) a p *
                      getArrayEntry (scaledCoeffRowsSchur b) (q' + 1) p)
                    (getArrayEntry (scaledCoeffRowsSchur b) (p - 1) (p - 1))
              return sigma) = _
        simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
        exact h_fold
      refine ⟨?_, ?_⟩
      · rw [getArrayEntry_scaledCoeffRowsSchur_eq_schurScaledCoeffEntry b (q' + 1)
          (q' + 1) (Nat.le_refl _) hqn]
        show schurScaledCoeffEntry (scaledCoeffRowsSchur b) (gramRows b) (q' + 1)
            (q' + 1) = _
        unfold schurScaledCoeffEntry
        rw [if_neg (Nat.succ_ne_zero q')]
        simp only [Nat.add_sub_cancel]
        rw [ih_diag,
          show getArrayEntry (gramRows b) (q' + 1) (q' + 1) =
              (Matrix.gramMatrix b)[(⟨q' + 1, hqn⟩ : Fin n)][
                (⟨q' + 1, hqn⟩ : Fin n)] from
            getArrayEntry_gramRows b ⟨q' + 1, hqn⟩ ⟨q' + 1, hqn⟩,
          h_sigma_closed (q' + 1) hqn (Nat.le_refl _)]
        grind
      · intro c hqc hcn
        have h_pa : q' + 1 ≤ c := Nat.le_of_lt hqc
        rw [getArrayEntry_scaledCoeffRowsSchur_eq_schurScaledCoeffEntry b c (q' + 1)
          h_pa hcn]
        show schurScaledCoeffEntry (scaledCoeffRowsSchur b) (gramRows b) c (q' + 1) = _
        unfold schurScaledCoeffEntry
        rw [if_neg (Nat.succ_ne_zero q')]
        simp only [Nat.add_sub_cancel]
        rw [ih_diag,
          show getArrayEntry (gramRows b) c (q' + 1) =
              (Matrix.gramMatrix b)[(⟨c, hcn⟩ : Fin n)][
                (⟨q' + 1, hqn⟩ : Fin n)] from
            getArrayEntry_gramRows b ⟨c, hcn⟩ ⟨q' + 1, hqn⟩,
          h_sigma_closed c hcn h_pa]
        grind

/-- Singular cascade at the Schur kernel. If the no-pivot Bareiss pass over
the full Gram matrix records an early singular step at column `s < j`, every
Schur-kernel entry in the column-`j`, weak-lower triangle (`j ≤ i`) vanishes.

The row-`s` column is cleared by combining the non-singular Schur≡Bareiss
correspondence at fuel `s`
(`getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing`) with the
column-zero structural lemma at the singular step
(`principalSubmatrix_gram_zero_pivot_column_zero`). Strong
induction on `j' ∈ (s, j]` then propagates the zeros via the Schur recurrence
`rows[i'][j'] = rows[j'-1][j'-1] · gram[i'][j'] - schurSigma i' j'`. The
diagonal factor `rows[j'-1][j'-1]` is zero by the row-`s` lemma when
`j' = s + 1` and by the cascade IH otherwise. The σ-fold collapses to zero
by sub-induction on the iteration count: the killing iteration `p = s`
makes all three relevant Schur entries zero (`rows[s][s] = 0` and
`rows[c][s] = 0` for `c ≥ s + 1`), so the σ-body `exactDiv` of zero by the
prev-pivot returns zero; subsequent iterations preserve zero via the outer
IH at columns `(s, j')`. The proof does not transitively cite
`getArrayEntry_scaledCoeffRowsSchur_eq` (the residual gap at line 6463). -/
theorem getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
    {n m : Nat} (b : Matrix Int n m) (hquot : StepWitness b)
    (i j : Nat) (hi : i < n) (hji : j ≤ i)
    (s : Nat) (hsj : s < j)
    (h_sing : (Matrix.noPivotLoop j
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    getArrayEntry (scaledCoeffRowsSchur b) i j = 0 := by
  have hjn : j < n := Nat.lt_of_le_of_lt hji hi
  have hsn : s < n := Nat.lt_trans hsj hjn
  have hs_succ_le_n : s + 1 ≤ n := hsn
  obtain ⟨h_s_prefix_none, _h_s_step, h_s_diag_zero⟩ :=
    noPivotLoop_prefix_state_at_singular (Matrix.gramMatrix b) j s hs_succ_le_n h_sing
  have h_corr_at_s :=
    getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing b hquot s hsn h_s_prefix_none
  -- Row-`s` is zero across the lower triangle (including the diagonal).
  have h_row_s_zero : ∀ (c : Nat), c < n → s ≤ c →
      getArrayEntry (scaledCoeffRowsSchur b) c s = 0 := by
    intro c hcn hcs
    by_cases hcs_eq : c = s
    · subst hcs_eq
      rw [h_corr_at_s.1]
      exact h_s_diag_zero
    · have hc_gt : s < c := Nat.lt_of_le_of_ne hcs (Ne.symm hcs_eq)
      have hs_succ_lt_n : s + 1 < n := Nat.lt_of_le_of_lt hc_gt hcn
      rw [h_corr_at_s.2 c hc_gt hcn]
      exact principalSubmatrix_gram_zero_pivot_column_zero
        b s hs_succ_lt_n hquot h_s_prefix_none h_s_diag_zero ⟨c, hcn⟩ hc_gt
  -- Strong induction on `j'` ∈ (s, j].
  suffices h_cascade : ∀ (j' : Nat), j' ≤ j → s < j' →
      ∀ (i' : Nat), j' ≤ i' → i' < n →
        getArrayEntry (scaledCoeffRowsSchur b) i' j' = 0 from
    h_cascade j (Nat.le_refl j) hsj i hji hi
  intro j' hj'j hsj' i' hj'i' hi'n
  revert hj'j hsj' i' hj'i' hi'n
  induction j' using Nat.strongRecOn with
  | ind j' ih =>
    intro hj'j hsj' i' hj'i' hi'n
    have hj'_pos : 0 < j' := Nat.lt_of_le_of_lt (Nat.zero_le _) hsj'
    have hj'n : j' < n := Nat.lt_of_le_of_lt hj'j hjn
    -- Apply the Schur recurrence at `(i', j')`.
    rw [getArrayEntry_scaledCoeffRowsSchur_eq_schurScaledCoeffEntry b i' j' hj'i' hi'n]
    show schurScaledCoeffEntry (scaledCoeffRowsSchur b) (gramRows b) i' j' = 0
    unfold schurScaledCoeffEntry
    rw [if_neg (Nat.ne_of_gt hj'_pos)]
    -- Diagonal factor at `(j' - 1, j' - 1)` is zero.
    have h_diag_zero :
        getArrayEntry (scaledCoeffRowsSchur b) (j' - 1) (j' - 1) = 0 := by
      have hj'_sub_one_lt_n : j' - 1 < n := by omega
      by_cases hj'_eq_s : j' - 1 = s
      · rw [hj'_eq_s]
        exact h_row_s_zero s hsn (Nat.le_refl s)
      · have hj'_gt : s < j' - 1 := by omega
        have hj'_sub_one_lt_j' : j' - 1 < j' := by omega
        have hj'_sub_one_le_j : j' - 1 ≤ j := by omega
        exact ih (j' - 1) hj'_sub_one_lt_j' hj'_sub_one_le_j hj'_gt
          (j' - 1) (Nat.le_refl _) hj'_sub_one_lt_n
    -- σ-fold value at `(i', j')` is zero, by sub-induction on the iteration prefix.
    have h_sigma_zero :
        schurSigma (scaledCoeffRowsSchur b) i' j' = 0 := by
      show (Id.run do
            let mut sigma :=
              getArrayEntry (scaledCoeffRowsSchur b) i' 0 *
                getArrayEntry (scaledCoeffRowsSchur b) j' 0
            for p in [1:j'] do
              sigma :=
                Matrix.exactDiv
                  (getArrayEntry (scaledCoeffRowsSchur b) p p * sigma +
                    getArrayEntry (scaledCoeffRowsSchur b) i' p *
                    getArrayEntry (scaledCoeffRowsSchur b) j' p)
                  (getArrayEntry (scaledCoeffRowsSchur b) (p - 1) (p - 1))
            return sigma) = 0
      simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
      have h_fold : ∀ (k : Nat), s ≤ k → k ≤ j' - 1 →
          (List.range' 1 k).foldl
            (fun σ p_iter =>
              Matrix.exactDiv
                (getArrayEntry (scaledCoeffRowsSchur b) p_iter p_iter * σ +
                  getArrayEntry (scaledCoeffRowsSchur b) i' p_iter *
                  getArrayEntry (scaledCoeffRowsSchur b) j' p_iter)
                (getArrayEntry (scaledCoeffRowsSchur b) (p_iter - 1) (p_iter - 1)))
            (getArrayEntry (scaledCoeffRowsSchur b) i' 0 *
              getArrayEntry (scaledCoeffRowsSchur b) j' 0) = 0 := by
        intro k
        induction k with
        | zero =>
          intro hsk _hkj'
          have hs_eq : s = 0 := Nat.le_zero.mp hsk
          simp only [List.range'_zero, List.foldl_nil]
          have hj'_ge_s : s ≤ j' := by omega
          have h_j'0 := h_row_s_zero j' hj'n hj'_ge_s
          rw [hs_eq] at h_j'0
          rw [h_j'0]
          simp
        | succ k' ih_k =>
          intro hsk hkj'
          have h_concat :
              List.range' 1 (k' + 1) = List.range' 1 k' ++ [k' + 1] := by
            have := List.range'_concat (s := 1) (n := k') (step := 1)
            simpa [Nat.add_comm 1 k'] using this
          rw [h_concat, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          by_cases hsk' : s ≤ k'
          · -- IH applies: the prefix fold is already zero.
            have hk'_le_j' : k' ≤ j' - 1 := by omega
            have ih_zero := ih_k hsk' hk'_le_j'
            rw [ih_zero]
            have hs_lt_kp1 : s < k' + 1 := Nat.lt_succ_of_le hsk'
            have hkp1_lt_j' : k' + 1 < j' := by omega
            have hkp1_le_j : k' + 1 ≤ j :=
              Nat.le_of_lt (Nat.lt_of_lt_of_le hkp1_lt_j' hj'j)
            have hkp1_lt_n : k' + 1 < n := Nat.lt_trans hkp1_lt_j' hj'n
            have hkp1_le_i' : k' + 1 ≤ i' := by omega
            have hkp1_le_j' : k' + 1 ≤ j' := by omega
            have h_diag :=
              ih (k' + 1) hkp1_lt_j' hkp1_le_j hs_lt_kp1 (k' + 1) (Nat.le_refl _) hkp1_lt_n
            have h_i_pkp1 :=
              ih (k' + 1) hkp1_lt_j' hkp1_le_j hs_lt_kp1 i' hkp1_le_i' hi'n
            have h_j_pkp1 :=
              ih (k' + 1) hkp1_lt_j' hkp1_le_j hs_lt_kp1 j' hkp1_le_j' hj'n
            rw [h_diag, h_i_pkp1, h_j_pkp1]
            simp [Matrix.exactDiv]
          · -- Killing iteration: `s = k' + 1`, so `rows[*][k' + 1] = 0`.
            have hs_eq : s = k' + 1 := by omega
            have hkp1_le_i' : k' + 1 ≤ i' := by omega
            have hkp1_le_j' : k' + 1 ≤ j' := by omega
            have hkp1_lt_n : k' + 1 < n := by omega
            have h_diag : getArrayEntry (scaledCoeffRowsSchur b) (k' + 1) (k' + 1) = 0 := by
              rw [show k' + 1 = s from hs_eq.symm]
              exact h_row_s_zero s hsn (Nat.le_refl _)
            have h_i_pkp1 : getArrayEntry (scaledCoeffRowsSchur b) i' (k' + 1) = 0 := by
              rw [show k' + 1 = s from hs_eq.symm]
              exact h_row_s_zero i' hi'n (by omega)
            have h_j_pkp1 : getArrayEntry (scaledCoeffRowsSchur b) j' (k' + 1) = 0 := by
              rw [show k' + 1 = s from hs_eq.symm]
              exact h_row_s_zero j' hj'n (by omega)
            rw [h_diag, h_i_pkp1, h_j_pkp1]
            simp [Matrix.exactDiv]
      have hsj'_sub_one : s ≤ j' - 1 := by omega
      exact h_fold (j' - 1) hsj'_sub_one (Nat.le_refl _)
    rw [h_diag_zero, h_sigma_zero]
    grind

/-- The per-row Schur scaled-coefficient kernel and the column-major Bareiss
array path produce identical integer values at every cell. Both arrays
contain the leading Gram determinant `d_{j+1}` on the diagonal and
`d_{j+1} · μ_{i,j}` below the diagonal, with zeros above; the recurrences
differ only in evaluation order. This equivalence is the bridge from the
Schur implementation to the existing invariant infrastructure proven about
`scaledCoeffRows`.

Closure routes the in-bounds `j ≤ i, j ≠ 0` case through Sub-D
(`getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing`) and Sub-C′
(`getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt`); the
out-of-bounds branch (`n ≤ i`) follows from both arrays having size `n`,
so the row entry is `default` on both sides. -/
theorem getArrayEntry_scaledCoeffRowsSchur_eq
    (b : Matrix Int n m) (hquot : StepWitness b) (i j : Nat) :
    getArrayEntry (scaledCoeffRowsSchur b) i j =
      getArrayEntry (scaledCoeffRows b) i j := by
  by_cases hij : i < j
  · rw [getArrayEntry_scaledCoeffRowsSchur_upper b i j hij,
      getArrayEntry_scaledCoeffRows_above b i j hij]
  · have hji : j ≤ i := Nat.le_of_not_lt hij
    by_cases hj : j = 0
    · subst hj
      rw [getArrayEntry_scaledCoeffRowsSchur_col_zero b i,
        getArrayEntry_scaledCoeffRows_col_zero b i]
    · by_cases hin : i < n
      · have hjn : j < n := Nat.lt_of_le_of_lt hji hin
        let iFin : Fin n := ⟨i, hin⟩
        let jFin : Fin n := ⟨j, hjn⟩
        cases h_sing : (Matrix.noPivotLoop j
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep with
        | none =>
          by_cases hij_eq : i = j
          · subst hij_eq
            have h_schur :=
              (getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing
                b hquot i hin h_sing).1
            have h_bareiss :=
              scaledCoeffRows_diag_eq_noPivotLoop_gramMatrix_of_no_singular
                b iFin h_sing
            rw [h_schur, h_bareiss]
          · have hji_lt : j < i := Nat.lt_of_le_of_ne hji (Ne.symm hij_eq)
            have h_schur :=
              (getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing
                b hquot j hjn h_sing).2 i hji_lt hin
            have h_bareiss :=
              scaledCoeffRows_lower_eq
                b iFin jFin hji_lt h_sing
            rw [h_schur, h_bareiss]
        | some s =>
          have hsj : s < j := by
            have h := noPivotLoop_singularStep_lt j
              (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
            show s < j
            simp [Matrix.noPivotInitialState] at h
            exact h
          have h_schur := getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
            b hquot i j hin hji s hsj h_sing
          rw [h_schur]
          by_cases hij_eq : i = j
          · subst hij_eq
            exact (scaledCoeffRows_diag_eq_zero_of_singularStep_lt
              b iFin s hsj h_sing).symm
          · have hji_lt : j < i := Nat.lt_of_le_of_ne hji (Ne.symm hij_eq)
            exact (scaledCoeffRows_eq_zero_of_singularStep_lt
              b iFin jFin hji_lt s h_sing).symm
      · have hin' : n ≤ i := Nat.le_of_not_lt hin
        have h_schur_size : (scaledCoeffRowsSchur b).size ≤ i :=
          (scaledCoeffRowsSchur_size b).symm ▸ hin'
        have h_bareiss_size : (scaledCoeffRows b).size = n := by
          unfold scaledCoeffRows
          rw [scaledCoeffArrayLoop_coeffs_size]
          exact zeroRows_size n
        have h_bareiss_size_le : (scaledCoeffRows b).size ≤ i :=
          h_bareiss_size.symm ▸ hin'
        have h_schur_default : (scaledCoeffRowsSchur b)[i]! = (default : Array Int) := by
          rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none h_schur_size, Option.getD_none]
        have h_bareiss_default : (scaledCoeffRows b)[i]! = (default : Array Int) := by
          rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none h_bareiss_size_le, Option.getD_none]
        unfold getArrayEntry
        rw [h_schur_default, h_bareiss_default]

/-- The packed Gram determinant vector agrees entrywise with `gramDet`: under a
step witness, its `k`-th component is the determinant of the leading `k × k` Gram
minor for every `k ≤ n`. This identifies the executable `gramDetVec` array pass
with its specification `gramDet`. -/
theorem gramDetVec_eq_gramDet (b : Matrix Int n m) (hquot : StepWitness b)
    (k : Nat) (hk : k ≤ n) :
    (gramDetVec b).get ⟨k, Nat.lt_succ_of_le hk⟩ = gramDet b k hk := by
  rcases k with _ | r
  · show (gramDetVec b).get ⟨0, _⟩ = gramDet b 0 hk
    have h_one : (gramDetVec b).get ⟨0, Nat.zero_lt_succ n⟩ = 1 := by
      simp [gramDetVec, data, gramDetVecFromScaledCoeffRows, Vector.get, Vector.toArray_ofFn]
    rw [show (gramDetVec b).get ⟨0, Nat.lt_succ_of_le hk⟩
          = (gramDetVec b).get ⟨0, Nat.zero_lt_succ n⟩ from rfl, h_one]
    exact (gramDet_zero b).symm
  · have hr : r < n := Nat.lt_of_succ_le hk
    show (gramDetVec b).get ⟨r + 1, _⟩ = gramDet b (r + 1) hk
    have hget :
        (gramDetVec b).get ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (getArrayEntry (scaledCoeffRowsSchur b) r r).toNat := by
      simp [gramDetVec, data, gramDetVecFromScaledCoeffRows, Vector.get, Vector.toArray_ofFn]
    rw [hget, getArrayEntry_scaledCoeffRowsSchur_eq b hquot]
    exact scaledCoeffRows_diag_toNat_eq_gramDet (b := b) hquot r hr

/-- Nat-level diagonal synchronization for the public scaled-coefficient
matrix. This is the Mathlib-free diagonal fact exposed by the shared array
pass; the stronger Int-valued diagonal statement additionally needs a
nonnegativity proof for the Bareiss/Gram determinant slot. -/
theorem scaledCoeffs_diag_toNat (b : Matrix Int n m) (hquot : StepWitness b)
    (i : Nat) (hi : i < n) :
    (GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩).toNat =
      gramDet b (i + 1) (Nat.succ_le_of_lt hi) := by
  rw [scaledCoeffs_entry_eq_getArrayEntry]
  have hpack :
      (gramDetVec b).get ⟨i + 1, Nat.succ_lt_succ hi⟩ =
        (getArrayEntry (scaledCoeffRowsSchur b) i i).toNat := by
    simp [gramDetVec, data, gramDetVecFromScaledCoeffRows, Vector.get, Vector.toArray_ofFn]
  rw [← hpack]
  exact gramDetVec_eq_gramDet (b := b) hquot (i + 1) (Nat.succ_le_of_lt hi)

/-- Signed diagonal information for the public scaled-coefficient matrix.
The diagonal slot is either the zero tail recorded after an earlier singular
no-pivot step, or the Bareiss determinant of the corresponding leading Gram
prefix. -/
theorem scaledCoeffs_diag_eq_zero_or_eq_principalSubmatrix_bareiss
    (b : Matrix Int n m) (hquot : StepWitness b)
    (i : Nat) (hi : i < n) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 0 ∨
      GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
        Matrix.bareiss
          (Matrix.principalSubmatrix (Matrix.gramMatrix b) (i + 1)
            (Nat.succ_le_of_lt hi)) := by
  rw [scaledCoeffs_entry_eq_getArrayEntry,
    getArrayEntry_scaledCoeffRowsSchur_eq b hquot]
  exact scaledCoeffRows_diag_eq_zero_or_eq_principalSubmatrix_bareiss (b := b) i hi

/-- Int-valued diagonal identity for the scaled Gram-Schmidt coefficients: once
the `(i, i)` slot is known nonnegative, it equals the Gram determinant
`gramDet b (i + 1)`. The `toNat` form (`scaledCoeffs_diag_toNat`) is
unconditional; the signed `Int` form needs the determinant slot to be
nonnegative. -/
theorem scaledCoeffs_diag_of_nonneg
    (b : Matrix Int n m) (hquot : StepWitness b)
    (i : Nat) (hi : i < n)
    (hnonneg : 0 ≤ GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi)) := by
  have hdiag := scaledCoeffs_diag_toNat (b := b) hquot i hi
  rw [← hdiag]
  exact (Int.toNat_of_nonneg hnonneg).symm

/-- Singular dual of `scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix`.
When the no-pivot Bareiss pass over the full Gram matrix records an early
singular step before reaching column `j`, the integral scaled Gram-Schmidt
coefficient below the diagonal at `(i, j)` is zero. The array loop halts at
the recorded singular column and the target column is never written. -/
theorem scaledCoeffs_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (hquot : StepWitness b)
    (i j : Fin n) (hji : j.val < i.val)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s)
    (_hsj : s < j.val) :
    GramSchmidt.entry (scaledCoeffs b) i j = 0 := by
  rw [scaledCoeffs_entry_eq_getArrayEntry,
    getArrayEntry_scaledCoeffRowsSchur_eq b hquot]
  exact scaledCoeffRows_eq_zero_of_singularStep_lt (b := b) i j hji s h_sing

/-- Non-singular companion of `scaledCoeffs_eq_zero_of_singularStep_lt`: when the
no-pivot Bareiss pass over the full Gram matrix reaches column `j` without
recording a singular step, the integral scaled Gram-Schmidt coefficient below
the diagonal at `(i, j)` matches the trailing entry of the no-pivot Bareiss-style
loop on the corresponding Cramer minor `scaledCoeffMatrix b i j hji`. -/
theorem scaledCoeffs_lower_eq_noPivotLoop_scaledCoeffMatrix
    (b : Matrix Int n m) (hquot : StepWitness b)
    (i j : Fin n) (hji : j.val < i.val)
    (h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (GramSchmidt.scaledCoeffMatrix b i j hji))).matrix[
        Fin.last j.val][Fin.last j.val] := by
  rw [scaledCoeffs_entry_eq_getArrayEntry,
    getArrayEntry_scaledCoeffRowsSchur_eq b hquot]
  exact scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix b i j hji h_nonsing


/-- For a `Matrix Int`, a row swap leaves any `Fin`-indexed row other than the
two swapped row indices unchanged. This is the row-access companion to
`Matrix.rowSwap` for the unchanged-row case. -/
private theorem rowSwap_row_eq_of_ne_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j r : Fin n')
    (hri : r.val ≠ i.val) (hrj : r.val ≠ j.val) :
    (Matrix.rowSwap M i j)[r] = M[r] := by
  apply Vector.ext
  intro c hc
  have hr_ne_j : r ≠ j := fun h => hrj (congrArg Fin.val h)
  have hr_ne_i : r ≠ i := fun h => hri (congrArg Fin.val h)
  have hget := Matrix.getElem_rowSwap M i j r ⟨c, hc⟩
  rw [if_neg hr_ne_j, if_neg hr_ne_i] at hget
  simpa [Matrix.row] using hget

/-- For a `Matrix Int`, the `Fin`-indexed left swap row `i` becomes the old row
`j`. This is the direct row-access form of `Matrix.rowSwap` for the first
swapped row. -/
theorem rowSwap_row_left_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap M i j)[i] = M[j] := by
  apply Vector.ext
  intro c hc
  by_cases hij : i = j
  · subst j
    have hget := Matrix.getElem_rowSwap M i i i ⟨c, hc⟩
    rw [if_pos rfl] at hget
    exact hget
  · have hget := Matrix.getElem_rowSwap M i j i ⟨c, hc⟩
    rw [if_neg hij, if_pos rfl] at hget
    simpa [Matrix.row] using hget

/-- For a `Matrix Int`, the `Fin`-indexed right swap row `j` becomes the old row
`i`. This is the companion row-access form of `Matrix.rowSwap` for the second
swapped row. -/
theorem rowSwap_row_right_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap M i j)[j] = M[i] := by
  apply Vector.ext
  intro c hc
  have hget := Matrix.getElem_rowSwap M i j j ⟨c, hc⟩
  rw [if_pos rfl] at hget
  simpa [Matrix.row] using hget

/-- Raw-`Nat` row-access version of `rowSwap_row_eq_of_ne_int`: with a bound
proof for row `r`, a `Matrix Int` row swap leaves that row unchanged when its
value is distinct from both swapped indices. -/
private theorem rowSwap_getRow_eq_of_ne_val_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') (r : Nat) (hr : r < n')
    (hri : r ≠ i.val) (hrj : r ≠ j.val) :
    (Matrix.rowSwap M i j).getRow ⟨r, hr⟩ = M.getRow ⟨r, hr⟩ :=
  Matrix.row_rowSwap_of_ne M (fun h => hri (congrArg Fin.val h)) (fun h => hrj (congrArg Fin.val h))

/-- Raw-`Nat` row-access version of `rowSwap_row_left_int`: after swapping rows
`i` and `j` in a `Matrix Int`, reading row `i.val` with an explicit bound proof
returns the old row `j`. -/
private theorem rowSwap_getRow_left_val_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap M i j).getRow i = M.getRow j :=
  Matrix.row_rowSwap_left M i j

/-- Raw-`Nat` row-access version of `rowSwap_row_right_int`: after swapping rows
`i` and `j` in a `Matrix Int`, reading row `j.val` with an explicit bound proof
returns the old row `i`. -/
private theorem rowSwap_getRow_right_val_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap M i j).getRow j = M.getRow i :=
  Matrix.row_rowSwap_right M i j

/-- Swapping the adjacent rows `km1` and `k` of the basis transposes the
scaled-coefficient Cramer minor for that pivot pair:
`scaledCoeffMatrix (rowSwap b km1 k) k km1 = (scaledCoeffMatrix b k km1)ᵀ`. This
is the matrix identity behind an LLL adjacent row swap, relating the coefficient
minor before and after the exchange. -/
theorem scaledCoeffMatrix_rowSwap_adjacent_pivot_transpose
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val)
    (hkm1k : km1.val < k.val) :
    GramSchmidt.scaledCoeffMatrix (Matrix.rowSwap b km1 k) k km1 hkm1k =
      (GramSchmidt.scaledCoeffMatrix b k km1 hkm1k).transpose := by
  let t := km1.val + 1
  let ht : t ≤ n := Nat.succ_le_of_lt km1.isLt
  let last : Fin t := ⟨km1.val, Nat.lt_succ_self km1.val⟩
  apply Hex.Matrix.ext
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  let p : Fin t := ⟨r, hr⟩
  let q : Fin t := ⟨c, hc⟩
  change
    (GramSchmidt.scaledCoeffMatrix (Matrix.rowSwap b km1 k) k km1 hkm1k)[p][q] =
      ((GramSchmidt.scaledCoeffMatrix b k km1 hkm1k).transpose)[p][q]
  have hp_lt_k : p.val < k.val := by
    dsimp [p, t]
    omega
  have hq_lt_k : q.val < k.val := by
    dsimp [q, t]
    omega
  have hp_ne_k : (GramSchmidt.liftFinLE p ht).val ≠ k.val := by
    dsimp [GramSchmidt.liftFinLE, p, t]
    omega
  have hq_ne_k : (GramSchmidt.liftFinLE q ht).val ≠ k.val := by
    dsimp [GramSchmidt.liftFinLE, q, t]
    omega
  have hlast_val : last.val = km1.val := rfl
  by_cases hq_last : q = last
  · have hq_val : q.val = km1.val := by
      simpa [last] using congrArg Fin.val hq_last
    by_cases hp_last : p = last
    · have hp_lift : GramSchmidt.liftFinLE p ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hp_last
      have hq_lift : GramSchmidt.liftFinLE q ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hq_last
      dsimp [GramSchmidt.scaledCoeffMatrix, Matrix.transpose, Matrix.col,
        Matrix.row, Matrix.ofFn]
      repeat rw [Vector.getElem_ofFn]
      rw [if_pos hq_val, if_pos (by simpa [last] using congrArg Fin.val hp_last),
        rowSwap_getRow_right_val_int]
      rw [show (GramSchmidt.liftFinLE (⟨p.val, hr⟩ : Fin t) _) = km1 by
        apply Fin.ext
        dsimp [GramSchmidt.liftFinLE]
        omega]
      rw [rowSwap_getRow_left_val_int]
      rw [show (GramSchmidt.liftFinLE (⟨q.val, hc⟩ : Fin t) _) = km1 by
        apply Fin.ext
        dsimp [GramSchmidt.liftFinLE]
        omega]
      exact dot_comm_int _ _
    · have hp_ne_km1 : (GramSchmidt.liftFinLE p ht).val ≠ km1.val := by
        intro h
        exact hp_last (Fin.ext (by simpa [last, GramSchmidt.liftFinLE] using h))
      have hq_lift : GramSchmidt.liftFinLE q ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hq_last
      have hp_val_ne : p.val ≠ km1.val := by
        intro h
        exact hp_last (Fin.ext (by simpa [last] using h))
      dsimp [GramSchmidt.scaledCoeffMatrix, Matrix.transpose, Matrix.col,
        Matrix.row, Matrix.ofFn]
      repeat rw [Vector.getElem_ofFn]
      rw [if_pos hq_val, if_neg hp_val_ne, rowSwap_getRow_right_val_int,
        rowSwap_getRow_eq_of_ne_val_int]
      · rw [show (GramSchmidt.liftFinLE q _) = km1 by
          apply Fin.ext
          dsimp [GramSchmidt.liftFinLE]
          omega]
        exact dot_comm_int _ _
      · dsimp [GramSchmidt.liftFinLE]
        omega
      · dsimp [GramSchmidt.liftFinLE]
        omega
  · have hq_ne_val : q.val ≠ km1.val := by
      intro h
      exact hq_last (Fin.ext (by simpa [last] using h))
    by_cases hp_last : p = last
    · have hp_val : p.val = km1.val := by
        simpa [last] using congrArg Fin.val hp_last
      have hp_lift : GramSchmidt.liftFinLE p ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hp_last
      have hq_ne_km1 : (GramSchmidt.liftFinLE q ht).val ≠ km1.val := by
        intro h
        exact hq_ne_val (by simpa [GramSchmidt.liftFinLE] using h)
      dsimp [GramSchmidt.scaledCoeffMatrix, Matrix.transpose, Matrix.col,
        Matrix.row, Matrix.ofFn]
      repeat rw [Vector.getElem_ofFn]
      rw [if_neg hq_ne_val, if_pos hp_val]
      rw [show (GramSchmidt.liftFinLE (⟨p.val, hr⟩ : Fin t) _) = km1 by
        apply Fin.ext
        dsimp [GramSchmidt.liftFinLE]
        omega]
      rw [rowSwap_getRow_left_val_int, rowSwap_getRow_eq_of_ne_val_int]
      · exact dot_comm_int _ _
      · dsimp [GramSchmidt.liftFinLE]
        omega
      · dsimp [GramSchmidt.liftFinLE]
        omega
    · have hp_ne_val : p.val ≠ km1.val := by
        intro h
        exact hp_last (Fin.ext (by simpa [last] using h))
      have hp_ne_km1 : (GramSchmidt.liftFinLE p ht).val ≠ km1.val := by
        intro h
        exact hp_ne_val (by simpa [GramSchmidt.liftFinLE] using h)
      have hq_ne_km1 : (GramSchmidt.liftFinLE q ht).val ≠ km1.val := by
        intro h
        exact hq_ne_val (by simpa [GramSchmidt.liftFinLE] using h)
      dsimp [GramSchmidt.scaledCoeffMatrix, Matrix.transpose, Matrix.col,
        Matrix.row, Matrix.ofFn]
      repeat rw [Vector.getElem_ofFn]
      rw [if_neg hq_ne_val, if_neg hp_ne_val, rowSwap_getRow_eq_of_ne_val_int]
      · rw [rowSwap_getRow_eq_of_ne_val_int]
        · exact dot_comm_int _ _
        · dsimp [GramSchmidt.liftFinLE]
          omega
        · dsimp [GramSchmidt.liftFinLE]
          omega
      · dsimp [GramSchmidt.liftFinLE]
        omega
      · dsimp [GramSchmidt.liftFinLE]
        omega

/-! ### Coefficient bordered minor and multilinearity entry equation

The `coeffBM` matrix shares its first `k` columns with `borderedMinor G k hk i j`
(those columns do not depend on `j`) and replaces the last column with the
indicator vector picking out row index `a`. The multilinearity entry equation
expands `Matrix.det (borderedMinor G k hk i j)` as a sum over `a` of
`Matrix.det (coeffBM G k hk i a) * G[a][j]`, applying `det_colReplace_sum_finRange`
to the indicator expansion of the last column. -/

/-- The coefficient bordered minor. Its first `k` columns match
`Matrix.borderedMinor G k hk i j` for any `j` (those columns are independent of
`j`), and its last column is the indicator vector for row index `a`. -/
private def coeffBM {n : Nat} (G : Matrix Int n n) (k : Nat) (hk : k < n)
    (i a : Fin n) : Matrix Int (k + 1) (k + 1) :=
  Matrix.ofFn fun r c =>
    let rr : Fin n :=
      if hr : r.val < k then ⟨r.val, Nat.lt_trans hr hk⟩
      else i
    if hc : c.val < k then
      let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
      G[(rr, cc)]
    else (if rr.val = a.val then (1 : Int) else (0 : Int))

end GramSchmidt.Int

namespace GramSchmidt.Rat

/-- The `k`-th Gram determinant for a rational input matrix.

This remains Mathlib-free API: it is the direct Hex determinant definition used
by rational Gram-Schmidt callers, not a theorem identifying an executable Hex
output with a Leibniz determinant. -/
@[expose]
def gramDet (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Rat :=
  Matrix.det (GramSchmidt.leadingGramMatrixRat b k hk)

end GramSchmidt.Rat
end Hex
