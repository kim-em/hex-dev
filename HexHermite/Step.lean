/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith
public import HexRowReduce.RowEchelon.Elementary

public section

/-!
Elementary two-row Hermite updates and accumulator operations.

The working matrix and every requested certificate follow the same schedule.
The form-only accumulator is `Unit`, so that path allocates no transform.
-/

namespace Hex.Matrix.Hermite

private theorem getElem_setRow (M : Matrix R n m) (dst r : Fin n)
    (v : Vector R m) (c : Fin m) :
    (M.setRow dst v)[r][c] = if r = dst then v[c] else M[r][c] := by
  by_cases h : r = dst
  · subst r
    rw [if_pos rfl, Matrix.setRow_get_self]
  · rw [if_neg h, Matrix.setRow_row_ne M dst r v h]

/-- Replace rows `i` and `k` by two simultaneous linear combinations. -/
@[expose]
def combineRows (M : Matrix Int n m) (i k : Fin n)
    (a b c d : Int) : Matrix Int n m :=
  let ri := Matrix.row M i
  let rk := Matrix.row M k
  let vi := Vector.ofFn fun j =>
    a * ri[j.val]'j.isLt + b * rk[j.val]'j.isLt
  if _h : i = k then
    M.setRow i vi
  else
    let vk := Vector.ofFn fun j =>
      c * ri[j.val]'j.isLt + d * rk[j.val]'j.isLt
    (M.setRow i vi).setRow k vk

/-- Entrywise characterization of `combineRows`. -/
@[simp, grind =]
theorem getElem_combineRows (M : Matrix Int n m) (i k r : Fin n)
    (j : Fin m) (a b c d : Int) :
    (combineRows M i k a b c d)[r][j] =
      if r = i then a * M[(i, j)] + b * M[(k, j)]
      else if r = k then c * M[(i, j)] + d * M[(k, j)]
      else M[(r, j)] := by
  unfold combineRows
  by_cases hik : i = k
  · rw [dif_pos hik, getElem_setRow]
    by_cases hr : r = k <;> simp [hik, hr, Matrix.row]
  · rw [dif_neg hik, getElem_setRow, getElem_setRow]
    by_cases hrk : r = k <;> by_cases hri : r = i <;> simp_all [Matrix.row]

/-- Replace columns `i` and `k` by two simultaneous linear combinations. -/
@[expose]
def combineCols (M : Matrix Int n m) (i k : Fin m)
    (a b c d : Int) : Matrix Int n m :=
  let ci := Vector.ofFn fun r => M[(r, i)]
  let ck := Vector.ofFn fun r => M[(r, k)]
  let vi := Vector.ofFn fun r =>
    a * ci[r.val]'r.isLt + b * ck[r.val]'r.isLt
  if h : i = k then
    M.setCol i fun r => vi[r.val]'r.isLt
  else
    let vk := Vector.ofFn fun r =>
      c * ci[r.val]'r.isLt + d * ck[r.val]'r.isLt
    (M.setCol i fun r => vi[r.val]'r.isLt).setCol k fun r => vk[r.val]'r.isLt

/-- Entrywise characterization of `combineCols`. -/
@[simp, grind =]
theorem getElem_combineCols (M : Matrix Int n m) (i k : Fin m)
    (r : Fin n) (j : Fin m)
    (a b c d : Int) :
    (combineCols M i k a b c d)[r][j] =
      if j = i then a * M[(r, i)] + b * M[(r, k)]
      else if j = k then c * M[(r, i)] + d * M[(r, k)]
      else M[(r, j)] := by
  unfold combineCols
  by_cases hik : i = k
  · rw [dif_pos hik, Matrix.getElem_setCol]
    by_cases hj : j = k <;>
      simp [hik, hj]
  · rw [dif_neg hik, Matrix.getElem_setCol, Matrix.getElem_setCol]
    by_cases hjk : j = k <;> by_cases hji : j = i <;>
      simp_all
/-- Simultaneous two-row replacement commutes with multiplication on the
right. -/
theorem combineRows_mul (A : Matrix Int n p) (B : Matrix Int p m)
    (i k : Fin n) (a b c d : Int) :
    combineRows A i k a b c d * B = combineRows (A * B) i k a b c d := by
  apply Matrix.ext_getElem
  intro r j
  rw [Matrix.getElem_mul]
  by_cases hri : r = i
  · subst r
    rw [show Matrix.row (combineRows A i k a b c d) i =
        a • Matrix.row A i + b • Matrix.row A k by
      ext q hq
      let qq : Fin p := ⟨q, hq⟩
      change (combineRows A i k a b c d)[i][qq] =
        (a • Matrix.row A i + b • Matrix.row A k)[qq]
      rw [getElem_combineRows]
      simp only [if_pos]
      rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested]
      simp only [Fin.getElem_fin, Vector.getElem_add, Vector.getElem_smul]
      rfl
      ]
    rw [Vector.dotProduct_add_left, Vector.dotProduct_smul_left,
      Vector.dotProduct_smul_left]
    rw [getElem_combineRows]
    simp only [if_pos, Matrix.getElem_pair_eq_nested]
    rw [Matrix.getElem_mul, Matrix.getElem_mul]
  · by_cases hrk : r = k
    · subst r
      rw [show Matrix.row (combineRows A i k a b c d) k =
          c • Matrix.row A i + d • Matrix.row A k by
        ext q hq
        let qq : Fin p := ⟨q, hq⟩
        change (combineRows A i k a b c d)[k][qq] =
          (c • Matrix.row A i + d • Matrix.row A k)[qq]
        rw [getElem_combineRows]
        simp only [if_neg hri, if_pos]
        rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested]
        simp only [Fin.getElem_fin, Vector.getElem_add, Vector.getElem_smul]
        rfl]
      rw [Vector.dotProduct_add_left, Vector.dotProduct_smul_left,
        Vector.dotProduct_smul_left]
      rw [getElem_combineRows]
      simp only [if_neg hri, if_pos, Matrix.getElem_pair_eq_nested]
      rw [Matrix.getElem_mul, Matrix.getElem_mul]
    · rw [show Matrix.row (combineRows A i k a b c d) r = Matrix.row A r by
        ext q hq
        let qq : Fin p := ⟨q, hq⟩
        change (combineRows A i k a b c d)[r][qq] = A[r][qq]
        rw [getElem_combineRows]
        simp [hri, hrk, Matrix.getElem_pair_eq_nested]]
      rw [getElem_combineRows]
      simp only [if_neg hri, if_neg hrk, Matrix.getElem_pair_eq_nested]
      exact (Matrix.getElem_mul A B r j).symm

/-- Transposition exchanges a simultaneous two-column replacement with the
same two-row replacement. -/
theorem transpose_combineCols (M : Matrix Int n m) (i k : Fin m)
    (a b c d : Int) :
    Matrix.transpose (combineCols M i k a b c d) =
      combineRows (Matrix.transpose M) i k a b c d := by
  apply Matrix.ext_getElem
  intro r j
  rw [Matrix.getElem_transpose]
  rw [getElem_combineCols, getElem_combineRows]
  simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_transpose]

/-- Simultaneous two-column replacement commutes with multiplication on the
left. -/
theorem mul_combineCols (A : Matrix Int p n) (B : Matrix Int n n) (i k : Fin n)
    (a b c d : Int) :
    A * combineCols B i k a b c d = combineCols (A * B) i k a b c d := by
  have ht :
      Matrix.transpose (A * combineCols B i k a b c d) =
        Matrix.transpose (combineCols (A * B) i k a b c d) := by
    calc
      Matrix.transpose (A * combineCols B i k a b c d) =
          Matrix.transpose (combineCols B i k a b c d) * Matrix.transpose A := by
            rw [Matrix.transpose_mul_of_mul_comm]
      _ = combineRows (Matrix.transpose B) i k a b c d * Matrix.transpose A := by
            rw [transpose_combineCols]
      _ = combineRows (Matrix.transpose B * Matrix.transpose A) i k a b c d := by
            rw [combineRows_mul]
      _ = combineRows (Matrix.transpose (A * B)) i k a b c d := by
            rw [Matrix.transpose_mul_of_mul_comm]
      _ = Matrix.transpose (combineCols (A * B) i k a b c d) := by
            rw [transpose_combineCols]
  have := congrArg Matrix.transpose ht
  simpa using this

theorem mul_colSwap (A : Matrix Int p n) (B : Matrix Int n n) (i k : Fin n) :
    A * Matrix.colSwap B i k = Matrix.colSwap (A * B) i k := by
  have ht : Matrix.transpose (A * Matrix.colSwap B i k) =
      Matrix.transpose (Matrix.colSwap (A * B) i k) := by
    calc
      Matrix.transpose (A * Matrix.colSwap B i k) =
          Matrix.transpose (Matrix.colSwap B i k) * Matrix.transpose A := by
            rw [Matrix.transpose_mul_of_mul_comm]
      _ = Matrix.rowSwap (Matrix.transpose B) i k * Matrix.transpose A := by
            rw [Matrix.transpose_colSwap]
      _ = Matrix.rowSwap (Matrix.transpose B * Matrix.transpose A) i k := by
            rw [Matrix.rowSwap_mul]
      _ = Matrix.rowSwap (Matrix.transpose (A * B)) i k := by
            rw [Matrix.transpose_mul_of_mul_comm]
      _ = Matrix.transpose (Matrix.colSwap (A * B) i k) := by
            rw [Matrix.transpose_colSwap]
  have := congrArg Matrix.transpose ht
  simpa using this

theorem mul_colScale (A : Matrix Int p n) (B : Matrix Int n n) (i : Fin n) (c : Int) :
    A * Matrix.colScale B i c = Matrix.colScale (A * B) i c := by
  have ht : Matrix.transpose (A * Matrix.colScale B i c) =
      Matrix.transpose (Matrix.colScale (A * B) i c) := by
    calc
      Matrix.transpose (A * Matrix.colScale B i c) =
          Matrix.transpose (Matrix.colScale B i c) * Matrix.transpose A := by
            rw [Matrix.transpose_mul_of_mul_comm]
      _ = Matrix.rowScale (Matrix.transpose B) i c * Matrix.transpose A := by
            rw [Matrix.transpose_colScale]
      _ = Matrix.rowScale (Matrix.transpose B * Matrix.transpose A) i c := by
            rw [Matrix.rowScale_mul]
      _ = Matrix.rowScale (Matrix.transpose (A * B)) i c := by
            rw [Matrix.transpose_mul_of_mul_comm]
      _ = Matrix.transpose (Matrix.colScale (A * B) i c) := by
            rw [Matrix.transpose_colScale]
  have := congrArg Matrix.transpose ht
  simpa using this

theorem swap_inverse_identity (i k : Fin n) :
    Matrix.rowSwap (Matrix.colSwap (Matrix.identity (R := Int) n) i k) i k =
      Matrix.identity n := by
  apply Matrix.ext_getElem
  intro r j
  simp only [Matrix.getElem_rowSwap, Matrix.getElem_colSwap,
    Matrix.getElem_identity]
  by_cases hri : r = i <;> by_cases hrk : r = k <;>
    by_cases hji : j = i <;> by_cases hjk : j = k <;> simp_all [eq_comm]

theorem negate_inverse_identity (i : Fin n) :
    Matrix.rowScale (Matrix.colScale (Matrix.identity (R := Int) n) i (-1))
      i (-1) = Matrix.identity n := by
  apply Matrix.ext_getElem
  intro r j
  simp only [Matrix.getElem_rowScale, Matrix.getElem_colScale,
    Matrix.getElem_identity]
  by_cases hri : r = i <;> by_cases hji : j = i <;> simp_all [eq_comm]

theorem add_inverse_identity (src dst : Fin n) (h : src ≠ dst) (c : Int) :
    Matrix.rowAdd (Matrix.colAdd (Matrix.identity (R := Int) n)
      dst src (-c)) src dst c = Matrix.identity n := by
  apply Matrix.ext_getElem
  intro r j
  simp only [Matrix.getElem_rowAdd, Matrix.getElem_colAdd,
    Matrix.getElem_identity]
  by_cases hrd : r = dst <;> by_cases hrs : r = src <;>
    by_cases hjs : j = src <;> by_cases hjd : j = dst <;>
    simp_all <;> grind

/-- A determinant-one two-row replacement followed on the right by its
two-column inverse fixes the identity matrix. -/
theorem combine_inverse_identity (i k : Fin n) (hik : i ≠ k)
    (a b c d : Int) (hdet : a * d - b * c = 1) :
    combineRows (combineCols (Matrix.identity (R := Int) n)
      i k d (-c) (-b) a) i k a b c d = Matrix.identity n := by
  apply Matrix.ext_getElem
  intro r j
  rw [getElem_combineRows]
  simp only [Matrix.getElem_pair_eq_nested, getElem_combineCols,
    Matrix.getElem_identity]
  by_cases hri : r = i <;> by_cases hrk : r = k <;>
    by_cases hji : j = i <;> by_cases hjk : j = k <;>
    simp_all <;> grind

/-- Operations performed on a companion accumulator by the Hermite sweep. -/
structure Accumulator (α : Type) (n : Nat) where
  init : α
  swap : α → Fin n → Fin n → α
  combine : α → Fin n → Fin n → Int → Int → Int → Int → α
  negate : α → Fin n → α
  add : α → Fin n → Fin n → Int → α

/-- The form-only accumulator. -/
@[expose]
def formAccumulator (n : Nat) : Accumulator Unit n where
  init := ()
  swap acc _ _ := acc
  combine acc _ _ _ _ _ _ := acc
  negate acc _ := acc
  add acc _ _ _ := acc

/-- Accumulator for the left transform `U`. -/
@[expose]
def transformAccumulator (n : Nat) : Accumulator (Matrix Int n n) n where
  init := Matrix.identity n
  swap U i k := Matrix.rowSwap U i k
  combine U i k a b c d := combineRows U i k a b c d
  negate U i := Matrix.rowScale U i (-1)
  add U src dst c := Matrix.rowAdd U src dst c

/-- Transform and explicitly accumulated inverse transform. -/
structure TransformPair (n : Nat) where
  transform : Matrix Int n n
  inverse : Matrix Int n n

/-- Accumulator for `(U, W)` with `W = U⁻¹`. -/
@[expose]
def inverseAccumulator (n : Nat) : Accumulator (TransformPair n) n where
  init := ⟨Matrix.identity n, Matrix.identity n⟩
  swap acc i k :=
    ⟨Matrix.rowSwap acc.transform i k, Matrix.colSwap acc.inverse i k⟩
  combine acc i k a b c d :=
    -- The caller supplies `[[a,b],[c,d]]` with determinant one. Its inverse is
    -- `[[d,-b],[-c,a]]`, and right multiplication updates columns.
    ⟨combineRows acc.transform i k a b c d,
      combineCols acc.inverse i k d (-c) (-b) a⟩
  negate acc i :=
    ⟨Matrix.rowScale acc.transform i (-1), Matrix.colScale acc.inverse i (-1)⟩
  add acc src dst c :=
    ⟨Matrix.rowAdd acc.transform src dst c,
      Matrix.colAdd acc.inverse dst src (-c)⟩

/-- Extended-GCD elimination of the entry in row `k`, using pivot row `i`.
The four returned coefficients form a determinant-one two-row update. -/
@[expose]
def gcdCoeffs (a b : Int) : Int × Int × Int × Int :=
  let (g, s, t) := HexArith.Int.extGcd a b
  let g' : Int := Int.ofNat g
  let qa := HexArith.Int.exactDiv a g'
  let qb := HexArith.Int.exactDiv b g'
  (s, t, -qb, qa)

/-- When the eliminated entry is nonzero, `gcdCoeffs` returns a
determinant-one update. -/
theorem gcdCoeffs_det {a b : Int} (hb : b ≠ 0) :
    let (x, y, z, w) := gcdCoeffs a b
    x * w - y * z = 1 := by
  rcases he : HexArith.Int.extGcd a b with ⟨g, s, t⟩
  have hspec := HexArith.Int.extGcd_spec a b
  rw [he] at hspec
  simp only at hspec
  rcases hspec with ⟨hg, hbez⟩
  have hga : (Int.ofNat g) ∣ a := by
    rw [hg]
    exact Int.gcd_dvd_left a b
  have hgb : (Int.ofNat g) ∣ b := by
    rw [hg]
    exact Int.gcd_dvd_right a b
  have hg0 : Int.ofNat g ≠ 0 := by
    intro hzero
    rcases hgb with ⟨q, hq⟩
    rw [hzero, Int.zero_mul] at hq
    exact hb hq
  have hqa : HexArith.Int.exactDiv a (Int.ofNat g) * Int.ofNat g = a := by
    simpa [HexArith.Int.exactDiv] using Int.ediv_mul_cancel hga
  have hqb : HexArith.Int.exactDiv b (Int.ofNat g) * Int.ofNat g = b := by
    simpa [HexArith.Int.exactDiv] using Int.ediv_mul_cancel hgb
  unfold gcdCoeffs
  rw [he]
  dsimp only
  simp only [Int.mul_neg, Int.sub_neg]
  apply Int.eq_of_mul_eq_mul_right hg0
  calc
    (s * HexArith.Int.exactDiv a (Int.ofNat g) +
        t * HexArith.Int.exactDiv b (Int.ofNat g)) * Int.ofNat g =
        s * a + t * b := by rw [Int.add_mul, Int.mul_assoc, hqa,
          Int.mul_assoc, hqb]
    _ = Int.ofNat g := by simpa [hg] using hbez
    _ = 1 * Int.ofNat g := by rw [Int.one_mul]

/-- The extended-GCD row update replaces `(a,b)` by a positive gcd and zero. -/
theorem gcdCoeffs_apply {a b : Int} (hb : b ≠ 0) :
    let (x, y, z, w) := gcdCoeffs a b
    0 < x * a + y * b ∧ z * a + w * b = 0 := by
  rcases he : HexArith.Int.extGcd a b with ⟨g, s, t⟩
  have hspec := HexArith.Int.extGcd_spec a b
  rw [he] at hspec
  simp only at hspec
  rcases hspec with ⟨hg, hbez⟩
  have hga : (Int.ofNat g) ∣ a := by
    rw [hg]
    exact Int.gcd_dvd_left a b
  have hgb : (Int.ofNat g) ∣ b := by
    rw [hg]
    exact Int.gcd_dvd_right a b
  have hgpos : 0 < Int.ofNat g := by
    apply Int.ofNat_lt.mpr
    rw [hg]
    exact Int.gcd_pos_of_ne_zero_right a hb
  have hqa : HexArith.Int.exactDiv a (Int.ofNat g) * Int.ofNat g = a := by
    simpa [HexArith.Int.exactDiv] using Int.ediv_mul_cancel hga
  have hqb : HexArith.Int.exactDiv b (Int.ofNat g) * Int.ofNat g = b := by
    simpa [HexArith.Int.exactDiv] using Int.ediv_mul_cancel hgb
  unfold gcdCoeffs
  rw [he]
  dsimp only
  constructor
  · rw [hbez]
    exact hgpos
  · rw [Int.neg_mul]
    apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hgpos)
    rw [Int.add_mul]
    have hleft :
        (-(HexArith.Int.exactDiv b (Int.ofNat g) * a)) * Int.ofNat g =
          -(HexArith.Int.exactDiv b (Int.ofNat g) * Int.ofNat g) * a := by
      simp only [Int.neg_mul]
      ac_rfl
    have hright :
        (HexArith.Int.exactDiv a (Int.ofNat g) * b) * Int.ofNat g =
          (HexArith.Int.exactDiv a (Int.ofNat g) * Int.ofNat g) * b := by
      ac_rfl
    rw [hleft, hright, hqb, hqa]
    rw [show -b * a = a * -b by simp [Int.mul_comm]]
    simp only [Int.zero_mul, Int.mul_neg]
    omega

/-- The pivot combination returned by `gcdCoeffs` is the canonical positive
integer gcd, not merely an unspecified positive associate. -/
theorem gcdCoeffs_pivot (a b : Int) :
    let (x, y, _z, _w) := gcdCoeffs a b
    x * a + y * b = Int.ofNat (Int.gcd a b) := by
  rcases he : HexArith.Int.extGcd a b with ⟨g, s, t⟩
  have hspec := HexArith.Int.extGcd_spec a b
  rw [he] at hspec
  simp only at hspec
  rcases hspec with ⟨hg, hbez⟩
  unfold gcdCoeffs
  rw [he]
  dsimp only
  rw [hbez, hg]
  rfl

end Hex.Matrix.Hermite
