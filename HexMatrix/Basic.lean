import Batteries.Data.List.Lemmas

/-!
Core dense matrix definitions for `hex-matrix`.

This module models matrices as `Vector (Vector R m) n` and provides the
basic executable operations needed by later linear-algebra algorithms:
row/column accessors, zero and identity matrices, dot products,
matrix-vector multiplication, matrix-matrix multiplication, and norm-squared
helpers.
-/
namespace Hex

universe u

/-- Dense `n × m` matrices over `R`, represented as vectors of rows. -/
abbrev Matrix (R : Type u) (n m : Nat) := Vector (Vector R m) n

namespace Vector

/-- Dot product of two vectors. -/
def dotProduct [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  (List.finRange n).foldl (fun acc i => acc + u[i] * v[i]) 0

private theorem foldl_dotProduct_sub_smul_rat
    (xs : List (Fin n)) (u v w : Vector Rat n) (c accU accV : Rat) :
    xs.foldl (fun acc i => acc + (u - c • v)[i] * w[i]) (accU - c * accV) =
      xs.foldl (fun acc i => acc + u[i] * w[i]) accU -
        c * xs.foldl (fun acc i => acc + v[i] * w[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp
  | cons i xs ih =>
      have hstart :
          accU - c * accV + (u - c • v)[i] * w[i] =
            (accU + u[i] * w[i]) - c * (accV + v[i] * w[i]) := by
        have hentry : (u - c • v)[i] = u[i] - c * v[i] := by
          change (u - c • v)[i.val] = u[i.val] - c * v[i.val]
          rw [Vector.getElem_sub, Vector.getElem_smul]
          rfl
        rw [hentry]
        grind
      simp only [List.foldl_cons]
      rw [hstart]
      exact ih (accU := accU + u[i] * w[i]) (accV := accV + v[i] * w[i])

/-- Dot product distributes over subtracting a scalar multiple in the left argument. -/
theorem dotProduct_sub_smul_rat (u v w : Vector Rat n) (c : Rat) :
    dotProduct (u - c • v) w = dotProduct u w - c * dotProduct v w := by
  have hzero : (0 : Rat) - 0 = 0 := by
    grind
  simpa [dotProduct, hzero] using
    foldl_dotProduct_sub_smul_rat (xs := List.finRange n) (u := u) (v := v) (w := w)
      (c := c) (accU := 0) (accV := 0)

/-- Zero specialization of `dotProduct_sub_smul`. -/
theorem dotProduct_sub_smul_eq_zero_rat (u v w : Vector Rat n) (c : Rat)
    (h : dotProduct u w = c * dotProduct v w) :
    dotProduct (u - c • v) w = 0 := by
  rw [dotProduct_sub_smul_rat, h]
  grind

/-- Squared Euclidean norm of a vector. -/
def normSq [Mul R] [Add R] [OfNat R 0] (v : Vector R n) : R :=
  dotProduct v v

/-- Squared Euclidean norm specialized to integer vectors. -/
def intNormSq (v : Vector Int n) : Int :=
  normSq v

/-- Squared Euclidean norm specialized to rational vectors. -/
def ratNormSq (v : Vector Rat n) : Rat :=
  normSq v

end Vector

namespace Matrix

/-- Build a matrix from an entry function. -/
def ofFn (f : Fin n → Fin m → R) : Matrix R n m :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

/-- Entry access for a matrix built from an entry function. -/
@[grind =] theorem getElem_ofFn (f : Fin n → Fin m → R) (i : Fin n) (j : Fin m) :
    (ofFn f)[i][j] = f i j := by
  simp [ofFn]

/-- The `i`-th row of a matrix. -/
def row (M : Matrix R n m) (i : Fin n) : Vector R m :=
  M[i]

/-- Entry access for a selected matrix row. -/
@[grind =] theorem row_getElem (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    (row M i)[j] = M[i][j] := by
  rfl

/-- The `j`-th column of a matrix. -/
def col (M : Matrix R n m) (j : Fin m) : Vector R n :=
  Vector.ofFn fun i => M[i][j]

/-- Entry access for a selected matrix column. -/
@[grind =] theorem col_getElem (M : Matrix R n m) (j : Fin m) (i : Fin n) :
    (col M j)[i] = M[i][j] := by
  simp [col]

/-- The transpose of a dense matrix. -/
def transpose (M : Matrix R n m) : Matrix R m n :=
  Vector.ofFn fun j => col M j

/-- Entry access for the transpose of a dense matrix. -/
@[grind =] theorem transpose_getElem (M : Matrix R n m) (i : Fin m) (j : Fin n) :
    (transpose M)[i][j] = M[j][i] := by
  simp [transpose, col]

/-- Transposing a dense matrix twice returns the original matrix. -/
@[simp, grind =] theorem transpose_transpose (M : Matrix R n m) :
    transpose (transpose M) = M := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin m := ⟨j, hj⟩
  show (transpose (transpose M))[ii][jj] = M[ii][jj]
  rw [transpose_getElem, transpose_getElem]

/-- The all-zero matrix. -/
protected def zero [OfNat R 0] : Matrix R n m :=
  ofFn fun _ _ => 0

instance [OfNat R 0] : Zero (Matrix R n m) where
  zero := Matrix.zero

/-- The identity matrix. -/
protected def identity [OfNat R 0] [OfNat R 1] : Matrix R n n :=
  ofFn fun i j => if i = j then 1 else 0

instance [OfNat R 0] [OfNat R 1] : One (Matrix R n n) where
  one := Matrix.identity

/-- Dot product of two vectors. -/
def dot [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  Hex.Vector.dotProduct u v

/-- Dot product distributes over subtracting a scalar multiple in the left argument. -/
theorem dot_sub_smul_rat (u v w : Vector Rat n) (c : Rat) :
    dot (u - c • v) w = dot u w - c * dot v w := by
  simpa [dot] using Hex.Vector.dotProduct_sub_smul_rat (u := u) (v := v) (w := w) (c := c)

/-- Zero specialization of `dot_sub_smul`. -/
theorem dot_sub_smul_eq_zero_rat (u v w : Vector Rat n) (c : Rat)
    (h : dot u w = c * dot v w) :
    dot (u - c • v) w = 0 := by
  rw [dot_sub_smul_rat, h]
  grind

/-- Multiply a matrix by a column vector. -/
def mulVec [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (v : Vector R m) :
    Vector R n :=
  Vector.ofFn fun i => dot (row M i) v

/-- Multiply two matrices. -/
def mul [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  ofFn fun i j => dot (row M i) (col N j)

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Vector R m) (Vector R n) where
  hMul := mulVec

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Matrix R m k) (Matrix R n k) where
  hMul := mul

/-- Entry characterization for matrix-vector multiplication. -/
@[grind =] theorem mulVec_getElem [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (v : Vector R m) (i : Fin n) :
    (M * v)[i] = dot (row M i) v := by
  show (mulVec M v)[i] = dot (row M i) v
  simp [mulVec]

/-- Entry characterization for matrix multiplication. -/
@[grind =] theorem mul_getElem [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (i : Fin n) (j : Fin k) :
    (M * N)[i][j] = dot (row M i) (col N j) := by
  show (mul M N)[i][j] = dot (row M i) (col N j)
  rw [mul, getElem_ofFn]

/-- A left fold `xs.foldl (· + f ·) acc` leaves the accumulator unchanged when `f`
vanishes on every element of `xs`; the base case for collapsing zero summands in the
fold-sum algebra. -/
private theorem foldl_add_eq_acc_ring {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R)
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
      have hac : acc + (0 : R) = acc := by grind
      rw [hac]
      exact ih acc hxs

/-- `xs.foldl (· + f ·) acc` splits as `acc + xs.foldl (· + f ·) 0`, pulling the running
accumulator out so a fold-sum can always be taken from a `0` start. -/
private theorem foldl_sum_start {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R) :
    xs.foldl (fun acc x => acc + f x) acc =
      acc + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
      grind
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x)]
      rw [ih (acc := (0 : R) + f x)]
      grind

/-- Two fold-sums over `xs` agree when their summand functions `f` and `g` agree
pointwise on `xs`; congruence for the fold-sum under the integrand. -/
private theorem foldl_sum_congr {R : Type u} [Add R]
    {α : Type v} (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      exact ih (acc + g x) hxs

/-- The fold-sum of a pointwise sum `f x + g x` equals the sum of the two separate
fold-sums; additivity of the fold-sum over its summand. -/
private theorem foldl_sum_add {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f g : α → R) :
    xs.foldl (fun acc x => acc + (f x + g x)) 0 =
      xs.foldl (fun acc x => acc + f x) 0 +
        xs.foldl (fun acc x => acc + g x) 0 := by
  induction xs with
  | nil =>
      simp
      grind
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [foldl_sum_start xs (fun x => f x + g x) (0 + (f x + g x))]
      rw [foldl_sum_start xs f (0 + f x)]
      rw [foldl_sum_start xs g (0 + g x)]
      rw [ih]
      grind

/-- A double fold-sum may exchange the order of its outer and inner index lists `xs` and
`ys`; the Fubini swap for fold-sums used to transpose iterated matrix sums. -/
private theorem foldl_sum_comm {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} {β : Type w} (xs : List α) (ys : List β) (g : α → β → R) :
    xs.foldl (fun acc x => acc + ys.foldl (fun acc y => acc + g x y) 0) 0 =
      ys.foldl (fun acc y => acc + xs.foldl (fun acc x => acc + g x y) 0) 0 := by
  induction xs with
  | nil =>
      symm
      apply foldl_add_eq_acc_ring
      intro y _hy
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [foldl_sum_start xs (fun x => ys.foldl (fun acc y => acc + g x y) 0)
        (0 + ys.foldl (fun acc y => acc + g x y) 0)]
      rw [ih]
      have hinner :
          ys.foldl
              (fun acc y =>
                acc + xs.foldl (fun acc x' => acc + g x' y) (0 + g x y)) 0 =
            ys.foldl
              (fun acc y =>
                acc + (g x y + xs.foldl (fun acc x' => acc + g x' y) 0)) 0 := by
        apply foldl_sum_congr
        intro y _hy
        rw [foldl_sum_start xs (fun x' => g x' y) (0 + g x y)]
        grind
      rw [hinner]
      rw [foldl_sum_add]
      grind

/-- Right multiplication by `c` distributes through a fold-sum, scaling each summand `f x`
to `f x * c`. -/
private theorem foldl_sum_mul_right {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (c acc : R) :
    xs.foldl (fun acc x => acc + f x) acc * c =
      xs.foldl (fun acc x => acc + f x * c) (acc * c) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x)]
      have hdist : (acc + f x) * c = acc * c + f x * c := by grind
      rw [hdist]

/-- Left multiplication by `c` distributes through a fold-sum, scaling each summand `f x`
to `c * f x`. -/
private theorem foldl_sum_mul_left {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (c acc : R) :
    c * xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + c * f x) (c * acc) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x)]
      have hdist : c * (acc + f x) = c * acc + c * f x := by grind
      rw [hdist]

/-- The fold-sum of a pointwise difference `f x - g x` equals the difference of the two
separate fold-sums. -/
private theorem foldl_sum_sub {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f g : α → R) (accF accG : R) :
    xs.foldl (fun acc x => acc + (f x - g x)) (accF - accG) =
      xs.foldl (fun acc x => acc + f x) accF -
        xs.foldl (fun acc x => acc + g x) accG := by
  induction xs generalizing accF accG with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hstep :
          accF - accG + (f x - g x) =
            (accF + f x) - (accG + g x) := by
        grind
      rw [hstep]
      exact ih (accF := accF + f x) (accG := accG + g x)

/-- Folding the indicator-weighted terms `(if i = l then 1 else 0) * f l` over a
duplicate-free list containing `i` picks out exactly `f i`, adding it to the accumulator;
the selection step behind reading a single matrix entry out of a sum. -/
private theorem foldl_indicator_mul_unique {R : Type u} [Lean.Grind.Ring R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n) (f : Fin n → R)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : R) :
    xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0) * f l) acc =
      acc + f i := by
  induction xs generalizing acc with
  | nil =>
      exact absurd hi List.not_mem_nil
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hieq | hitail
      · subst i
        have hxs_zero :
            ∀ y ∈ xs, (if x = y then (1 : R) else 0) * f y = 0 := by
          intro y hy
          have hxy : x ≠ y := fun heq => (List.nodup_cons.mp hnodup).1 (heq ▸ hy)
          rw [if_neg hxy]
          grind
        rw [if_pos rfl]
        rw [foldl_add_eq_acc_ring xs _ _ hxs_zero]
        grind
      · have hxi : i ≠ x := by
          intro heq
          rw [← heq] at hnodup
          exact (List.nodup_cons.mp hnodup).1 hitail
        rw [if_neg hxi]
        have hzero : (0 : R) * f x = 0 := by grind
        rw [hzero]
        have hac : acc + (0 : R) = acc := by grind
        rw [hac]
        exact ih hitail (List.nodup_cons.mp hnodup).2 acc

/-- Matrix multiplication associates with matrix-vector multiplication. -/
theorem mul_assoc_vec [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (v : Vector R k) :
    (A * B) * v = A * (B * v) := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, mul, dot, row, col, Hex.Vector.dotProduct, ofFn]
  change
    (List.finRange k).foldl
        (fun acc l =>
          acc + (List.finRange m).foldl (fun acc j => acc + A[ii][j] * B[j][l]) 0 *
            v[l]) 0 =
      (List.finRange m).foldl
        (fun acc j =>
          acc + A[ii][j] *
            (List.finRange k).foldl (fun acc l => acc + B[j][l] * v[l]) 0) 0
  calc
    (List.finRange k).foldl
        (fun acc l =>
          acc + (List.finRange m).foldl (fun acc j => acc + A[ii][j] * B[j][l]) 0 *
            v[l]) 0 =
        (List.finRange k).foldl
          (fun acc l =>
            acc + (List.finRange m).foldl
              (fun acc j => acc + A[ii][j] * B[j][l] * v[l]) 0) 0 := by
          apply foldl_sum_congr
          intro l _hl
          rw [foldl_sum_mul_right]
          grind
    _ = (List.finRange m).foldl
        (fun acc j =>
          acc + A[ii][j] *
            (List.finRange k).foldl (fun acc l => acc + B[j][l] * v[l]) 0) 0 := by
          rw [foldl_sum_comm]
          apply foldl_sum_congr
          intro j _hj
          rw [foldl_sum_mul_left]
          have hzero : A[ii][j] * (0 : R) = 0 := by grind
          rw [hzero]
          apply foldl_sum_congr
          intro l _hl
          grind

/-- Transpose reverses matrix multiplication over a commutative coefficient type. -/
theorem transpose_mul_of_mul_comm [Lean.Grind.Ring R]
    (hmul_comm : ∀ a b : R, a * b = b * a)
    (A : Matrix R n m) (B : Matrix R m k) :
    Matrix.transpose (A * B) = Matrix.transpose B * Matrix.transpose A := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin k := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (Matrix.transpose (A * B))[ii][jj] = (Matrix.transpose B * Matrix.transpose A)[ii][jj]
  rw [transpose_getElem]
  change (A * B)[jj][ii] = (Matrix.transpose B * Matrix.transpose A)[ii][jj]
  simp [HMul.hMul, mul, dot, row, col, transpose, Hex.Vector.dotProduct, ofFn]
  change
    (List.finRange m).foldl (fun acc l => acc + A[jj][l] * B[l][ii]) 0 =
      (List.finRange m).foldl (fun acc l => acc + B[l][ii] * A[jj][l]) 0
  apply foldl_sum_congr
  intro l _hl
  rw [hmul_comm]

/-- Left-multiplication by the identity matrix leaves a vector unchanged. -/
@[simp, grind =] theorem one_mulVec [Lean.Grind.Ring R] (v : Vector R n) :
    (1 : Matrix R n n) * v = v := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, dot, row, Hex.Vector.dotProduct]
  change (List.finRange n).foldl
      (fun acc j => acc + (1 : Matrix R n n)[ii][j] * v[j]) 0 =
    v[ii]
  calc
    (List.finRange n).foldl
        (fun acc j => acc + (1 : Matrix R n n)[ii][j] * v[j]) 0 =
        (List.finRange n).foldl
          (fun acc j => acc + (if ii = j then (1 : R) else 0) * v[j]) 0 := by
          apply foldl_sum_congr
          intro j _hj
          simp [show (1 : Matrix R n n) = Matrix.identity from rfl, Matrix.identity, ofFn]
    _ = v[ii] := by
          rw [foldl_indicator_mul_unique (List.finRange n) ii (fun j => v[j])
            (List.mem_finRange _) (List.nodup_finRange n) 0]
          grind

/-- Left-multiplication by the identity matrix leaves a matrix unchanged. -/
@[simp, grind =] theorem one_mul [Lean.Grind.Ring R] (M : Matrix R n m) :
    (1 : Matrix R n n) * M = M := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin m := ⟨j, hj⟩
  change ((1 : Matrix R n n) * M)[ii][jj] = M[ii][jj]
  simp [HMul.hMul, mul, dot, row, col, Hex.Vector.dotProduct]
  simp [ofFn]
  change
    (List.finRange n).foldl
        (fun acc l => acc + (1 : Matrix R n n)[ii][l] * M[l][jj]) 0 =
      M[ii][jj]
  calc
    (List.finRange n).foldl
        (fun acc l => acc + (1 : Matrix R n n)[ii][l] * M[l][jj]) 0 =
        (List.finRange n).foldl
          (fun acc l => acc + (if ii = l then (1 : R) else 0) * M[l][jj]) 0 := by
          apply foldl_sum_congr
          intro l _hl
          simp [show (1 : Matrix R n n) = Matrix.identity from rfl, Matrix.identity, ofFn]
    _ = M[ii][jj] := by
          rw [foldl_indicator_mul_unique (List.finRange n) ii (fun l => M[l][jj])
            (List.mem_finRange _) (List.nodup_finRange n) 0]
          grind

/-- Right-multiplication by the identity matrix leaves a matrix unchanged. -/
@[simp, grind =] theorem mul_one [Lean.Grind.Ring R] (M : Matrix R n m) :
    M * (1 : Matrix R m m) = M := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin m := ⟨j, hj⟩
  change (M * (1 : Matrix R m m))[ii][jj] = M[ii][jj]
  simp [HMul.hMul, mul, dot, row, col, Hex.Vector.dotProduct]
  simp [ofFn]
  change
    (List.finRange m).foldl
        (fun acc l => acc + M[ii][l] * (1 : Matrix R m m)[l][jj]) 0 =
      M[ii][jj]
  calc
    (List.finRange m).foldl
        (fun acc l => acc + M[ii][l] * (1 : Matrix R m m)[l][jj]) 0 =
        (List.finRange m).foldl
          (fun acc l => acc + (if jj = l then (1 : R) else 0) * M[ii][l]) 0 := by
          apply foldl_sum_congr
          intro l _hl
          simp [show (1 : Matrix R m m) = Matrix.identity from rfl, Matrix.identity, ofFn]
          split <;> grind
    _ = M[ii][jj] := by
          rw [foldl_indicator_mul_unique (List.finRange m) jj (fun l => M[ii][l])
            (List.mem_finRange _) (List.nodup_finRange m) 0]
          grind

/-- Matrix multiplication is associative. -/
theorem mul_assoc [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (C : Matrix R k l) :
    (A * B) * C = A * (B * C) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin l := ⟨j, hj⟩
  change ((A * B) * C)[ii][jj] = (A * (B * C))[ii][jj]
  simpa [HMul.hMul, mulVec, mul, dot, row, col, Hex.Vector.dotProduct, ofFn] using
    congrArg (fun v => v[ii]) (mul_assoc_vec A B (col C jj))

/-- Matrix-vector multiplication sends the zero vector to the zero vector. -/
@[simp, grind =] theorem mulVec_zero [Lean.Grind.Ring R] (A : Matrix R n m) :
    A * (0 : Vector R m) = 0 := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, dot, row, Hex.Vector.dotProduct]
  change (List.finRange m).foldl (fun acc j => acc + A[ii][j] * (0 : R)) 0 = 0
  apply foldl_add_eq_acc_ring
  intro j _hj
  grind

/-- The zero matrix sends every vector to the zero vector. -/
@[simp, grind =] theorem zero_mulVec [Lean.Grind.Ring R] (v : Vector R m) :
    (0 : Matrix R n m) * v = 0 := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, dot, row, Hex.Vector.dotProduct]
  change (List.finRange m).foldl (fun acc j => acc + (0 : Matrix R n m)[ii][j] * v[j]) 0 = 0
  apply foldl_add_eq_acc_ring
  intro j _hj
  change (Matrix.zero : Matrix R n m)[ii][j] * v[j] = 0
  simpa [Matrix.zero, ofFn] using Lean.Grind.Semiring.zero_mul v[j]

/-- Multiplication by `Q - I`, expressed entrywise, is `Q * v - v`. -/
theorem sub_identity_mulVec [Lean.Grind.Ring R] (Q : Matrix R n n) (v : Vector R n) :
    @mulVec R n n inferInstance inferInstance inferInstance
        (ofFn fun i j => Q[i][j] - if i = j then 1 else 0) v =
      @mulVec R n n inferInstance inferInstance inferInstance Q v - v := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [mulVec, dot, row, Hex.Vector.dotProduct, ofFn]
  change
    (List.finRange n).foldl
        (fun acc j => acc + (Q[ii][j] - if ii = j then 1 else 0) * v[j]) 0 =
      (List.finRange n).foldl (fun acc j => acc + Q[ii][j] * v[j]) 0 - v[ii]
  calc
    (List.finRange n).foldl
        (fun acc j => acc + (Q[ii][j] - if ii = j then 1 else 0) * v[j]) 0 =
        (List.finRange n).foldl
          (fun acc j => acc + (Q[ii][j] * v[j] - (if ii = j then 1 else 0) * v[j]))
          ((0 : R) - 0) := by
          have hzero : (0 : R) - 0 = 0 := by grind
          rw [hzero]
          apply foldl_sum_congr
          intro j _hj
          grind
    _ = (List.finRange n).foldl (fun acc j => acc + Q[ii][j] * v[j]) 0 -
          (List.finRange n).foldl
            (fun acc j => acc + (if ii = j then 1 else 0) * v[j]) 0 := by
          rw [foldl_sum_sub]
    _ = (List.finRange n).foldl (fun acc j => acc + Q[ii][j] * v[j]) 0 - v[ii] := by
          rw [foldl_indicator_mul_unique (List.finRange n) ii (fun j => v[j])
            (List.mem_finRange _) (List.nodup_finRange n) 0]
          grind

/-- Squared Euclidean norm of a vector. -/
def normSq [Mul R] [Add R] [OfNat R 0] (v : Vector R n) : R :=
  Hex.Vector.normSq v

/-- Squared Euclidean norm specialized to integer vectors. -/
def intNormSq (v : Vector Int n) : Int :=
  Hex.Vector.intNormSq v

/-- Squared Euclidean norm specialized to rational vectors. -/
def ratNormSq (v : Vector Rat n) : Rat :=
  Hex.Vector.ratNormSq v

/-- Gram matrix of the rows of a dense matrix. -/
def gramMatrix [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) : Matrix R n n :=
  ofFn fun i j => Hex.Vector.dotProduct (row M i) (row M j)

/-- Entry characterization for the Gram matrix of the rows of a dense matrix. -/
@[grind =] theorem gramMatrix_getElem [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (i j : Fin n) :
    (gramMatrix M)[i][j] = Hex.Vector.dotProduct (row M i) (row M j) := by
  rw [gramMatrix, getElem_ofFn]

/-- Leading principal `(k + 1) × (k + 1)` submatrix of a square matrix. -/
def submatrix (M : Matrix R n n) (k : Fin n) : Matrix R (k.val + 1) (k.val + 1) :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt k.isLt)⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
    M[ii][jj]

/-- Leading principal `k × k` prefix of a square matrix. This variant includes
the empty prefix and is convenient for Bareiss pivot/minor statements. -/
def leadingPrefix (M : Matrix R n n) (k : Nat) (hk : k ≤ n) : Matrix R k k :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    M[ii][jj]

/-- The first `k` rows of a matrix, retaining all source columns. -/
def leadingRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n) : Matrix R k m :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    M[ii][j]

/-- Entry formula for the `k × k` leading prefix: the `(i, j)` entry resolves to
the source entry `M[i][j]` at the same coordinates, reembedded into `Fin n`. This
is the `simp` normalization that rewrites a prefix lookup back to a source lookup
in determinant expansions. -/
@[grind =] theorem leadingPrefix_entry (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (leadingPrefix M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]) := by
  simp [leadingPrefix, ofFn]

/-- Entry formula for the first-`k`-rows slice: the `(i, j)` entry resolves to the
source entry `M[i][j]` with the row index reembedded into `Fin n` and the column
index `j` retained unchanged. This is the `simp` normalization a determinant
expansion relies on to rewrite a row-slice lookup back to a source lookup. -/
@[grind =] theorem leadingRows_entry (M : Matrix R n m) (k : Nat) (hk : k ≤ n)
    (i : Fin k) (j : Fin m) :
    (leadingRows M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       M[ii][j]) := by
  simp [leadingRows, ofFn]

/-- Entry formula for the `(k + 1)` leading submatrix: the `(i, j)` entry resolves
to the source entry `M[i][j]` at the same coordinates, reembedded into `Fin n` via
`k.val + 1 ≤ n`. This is the `simp` normalization that rewrites a submatrix lookup
back to a source lookup in determinant expansions. -/
@[grind =] theorem submatrix_entry (M : Matrix R n n) (k : Fin n)
    (i j : Fin (k.val + 1)) :
    (submatrix M k)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt k.isLt)⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
       M[ii][jj]) := by
  simp [submatrix, ofFn]

/-- The existing `submatrix` API is the `(k + 1)` leading-prefix API at the
same boundary. -/
theorem submatrix_eq_leadingPrefix (M : Matrix R n n) (k : Fin n) :
    submatrix M k = leadingPrefix M (k.val + 1) (Nat.succ_le_of_lt k.isLt) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [submatrix, leadingPrefix, ofFn]

/-- Bordered Bareiss minor with the first `k` rows/columns and one extra
border row `i` and column `j`. For Bareiss applications `i` and `j` are in the
trailing part, but the constructor is total and leaves that side condition to
the invariant using it. -/
def borderedMinor (M : Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n) :
    Matrix R (k + 1) (k + 1) :=
  ofFn fun r c =>
    let rr : Fin n :=
      if hr : r.val < k then
        ⟨r.val, Nat.lt_trans hr hk⟩
      else
        i
    let cc : Fin n :=
      if hc : c.val < k then
        ⟨c.val, Nat.lt_trans hc hk⟩
      else
        j
    M[rr][cc]

/-- Interior-block case of the bordered-minor entry formula: when both `r.val < k`
and `c.val < k`, the `(r, c)` entry resolves to the source entry `M[r][c]` at the
reembedded leading-block coordinates, independent of the border row `i` and column
`j`. This is the `simp` normalization for the top-left `k × k` block. -/
@[grind =] theorem borderedMinor_entry_lt_lt (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (r c : Fin (k + 1)) (hr : r.val < k) (hc : c.val < k) :
    (borderedMinor M k hk i j)[r][c] =
      (let rr : Fin n := ⟨r.val, Nat.lt_trans hr hk⟩
       let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
       M[rr][cc]) := by
  simp [borderedMinor, ofFn, hr, hc]

/-- Border-column case of the bordered-minor entry formula: at the final column
`Fin.last k` with `r.val < k`, the `(r, last)` entry resolves to the source entry
`M[r][j]`, taking the border column `j` and the reembedded leading-block row. This
is the `simp` normalization for the appended border column. -/
@[grind =] theorem borderedMinor_entry_lt_last (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (r : Fin (k + 1)) (hr : r.val < k) :
    (borderedMinor M k hk i j)[r][Fin.last k] =
      (let rr : Fin n := ⟨r.val, Nat.lt_trans hr hk⟩
       M[rr][j]) := by
  simp [borderedMinor, ofFn, hr]

/-- Border-row case of the bordered-minor entry formula: at the final row
`Fin.last k` with `c.val < k`, the `(last, c)` entry resolves to the source entry
`M[i][c]`, taking the border row `i` and the reembedded leading-block column. This
is the `simp` normalization for the appended border row. -/
@[grind =] theorem borderedMinor_entry_last_lt (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (c : Fin (k + 1)) (hc : c.val < k) :
    (borderedMinor M k hk i j)[Fin.last k][c] =
      (let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
       M[i][cc]) := by
  simp [borderedMinor, ofFn, hc]

/-- Corner case of the bordered-minor entry formula: at the bottom-right corner
`(Fin.last k, Fin.last k)`, the entry resolves to the source entry `M[i][j]` formed
from the border row `i` and border column `j`. This is the `simp` normalization for
the corner that a determinant expansion isolates last. -/
@[grind =] theorem borderedMinor_entry_last_last (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) :
    (borderedMinor M k hk i j)[Fin.last k][Fin.last k] = M[i][j] := by
  simp [borderedMinor, ofFn]

/-- The top-left `k × k` block of a bordered minor is the leading prefix of the
source matrix. This is the reindexing fact used when a determinant expansion
isolates the final border row/column. -/
theorem leadingPrefix_borderedMinor_eq_leadingPrefix (M : Matrix R n n) (k : Nat)
    (hk : k < n) (i j : Fin n) :
    leadingPrefix (borderedMinor M k hk i j) k (Nat.le_succ k) =
      leadingPrefix M k (Nat.le_of_lt hk) := by
  apply Vector.ext
  intro r _hr
  apply Vector.ext
  intro c _hc
  simp [leadingPrefix, borderedMinor, ofFn]

/-- The top-left `(k + 1) × (k + 1)` block of the next bordered minor is the
current bordered minor whose extra row/column are the `k`-th source row/column. -/
theorem leadingPrefix_borderedMinor_succ_eq_borderedMinor (M : Matrix R n n)
    (k : Nat) (hk : k < n) (hnext : k + 1 < n) (i j : Fin n) :
    leadingPrefix (borderedMinor M (k + 1) hnext i j) (k + 1)
        (Nat.le_succ (k + 1)) =
      borderedMinor M k hk ⟨k, hk⟩ ⟨k, hk⟩ := by
  apply Vector.ext
  intro r _hr
  apply Vector.ext
  intro c _hc
  by_cases hrk : r < k <;> by_cases hck : c < k
  · simp [leadingPrefix, borderedMinor, ofFn, hrk, hck]
  · have hc_eq : c = k := by omega
    simp [leadingPrefix, borderedMinor, ofFn, hrk, hc_eq]
  · have hr_eq : r = k := by omega
    simp [leadingPrefix, borderedMinor, ofFn, hck, hr_eq]
  · have hr_eq : r = k := by omega
    have hc_eq : c = k := by omega
    simp [leadingPrefix, borderedMinor, ofFn, hr_eq, hc_eq]

/-- The identity matrix entry function: `1[i][j] = 1` if `i = j`, else `0`. -/
@[grind =] theorem getElem_one [OfNat R 0] [OfNat R 1] {n : Nat} (i j : Fin n) :
    (1 : Matrix R n n)[i][j] = if i = j then (1 : R) else 0 := by
  simp [show (1 : Matrix R n n) = Matrix.identity from rfl, Matrix.identity, ofFn]

/-- The identity matrix is its own transpose. -/
@[simp, grind =] theorem transpose_one [OfNat R 0] [OfNat R 1] {n : Nat} :
    Matrix.transpose (1 : Matrix R n n) = (1 : Matrix R n n) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  show (Matrix.transpose (1 : Matrix R n n))[ii][jj] = (1 : Matrix R n n)[ii][jj]
  rw [transpose_getElem, getElem_one, getElem_one]
  by_cases hij : ii = jj
  · have hji : jj = ii := hij.symm
    rw [if_pos hij, if_pos hji]
  · have hji : jj ≠ ii := fun h => hij h.symm
    rw [if_neg hij, if_neg hji]

/-- A foldl whose every step adds `0` reduces to the initial accumulator. -/
private theorem foldl_add_eq_acc {R : Type u} [Lean.Grind.CommRing R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R)
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
      have hac : acc + (0 : R) = acc := by grind
      rw [hac]
      exact ih acc hxs

/-- A foldl summing an indicator function picks out the unique matching index. -/
private theorem foldl_indicator_unique {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : R) :
    xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0)) acc = acc + 1 := by
  induction xs generalizing acc with
  | nil => exact absurd hi (List.not_mem_nil)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hieq | hitail
      · have hx_eq : (if i = x then (1 : R) else 0) = 1 := by
          rw [hieq]; simp
        rw [hx_eq]
        have hxs_zero : ∀ y ∈ xs, (if i = y then (1 : R) else 0) = 0 := by
          intro y hy
          have hyx : y ≠ x := fun heq => by
            rw [heq] at hy
            exact (List.nodup_cons.mp hnodup).1 hy
          have hiy : i ≠ y := by
            rw [hieq]; exact fun h => hyx h.symm
          simp [hiy]
        rw [foldl_add_eq_acc xs _ _ hxs_zero]
      · have hxi : i ≠ x := by
          intro heq
          rw [← heq] at hnodup
          exact (List.nodup_cons.mp hnodup).1 hitail
        have hx_eq : (if i = x then (1 : R) else 0) = 0 := by simp [hxi]
        rw [hx_eq]
        have hac : acc + (0 : R) = acc := by grind
        rw [hac]
        exact ih hitail (List.nodup_cons.mp hnodup).2 acc

/-- Squaring an indicator gives the same indicator. -/
private theorem foldl_indicator_square_eq {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n) (acc : R) :
    xs.foldl (fun acc l =>
        acc + (if i = l then (1 : R) else 0) * (if i = l then (1 : R) else 0)) acc =
      xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0)) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hsq :
          (if i = x then (1 : R) else 0) * (if i = x then (1 : R) else 0) =
            if i = x then (1 : R) else 0 := by
        by_cases h : i = x
        · rw [if_pos h]; grind
        · rw [if_neg h]; grind
      rw [hsq]
      exact ih _

/-- Strip `Vector.ofFn` lookups inside a dotProduct-style foldl body. -/
private theorem foldl_dotProduct_basis_body {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (xs : List (Fin n)) (i j : Fin n) (acc : R) :
    xs.foldl
        (fun acc l =>
          acc +
            (Vector.ofFn fun b : Fin n => (if i = b then (1 : R) else 0))[l] *
              (Vector.ofFn fun b : Fin n => (if j = b then (1 : R) else 0))[l]) acc =
      xs.foldl
        (fun acc l =>
          acc + (if i = l then (1 : R) else 0) * (if j = l then (1 : R) else 0)) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hxi : (Vector.ofFn fun b : Fin n => (if i = b then (1 : R) else 0))[x] =
          if i = x then (1 : R) else 0 := by simp
      have hxj : (Vector.ofFn fun b : Fin n => (if j = b then (1 : R) else 0))[x] =
          if j = x then (1 : R) else 0 := by simp
      rw [hxi, hxj]
      exact ih (acc + (if i = x then 1 else 0) * (if j = x then 1 else 0))

/-- Dot product of the `i`-th and `j`-th identity rows.

Left `@[simp]`-only (not promoted to `grind =`): the indices `i j` appear only
under the `ofFn` binders, so the LHS pattern `dotProduct (ofFn _) (ofFn _)`
cannot instantiate them and `grind =` rejects it. -/
@[simp] theorem dotProduct_basis_basis {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (i j : Fin n) :
    Hex.Vector.dotProduct
        (Vector.ofFn fun b : Fin n => (if i = b then (1 : R) else 0))
        (Vector.ofFn fun b : Fin n => (if j = b then (1 : R) else 0)) =
      if i = j then 1 else 0 := by
  unfold Hex.Vector.dotProduct
  rw [foldl_dotProduct_basis_body]
  by_cases hij : i = j
  · subst hij
    rw [foldl_indicator_square_eq]
    rw [foldl_indicator_unique (List.finRange n) i (List.mem_finRange i)
      (List.nodup_finRange n) (0 : R)]
    rw [if_pos rfl]; grind
  · have hzero : ∀ l ∈ List.finRange n,
        (if i = l then (1 : R) else 0) * (if j = l then (1 : R) else 0) = 0 := by
      intro l _
      by_cases hil : i = l
      · have hjl : j ≠ l := fun heq => hij (hil.trans heq.symm)
        rw [if_pos hil, if_neg hjl]; grind
      · rw [if_neg hil]; grind
    rw [foldl_add_eq_acc (List.finRange n) _ _ hzero]
    rw [if_neg hij]

/-- The Gram matrix of the identity is the identity. -/
@[simp, grind =] theorem gramMatrix_one {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    gramMatrix (1 : Matrix R n n) = (1 : Matrix R n n) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hrow_i : (1 : Matrix R n n).row ⟨i, hi⟩ =
      Vector.ofFn fun b : Fin n => (if (⟨i, hi⟩ : Fin n) = b then (1 : R) else 0) := by
    apply Vector.ext
    intro a ha
    show ((1 : Matrix R n n).row ⟨i, hi⟩)[(⟨a, ha⟩ : Fin n)] =
      (Vector.ofFn fun b : Fin n => if (⟨i, hi⟩ : Fin n) = b then (1 : R) else 0)[
        (⟨a, ha⟩ : Fin n)]
    rw [Matrix.row, getElem_one]
    simp
  have hrow_j : (1 : Matrix R n n).row ⟨j, hj⟩ =
      Vector.ofFn fun b : Fin n => (if (⟨j, hj⟩ : Fin n) = b then (1 : R) else 0) := by
    apply Vector.ext
    intro a ha
    show ((1 : Matrix R n n).row ⟨j, hj⟩)[(⟨a, ha⟩ : Fin n)] =
      (Vector.ofFn fun b : Fin n => if (⟨j, hj⟩ : Fin n) = b then (1 : R) else 0)[
        (⟨a, ha⟩ : Fin n)]
    rw [Matrix.row, getElem_one]
    simp
  show (gramMatrix (1 : Matrix R n n))[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)] =
    (1 : Matrix R n n)[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)]
  have hgram :
      (gramMatrix (1 : Matrix R n n))[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)] =
        Hex.Vector.dotProduct ((1 : Matrix R n n).row ⟨i, hi⟩)
          ((1 : Matrix R n n).row ⟨j, hj⟩) := by
    unfold gramMatrix ofFn
    simp
  rw [hgram, hrow_i, hrow_j, dotProduct_basis_basis, getElem_one]

/-- The leading principal `(k + 1) × (k + 1)` submatrix of the identity is the
identity. -/
@[simp, grind =] theorem submatrix_one {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat} (k : Fin n) :
    submatrix (1 : Matrix R n n) k = (1 : Matrix R (k.val + 1) (k.val + 1)) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  show (submatrix (1 : Matrix R n n) k)[(⟨i, hi⟩ : Fin (k.val + 1))][
      (⟨j, hj⟩ : Fin (k.val + 1))] =
    (1 : Matrix R (k.val + 1) (k.val + 1))[(⟨i, hi⟩ : Fin (k.val + 1))][
      (⟨j, hj⟩ : Fin (k.val + 1))]
  rw [submatrix_entry]
  rw [getElem_one (i := (⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩ : Fin n))]
  rw [getElem_one (i := (⟨i, hi⟩ : Fin (k.val + 1)))]
  by_cases hij : (⟨i, hi⟩ : Fin (k.val + 1)) = ⟨j, hj⟩
  · have hval : i = j := Fin.val_eq_of_eq hij
    have hijn :
        (⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩ : Fin n) =
          ⟨j, Nat.lt_of_lt_of_le hj (Nat.succ_le_of_lt k.isLt)⟩ := by
      apply Fin.eq_of_val_eq; exact hval
    simp [hij, hijn]
  · have hval : i ≠ j := fun heq => hij (by apply Fin.eq_of_val_eq; exact heq)
    have hijn :
        (⟨i, Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt k.isLt)⟩ : Fin n) ≠
          ⟨j, Nat.lt_of_lt_of_le hj (Nat.succ_le_of_lt k.isLt)⟩ := fun heq =>
      hval (Fin.val_eq_of_eq heq)
    simp [hij, hijn]

end Matrix
end Hex

namespace Vector

/--
In-place update of the element at index `i` via `f`, wrapping `Array.modify`
so the underlying swap-with-placeholder ownership transfer survives codegen.
Calling `xs.set i (f xs[i])` forces a `lean_inc` on the borrowed entry and
loses uniqueness on nested-array shapes (e.g. matrix rows); `modify` avoids
that copy when `xs` is uniquely owned.
-/
@[inline] def modify (xs : Vector α n) (i : Nat) (f : α → α) : Vector α n :=
  ⟨xs.toArray.modify i f, by simp⟩

end Vector
