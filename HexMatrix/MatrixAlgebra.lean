module

public import HexMatrix.Basic
public import Batteries.Data.List.Lemmas

public section

/-!
Algebraic laws for dense matrix multiplication.
-/

namespace Hex

universe u v w

namespace Matrix

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

/-- The fold-sum of a pointwise sum splits into two fold-sums, provided the initial
accumulator already splits the same way. -/
private theorem foldl_sum_add_of_acc {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f g : α → R) (acc accF accG : R)
    (hacc : acc = accF + accG) :
    xs.foldl (fun acc x => acc + (f x + g x)) acc =
      xs.foldl (fun acc x => acc + f x) accF +
        xs.foldl (fun acc x => acc + g x) accG := by
  induction xs generalizing acc accF accG with
  | nil =>
      simpa only [List.foldl_nil] using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [hacc]
      grind

/-- The fold-sum of a pointwise sum `f x + g x` equals the sum of the two separate
fold-sums; additivity of the fold-sum over its summand. -/
private theorem foldl_sum_add {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f g : α → R) :
    xs.foldl (fun acc x => acc + (f x + g x)) 0 =
      xs.foldl (fun acc x => acc + f x) 0 +
        xs.foldl (fun acc x => acc + g x) 0 := by
  exact foldl_sum_add_of_acc xs f g 0 0 0 (by grind)

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

/-- Negation distributes through a fold-sum. -/
private theorem foldl_sum_neg {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R) :
    xs.foldl (fun acc x => acc + -f x) (-acc) =
      -xs.foldl (fun acc x => acc + f x) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [show -acc + -f x = -(acc + f x) by grind]
      exact ih (acc + f x)

/-- The fold-sum of a pointwise difference `f x - g x` equals the difference of the two
separate fold-sums. -/
private theorem foldl_sum_sub {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f g : α → R) (accF accG : R) :
    xs.foldl (fun acc x => acc + (f x - g x)) (accF - accG) =
      xs.foldl (fun acc x => acc + f x) accF -
        xs.foldl (fun acc x => acc + g x) accG := by
  rw [show accF - accG = accF + -accG by grind]
  calc
    xs.foldl (fun acc x => acc + (f x - g x)) (accF + -accG) =
        xs.foldl (fun acc x => acc + (f x + -g x)) (accF + -accG) := by
      apply foldl_sum_congr
      intro x _hx
      grind
    _ = xs.foldl (fun acc x => acc + f x) accF -
          xs.foldl (fun acc x => acc + g x) accG := by
      rw [foldl_sum_add_of_acc xs f (fun x => -g x) (accF + -accG) accF (-accG)
        (by grind)]
      rw [foldl_sum_neg]
      grind

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
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, mul, row, col, Hex.Vector.dotProduct, ofFn]
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
theorem transpose_mul_of_mul_comm [Lean.Grind.CommRing R]
    (A : Matrix R n m) (B : Matrix R m k) :
    Matrix.transpose (A * B) = Matrix.transpose B * Matrix.transpose A := by
  ext i hi j hj
  let ii : Fin k := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (Matrix.transpose (A * B))[ii][jj] = (Matrix.transpose B * Matrix.transpose A)[ii][jj]
  rw [transpose_getElem]
  change (A * B)[jj][ii] = (Matrix.transpose B * Matrix.transpose A)[ii][jj]
  simp [HMul.hMul, mul, row, col, transpose, Hex.Vector.dotProduct, ofFn]
  change
    (List.finRange m).foldl (fun acc l => acc + A[jj][l] * B[l][ii]) 0 =
      (List.finRange m).foldl (fun acc l => acc + B[l][ii] * A[jj][l]) 0
  apply foldl_sum_congr
  intro l _hl
  rw [Lean.Grind.CommSemiring.mul_comm]

/-- Left-multiplication by the identity matrix leaves a vector unchanged. -/
@[simp, grind =] theorem one_mulVec [Lean.Grind.Ring R] (v : Vector R n) :
    (1 : Matrix R n n) * v = v := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, row, Hex.Vector.dotProduct]
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
          rw [getElem_one]
    _ = v[ii] := by
          rw [foldl_indicator_mul_unique (List.finRange n) ii (fun j => v[j])
            (List.mem_finRange _) (List.nodup_finRange n) 0]
          grind

/-- Left-multiplication by the identity matrix leaves a matrix unchanged. -/
@[simp, grind =] theorem one_mul [Lean.Grind.Ring R] (M : Matrix R n m) :
    (1 : Matrix R n n) * M = M := by
  ext i hi j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin m := ⟨j, hj⟩
  change ((1 : Matrix R n n) * M)[ii][jj] = M[ii][jj]
  simp [HMul.hMul, mul, row, col, Hex.Vector.dotProduct]
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
          rw [getElem_one]
    _ = M[ii][jj] := by
          rw [foldl_indicator_mul_unique (List.finRange n) ii (fun l => M[l][jj])
            (List.mem_finRange _) (List.nodup_finRange n) 0]
          grind

/-- Right-multiplication by the identity matrix leaves a matrix unchanged. -/
@[simp, grind =] theorem mul_one [Lean.Grind.Ring R] (M : Matrix R n m) :
    M * (1 : Matrix R m m) = M := by
  ext i hi j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin m := ⟨j, hj⟩
  change (M * (1 : Matrix R m m))[ii][jj] = M[ii][jj]
  simp [HMul.hMul, mul, row, col, Hex.Vector.dotProduct]
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
          rw [getElem_one]
          split <;> grind
    _ = M[ii][jj] := by
          rw [foldl_indicator_mul_unique (List.finRange m) jj (fun l => M[ii][l])
            (List.mem_finRange _) (List.nodup_finRange m) 0]
          grind

/-- Matrix multiplication is associative. -/
theorem mul_assoc [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (C : Matrix R k l) :
    (A * B) * C = A * (B * C) := by
  ext i hi j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin l := ⟨j, hj⟩
  change ((A * B) * C)[ii][jj] = (A * (B * C))[ii][jj]
  simpa [HMul.hMul, mulVec, mul, row, col, Hex.Vector.dotProduct, ofFn] using
    congrArg (fun v => v[ii]) (mul_assoc_vec A B (col C jj))

/-- Matrix-vector multiplication sends the zero vector to the zero vector. -/
@[simp, grind =] theorem mulVec_zero [Lean.Grind.Ring R] (A : Matrix R n m) :
    A * (0 : Vector R m) = 0 := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, row, Hex.Vector.dotProduct]
  change (List.finRange m).foldl (fun acc j => acc + A[ii][j] * (0 : R)) 0 = 0
  apply foldl_add_eq_acc_ring
  intro j _hj
  grind

/-- The zero matrix sends every vector to the zero vector. -/
@[simp, grind =] theorem zero_mulVec [Lean.Grind.Ring R] (v : Vector R m) :
    (0 : Matrix R n m) * v = 0 := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, row, Hex.Vector.dotProduct]
  change (List.finRange m).foldl (fun acc j => acc + (0 : Matrix R n m)[ii][j] * v[j]) 0 = 0
  apply foldl_add_eq_acc_ring
  intro j _hj
  change (Matrix.zero : Matrix R n m)[ii][j] * v[j] = 0
  simpa [Matrix.zero, ofFn] using Lean.Grind.Semiring.zero_mul v[j]

/-- Multiplication by `Q - I`, expressed entrywise, is `Q * v - v`. -/
theorem sub_identity_mulVec [Lean.Grind.Ring R] (Q : Matrix R n n) (v : Vector R n) :
    mulVec (R := R) (n := n) (m := n)
        (ofFn fun i j => Q[i][j] - if i = j then 1 else 0) v =
      mulVec (R := R) (n := n) (m := n) Q v - v := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [mulVec, row, Hex.Vector.dotProduct, ofFn]
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

end Matrix

end Hex
