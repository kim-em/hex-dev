import HexGramSchmidt.Int
import HexMatrixMathlib.Determinant

/-!
Mathlib-side identification of the executable Cramer-style scaled coefficient
matrix entry with the public Bareiss determinant.

The Mathlib-free file `HexGramSchmidt/Int.lean` packages the executable
scaled-coefficient array entry as the no-pivot Bareiss trailing value on
`GramSchmidt.scaledCoeffMatrix` (via `scaledCoeffRows_lower_eq_…`). The
public Bareiss algorithm `Matrix.bareiss`, however, may insert a row swap
when a diagonal pivot is zero, so the executable array entry need not
match the public Bareiss value on the Cramer minor without crossing the
Bareiss/Leibniz determinant identity: the geometric vanishing in the
singular branch is visible only through the Leibniz determinant.

Per `SPEC/Libraries/hex-gram-schmidt.md` ("Proof path governs placement,
not just statement"), the identification therefore lives in
`HexGramSchmidtMathlib`. The proof reaches the executable determinant
surface by composing `HexMatrixMathlib.bareiss_eq_mathlib_det` with
`HexMatrixMathlib.det_eq.symm`, both owned by `hex-matrix-mathlib`.
-/

namespace Hex
namespace GramSchmidt
namespace Int

/-- Bareiss agrees with the Leibniz determinant on the Cramer matrix used by
the scaled-coefficient formula. -/
private theorem scaledCoeffMatrix_bareiss_eq_det
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    ((Matrix.bareiss
        (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj) :
          Int) : Rat) =
      ((Matrix.det
        (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj) :
          Int) : Rat) :=
  by exact_mod_cast
    (HexMatrixMathlib.bareiss_eq_mathlib_det
        (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj)).trans
      (HexMatrixMathlib.det_eq
        (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj)).symm

/-- Leading integer Gram determinants are nonnegative. -/
theorem leadingGramMatrixInt_det_nonneg
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n) :
    0 ≤ Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) := by
  let rowPrefix : Matrix Int t m :=
    Matrix.ofFn fun i j =>
      (b.row ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht⟩)[j]
  have hgram :
      GramSchmidt.leadingGramMatrixInt b t ht =
        Matrix.gramMatrix rowPrefix := by
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simp [GramSchmidt.leadingGramMatrixInt, rowPrefix, Matrix.gramMatrix, Matrix.dot,
      Matrix.row, Matrix.ofFn, GramSchmidt.liftFinLE]
  rw [hgram]
  exact Matrix.det_gramMatrix_nonneg rowPrefix

private theorem gramDet_pos_core (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  cases k with
  | zero =>
      omega
  | succ r =>
      have hrn : r < n := Nat.lt_of_succ_le hk
      exact hli ⟨r, hrn⟩

/-! ### Helpers for `gramDet_eq_prod_normSq_core`

The remaining theorems below build the rational column-operation reduction
from the leading Gram matrix to the diagonal Gram-Schmidt norm-squared
matrix, plus the integer→rational cast law for `det`. -/

/-- Casting Int → Rat distributes over a `List.foldl` sum. -/
private theorem foldl_intCast_add_aux {α : Type v}
    (xs : List α) (f : α → Int) (acc : Int) :
    ((xs.foldl (fun acc x => acc + f x) acc : Int) : Rat) =
      xs.foldl (fun (acc' : Rat) x => acc' + ((f x : Int) : Rat)) ((acc : Rat)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hi := ih (acc := acc + f x)
      simpa [Rat.intCast_add] using hi

/-- Casting Int → Rat distributes over a `List.foldl` product. -/
private theorem foldl_intCast_mul_aux {α : Type v}
    (xs : List α) (f : α → Int) (acc : Int) :
    ((xs.foldl (fun acc x => acc * f x) acc : Int) : Rat) =
      xs.foldl (fun (acc' : Rat) x => acc' * ((f x : Int) : Rat)) ((acc : Rat)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hi := ih (acc := acc * f x)
      simpa [Rat.intCast_mul] using hi

/-- `detSign` produces `1` or `-1`, which lifts identically through the
Int → Rat cast. -/
private theorem detSign_intCast {k : Nat} (perm : Vector (Fin k) k) :
    ((Matrix.detSign perm : Int) : Rat) = (Matrix.detSign perm : Rat) := by
  unfold Matrix.detSign
  by_cases h : Matrix.inversionCount perm.toList % 2 = 0
  · simp [h]
  · simp [h]

/-- The cast of an Int matrix to a Rat matrix by entry-wise Int.cast. -/
private def castIntDetMatrix {k : Nat} (M : Matrix Int k k) : Matrix Rat k k :=
  Matrix.ofFn fun i j => ((M[i][j] : Int) : Rat)

@[simp] private theorem castIntDetMatrix_get {k : Nat}
    (M : Matrix Int k k) (i j : Fin k) :
    (castIntDetMatrix M)[i][j] = ((M[i][j] : Int) : Rat) := by
  simp [castIntDetMatrix, Matrix.ofFn]

private theorem foldl_mul_congr_simple {α : Type v} {R : Type w} [Mul R]
    (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc * f x) acc =
      xs.foldl (fun acc x => acc * g x) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      rw [hx]
      exact ih (acc * g x) (fun y hy => h y (by simp [hy]))

private theorem detProduct_intCast {k : Nat}
    (M : Matrix Int k k) (perm : Vector (Fin k) k) :
    ((Matrix.detProduct M perm : Int) : Rat) =
      Matrix.detProduct (castIntDetMatrix M) perm := by
  unfold Matrix.detProduct
  rw [foldl_intCast_mul_aux (xs := List.finRange k)
    (f := fun i => M[i][perm[i]]) (acc := 1)]
  rw [show ((1 : Int) : Rat) = (1 : Rat) from rfl]
  apply foldl_mul_congr_simple
  intro i _hi
  rw [castIntDetMatrix_get]

private theorem detTerm_intCast {k : Nat}
    (M : Matrix Int k k) (perm : Vector (Fin k) k) :
    ((Matrix.detTerm M perm : Int) : Rat) =
      Matrix.detTerm (castIntDetMatrix M) perm := by
  unfold Matrix.detTerm
  rw [Rat.intCast_mul, detSign_intCast, detProduct_intCast]

private theorem foldl_sum_congr_simple {α : Type v} {R : Type w} [Add R]
    (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      rw [hx]
      exact ih (acc + g x) (fun y hy => h y (by simp [hy]))

private theorem det_intCast {k : Nat} (M : Matrix Int k k) :
    ((Matrix.det M : Int) : Rat) = Matrix.det (castIntDetMatrix M) := by
  unfold Matrix.det
  rw [foldl_intCast_add_aux (xs := Matrix.permutationVectors k)
    (f := fun perm => Matrix.detTerm M perm) (acc := 0)]
  rw [show ((0 : Int) : Rat) = (0 : Rat) from rfl]
  apply foldl_sum_congr_simple
  intro perm _hperm
  exact detTerm_intCast M perm

/-- Right-side dot product distributes over vector addition. -/
theorem dot_add_right_rat {m' : Nat} (u v w : Vector Rat m') :
    Matrix.dot u (v + w) = Matrix.dot u v + Matrix.dot u w := by
  unfold Matrix.dot Hex.Vector.dotProduct
  have h :
      ∀ (xs : List (Fin m')) (accV accW : Rat),
        xs.foldl (fun acc i => acc + u[i] * (v + w)[i]) (accV + accW) =
          xs.foldl (fun acc i => acc + u[i] * v[i]) accV +
            xs.foldl (fun acc i => acc + u[i] * w[i]) accW := by
    intro xs
    induction xs with
    | nil => intro accV accW; simp
    | cons i xs ih =>
        intro accV accW
        have hentry : (v + w)[i] = v[i] + w[i] := by
          change (v + w)[i.val] = v[i.val] + w[i.val]
          rw [Vector.getElem_add]
        simp only [List.foldl_cons]
        have hstart :
            accV + accW + u[i] * (v + w)[i] =
              (accV + u[i] * v[i]) + (accW + u[i] * w[i]) := by
          rw [hentry]
          grind
        rw [hstart]
        exact ih (accV + u[i] * v[i]) (accW + u[i] * w[i])
  have hzero : (0 : Rat) + 0 = 0 := by grind
  simpa [hzero] using h (List.finRange m') 0 0

/-- Right-side dot product distributes over scalar multiplication. -/
theorem dot_smul_right_rat {m' : Nat} (s : Rat) (u v : Vector Rat m') :
    Matrix.dot u (s • v) = s * Matrix.dot u v := by
  unfold Matrix.dot Hex.Vector.dotProduct
  have h :
      ∀ (xs : List (Fin m')) (acc : Rat),
        xs.foldl (fun acc i => acc + u[i] * (s • v)[i]) (s * acc) =
          s * xs.foldl (fun acc i => acc + u[i] * v[i]) acc := by
    intro xs
    induction xs with
    | nil => intro acc; simp
    | cons i xs ih =>
        intro acc
        have hentry : (s • v)[i] = s * v[i] := by
          change (s • v)[i.val] = s * v[i.val]
          rw [Vector.getElem_smul]
          rfl
        simp only [List.foldl_cons]
        have hstart :
            s * acc + u[i] * (s • v)[i] = s * (acc + u[i] * v[i]) := by
          rw [hentry]
          grind
        rw [hstart]
        exact ih (acc + u[i] * v[i])
  have hzero : s * (0 : Rat) = 0 := by grind
  simpa [hzero] using h (List.finRange m') 0

/-- Dot product of a vector against the zero vector is zero. -/
private theorem dot_zero_right_rat {m' : Nat} (u : Vector Rat m') :
    Matrix.dot u (0 : Vector Rat m') = 0 := by
  unfold Matrix.dot Hex.Vector.dotProduct
  have h : ∀ (xs : List (Fin m')) (acc : Rat),
      xs.foldl (fun acc i => acc + u[i] * (0 : Vector Rat m')[i]) acc = acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        have hzero : (0 : Vector Rat m')[i] = 0 := by
          change (0 : Vector Rat m')[i.val] = 0
          rw [Vector.getElem_zero]
        rw [hzero]
        have : acc + u[i] * 0 = acc := by grind
        rw [this]
        exact ih acc
  exact h (List.finRange m') 0

/-- Folding a sum with an initial value separates: the result equals the
initial value plus the same fold from zero. -/
private theorem foldl_sum_start_rat {α : Type v}
    (xs : List α) (f : α → Rat) (acc : Rat) :
    xs.foldl (fun acc x => acc + f x) acc =
      acc + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x)]
      rw [ih (acc := (0 : Rat) + f x)]
      grind

/-- Rational dot product is commutative. -/
private theorem dot_comm_rat {m' : Nat} (u v : Vector Rat m') :
    Matrix.dot u v = Matrix.dot v u := by
  unfold Matrix.dot Hex.Vector.dotProduct
  have h : ∀ (xs : List (Fin m')) (accU accV : Rat),
      accU = accV →
        xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
          xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
    intro xs
    induction xs with
    | nil => intro accU accV h; exact h
    | cons i xs ih =>
        intro accU accV h
        simp only [List.foldl_cons]
        apply ih
        rw [h]
        grind
  exact h (List.finRange m') 0 0 rfl

/-- Right-side dot product distribution over a `prefixCombination`. -/
private theorem dot_prefixCombination_right_rat
    (coeffs : Matrix Rat n n) (basisM : Matrix Rat n m)
    (i : Nat) (hi : i < n) (u : Vector Rat m) :
    Matrix.dot u (GramSchmidt.prefixCombination coeffs basisM i hi) =
      (List.finRange i).foldl
        (fun (acc : Rat) (j : Fin i) =>
          acc +
            GramSchmidt.entry coeffs ⟨i, hi⟩
                ⟨j.val, Nat.lt_trans j.isLt hi⟩ *
              Matrix.dot u
                (basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩)) 0 := by
  unfold GramSchmidt.prefixCombination
  have hgen :
      ∀ (xs : List (Fin i)) (acc : Vector Rat m),
        Matrix.dot u
            (xs.foldl
              (fun acc (j : Fin i) =>
                acc +
                  GramSchmidt.entry coeffs ⟨i, hi⟩
                      ⟨j.val, Nat.lt_trans j.isLt hi⟩ •
                    basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩)
              acc) =
          Matrix.dot u acc +
            xs.foldl
              (fun (acc' : Rat) (j : Fin i) =>
                acc' +
                  GramSchmidt.entry coeffs ⟨i, hi⟩
                      ⟨j.val, Nat.lt_trans j.isLt hi⟩ *
                    Matrix.dot u
                      (basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩)) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih]
        rw [dot_add_right_rat, dot_smul_right_rat]
        rw [foldl_sum_start_rat xs _
          ((0 : Rat) + (GramSchmidt.entry coeffs ⟨i, hi⟩
              ⟨x.val, Nat.lt_trans x.isLt hi⟩ *
            Matrix.dot u
              (basisM.row ⟨x.val, Nat.lt_trans x.isLt hi⟩)))]
        grind
  rw [hgen (List.finRange i) 0]
  rw [dot_zero_right_rat]
  grind

/-- Dot product against a `prefixCombination` is zero when the right vector is
orthogonal to every contributing basis row. -/
private theorem dot_prefixCombination_right_eq_zero_of_dot_zero
    (coeffs : Matrix Rat n n) (basisM : Matrix Rat n m)
    (i : Nat) (hi : i < n) (u : Vector Rat m)
    (h : ∀ (j : Fin i),
      Matrix.dot u
          (basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩) = 0) :
    Matrix.dot u (GramSchmidt.prefixCombination coeffs basisM i hi) = 0 := by
  rw [dot_prefixCombination_right_rat]
  -- All terms are zero: the foldl with each entry = 0 reduces to 0.
  induction (List.finRange i) with
  | nil => rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [h j]
      have h0 : (0 : Rat) + GramSchmidt.entry coeffs ⟨i, hi⟩
          ⟨j.val, Nat.lt_trans j.isLt hi⟩ * 0 = 0 := by grind
      rw [h0]
      exact ih

/-- Cast an Int matrix row to a Rat row by entry-wise `Int.cast`. -/
private def castIntRow (b : Matrix Int n m) (i : Fin n) : Vector Rat m :=
  Vector.map (fun x : Int => (x : Rat)) (b.row i)

/-- Cast an Int matrix to the Rat matrix whose rows are `castIntRow`. -/
private def castIntMatrixRat (b : Matrix Int n m) : Matrix Rat n m :=
  Vector.map (fun row => Vector.map (fun x : Int => (x : Rat)) row) b

/-- Coefficients of the projection of row `i` onto the Gram-Schmidt prefix
`0, ..., j`, indexed by that prefix. -/
private noncomputable def projectionCoeffPrefix
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Vector Rat (j + 1) :=
  Vector.ofFn fun q =>
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩
      ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hj)⟩

/-- The Gram-Schmidt prefix projection of row `i` onto rows `0, ..., j`, still
written in the orthogonal basis rows. -/
private noncomputable def basisPrefixProjection
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Vector Rat m :=
  Matrix.rowCombination (GramSchmidt.prefixRows (basis b) j hj)
    (projectionCoeffPrefix b i j hi hj)

private theorem basisPrefixProjection_mem_basisSpan
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    GramSchmidt.prefixSpan (basis b) j hj
      (basisPrefixProjection b i j hi hj) := by
  exact ⟨projectionCoeffPrefix b i j hi hj, rfl⟩

private theorem basisPrefixProjection_mem_originalSpan
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    GramSchmidt.prefixSpan (castIntMatrixRat b) j hj
      (basisPrefixProjection b i j hi hj) := by
  simpa [castIntMatrixRat] using
    ((basis_span b j hj (basisPrefixProjection b i j hi hj)).mp
      (basisPrefixProjection_mem_basisSpan b i j hi hj))

/-- Original-row coordinates for the projection of row `i` onto the row prefix
`0, ..., j`. The coordinates are chosen through the proved span equivalence
between original rows and Gram-Schmidt rows. -/
private noncomputable def originalProjectionCoords
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Vector Rat (j + 1) :=
  Classical.choose (basisPrefixProjection_mem_originalSpan b i j hi hj)

/-- The chosen original-row coordinates reconstruct the same projection vector
as the Gram-Schmidt prefix coefficients. -/
private theorem originalProjectionCoords_spec
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Matrix.rowCombination (GramSchmidt.prefixRows (castIntMatrixRat b) j hj)
        (originalProjectionCoords b i j hi hj) =
      basisPrefixProjection b i j hi hj := by
  exact Classical.choose_spec (basisPrefixProjection_mem_originalSpan b i j hi hj)

private theorem rowCombination_eq_foldl_rows_rat
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

private theorem dot_rowCombination_right_rat
    (u : Vector Rat m) (M : Matrix Rat n m) (c : Vector Rat n) :
    Matrix.dot u (Matrix.rowCombination M c) =
      (List.finRange n).foldl
        (fun acc j => acc + c[j] * Matrix.dot u (M.row j)) 0 := by
  rw [rowCombination_eq_foldl_rows_rat]
  have hgen :
      ∀ xs : List (Fin n), ∀ acc : Vector Rat m,
        Matrix.dot u (xs.foldl (fun acc j => acc + c[j] • M.row j) acc) =
          Matrix.dot u acc +
            xs.foldl (fun acc' j => acc' + c[j] * Matrix.dot u (M.row j)) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp only [List.foldl_nil]
        grind
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih]
        rw [dot_add_right_rat, dot_smul_right_rat]
        rw [foldl_sum_start_rat xs _
          ((0 : Rat) + c[x] * Matrix.dot u (M.row x))]
        grind
  rw [hgen (List.finRange n) 0]
  rw [dot_zero_right_rat]
  grind

/-- Dotting the projection with an original prefix row is the corresponding
linear combination of original Gram-matrix entries. -/
private theorem originalProjectionCoords_dot_eq_gram_combination
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n)
    (p : Fin (j + 1)) :
    Matrix.dot
        (castIntRow b
          ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_of_lt hj)⟩)
        (basisPrefixProjection b i j hi hj) =
      (List.finRange (j + 1)).foldl
        (fun acc q =>
          acc + (originalProjectionCoords b i j hi hj)[q] *
            Matrix.dot
              (castIntRow b
                ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_of_lt hj)⟩)
              (castIntRow b
                ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hj)⟩)) 0 := by
  rw [← originalProjectionCoords_spec b i j hi hj]
  rw [dot_rowCombination_right_rat]
  apply foldl_sum_congr_simple
  intro q _hq
  simp [GramSchmidt.prefixRows, Matrix.row, castIntMatrixRat, castIntRow]

/-- Auxiliary matrix `M_final` whose `(i, j)` entry is the rational inner
product `⟨b_i, b*_j⟩` between the cast integer row `b_i` and the
Gram-Schmidt orthogonal basis row `b*_j`. -/
private noncomputable def auxMatrix (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    Matrix Rat k k :=
  Matrix.ofFn fun i j =>
    Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
      ((basis b).row (GramSchmidt.liftFinLE j hk))

private theorem auxMatrix_get (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (auxMatrix b k hk)[i][j] =
      Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
        ((basis b).row (GramSchmidt.liftFinLE j hk)) := by
  simp [auxMatrix, Matrix.ofFn]

/-- The cast Int row decomposes as `b*_i + prefixCombination`. -/
private theorem castIntRow_decomposition
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    castIntRow b ⟨i, hi⟩ =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  exact basis_decomposition (b := b) i hi

/-- `auxMatrix` is lower triangular: entries above the diagonal vanish. -/
private theorem auxMatrix_zero_above (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) (hij : i.val < j.val) :
    (auxMatrix b k hk)[i][j] = 0 := by
  rw [auxMatrix_get]
  have hi' : i.val < n := Nat.lt_of_lt_of_le i.isLt hk
  have hj' : j.val < n := Nat.lt_of_lt_of_le j.isLt hk
  have hij' : i.val ≠ j.val := Nat.ne_of_lt hij
  -- liftFinLE i hk = ⟨i.val, hi'⟩ definitionally.
  rw [show GramSchmidt.liftFinLE i hk = ⟨i.val, hi'⟩ from rfl]
  rw [show GramSchmidt.liftFinLE j hk = ⟨j.val, hj'⟩ from rfl]
  rw [castIntRow_decomposition b i.val hi']
  rw [dot_comm_rat]
  rw [dot_add_right_rat]
  rw [dot_comm_rat ((basis b).row ⟨j.val, hj'⟩) ((basis b).row ⟨i.val, hi'⟩)]
  rw [basis_orthogonal b i.val j.val hi' hj' hij']
  -- Second term: prefixCombination orthogonal to ((basis b).row j).
  have hprefix :
      Matrix.dot ((basis b).row ⟨j.val, hj'⟩)
          (GramSchmidt.prefixCombination (coeffs b) (basis b) i.val hi') = 0 := by
    apply dot_prefixCombination_right_eq_zero_of_dot_zero
      (coeffs := coeffs b) (basisM := basis b) (i := i.val) (hi := hi')
      (u := (basis b).row ⟨j.val, hj'⟩)
    intro p
    have hp' : p.val < i.val := p.isLt
    have hpj : p.val ≠ j.val := Nat.ne_of_lt (Nat.lt_trans hp' hij)
    have hpj_lt : p.val < n := Nat.lt_trans hp' hi'
    exact basis_orthogonal b j.val p.val hj' hpj_lt fun h => hpj h.symm
  rw [hprefix]
  grind

/-- Diagonal of `auxMatrix` is the squared norm of the corresponding basis row. -/
private theorem auxMatrix_diag (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (i : Fin k) :
    (auxMatrix b k hk)[i][i] =
      Vector.normSq ((basis b).row (GramSchmidt.liftFinLE i hk)) := by
  rw [auxMatrix_get]
  have hi' : i.val < n := Nat.lt_of_lt_of_le i.isLt hk
  rw [show GramSchmidt.liftFinLE i hk = ⟨i.val, hi'⟩ from rfl]
  rw [castIntRow_decomposition b i.val hi']
  rw [dot_comm_rat]
  rw [dot_add_right_rat]
  -- First term: dot ((basis b).row i) ((basis b).row i) = normSq ((basis b).row i)
  -- Second term: dot ((basis b).row i) prefixCombination = 0.
  have hprefix :
      Matrix.dot ((basis b).row ⟨i.val, hi'⟩)
          (GramSchmidt.prefixCombination (coeffs b) (basis b) i.val hi') = 0 := by
    apply dot_prefixCombination_right_eq_zero_of_dot_zero
      (coeffs := coeffs b) (basisM := basis b) (i := i.val) (hi := hi')
      (u := (basis b).row ⟨i.val, hi'⟩)
    intro p
    have hp' : p.val < i.val := p.isLt
    have hpi : p.val ≠ i.val := Nat.ne_of_lt hp'
    have hpi_lt : p.val < n := Nat.lt_trans hp' hi'
    exact basis_orthogonal b i.val p.val hi' hpi_lt fun h => hpi h.symm
  rw [hprefix]
  -- Remaining: dot ((basis b).row i) ((basis b).row i) + 0 = normSq ((basis b).row i)
  have hns :
      Vector.normSq ((basis b).row ⟨i.val, hi'⟩) =
        Matrix.dot ((basis b).row ⟨i.val, hi'⟩) ((basis b).row ⟨i.val, hi'⟩) := by
    rfl
  rw [hns]
  grind

/-- The determinant of `auxMatrix` equals the product of squared norms. -/
private theorem auxMatrix_det_eq_prod_normSq (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    Matrix.det (auxMatrix b k hk) = gramSchmidtNormProduct b k hk := by
  rw [Matrix.det_lowerTriangular_eq_foldl_diag (auxMatrix b k hk)
    (fun i j hij => auxMatrix_zero_above b k hk i j hij)]
  unfold gramSchmidtNormProduct
  -- Both foldls are over `List.finRange k`. The diagonal of auxMatrix at i
  -- equals Vector.normSq of (basis b) row at the lifted index.
  apply foldl_mul_congr_simple
  intro i _hi
  rw [auxMatrix_diag b k hk i]
  rfl

/-- Interpolating matrix between `leadingGramMatrixRat (castIntMatrix b)` (at
`s = 0`) and `auxMatrix b k hk` (at `s = k`). Columns with index `< s` have
already been replaced by basis-row dot products; columns with index `≥ s`
still hold the original `b`-row dot products. -/
private noncomputable def progressMatrix (b : Matrix Int n m) (k : Nat)
    (hk : k ≤ n) (s : Nat) : Matrix Rat k k :=
  Matrix.ofFn fun i j =>
    if j.val < s then
      Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
        ((basis b).row (GramSchmidt.liftFinLE j hk))
    else
      Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
        (castIntRow b (GramSchmidt.liftFinLE j hk))

private theorem progressMatrix_get_lt (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (s : Nat) (i j : Fin k) (hj : j.val < s) :
    (progressMatrix b k hk s)[i][j] =
      Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
        ((basis b).row (GramSchmidt.liftFinLE j hk)) := by
  simp [progressMatrix, Matrix.ofFn, hj]

private theorem progressMatrix_get_ge (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (s : Nat) (i j : Fin k) (hj : ¬ j.val < s) :
    (progressMatrix b k hk s)[i][j] =
      Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
        (castIntRow b (GramSchmidt.liftFinLE j hk)) := by
  simp [progressMatrix, Matrix.ofFn, hj]

/-- At `s = k`, `progressMatrix` matches `auxMatrix`. -/
private theorem progressMatrix_full_eq_auxMatrix (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    progressMatrix b k hk k = auxMatrix b k hk := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin k := ⟨i, hi⟩
  let jj : Fin k := ⟨j, hj⟩
  have hjlt : jj.val < k := hj
  change (progressMatrix b k hk k)[ii][jj] = (auxMatrix b k hk)[ii][jj]
  rw [progressMatrix_get_lt b k hk k ii jj hjlt]
  rw [auxMatrix_get]

/-- The col-op coefficient list for the `s`-th transition step: indices
`p : Fin s` lifted into `Fin k`. -/
private def progressMatrixSources (k : Nat) (s : Nat) (hs : s < k) :
    List (Fin k) :=
  (List.finRange s).map fun p => ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩

/-- Sources are all strictly below `s` and hence distinct from `⟨s, hs⟩`. -/
private theorem progressMatrixSources_ne_dst (k : Nat) (s : Nat) (hs : s < k)
    (src : Fin k) (hmem : src ∈ progressMatrixSources k s hs) :
    src ≠ ⟨s, hs⟩ := by
  unfold progressMatrixSources at hmem
  rw [List.mem_map] at hmem
  obtain ⟨p, _, hp⟩ := hmem
  intro h
  have hval := congrArg Fin.val h
  rw [← hp] at hval
  exact Nat.ne_of_lt p.isLt hval

/-- The col-op coefficient for source `src : Fin k`: equals
`-(coeffs b)[s][src.val]`. -/
private noncomputable def progressMatrixCoeff (b : Matrix Int n m) (k : Nat)
    (hk : k ≤ n) (s : Nat) (hs : s < k) (src : Fin k) : Rat :=
  -(GramSchmidt.entry (coeffs b)
    ⟨s, Nat.lt_of_lt_of_le hs hk⟩
    ⟨src.val, Nat.lt_of_lt_of_le src.isLt hk⟩)

/-- The matrix transition for one col-op step: column `s` of
`progressMatrix b k hk (s+1)` equals column `s` of `progressMatrix b k hk s`
plus a linear combination of columns with index `< s`. -/
private theorem progressMatrix_succ_eq_colReplace
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) (s : Nat) (hs : s < k) :
    progressMatrix b k hk (s + 1) =
      Matrix.colReplace (progressMatrix b k hk s) (⟨s, hs⟩ : Fin k)
        (fun i =>
          (progressMatrix b k hk s)[i][(⟨s, hs⟩ : Fin k)] +
          (progressMatrixSources k s hs).foldl
            (fun acc src =>
              acc + progressMatrixCoeff b k hk s hs src *
                (progressMatrix b k hk s)[i][src]) 0) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin k := ⟨i, hi⟩
  change (progressMatrix b k hk (s + 1))[ii][(⟨j, hj⟩ : Fin k)] =
    (Matrix.colReplace (progressMatrix b k hk s) (⟨s, hs⟩ : Fin k)
      (fun i' =>
        (progressMatrix b k hk s)[i'][(⟨s, hs⟩ : Fin k)] +
        (progressMatrixSources k s hs).foldl
          (fun acc src =>
            acc + progressMatrixCoeff b k hk s hs src *
              (progressMatrix b k hk s)[i'][src]) 0))[ii][(⟨j, hj⟩ : Fin k)]
  rw [Matrix.colReplace_get]
  -- Case split on Fin k equality.
  by_cases hjs : (⟨j, hj⟩ : Fin k) = (⟨s, hs⟩ : Fin k)
  · -- Column s case.
    rw [if_pos hjs]
    -- Get j = s from the Fin equality, then substitute hj with hs.
    have hjs_val : j = s := congrArg Fin.val hjs
    -- Replace [⟨j, hj⟩] with [⟨s, hs⟩] in the LHS by the Fin equality.
    -- Use Vector.ext-like rewrite: re-express the LHS at ⟨s, hs⟩ via congrArg.
    have hLHS_eq :
        (progressMatrix b k hk (s + 1))[ii][(⟨j, hj⟩ : Fin k)] =
          (progressMatrix b k hk (s + 1))[ii][(⟨s, hs⟩ : Fin k)] := by
      congr 1
    rw [hLHS_eq]
    -- LHS: progressMatrix b k hk (s+1) at column ⟨s, hs⟩.
    have hjlt : (⟨s, hs⟩ : Fin k).val < s + 1 := Nat.lt_succ_self s
    rw [progressMatrix_get_lt b k hk (s + 1) ii (⟨s, hs⟩ : Fin k) hjlt]
    have hjnlt : ¬ (⟨s, hs⟩ : Fin k).val < s := Nat.lt_irrefl s
    rw [progressMatrix_get_ge b k hk s ii (⟨s, hs⟩ : Fin k) hjnlt]
    -- LHS = Matrix.dot (castIntRow b (lift ii)) ((basis b).row (lift ⟨s, hs⟩))
    -- RHS' first piece = Matrix.dot (castIntRow b (lift ii)) (castIntRow b (lift ⟨s, hs⟩))
    -- We need: LHS = RHS' first + foldl (coeff * (basis row p))
    have hsn : s < n := Nat.lt_of_lt_of_le hs hk
    have hslift : GramSchmidt.liftFinLE (⟨s, hs⟩ : Fin k) hk = ⟨s, hsn⟩ := rfl
    rw [hslift]
    -- decomposition castIntRow b ⟨s, hsn⟩ = (basis b).row ⟨s, hsn⟩ + prefixComb
    rw [castIntRow_decomposition b s hsn]
    rw [dot_add_right_rat]
    -- LHS = dot (castIntRow ii) ((basis b).row ⟨s, _⟩)
    -- RHS_first = dot (castIntRow ii) ((basis b).row ⟨s, _⟩) + dot (castIntRow ii) prefixComb
    -- So we need: dot (castIntRow ii) ((basis b).row ⟨s,_⟩) = (above) + foldl
    -- => 0 = dot (castIntRow ii) prefixComb + foldl
    -- Use: dot (castIntRow ii) prefixComb = foldl coeff * dot (castIntRow ii) basis_row_p
    -- And dot (castIntRow ii) basis_row_p = progressMatrix s at [ii][⟨p, _⟩] for p < s.
    rw [dot_prefixCombination_right_rat (coeffs := coeffs b) (basisM := basis b)
      (i := s) (hi := hsn)]
    -- Now show the two foldls cancel.
    -- The foldl on the LHS has +entry * dot, and we need to match the - on RHS.
    -- It's easier to subtract from both sides to show RHS - LHS = 0.
    -- Actually: LHS + foldl_lhs = LHS_first + foldl_rhs
    -- where foldl_lhs has positive entries, foldl_rhs has negative entries.
    -- Equivalently: foldl_lhs + foldl_rhs = 0 (since LHS = LHS_first).
    -- Let's match them.
    have hfold_match :
        (List.finRange s).foldl
          (fun (acc : Rat) (jp : Fin s) =>
            acc +
              GramSchmidt.entry (coeffs b) ⟨s, hsn⟩
                  ⟨jp.val, Nat.lt_trans jp.isLt hsn⟩ *
                Matrix.dot (castIntRow b (GramSchmidt.liftFinLE ii hk))
                  ((basis b).row ⟨jp.val, Nat.lt_trans jp.isLt hsn⟩)) 0 =
        - ((progressMatrixSources k s hs).foldl
          (fun acc src =>
            acc + progressMatrixCoeff b k hk s hs src *
              (progressMatrix b k hk s)[ii][src]) 0) := by
      -- Match term by term: each entry on LHS = -coeff * progressMatrix entry.
      -- The progressMatrix entry at src (which is some ⟨p.val, _⟩ for p < s)
      -- equals dot (castIntRow ii) ((basis b).row ⟨src.val, _⟩) since src.val < s.
      unfold progressMatrixSources progressMatrixCoeff
      -- Move the negation inside the foldl.
      have hneg_foldl :
          - ((List.finRange s).map fun p =>
              (⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩ : Fin k)).foldl
            (fun acc src =>
              acc + (-GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨src.val, Nat.lt_of_lt_of_le src.isLt hk⟩) *
                (progressMatrix b k hk s)[ii][src]) 0 =
            ((List.finRange s).map fun p =>
              (⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩ : Fin k)).foldl
            (fun acc src =>
              acc + GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨src.val, Nat.lt_of_lt_of_le src.isLt hk⟩ *
                (progressMatrix b k hk s)[ii][src]) 0 := by
        -- Induction over the mapped list, factoring out negation.
        generalize hmap : (List.finRange s).map (fun p : Fin s =>
              (⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩ : Fin k)) = lst
        clear hmap
        induction lst with
        | nil => simp
        | cons x xs ih =>
            simp only [List.foldl_cons]
            -- Use foldl_sum_start_rat to factor out, then match.
            rw [foldl_sum_start_rat xs _
              ((0 : Rat) + (-GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨x.val, Nat.lt_of_lt_of_le x.isLt hk⟩) *
                (progressMatrix b k hk s)[ii][x])]
            rw [foldl_sum_start_rat xs _
              ((0 : Rat) + GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨x.val, Nat.lt_of_lt_of_le x.isLt hk⟩ *
                (progressMatrix b k hk s)[ii][x])]
            grind
      rw [hneg_foldl]
      -- Now compare the LHS foldl with the foldl over the mapped list.
      -- LHS uses xs := List.finRange s indexed by p : Fin s.
      -- RHS uses xs.map (lift p), then progressMatrix at lifted src.
      -- We use List.foldl_map.
      rw [List.foldl_map]
      -- Now both foldls are over List.finRange s.
      apply foldl_sum_congr_simple
      intro p _hp
      -- LHS body: entry * dot (castIntRow ii) ((basis b).row ⟨p.val, _⟩)
      -- RHS body: entry * (progressMatrix b k hk s)[ii][⟨p.val, _⟩]
      -- Need: dot (castIntRow ii) ((basis b).row ⟨p.val, _⟩) =
      --       (progressMatrix b k hk s)[ii][⟨p.val, _⟩]
      have hp_lt : p.val < s := p.isLt
      let pp : Fin k := ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩
      have hpp_lt_s : pp.val < s := hp_lt
      rw [progressMatrix_get_lt b k hk s ii pp hpp_lt_s]
      rfl
    -- Now use hfold_match to conclude.
    grind
  · -- j ≠ s case.
    rw [if_neg hjs]
    have hjs_ne : j ≠ s := fun h => hjs (Fin.ext h)
    by_cases hjlt : j < s
    · -- j < s: both versions use basis-row dot.
      have hjlt' : j < s + 1 := Nat.lt_succ_of_lt hjlt
      have hj_idx_lt_succ : (⟨j, hj⟩ : Fin k).val < s + 1 := hjlt'
      have hj_idx_lt : (⟨j, hj⟩ : Fin k).val < s := hjlt
      rw [progressMatrix_get_lt b k hk (s + 1) ii (⟨j, hj⟩ : Fin k) hj_idx_lt_succ]
      rw [progressMatrix_get_lt b k hk s ii (⟨j, hj⟩ : Fin k) hj_idx_lt]
    · -- j ≥ s. Since j ≠ s, we have j > s.
      have hjge : j ≥ s := Nat.le_of_not_lt hjlt
      have hjgt : j > s := Nat.lt_of_le_of_ne hjge fun h => hjs_ne h.symm
      have hj_idx_nlt_succ : ¬ (⟨j, hj⟩ : Fin k).val < s + 1 := by
        change ¬ j < s + 1; omega
      have hj_idx_nlt : ¬ (⟨j, hj⟩ : Fin k).val < s := hjlt
      rw [progressMatrix_get_ge b k hk (s + 1) ii (⟨j, hj⟩ : Fin k) hj_idx_nlt_succ]
      rw [progressMatrix_get_ge b k hk s ii (⟨j, hj⟩ : Fin k) hj_idx_nlt]

/-- The col-op step preserves the determinant. -/
private theorem progressMatrix_succ_det
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) (s : Nat) (hs : s < k) :
    Matrix.det (progressMatrix b k hk (s + 1)) =
      Matrix.det (progressMatrix b k hk s) := by
  rw [progressMatrix_succ_eq_colReplace b k hk s hs]
  apply Matrix.det_colReplace_add_otherCols
  exact progressMatrixSources_ne_dst k s hs

/-- All progress matrices have the same determinant: induct from 0 to k. -/
private theorem progressMatrix_det_invariant
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) (s : Nat) (hs : s ≤ k) :
    Matrix.det (progressMatrix b k hk s) = Matrix.det (progressMatrix b k hk 0) := by
  induction s with
  | zero => rfl
  | succ s ih =>
      have hslt : s < k := Nat.lt_of_succ_le hs
      have hsle : s ≤ k := Nat.le_of_lt hslt
      rw [progressMatrix_succ_det b k hk s hslt]
      exact ih hsle

/-- Dot product of cast integer rows equals the rational cast of the integer
dot product. -/
private theorem dot_castIntRow_eq_cast_dot
    (b : Matrix Int n m) (i j : Fin n) :
    Matrix.dot (castIntRow b i) (castIntRow b j) =
      ((Matrix.dot (b.row i) (b.row j) : Int) : Rat) := by
  unfold Matrix.dot Hex.Vector.dotProduct
  rw [foldl_intCast_add_aux (xs := List.finRange m)
    (f := fun k : Fin m => (b.row i)[k] * (b.row j)[k]) (acc := 0)]
  rw [show ((0 : Int) : Rat) = (0 : Rat) from rfl]
  apply foldl_sum_congr_simple
  intro k _hk
  unfold castIntRow
  have hi_entry : (Vector.map (fun x : Int => (x : Rat)) (b.row i))[k] = ((b.row i)[k] : Rat) := by
    change (Vector.map (fun x : Int => (x : Rat)) (b.row i))[k.val] = ((b.row i)[k.val] : Rat)
    rw [Vector.getElem_map]
  have hj_entry : (Vector.map (fun x : Int => (x : Rat)) (b.row j))[k] = ((b.row j)[k] : Rat) := by
    change (Vector.map (fun x : Int => (x : Rat)) (b.row j))[k.val] = ((b.row j)[k.val] : Rat)
    rw [Vector.getElem_map]
  rw [hi_entry, hj_entry]
  rw [Rat.intCast_mul]

/-- The original-row coordinates chosen for the Gram-Schmidt prefix projection
solve the leading Gram linear system whose right-hand side is obtained by
dotting prefix rows with that projection. This is the matrix/vector form of
`originalProjectionCoords_dot_eq_gram_combination`; the downstream Cramer
identification rewrites the right-hand side to the replacement Gram column. -/
private theorem scaledCoeffMatrix_replacementColumn_solve
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i)
    (p : Fin (j + 1)) :
    (castIntDetMatrix
        (GramSchmidt.leadingGramMatrixInt b (j + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hj hi))) *
        originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[p] =
        Matrix.dot
          (castIntRow b
            ⟨p.val, Nat.lt_of_lt_of_le p.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
          (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) := by
  have hsys :=
    originalProjectionCoords_dot_eq_gram_combination
      (b := b) (i := i) (j := j) (hi := hi)
      (hj := Nat.lt_trans hj hi) p
  change
    (Matrix.mulVec
        (castIntDetMatrix
          (GramSchmidt.leadingGramMatrixInt b (j + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hj hi))))
        (originalProjectionCoords b i j hi (Nat.lt_trans hj hi)))[p] =
      Matrix.dot
        (castIntRow b
          ⟨p.val, Nat.lt_of_lt_of_le p.isLt
            (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi))
  rw [hsys]
  unfold Matrix.mulVec Matrix.row
  have hleft :
      (Vector.ofFn fun i' : Fin (j + 1) =>
          Matrix.dot
            (castIntDetMatrix
              (GramSchmidt.leadingGramMatrixInt b (j + 1)
                (Nat.succ_le_of_lt (Nat.lt_trans hj hi))))[i']
            (originalProjectionCoords b i j hi (Nat.lt_trans hj hi)))[p] =
        Matrix.dot
          (castIntDetMatrix
            (GramSchmidt.leadingGramMatrixInt b (j + 1)
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))))[p]
          (originalProjectionCoords b i j hi (Nat.lt_trans hj hi)) := by
    simp [Vector.getElem_ofFn]
  rw [hleft]
  change
    (List.finRange (j + 1)).foldl
      (fun acc q =>
        acc +
          (castIntDetMatrix
            (GramSchmidt.leadingGramMatrixInt b (j + 1)
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))))[p][q] *
            (originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[q]) 0 =
    (List.finRange (j + 1)).foldl
      (fun acc q =>
        acc +
          (originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[q] *
            Matrix.dot
              (castIntRow b
                ⟨p.val, Nat.lt_of_lt_of_le p.isLt
                  (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
              (castIntRow b
                ⟨q.val, Nat.lt_of_lt_of_le q.isLt
                  (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)) 0
  apply foldl_sum_congr_simple
  intro q _hq
  rw [castIntDetMatrix_get]
  simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, GramSchmidt.liftFinLE]
  rw [← dot_castIntRow_eq_cast_dot b
    (⟨p.val, Nat.lt_of_lt_of_le p.isLt
      (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩ : Fin n)
    (⟨q.val, Nat.lt_of_lt_of_le q.isLt
      (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩ : Fin n)]
  grind

/-- At `s = 0`, `progressMatrix` equals the entry-wise cast of
`leadingGramMatrixInt`. -/
private theorem progressMatrix_zero_eq_castIntDetMatrix (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    progressMatrix b k hk 0 =
      castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin k := ⟨i, hi⟩
  let jj : Fin k := ⟨j, hj⟩
  change (progressMatrix b k hk 0)[ii][jj] =
    (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk))[ii][jj]
  have hjnlt : ¬ jj.val < 0 := Nat.not_lt_zero _
  rw [progressMatrix_get_ge b k hk 0 ii jj hjnlt]
  rw [castIntDetMatrix_get]
  -- LHS: Matrix.dot (castIntRow b (lift ii)) (castIntRow b (lift jj))
  -- RHS: ((leadingGramMatrixInt b k hk)[ii][jj] : Int : Rat)
  --   = (Matrix.dot (b.row (lift ii)) (b.row (lift jj)) : Int : Rat)
  rw [dot_castIntRow_eq_cast_dot]
  -- Match up the leadingGramMatrixInt entry definition.
  simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn]

/-- `(gramDet b k hk : Rat)` equals the determinant of `progressMatrix` at the
starting index `s = 0`. -/
private theorem gramDet_rat_eq_progressMatrix_zero_det (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = Matrix.det (progressMatrix b k hk 0) := by
  -- (gramDet b k hk : Rat) = ((Matrix.det leadingGramMatrixInt b k hk : Int) : Rat)
  -- via leadingGramMatrixInt_det_nonneg + bareiss_eq_det.
  have hdet_int :
      Matrix.det (GramSchmidt.leadingGramMatrixInt b k hk) =
        Int.ofNat (gramDet b k hk) := by
    rw [gramDet, HexMatrixMathlib.bareiss_eq_mathlib_det, ← HexMatrixMathlib.det_eq]
    exact (Int.toNat_of_nonneg (leadingGramMatrixInt_det_nonneg b k hk)).symm
  have hstep1 : ((gramDet b k hk : Int) : Rat) =
      ((Matrix.det (GramSchmidt.leadingGramMatrixInt b k hk) : Int) : Rat) := by
    rw [hdet_int]
    rfl
  -- ((det leadingGramMatrixInt b k hk : Int) : Rat) = det (castIntDetMatrix _)
  -- via det_intCast.
  have hstep2 : ((Matrix.det (GramSchmidt.leadingGramMatrixInt b k hk) : Int) : Rat) =
      Matrix.det (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk)) :=
    det_intCast (GramSchmidt.leadingGramMatrixInt b k hk)
  -- det (castIntDetMatrix _) = det (progressMatrix b k hk 0) via progressMatrix_zero_eq.
  have hstep3 :
      Matrix.det (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk)) =
        Matrix.det (progressMatrix b k hk 0) := by
    rw [progressMatrix_zero_eq_castIntDetMatrix]
  -- Now (gramDet b k hk : Rat) = ((gramDet : Int) : Rat) by cast chain.
  have hcast_chain : ((gramDet b k hk : Nat) : Rat) =
      ((gramDet b k hk : Int) : Rat) := by
    push_cast; rfl
  rw [hcast_chain]
  rw [hstep1, hstep2, hstep3]

/-- Core proof of the Gram-determinant / squared-norm product identity.

Chain: `(gramDet b k hk : Rat) = det (progressMatrix b k hk 0) =
det (progressMatrix b k hk k) = det (auxMatrix b k hk) = gramSchmidtNormProduct`.
Note: the proof does not use the independence hypothesis since both sides are
computed purely from `b`. The hypothesis is kept for parity with the public
theorem and downstream callers. -/
private theorem gramDet_eq_prod_normSq_core (b : Matrix Int n m)
    (_hli : independent b) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk := by
  rw [gramDet_rat_eq_progressMatrix_zero_det b k hk]
  rw [← progressMatrix_det_invariant b k hk k (Nat.le_refl k)]
  rw [progressMatrix_full_eq_auxMatrix]
  exact auxMatrix_det_eq_prod_normSq b k hk

theorem gramDet_eq_prod_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk :=
  gramDet_eq_prod_normSq_core b hli k hk

theorem gramDet_pos (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  exact gramDet_pos_core b hli k hk hk'

/-- One-step extension of `gramSchmidtNormProduct`: appending the `k`-th
factor multiplies the `k`-fold product by `Vector.normSq ((basis b).row ⟨k, _⟩)`.
This is a `List.finRange` cancellation lemma; positivity of the leading Gram
determinant is handled separately by `gramDet_pos`. -/
theorem gramSchmidtNormProduct_succ (b : Matrix Int n m)
    (k : Nat) (hk : k + 1 ≤ n) :
    gramSchmidtNormProduct b (k + 1) hk =
      gramSchmidtNormProduct b k (Nat.le_of_succ_le hk) *
        Vector.normSq ((basis b).row ⟨k, Nat.lt_of_succ_le hk⟩) := by
  unfold gramSchmidtNormProduct
  rw [List.finRange_succ_last]
  rw [List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  rfl

private theorem basis_normSq_core (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k < n) :
    Vector.normSq ((basis b).row ⟨k, hk⟩) =
      (gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Rat) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  have hk_le : k ≤ n := Nat.le_of_lt hk
  have hden_pos : 0 < (gramDet b k hk_le : Rat) := by
    rw [Rat.natCast_pos]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; rw [gramDet_zero]; decide
    · exact gramDet_pos b hli k hk_le hkpos
  have hprod_ne : gramSchmidtNormProduct b k hk_le ≠ 0 := by
    rw [← gramDet_eq_prod_normSq b hli k hk_le]
    exact Rat.ne_of_gt hden_pos
  rw [gramDet_eq_prod_normSq b hli (k + 1) (Nat.succ_le_of_lt hk)]
  rw [gramDet_eq_prod_normSq b hli k hk_le]
  rw [gramSchmidtNormProduct_succ b k (Nat.succ_le_of_lt hk)]
  rw [Rat.mul_comm]
  exact (Rat.mul_div_cancel hprod_ne).symm

theorem basis_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k < n) :
    Vector.normSq ((basis b).row ⟨k, hk⟩) =
      (gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Rat) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  exact basis_normSq_core b hli k hk

/-- Original-row dot products vanish against orthogonal basis vectors of higher
index. For `p < r`, `castIntRow b p` lies in the basis-vector span of indices
`≤ p`, which is orthogonal to `(basis b).row r`. -/
private theorem dot_castIntRow_basis_eq_zero_of_lt
    (b : Matrix Int n m) (p r : Nat) (hp : p < n) (hr : r < n) (hpr : p < r) :
    Matrix.dot (castIntRow b ⟨p, hp⟩) ((basis b).row ⟨r, hr⟩) = 0 := by
  rw [dot_comm_rat]
  rw [castIntRow_decomposition b p hp]
  rw [dot_add_right_rat]
  have hbasis : Matrix.dot ((basis b).row ⟨r, hr⟩) ((basis b).row ⟨p, hp⟩) = 0 :=
    basis_orthogonal b r p hr hp (Nat.ne_of_gt hpr)
  have hprefix : Matrix.dot ((basis b).row ⟨r, hr⟩)
      (GramSchmidt.prefixCombination (coeffs b) (basis b) p hp) = 0 := by
    apply dot_prefixCombination_right_eq_zero_of_dot_zero
      (coeffs := coeffs b) (basisM := basis b) (i := p) (hi := hp)
      (u := (basis b).row ⟨r, hr⟩)
    intro p'
    have hp'_lt_p : p'.val < p := p'.isLt
    have hp'_lt_r : p'.val < r := Nat.lt_trans hp'_lt_p hpr
    have hp'_lt_n : p'.val < n := Nat.lt_trans hp'_lt_p hp
    exact basis_orthogonal b r p'.val hr hp'_lt_n (Nat.ne_of_gt hp'_lt_r)
  rw [hbasis, hprefix]
  grind

/-- Truncate a `Fin m` foldl to `Fin k₀` when the proof-indexed body vanishes
on indices `≥ k₀` and `k₀ ≤ m`. Induction is on `m`. -/
private theorem foldl_finRange_truncate_zero_above
    {n : Nat} (body : ∀ (k : Nat), k < n → Rat) (acc : Rat) (k₀ : Nat)
    (h_zero : ∀ r : Nat, k₀ ≤ r → (hrn : r < n) → body r hrn = 0) :
    ∀ (m : Nat) (hk : m ≤ n) (hkk : k₀ ≤ m),
      (List.finRange m).foldl
          (fun (acc' : Rat) (r : Fin m) =>
            acc' + body r.val (Nat.lt_of_lt_of_le r.isLt hk)) acc =
        (List.finRange k₀).foldl
          (fun (acc' : Rat) (q : Fin k₀) =>
            acc' + body q.val (Nat.lt_of_lt_of_le q.isLt (Nat.le_trans hkk hk))) acc := by
  intro m
  induction m with
  | zero =>
      intro _ hkk
      have hk₀ : k₀ = 0 := Nat.eq_zero_of_le_zero hkk
      subst hk₀
      rfl
  | succ m ih =>
      intro hk hkk
      rcases Nat.lt_or_ge m k₀ with hmk | hkm
      · have hk_eq : k₀ = m + 1 := Nat.le_antisymm hkk (Nat.succ_le_of_lt hmk)
        subst hk_eq
        rfl
      · have hk' : m ≤ n := Nat.le_of_succ_le hk
        have h_last_lt : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hk
        have h_last_zero : body m h_last_lt = 0 := h_zero m hkm h_last_lt
        rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
        simp only [List.foldl_cons, List.foldl_nil]
        have h_last :
            body (Fin.last m).val
                (Nat.lt_of_lt_of_le (Fin.last m).isLt hk) = 0 :=
          h_last_zero
        rw [h_last, Rat.add_zero]
        exact ih hk' hkm

/-- The Gram-Schmidt prefix projection of row `i` onto the span of rows
`0, ..., j` agrees with `castIntRow b i` when dotted with `castIntRow b p` for
any `p ≤ j < i`. The residue between the two lies in the span of basis vectors
of indices `> j`, hence orthogonal to `castIntRow b p`. -/
private theorem dot_castIntRow_castIntRow_eq_dot_basisPrefixProjection
    (b : Matrix Int n m) (i j p : Nat) (hi : i < n) (hj : j < i)
    (hp_le_j : p ≤ j) (hp : p < n) :
    Matrix.dot (castIntRow b ⟨p, hp⟩) (castIntRow b ⟨i, hi⟩) =
      Matrix.dot (castIntRow b ⟨p, hp⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) := by
  -- Substitute `i = (j + 1) + d` so the foldl bounds align with the helper.
  obtain ⟨d, rfl⟩ : ∃ d, i = (j + 1) + d := ⟨i - (j + 1), by omega⟩
  have hkdn : (j + 1) + d ≤ n := Nat.le_of_lt hi
  -- LHS via basis_decomposition for `castIntRow b i`.
  rw [castIntRow_decomposition b ((j + 1) + d) hi]
  rw [dot_add_right_rat]
  rw [dot_castIntRow_basis_eq_zero_of_lt b p ((j + 1) + d) hp hi
    (Nat.lt_of_le_of_lt hp_le_j hj)]
  rw [Rat.zero_add]
  rw [dot_prefixCombination_right_rat (coeffs := coeffs b) (basisM := basis b)
    (i := (j + 1) + d) (hi := hi) (u := castIntRow b ⟨p, hp⟩)]
  -- RHS unfold and expand basisPrefixProjection.
  unfold basisPrefixProjection
  rw [dot_rowCombination_right_rat]
  -- Define a Nat-indexed body shared by both sides.
  let body : ∀ (k : Nat), k < n → Rat := fun k hk =>
    GramSchmidt.entry (coeffs b) ⟨(j + 1) + d, hi⟩ ⟨k, hk⟩ *
      Matrix.dot (castIntRow b ⟨p, hp⟩) ((basis b).row ⟨k, hk⟩)
  -- Normalize the RHS foldl body to use `body`. The literal proof inside the
  -- unfolded `basisPrefixProjection` is `Nat.lt_trans hj hi`.
  have hRHS :
      (List.finRange (j + 1)).foldl
          (fun (acc' : Rat) (q : Fin (j + 1)) =>
            acc' +
              (projectionCoeffPrefix b ((j + 1) + d) j hi
                (Nat.lt_trans hj hi))[q] *
              Matrix.dot (castIntRow b ⟨p, hp⟩)
                ((GramSchmidt.prefixRows (basis b) j (Nat.lt_trans hj hi)).row q)) 0 =
        (List.finRange (j + 1)).foldl
          (fun (acc' : Rat) (q : Fin (j + 1)) =>
            acc' + body q.val (Nat.lt_of_lt_of_le q.isLt
              (Nat.le_trans (Nat.le_add_right (j + 1) d) hkdn))) 0 := by
    apply foldl_sum_congr_simple
    intro q _hq
    have hq_lt_n : q.val < n :=
      Nat.lt_of_lt_of_le q.isLt (Nat.le_trans (Nat.le_add_right (j + 1) d) hkdn)
    have hcoeff :
        (projectionCoeffPrefix b ((j + 1) + d) j hi (Nat.lt_trans hj hi))[q] =
          GramSchmidt.entry (coeffs b) ⟨(j + 1) + d, hi⟩ ⟨q.val, hq_lt_n⟩ := by
      simp [projectionCoeffPrefix, Vector.getElem_ofFn]
    have hrow :
        (GramSchmidt.prefixRows (basis b) j (Nat.lt_trans hj hi)).row q =
          (basis b).row ⟨q.val, hq_lt_n⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn]
    rw [hcoeff, hrow]
  rw [hRHS]
  -- Apply foldl truncation. By proof irrelevance the LHS body matches.
  exact foldl_finRange_truncate_zero_above body 0 (j + 1)
    (by
      intro r hjr hrn
      show GramSchmidt.entry (coeffs b) ⟨(j + 1) + d, hi⟩ ⟨r, hrn⟩ *
          Matrix.dot (castIntRow b ⟨p, hp⟩) ((basis b).row ⟨r, hrn⟩) = 0
      have hpr : p < r := Nat.lt_of_le_of_lt hp_le_j (Nat.lt_of_succ_le hjr)
      rw [dot_castIntRow_basis_eq_zero_of_lt b p r hp hrn hpr]
      grind)
    ((j + 1) + d) hkdn (Nat.le_add_right (j + 1) d)

private theorem dot_basisPrefixProjection_eq_castIntGram
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i)
    (p : Fin (j + 1)) :
    Matrix.dot
        (castIntRow b
          ⟨p.val, Nat.lt_of_lt_of_le p.isLt
            (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) =
      ((Matrix.dot
          (b.row
            ⟨p.val, Nat.lt_of_lt_of_le p.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
          (b.row ⟨i, hi⟩) : Int) : Rat) := by
  rw [← dot_castIntRow_eq_cast_dot b
    (⟨p.val, Nat.lt_of_lt_of_le p.isLt
      (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩ : Fin n)
    (⟨i, hi⟩ : Fin n)]
  exact
    (dot_castIntRow_castIntRow_eq_dot_basisPrefixProjection
      b i j p.val hi hj (Nat.le_of_lt_succ p.isLt)
      (Nat.lt_of_lt_of_le p.isLt
        (Nat.succ_le_of_lt (Nat.lt_trans hj hi)))).symm

private theorem scaledCoeffMatrix_replacementColumn_solve_intGram
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i)
    (p : Fin (j + 1)) :
    (castIntDetMatrix
        (GramSchmidt.leadingGramMatrixInt b (j + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hj hi))) *
        originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[p] =
      ((Matrix.dot
          (b.row
            ⟨p.val, Nat.lt_of_lt_of_le p.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
          (b.row ⟨i, hi⟩) : Int) : Rat) := by
  rw [scaledCoeffMatrix_replacementColumn_solve b i j hi hj p]
  exact dot_basisPrefixProjection_eq_castIntGram b i j hi hj p

/-- Isolate the last term in a `foldl` over `List.finRange (k + 1)` when every
earlier term vanishes. -/
private theorem foldl_finRange_succ_isolate_last
    (k : Nat) (f : Fin (k + 1) → Rat)
    (h_zero : ∀ q : Fin (k + 1), q.val < k → f q = 0) :
    (List.finRange (k + 1)).foldl
        (fun (acc : Rat) (q : Fin (k + 1)) => acc + f q) 0 =
      f (Fin.last k) := by
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  have hfold_zero :
      (List.finRange k).foldl
          (fun (acc : Rat) (q : Fin k) => acc + f (Fin.castSucc q)) 0 = 0 := by
    have hgen : ∀ (xs : List (Fin k)) (acc : Rat),
        xs.foldl (fun acc' q => acc' + f (Fin.castSucc q)) acc = acc := by
      intro xs
      induction xs with
      | nil => intro acc; rfl
      | cons q xs ih =>
          intro acc
          simp only [List.foldl_cons]
          have hq : f (Fin.castSucc q) = 0 := h_zero (Fin.castSucc q) q.isLt
          rw [hq, Rat.add_zero]
          exact ih acc
    exact hgen (List.finRange k) 0
  rw [hfold_zero, Rat.zero_add]

/-- Dotting `basisPrefixProjection b i j` with the Gram-Schmidt basis vector
`(basis b).row ⟨j, _⟩` extracts the projection coefficient `coeffs[i][j]`,
weighted by `(basis b).row j`'s squared norm. -/
private theorem dot_basis_basisPrefixProjection_eq_coeff_mul_normSq
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    Matrix.dot ((basis b).row ⟨j, Nat.lt_trans hj hi⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) =
      GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ *
        Vector.normSq ((basis b).row ⟨j, Nat.lt_trans hj hi⟩) := by
  have hjlt : j < n := Nat.lt_trans hj hi
  unfold basisPrefixProjection
  rw [dot_rowCombination_right_rat]
  -- Isolate the q = ⟨j, lt_succ_self j⟩ term in the foldl.
  rw [foldl_finRange_succ_isolate_last j _ ?_]
  · -- Last term: projectionCoeffPrefix[⟨j, _⟩] * dot basis[j] basis[j].
    have hrow :
        (GramSchmidt.prefixRows (basis b) j hjlt).row (Fin.last j) =
          (basis b).row ⟨j, hjlt⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn, Fin.last]
    have hcoeff :
        (projectionCoeffPrefix b i j hi hjlt)[Fin.last j] =
          GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ := by
      simp [projectionCoeffPrefix, Vector.getElem_ofFn, Fin.last]
    rw [hcoeff, hrow]
    rfl
  · -- For q < j: dot basis[j] basis[q.val_lift] = 0.
    intro q hqval
    have hq_lt_n : q.val < n :=
      Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hjlt)
    have hrow :
        (GramSchmidt.prefixRows (basis b) j hjlt).row q =
          (basis b).row ⟨q.val, hq_lt_n⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn]
    rw [hrow]
    rw [basis_orthogonal b j q.val hjlt hq_lt_n (Nat.ne_of_gt hqval)]
    grind

/-- Dotting `basisPrefixProjection b i j` with `(basis b).row ⟨j, _⟩` also
extracts the original-row coordinate, weighted by the squared norm. -/
private theorem dot_basis_basisPrefixProjection_eq_origProjCoords_mul_normSq
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    Matrix.dot ((basis b).row ⟨j, Nat.lt_trans hj hi⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) =
      (originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[Fin.last j] *
        Vector.normSq ((basis b).row ⟨j, Nat.lt_trans hj hi⟩) := by
  have hjlt : j < n := Nat.lt_trans hj hi
  rw [← originalProjectionCoords_spec b i j hi hjlt]
  rw [dot_rowCombination_right_rat]
  rw [foldl_finRange_succ_isolate_last j _ ?_]
  · -- Last term: origProjCoords[⟨j, _⟩] * dot basis[j] (cast b row j).
    -- castIntMatrixRat b row at ⟨j, _⟩ = castIntRow b ⟨j, _⟩.
    have hrow :
        (GramSchmidt.prefixRows (castIntMatrixRat b) j hjlt).row (Fin.last j) =
          castIntRow b ⟨j, hjlt⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn,
        castIntMatrixRat, castIntRow, Fin.last]
    rw [hrow]
    -- dot basis[j] castIntRow b j = dot basis[j] (basis[j] + prefixComb) = normSq + 0.
    rw [castIntRow_decomposition b j hjlt]
    rw [dot_add_right_rat]
    have hbasis_self :
        Matrix.dot ((basis b).row ⟨j, hjlt⟩) ((basis b).row ⟨j, hjlt⟩) =
          Vector.normSq ((basis b).row ⟨j, hjlt⟩) := rfl
    rw [hbasis_self]
    have hprefix :
        Matrix.dot ((basis b).row ⟨j, hjlt⟩)
            (GramSchmidt.prefixCombination (coeffs b) (basis b) j hjlt) = 0 := by
      apply dot_prefixCombination_right_eq_zero_of_dot_zero
        (coeffs := coeffs b) (basisM := basis b) (i := j) (hi := hjlt)
        (u := (basis b).row ⟨j, hjlt⟩)
      intro r
      have hr_lt_j : r.val < j := r.isLt
      have hr_lt_n : r.val < n := Nat.lt_trans hr_lt_j hjlt
      exact basis_orthogonal b j r.val hjlt hr_lt_n (Nat.ne_of_gt hr_lt_j)
    rw [hprefix, Rat.add_zero]
  · -- For q < j: dot basis[j] castIntRow b q = 0.
    intro q hqval
    have hq_lt_n : q.val < n :=
      Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hjlt)
    have hrow :
        (GramSchmidt.prefixRows (castIntMatrixRat b) j hjlt).row q =
          castIntRow b ⟨q.val, hq_lt_n⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn,
        castIntMatrixRat, castIntRow]
    rw [hrow]
    rw [dot_comm_rat]
    rw [dot_castIntRow_basis_eq_zero_of_lt b q.val j hq_lt_n hjlt hqval]
    grind

/-- The Gram-determinant succession: `(gramDet (j+1) : Rat)` factors as
`(gramSchmidtNormProduct j) * normSq(basis[j])`. -/
theorem gramDet_succ_rat
    (b : Matrix Int n m) (j : Nat) (hjsuc : j + 1 ≤ n) :
    (gramDet b (j + 1) hjsuc : Rat) =
      gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
        Vector.normSq ((basis b).row ⟨j, Nat.lt_of_succ_le hjsuc⟩) := by
  have hgd_eq_gsnp :
      (gramDet b (j + 1) hjsuc : Rat) = gramSchmidtNormProduct b (j + 1) hjsuc := by
    rw [gramDet_rat_eq_progressMatrix_zero_det]
    rw [← progressMatrix_det_invariant b (j + 1) hjsuc (j + 1) (Nat.le_refl _)]
    rw [progressMatrix_full_eq_auxMatrix]
    exact auxMatrix_det_eq_prod_normSq b (j + 1) hjsuc
  rw [hgd_eq_gsnp]
  exact gramSchmidtNormProduct_succ b j hjsuc

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
        Matrix.colReplace
          (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
          (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
          (fun p : Fin (j + 1) =>
            Matrix.dot
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
        (Matrix.colReplace _ _ _)[pp][cc]
    rw [Matrix.colReplace_get, castIntDetMatrix_get]
    by_cases hc_eq : cc = (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
    · rw [if_pos hc_eq]
      have hc_val : cc.val = j := congrArg Fin.val hc_eq
      have hsc :
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj)[pp][cc] =
            Matrix.dot
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨i, hi⟩) := by
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn,
          GramSchmidt.liftFinLE, hc_val]
      rw [hsc, ← dot_castIntRow_eq_cast_dot]
    · rw [if_neg hc_eq, castIntDetMatrix_get]
      have hc_ne : cc.val ≠ j := fun h => hc_eq (Fin.ext h)
      have hsc :
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj)[pp][cc] =
            Matrix.dot
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt hjsuc⟩) := by
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn,
          GramSchmidt.liftFinLE, hc_ne]
      have hG :
          (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc)[pp][cc] =
            Matrix.dot
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt hjsuc⟩) := by
        simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn,
          GramSchmidt.liftFinLE]
      rw [hsc, hG]
  rw [hM_colReplace]
  -- Step 2: rewrite the replacement column as `castG * originalProjectionCoords`.
  have hcol_lin_comb :
      (fun p : Fin (j + 1) =>
        Matrix.dot
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
    rw [dot_castIntRow_castIntRow_eq_dot_basisPrefixProjection b i j p.val hi hj
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
            Matrix.dot
              (castIntDetMatrix
                (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[i']
              (originalProjectionCoords b i j hi hjlt))[p] =
          Matrix.dot
            (castIntDetMatrix
              (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[p]
            (originalProjectionCoords b i j hi hjlt) := by
      simp [Vector.getElem_ofFn]
    rw [hleft]
    unfold Matrix.dot Hex.Vector.dotProduct
    apply foldl_sum_congr_simple
    intro q _hq
    grind
  rw [hcol_lin_comb]
  -- Step 3: apply det_colReplace_sum_finRange.
  rw [Matrix.det_colReplace_sum_finRange]
  -- Step 4: isolate the q = ⟨j, _⟩ term.
  rw [foldl_finRange_succ_isolate_last j _ ?_]
  · -- Last term: origProjCoords[⟨j, _⟩] * det castG.
    have hlast_self :
        Matrix.colReplace
            (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
            (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
            (fun p : Fin (j + 1) =>
              (castIntDetMatrix
                (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[p][Fin.last j]) =
          castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc) :=
      Matrix.colReplace_self _ _
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
    rw [Matrix.det_colReplace_existing_col_eq_zero _ _ _ hq_ne]
    grind

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
    have h_vec_gd := gramDetVecEntry_eq_gramDet (b := b) (j.val + 1) hsucc
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
private theorem trailing_eq_at_step_local
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
private theorem noPivotLoop_augmentedGram_invariant
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
private theorem noPivotLoop_initial_step_eq_and_fuel_succ_le_of_no_sing
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
private theorem prevPivot_eq_at_step_local
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
def StepWitness.ofGram (b : Matrix Int n m) :
    Hex.GramSchmidt.Int.StepWitness b := by
  intro fuel hinv h_canon h_prefix_none hnext hp i hi
  -- Prepare bound facts and the step equality before refining.
  set state := Matrix.noPivotLoop fuel
    (Matrix.noPivotInitialState (Matrix.gramMatrix b)) with hstate
  obtain ⟨h_step_eq_fuel, hfuel_n_le⟩ :=
    noPivotLoop_initial_step_eq_and_fuel_succ_le_of_no_sing (Matrix.gramMatrix b)
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

/-- Non-singular branch of the Cramer/Bareiss identity: when the no-pivot
Bareiss pass over the Gram matrix reaches column `j` without recording a
singular step, the executable scaled coefficient agrees with the public
row-pivoted Bareiss determinant of the Cramer minor. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss_of_no_singular
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  have hjn : j.val < n := Nat.lt_trans hji i.isLt
  -- Convert the LHS to the trailing entry of the no-pivot loop on `scaledCoeffMatrix`.
  rw [scaledCoeffs_lower_eq_noPivotLoop_scaledCoeffMatrix b (StepWitness.ofGram b)
    i j hji h_nonsing]
  -- Propagate non-singularity from `gramMatrix b` to `scaledCoeffMatrix b i j hji`
  -- via the bordered-minor identification.
  have h_sync :=
    noPivotLoop_full_eq_borderedMinor_at_trailing (Matrix.gramMatrix b) j.val hjn
      ⟨j.val, hjn⟩ i (Nat.le_refl j.val) (Nat.le_of_lt hji)
  have h_bm_nonsing :
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (Matrix.borderedMinor (Matrix.gramMatrix b) j.val hjn
            ⟨j.val, hjn⟩ i))).singularStep = none := by
    rw [← h_sync.2]; exact h_nonsing
  have h_sc_nonsing :
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (GramSchmidt.scaledCoeffMatrix b i j hji))).singularStep = none := by
    rw [scaledCoeffMatrix_eq_borderedMinor]; exact h_bm_nonsing
  exact (Matrix.bareiss_eq_noPivotLoop_last_of_no_singular
    (GramSchmidt.scaledCoeffMatrix b i j hji) h_sc_nonsing).symm

/-- Cramer/Bareiss identity: below the diagonal, the integral scaled
Gram-Schmidt coefficient is exactly the public Bareiss determinant of the
Cramer minor `scaledCoeffMatrix`. The proof splits on whether the no-pivot
Bareiss pass over `gramMatrix b` reaches column `j` without recording a
singular step:

- Non-singular branch: defer to
  `scaledCoeffs_eq_scaledCoeffMatrix_bareiss_of_no_singular`.
- Singular branch: both sides vanish — the executable scaled coefficient is
  zero by `scaledCoeffs_eq_zero_of_singularStep_lt` (the lifted lower-column
  singular lemma from #4166), and the public Bareiss determinant of the
  Cramer minor is zero by composing `HexMatrixMathlib.bareiss_eq_mathlib_det`,
  `HexMatrixMathlib.det_eq.symm`, and
  `scaledCoeffMatrix_det_eq_zero_of_singularStep_lt`. The latter Mathlib-free
  helper internally lifts partial-pass singularity to the full
  `bareissNoPivotData` pass and applies the Cramer determinant identity.

The private `scaledCoeffRows_lower_eq_coeffs` helper below reroutes through
this case-split identity instead of the older chain proof. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_bareiss
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  cases h_sing : (Matrix.noPivotLoop j.val
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep with
  | none =>
      exact scaledCoeffs_eq_scaledCoeffMatrix_bareiss_of_no_singular b i j hji h_sing
  | some s =>
      have hsj : s < j.val := by
        have h := noPivotLoop_singularStep_lt j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
        change s < 0 + j.val at h
        omega
      have h_lhs : GramSchmidt.entry (scaledCoeffs b) i j = 0 :=
        scaledCoeffs_eq_zero_of_singularStep_lt b (StepWitness.ofGram b)
          i j hji s h_sing hsj
      have h_det := scaledCoeffMatrix_det_eq_zero_of_singularStep_lt
        b i j hji s h_sing
      have hbareiss_zero :
          Hex.Matrix.bareiss (GramSchmidt.scaledCoeffMatrix b i j hji) = 0 :=
        ((HexMatrixMathlib.bareiss_eq_mathlib_det _).trans
          (HexMatrixMathlib.det_eq _).symm).trans h_det
      rw [h_lhs, hbareiss_zero]

/-- The fraction-free scaled-coefficient loop computes the Cramer/Bareiss
integer equal to `d[j+1] * μ[i,j]` below the diagonal. -/
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
  rw [h_array,
    scaledCoeffs_eq_scaledCoeffMatrix_bareiss b ⟨i, hi⟩ ⟨j, hjlt⟩ hj,
    scaledCoeffMatrix_bareiss_eq_det b i j hi hj]
  exact scaledCoeffMatrix_det_eq_gramDet_mul_coeffs b i j hi hj

/-- Below the diagonal, the rational image of the integer scaled
Gram-Schmidt coefficient factors as `gramDet b (j+1) * coeffs[i,j]`. The
proof routes through `scaledCoeffs_eq_scaledCoeffMatrix_bareiss` (via
`scaledCoeffRows_lower_eq_coeffs`) instead of the older chain proof that
depended on `scaledCoeffs_eq_scaledCoeffMatrix_det`. -/
theorem scaledCoeffs_eq (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < i) :
    ((GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ : Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ := by
  have h_array :
      GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ =
        getArrayEntry (scaledCoeffRows b) i j := by
    rw [scaledCoeffs_entry_eq_getArrayEntry,
      getArrayEntry_scaledCoeffRowsSchur_eq b (StepWitness.ofGram b)]
  rw [h_array]
  exact scaledCoeffRows_lower_eq_coeffs b i j hi hj

/-! ### Adjacent-swap pivot Gram-determinant product

Swapping adjacent rows `km1, k` (with `km1 + 1 = k`) of `b` changes only the
leading `k × k` Gram determinant within `0 ≤ t ≤ k + 1`. The new pivot Gram
determinant `gramDet (rowSwap b km1 k) k` satisfies the integer product
identity

    gramDet b' k · gramDet b k = gramDet b (k+1) · gramDet b km1 + B²

where `B = (scaledCoeffs b)[k][km1]`. This is the fraction-free form of the
standard rational adjacent-swap update used by integer LLL. -/

/-- If two integers cast to equal rationals, they are equal. -/
private theorem intCast_rat_injective_int_eq {a b : Int} (h : (a : Rat) = (b : Rat)) :
    a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by
    push_cast
    grind
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega

theorem dot_add_left_rat {m' : Nat} (u v w : Vector Rat m') :
    Matrix.dot (u + v) w = Matrix.dot u w + Matrix.dot v w := by
  rw [dot_comm_rat (u := u + v) (v := w)]
  rw [dot_add_right_rat (u := w) (v := u) (w := v)]
  rw [dot_comm_rat (u := w) (v := u), dot_comm_rat (u := w) (v := v)]

theorem dot_smul_left_rat {m' : Nat} (s : Rat) (u v : Vector Rat m') :
    Matrix.dot (s • u) v = s * Matrix.dot u v := by
  rw [dot_comm_rat (u := s • u) (v := v)]
  rw [dot_smul_right_rat (s := s) (u := v) (v := u)]
  rw [dot_comm_rat (u := v) (v := u)]

/-- Pythagoras: if `curr ⊥ prev`, then the squared norm of `curr + μ • prev`
splits as `‖curr‖² + μ² · ‖prev‖²`. -/
theorem normSq_add_smul_orthogonal_rat {m' : Nat}
    (curr prev : Vector Rat m') (μ : Rat)
    (horth : Matrix.dot curr prev = 0) :
    Vector.normSq (curr + μ • prev) =
      Vector.normSq curr + μ ^ 2 * Vector.normSq prev := by
  show Matrix.dot (curr + μ • prev) (curr + μ • prev) =
    Matrix.dot curr curr + μ ^ 2 * Matrix.dot prev prev
  rw [dot_add_left_rat (u := curr) (v := μ • prev) (w := curr + μ • prev)]
  rw [dot_add_right_rat (u := curr) (v := curr) (w := μ • prev)]
  rw [dot_add_right_rat (u := μ • prev) (v := curr) (w := μ • prev)]
  rw [dot_smul_right_rat (s := μ) (u := curr) (v := prev)]
  rw [dot_smul_left_rat (s := μ) (u := prev) (v := curr)]
  rw [dot_smul_left_rat (s := μ) (u := prev) (v := μ • prev)]
  rw [dot_smul_right_rat (s := μ) (u := prev) (v := prev)]
  have horth_swap : Matrix.dot prev curr = 0 := by
    rw [dot_comm_rat]; exact horth
  rw [horth, horth_swap]
  grind

/-- For `j < km1.val`, the Gram-Schmidt basis row is unchanged by the swap
of rows `km1, k`. The norm-square product over indices `< km1.val` therefore
agrees on `b` and `Matrix.rowSwap b km1 k`. -/
theorem gramSchmidtNormProduct_rowSwap_below
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1k : km1.val < k.val) :
    gramSchmidtNormProduct (Matrix.rowSwap b km1 k) km1.val
        (Nat.le_of_lt km1.isLt) =
      gramSchmidtNormProduct b km1.val (Nat.le_of_lt km1.isLt) := by
  unfold gramSchmidtNormProduct
  apply foldl_mul_congr_simple
  intro j _hj
  have hj_lt_km1 : j.val < km1.val := j.isLt
  congr 1
  exact basis_rowSwap_of_before b km1 k
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt km1.isLt)⟩ hkm1k hj_lt_km1

/-- Unconditional version of `gramDet_eq_prod_normSq`: the leading Gram
determinant casts to the rational `gramSchmidtNormProduct` without requiring
linear independence. The `independent` hypothesis in the public theorem is
not actually used by the proof. -/
theorem gramDet_eq_prod_normSq_uncond (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk := by
  rw [gramDet_rat_eq_progressMatrix_zero_det b k hk]
  rw [← progressMatrix_det_invariant b k hk k (Nat.le_refl k)]
  rw [progressMatrix_full_eq_auxMatrix]
  exact auxMatrix_det_eq_prod_normSq b k hk

/-- `gramDet` is independent of the propositional `≤ n` proof, and depends only
on the Nat value `k`. Two `gramDet` calls with equal `Nat` arguments produce
equal values. -/
theorem gramDet_subst_val
    (b : Matrix Int n m) (j₁ j₂ : Nat) (h₁ : j₁ ≤ n) (h₂ : j₂ ≤ n)
    (he : j₁ = j₂) :
    gramDet b j₁ h₁ = gramDet b j₂ h₂ := by
  subst he
  rfl

/-- Same as `gramDet_subst_val` for `gramSchmidtNormProduct`. -/
theorem gramSchmidtNormProduct_subst_val
    (b : Matrix Int n m) (j₁ j₂ : Nat) (h₁ : j₁ ≤ n) (h₂ : j₂ ≤ n)
    (he : j₁ = j₂) :
    gramSchmidtNormProduct b j₁ h₁ = gramSchmidtNormProduct b j₂ h₂ := by
  subst he
  rfl

/-- Integer fraction-free identity for the leading pivot Gram determinant
after swapping adjacent rows `km1, k` with `km1.val + 1 = k.val`:

    gramDet b' k · gramDet b k = gramDet b (k+1) · gramDet b km1 + B²

where `B = (scaledCoeffs b)[k][km1]`. This is the algebraic heart of the
integer LLL adjacent-swap update. -/
theorem gramDet_rowSwap_adjacent_pivot_product
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
    ((gramDet (Matrix.rowSwap b km1 k) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) *
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
        B ^ 2 := by
  intro B
  have hkm1k : km1.val < k.val := by omega
  have hkm1_le_n : km1.val ≤ n := Nat.le_of_lt km1.isLt
  have hk_le_n : k.val ≤ n := Nat.le_of_lt k.isLt
  have hk1_le_n : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
  have hkm1_succ_le : km1.val + 1 ≤ n := Nat.succ_le_of_lt km1.isLt
  -- Local abbreviations on the rational side.
  let μ : Rat := GramSchmidt.entry (coeffs b) k km1
  let prev : Vector Rat m := (basis b).row km1
  let curr : Vector Rat m := (basis b).row k
  let G : Rat := gramSchmidtNormProduct b km1.val hkm1_le_n
  let Nkm1 : Rat := Vector.normSq prev
  let Nk : Rat := Vector.normSq curr
  -- Rational expressions for each Gram determinant we touch.
  have hdkm1_rat : (gramDet b km1.val hkm1_le_n : Rat) = G :=
    gramDet_eq_prod_normSq_uncond b km1.val hkm1_le_n
  -- gramDet b k.val = gramDet b (km1.val + 1) = G * Nkm1.
  have hdk_rat : (gramDet b k.val hk_le_n : Rat) = G * Nkm1 := by
    have h_succ := gramDet_succ_rat b km1.val hkm1_succ_le
    have hgd_eq :
        gramDet b (km1.val + 1) hkm1_succ_le = gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    rw [← hgd_eq, h_succ]
  -- gramDet b (k.val + 1) = G * Nkm1 * Nk.
  have hdkp1_rat : (gramDet b (k.val + 1) hk1_le_n : Rat) = G * Nkm1 * Nk := by
    have h_succ := gramDet_succ_rat b k.val hk1_le_n
    have hgnp_k_eq :
        gramSchmidtNormProduct b k.val hk_le_n =
          gramSchmidtNormProduct b (km1.val + 1) hkm1_succ_le :=
      gramSchmidtNormProduct_subst_val b _ _ _ _ hkm1.symm
    rw [h_succ, hgnp_k_eq,
        gramSchmidtNormProduct_succ b km1.val hkm1_succ_le]
  -- Basis orthogonality between curr and prev.
  have horth : Matrix.dot curr prev = 0 :=
    basis_orthogonal b k.val km1.val k.isLt km1.isLt (by omega)
  -- New basis row at km1 of the swapped matrix is `curr + μ • prev`.
  have hbasis_swap :
      (basis (Matrix.rowSwap b km1 k)).row km1 = curr + μ • prev :=
    basis_rowSwap_adjacent_prev b km1 k hkm1
  -- gramDet (rowSwap b km1 k) k.val = G * (Nk + μ^2 * Nkm1).
  have hdprime_rat :
      (gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n : Rat) =
        G * (Nk + μ ^ 2 * Nkm1) := by
    have h_succ :=
      gramDet_succ_rat (Matrix.rowSwap b km1 k) km1.val hkm1_succ_le
    have hgd_eq :
        gramDet (Matrix.rowSwap b km1 k) (km1.val + 1) hkm1_succ_le =
          gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n :=
      gramDet_subst_val (Matrix.rowSwap b km1 k) _ _ _ _ hkm1
    rw [← hgd_eq, h_succ,
        gramSchmidtNormProduct_rowSwap_below b km1 k hkm1k]
    show G * Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row
        ⟨km1.val, km1.isLt⟩) = G * (Nk + μ ^ 2 * Nkm1)
    have hbasis_row :
        (basis (Matrix.rowSwap b km1 k)).row ⟨km1.val, km1.isLt⟩ =
          curr + μ • prev := hbasis_swap
    rw [hbasis_row, normSq_add_smul_orthogonal_rat curr prev μ horth]
  -- Rational expression for B.
  have hB_rat : ((B : Int) : Rat) = G * Nkm1 * μ := by
    show ((GramSchmidt.entry (scaledCoeffs b) k km1 : Int) : Rat) =
        G * Nkm1 * μ
    rw [scaledCoeffs_eq b k.val km1.val k.isLt hkm1k]
    have hgd_eq :
        gramDet b (km1.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hkm1k k.isLt)) =
          gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    show (gramDet b (km1.val + 1) _ : Rat) *
        GramSchmidt.entry (coeffs b) ⟨k.val, k.isLt⟩
          ⟨km1.val, Nat.lt_trans hkm1k k.isLt⟩ = G * Nkm1 * μ
    rw [hgd_eq, hdk_rat]
  -- Promote to Rat and discharge.
  apply intCast_rat_injective_int_eq
  push_cast
  rw [hdprime_rat, hdk_rat, hdkp1_rat, hdkm1_rat, hB_rat]
  grind

/-- All-zero foldl: when every term in the foldl is zero, the result equals
the initial accumulator. -/
private theorem foldl_add_zero_of_all_zero_rat {α : Type}
    (f : α → Rat) (xs : List α) (h : ∀ x ∈ xs, f x = 0) (acc : Rat) :
    xs.foldl (fun acc' x => acc' + f x) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := h x (by simp)
      rw [hx, Rat.add_zero]
      exact ih (fun y hy => h y (by simp [hy])) acc

/-- Foldl isolation: when every term except the `j`-th vanishes, the foldl
over `List.finRange i` collapses to `f ⟨j, hj⟩`. -/
private theorem foldl_finRange_isolate_rat :
    ∀ (i : Nat) (j : Nat) (hj : j < i) (f : Fin i → Rat),
      (∀ q : Fin i, q.val ≠ j → f q = 0) →
      (List.finRange i).foldl (fun acc q => acc + f q) 0 = f ⟨j, hj⟩
  | 0, _, hj, _, _ => absurd hj (Nat.not_lt_zero _)
  | i + 1, j, hj, f, h_zero => by
      rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hj_eq : j = i
      · -- j = i: the `Fin.last i` term contributes `f ⟨j, hj⟩`.
        subst hj_eq
        have hzero_pre : ∀ q : Fin j, f (Fin.castSucc q) = 0 := by
          intro q
          apply h_zero
          have : (Fin.castSucc q).val = q.val := rfl
          rw [this]
          exact Nat.ne_of_lt q.isLt
        have hmem_zero : ∀ q ∈ List.finRange j, f (Fin.castSucc q) = 0 := by
          intro q _
          exact hzero_pre q
        have hfold_zero :
            (List.finRange j).foldl
                (fun (acc : Rat) (q : Fin j) => acc + f (Fin.castSucc q)) 0 = 0 :=
          foldl_add_zero_of_all_zero_rat (fun q => f (Fin.castSucc q))
            (List.finRange j) hmem_zero 0
        rw [hfold_zero, Rat.zero_add]
        rfl
      · -- j < i: recurse on the smaller range.
        have hjlt : j < i := by omega
        have hlast_zero : f (Fin.last i) = 0 := by
          apply h_zero
          have : (Fin.last i).val = i := rfl
          rw [this]
          omega
        rw [hlast_zero, Rat.add_zero]
        have hzero_pre : ∀ q : Fin i, q.val ≠ j → f (Fin.castSucc q) = 0 := by
          intro q hq_ne
          apply h_zero
          have : (Fin.castSucc q).val = q.val := rfl
          rw [this]
          exact hq_ne
        have hih := foldl_finRange_isolate_rat i j hjlt
          (fun q => f (Fin.castSucc q)) hzero_pre
        rw [hih]
        rfl

/-- Dotting the `j`-th Gram-Schmidt basis row with the integer-cast `i`-th
input row picks out the `(i, j)` Gram-Schmidt coefficient weighted by the
squared norm of the basis row. Holds unconditionally: when the basis row is
zero, both sides vanish (orthogonality + the `if`-branch in
`coeffs_lower_projection`). -/
theorem dot_basis_castRow_eq_coeffs_mul_normSq
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    Matrix.dot ((basis b).row ⟨j, Nat.lt_trans hj hi⟩)
        (Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i, hi⟩)) =
      GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ *
        Vector.normSq ((basis b).row ⟨j, Nat.lt_trans hj hi⟩) := by
  have hjlt : j < n := Nat.lt_trans hj hi
  -- Expand `castIntRow b i` via `basis_decomposition`.
  have hrow := castIntRow_decomposition b i hi
  show Matrix.dot ((basis b).row ⟨j, hjlt⟩) (castIntRow b ⟨i, hi⟩) = _
  rw [hrow]
  rw [dot_add_right_rat]
  -- First term: `dot basis[j] basis[i] = 0` by orthogonality (j ≠ i).
  rw [basis_orthogonal b j i hjlt hi (Nat.ne_of_lt hj)]
  rw [Rat.zero_add]
  -- Second term: linearise the prefixCombination, then isolate the j-th index.
  rw [dot_prefixCombination_right_rat (coeffs := coeffs b) (basisM := basis b)
      (i := i) (hi := hi) (u := (basis b).row ⟨j, hjlt⟩)]
  have h_zero_term : ∀ q : Fin i, q.val ≠ j →
      GramSchmidt.entry (coeffs b) ⟨i, hi⟩
            ⟨q.val, Nat.lt_trans q.isLt hi⟩ *
          Matrix.dot ((basis b).row ⟨j, hjlt⟩)
            ((basis b).row ⟨q.val, Nat.lt_trans q.isLt hi⟩) = 0 := by
    intro q hqj
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt hi
    rw [basis_orthogonal b j q.val hjlt hq_lt_n fun h => hqj h.symm]
    grind
  rw [foldl_finRange_isolate_rat i j hj _ h_zero_term]
  -- After isolation: c[i][j] * dot basis[j] basis[j] = c[i][j] * normSq basis[j].
  rfl

/-- Foldl isolation for two indices: when every term except those at `j₁` and `j₂`
vanishes, the foldl over `List.finRange i` collapses to `f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩`. -/
private theorem foldl_finRange_isolate_two_rat :
    ∀ (i : Nat) (j₁ j₂ : Nat) (hj₁ : j₁ < i) (hj₂ : j₂ < i) (hne : j₁ ≠ j₂)
      (f : Fin i → Rat),
      (∀ q : Fin i, q.val ≠ j₁ → q.val ≠ j₂ → f q = 0) →
      (List.finRange i).foldl (fun acc q => acc + f q) 0 =
        f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
  | 0, _, _, hj₁, _, _, _, _ => absurd hj₁ (Nat.not_lt_zero _)
  | i + 1, j₁, j₂, hj₁, hj₂, hne, f, h_zero => by
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases h1 : j₁ = i
    · -- j₁ = i; then j₂ < i and j₂ ≠ i.
      subst h1
      have hj₂_lt : j₂ < j₁ := by
        have h_le : j₂ ≤ j₁ := Nat.lt_succ_iff.mp hj₂
        exact Nat.lt_of_le_of_ne h_le (fun h => hne h.symm)
      have hzero_pre : ∀ q : Fin j₁, q.val ≠ j₂ → f (Fin.castSucc q) = 0 := by
        intro q hqj₂
        apply h_zero
        · show q.val ≠ j₁
          exact Nat.ne_of_lt q.isLt
        · show q.val ≠ j₂
          exact hqj₂
      have hih := foldl_finRange_isolate_rat j₁ j₂ hj₂_lt
        (fun q => f (Fin.castSucc q)) hzero_pre
      rw [hih]
      have h_cast_j₂ : (Fin.castSucc ⟨j₂, hj₂_lt⟩ : Fin (j₁ + 1)) = ⟨j₂, hj₂⟩ := by
        apply Fin.ext; rfl
      have h_last : (Fin.last j₁ : Fin (j₁ + 1)) = ⟨j₁, hj₁⟩ := by
        apply Fin.ext; rfl
      show f (Fin.castSucc ⟨j₂, hj₂_lt⟩) + f (Fin.last j₁) = f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
      rw [h_cast_j₂, h_last]
      ring
    · by_cases h2 : j₂ = i
      · -- j₂ = i; then j₁ < i.
        subst h2
        have hj₁_lt : j₁ < j₂ := by
          have h_le : j₁ ≤ j₂ := Nat.lt_succ_iff.mp hj₁
          exact Nat.lt_of_le_of_ne h_le h1
        have hzero_pre : ∀ q : Fin j₂, q.val ≠ j₁ → f (Fin.castSucc q) = 0 := by
          intro q hqj₁
          apply h_zero
          · show q.val ≠ j₁
            exact hqj₁
          · show q.val ≠ j₂
            exact Nat.ne_of_lt q.isLt
        have hih := foldl_finRange_isolate_rat j₂ j₁ hj₁_lt
          (fun q => f (Fin.castSucc q)) hzero_pre
        rw [hih]
        have h_cast_j₁ : (Fin.castSucc ⟨j₁, hj₁_lt⟩ : Fin (j₂ + 1)) = ⟨j₁, hj₁⟩ := by
          apply Fin.ext; rfl
        have h_last : (Fin.last j₂ : Fin (j₂ + 1)) = ⟨j₂, hj₂⟩ := by
          apply Fin.ext; rfl
        show f (Fin.castSucc ⟨j₁, hj₁_lt⟩) + f (Fin.last j₂) = f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
        rw [h_cast_j₁, h_last]
      · -- Both j₁ < i, j₂ < i: last term vanishes, recurse.
        have hj₁_lt : j₁ < i := by
          have h_le : j₁ ≤ i := Nat.lt_succ_iff.mp hj₁
          exact Nat.lt_of_le_of_ne h_le h1
        have hj₂_lt : j₂ < i := by
          have h_le : j₂ ≤ i := Nat.lt_succ_iff.mp hj₂
          exact Nat.lt_of_le_of_ne h_le h2
        have hlast_zero : f (Fin.last i) = 0 := by
          apply h_zero
          · show (Fin.last i).val ≠ j₁
            show i ≠ j₁
            exact fun h => h1 h.symm
          · show (Fin.last i).val ≠ j₂
            show i ≠ j₂
            exact fun h => h2 h.symm
        rw [hlast_zero, Rat.add_zero]
        have hzero_pre : ∀ q : Fin i, q.val ≠ j₁ → q.val ≠ j₂ → f (Fin.castSucc q) = 0 := by
          intro q hqj₁ hqj₂
          apply h_zero
          · show q.val ≠ j₁
            exact hqj₁
          · show q.val ≠ j₂
            exact hqj₂
        have hih := foldl_finRange_isolate_two_rat i j₁ j₂ hj₁_lt hj₂_lt hne
          (fun q => f (Fin.castSucc q)) hzero_pre
        rw [hih]
        have h_cast_j₁ : (Fin.castSucc ⟨j₁, hj₁_lt⟩ : Fin (i + 1)) = ⟨j₁, hj₁⟩ := by
          apply Fin.ext; rfl
        have h_cast_j₂ : (Fin.castSucc ⟨j₂, hj₂_lt⟩ : Fin (i + 1)) = ⟨j₂, hj₂⟩ := by
          apply Fin.ext; rfl
        show f (Fin.castSucc ⟨j₁, hj₁_lt⟩) + f (Fin.castSucc ⟨j₂, hj₂_lt⟩) =
          f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
        rw [h_cast_j₁, h_cast_j₂]

/-- For an adjacent row swap `b' = rowSwap b km1 k` with `km1.val + 1 = k.val`,
the dot product of the swapped `k`-th basis row with the original `km1`-th basis
row equals the squared norm of the swapped `k`-th basis row. Equivalently,
`dot u_k prev = ||u_k||²`, where `u_k = (basis b').row k` and `prev = (basis b).row km1`.

The proof routes both sides through `dot u_k (cast b.row km1) = dot u_k (cast b'.row k)`
(the cast vectors agree because `b'.row k = b.row km1` from the row swap),
expanding each side via `basis_decomposition`. The prefix combinations vanish on
both sides because `u_k = (basis b').row k` is orthogonal to every `(basis b').row q`
with `q < k`, and the relevant `(basis b).row q` agrees with `(basis b').row q`
for `q < km1`. -/
theorem dot_basis_rowSwap_curr_prev_eq_normSq
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row km1) =
      Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row k) := by
  have hkm1k : km1.val < k.val := by omega
  -- Row equality: (rowSwap b km1 k).row k = b.row km1.
  have hrow_eq : (Matrix.rowSwap b km1 k).row k = b.row km1 := by
    apply Vector.ext
    intro idx hidx
    let c : Fin m := ⟨idx, hidx⟩
    change (Matrix.rowSwap b km1 k)[k][c] = b[km1][c]
    rw [Matrix.rowSwap_getElem]
    simp
  -- prefixCombination of b at km1 vanishes against u_k.
  have hpfx_b_zero :
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
          (GramSchmidt.prefixCombination (coeffs b) (basis b) km1.val km1.isLt) = 0 := by
    apply dot_prefixCombination_right_eq_zero_of_dot_zero
    intro q
    have hq_lt_km1 : q.val < km1.val := q.isLt
    have hq_lt_k : q.val < k.val := by omega
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt km1.isLt
    have hbeq : (basis b).row ⟨q.val, hq_lt_n⟩ =
        (basis (Matrix.rowSwap b km1 k)).row ⟨q.val, hq_lt_n⟩ :=
      (basis_rowSwap_of_before b km1 k ⟨q.val, hq_lt_n⟩ hkm1k hq_lt_km1).symm
    rw [hbeq]
    exact basis_orthogonal (Matrix.rowSwap b km1 k) k.val q.val k.isLt hq_lt_n
      (Nat.ne_of_gt hq_lt_k)
  -- prefixCombination of b' at k vanishes against u_k.
  have hpfx_b'_zero :
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
          (GramSchmidt.prefixCombination (coeffs (Matrix.rowSwap b km1 k))
            (basis (Matrix.rowSwap b km1 k)) k.val k.isLt) = 0 := by
    apply dot_prefixCombination_right_eq_zero_of_dot_zero
    intro q
    have hq_lt_k : q.val < k.val := q.isLt
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt k.isLt
    exact basis_orthogonal (Matrix.rowSwap b km1 k) k.val q.val k.isLt hq_lt_n
      (Nat.ne_of_gt hq_lt_k)
  -- dot u_k (cast b.row km1) = dot u_k (basis b.row km1)
  have hdot_cast_b_km1 :
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
          (Vector.map (fun x : Int => (x : Rat)) (b.row km1)) =
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row km1) := by
    have hdec := basis_decomposition b km1.val km1.isLt
    show Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
        (Vector.map (fun x : Int => (x : Rat)) (b.row ⟨km1.val, km1.isLt⟩)) = _
    rw [hdec, dot_add_right_rat, hpfx_b_zero, Rat.add_zero]
  -- dot u_k (cast b'.row k) = ||u_k||²
  have hdot_cast_b'_k :
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
          (Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row k)) =
      Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row k) := by
    have hdec := basis_decomposition (Matrix.rowSwap b km1 k) k.val k.isLt
    show Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
        (Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row ⟨k.val, k.isLt⟩)) = _
    rw [hdec, dot_add_right_rat, hpfx_b'_zero, Rat.add_zero]
    rfl
  -- cast b.row km1 = cast b'.row k via hrow_eq.
  have hcast_eq :
      Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row k) =
      Vector.map (fun x : Int => (x : Rat)) (b.row km1) := by
    rw [hrow_eq]
  -- Combine.
  rw [← hdot_cast_b_km1, ← hcast_eq, hdot_cast_b'_k]

/-- For an adjacent row swap `b' = rowSwap b km1 k` with `km1.val + 1 = k.val`,
the dot product of the swapped `k`-th basis row with the integer-cast `i`-th
input row (for `i > k`) decomposes as the dot product of `u_k` with the original
`km1`-th basis row times a linear combination of the original `km1`-th and
`k`-th coefficients of row `i`.

Concretely, with `μ = c[k][km1]`:
  `dot u_k (cast b.row i) = (dot u_k prev) * (c[i][km1] - μ * c[i][k])`

This is the "Cramer-style" dot product expansion that, combined with
`dot_basis_rowSwap_curr_prev_eq_normSq`, lets us extract `c'[i][k]` from the
b'-side Cramer formula `c'[i][k] * ||u_k||² = dot u_k (cast b.row i)`. -/
theorem dot_basis_rowSwap_curr_castRow_eq
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val)
    (i : Fin n) (hki : k.val < i.val) :
    Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
        (Vector.map (fun x : Int => (x : Rat)) (b.row i)) =
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row km1) *
        (GramSchmidt.entry (coeffs b) i ⟨km1.val, Nat.lt_trans (Nat.lt_of_succ_le
          (le_of_eq hkm1)) k.isLt⟩ -
         GramSchmidt.entry (coeffs b) k ⟨km1.val, Nat.lt_trans (Nat.lt_of_succ_le
          (le_of_eq hkm1)) k.isLt⟩ *
         GramSchmidt.entry (coeffs b) i k) := by
  have hkm1k : km1.val < k.val := by omega
  have hkm1_lt_i : km1.val < i.val := by omega
  have hkm1_lt_n : km1.val < n := Nat.lt_trans hkm1k k.isLt
  -- The dot product `D = dot u_k prev`.
  set D : Rat := Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row km1) with hD_def
  -- Step A: dot u_k cast b.row i = dot u_k basis b.row i + dot u_k prefixCombination(b, i)
  have hdec_b_i := basis_decomposition b i.val i.isLt
  show Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
      (Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i.val, i.isLt⟩)) = _
  rw [hdec_b_i, dot_add_right_rat]
  -- dot u_k basis b.row i = 0 (basis b.row i = basis b'.row i and orthogonality).
  have hdot_basis_i :
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row ⟨i.val, i.isLt⟩) = 0 := by
    have hbasis_eq : (basis b).row ⟨i.val, i.isLt⟩ =
        (basis (Matrix.rowSwap b km1 k)).row ⟨i.val, i.isLt⟩ :=
      (basis_rowSwap_of_after b km1 k ⟨i.val, i.isLt⟩ hkm1 hki).symm
    rw [hbasis_eq]
    exact basis_orthogonal (Matrix.rowSwap b km1 k) k.val i.val k.isLt i.isLt (Nat.ne_of_lt hki)
  rw [hdot_basis_i, Rat.zero_add]
  -- Linearise dot u_k prefixCombination(b, i) into a foldl.
  rw [dot_prefixCombination_right_rat (coeffs := coeffs b) (basisM := basis b)
      (i := i.val) (hi := i.isLt) (u := (basis (Matrix.rowSwap b km1 k)).row k)]
  -- Apply two-isolate at j₁ = km1.val, j₂ = k.val.
  have hkm1_ne_k_val : km1.val ≠ k.val := by omega
  -- Define f
  set f : Fin i.val → Rat := fun q =>
    GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩
        ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩ *
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
        ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩) with hf_def
  -- For q ≠ km1, k: f q = 0.
  have h_zero : ∀ q : Fin i.val, q.val ≠ km1.val → q.val ≠ k.val → f q = 0 := by
    intro q hq_km1 hq_k
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt i.isLt
    -- basis b.row q = basis b'.row q  (either q < km1 or q > k)
    have hbasis_eq_q : (basis b).row ⟨q.val, hq_lt_n⟩ =
        (basis (Matrix.rowSwap b km1 k)).row ⟨q.val, hq_lt_n⟩ := by
      by_cases hcase : q.val < km1.val
      · exact (basis_rowSwap_of_before b km1 k ⟨q.val, hq_lt_n⟩ hkm1k hcase).symm
      · have hge_km1 : km1.val ≤ q.val := Nat.le_of_not_lt hcase
        have h_gt_km1 : km1.val < q.val := Nat.lt_of_le_of_ne hge_km1 (fun h => hq_km1 h.symm)
        have h_gt_k : k.val < q.val := by omega
        exact (basis_rowSwap_of_after b km1 k ⟨q.val, hq_lt_n⟩ hkm1 h_gt_k).symm
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ _ *
        Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
          ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩) = 0
    rw [hbasis_eq_q]
    rw [basis_orthogonal (Matrix.rowSwap b km1 k) k.val q.val k.isLt hq_lt_n
      (fun h => hq_k h.symm)]
    grind
  have hfoldl_eq :
      (List.finRange i.val).foldl (fun (acc : Rat) (q : Fin i.val) => acc + f q) 0 =
      f ⟨km1.val, hkm1_lt_i⟩ + f ⟨k.val, hki⟩ :=
    foldl_finRange_isolate_two_rat i.val km1.val k.val hkm1_lt_i hki hkm1_ne_k_val f h_zero
  -- The foldl on the goal matches our `f`.
  show (List.finRange i.val).foldl
      (fun (acc : Rat) (q : Fin i.val) =>
        acc + GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩
              ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩ *
            Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
              ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩)) 0 = _
  rw [show (fun (acc : Rat) (q : Fin i.val) =>
        acc + GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩
              ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩ *
            Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
              ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩)) =
       (fun (acc : Rat) (q : Fin i.val) => acc + f q) from rfl]
  rw [hfoldl_eq]
  -- Compute f at km1 and k.
  -- f ⟨km1.val, _⟩ = c[i][km1] * dot u_k (basis b.row km1) = c[i][km1] * D
  -- f ⟨k.val, _⟩ = c[i][k] * dot u_k (basis b.row k) = c[i][k] * dot u_k curr
  -- Use orthogonality: u_k ⊥ basis b'.row km1 = curr + μ * prev.
  --   ⟹ dot u_k curr + μ * D = 0 ⟹ dot u_k curr = -μ * D.
  set μ : Rat := GramSchmidt.entry (coeffs b) k km1 with hμ_def
  have hbasis_swap :
      (basis (Matrix.rowSwap b km1 k)).row km1 = (basis b).row k + μ • (basis b).row km1 :=
    basis_rowSwap_adjacent_prev b km1 k hkm1
  have hdot_swap_zero :
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
        ((basis (Matrix.rowSwap b km1 k)).row km1) = 0 :=
    basis_orthogonal (Matrix.rowSwap b km1 k) k.val km1.val k.isLt km1.isLt
      (fun h => Nat.lt_irrefl km1.val (h ▸ hkm1k))
  -- Expand the orthogonality via the basis swap.
  have hdot_curr :
      Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row k) = -μ * D := by
    have h := hdot_swap_zero
    rw [hbasis_swap] at h
    rw [dot_add_right_rat, dot_smul_right_rat] at h
    -- h : dot u_k curr + μ * (dot u_k prev) = 0
    -- i.e., dot u_k curr + μ * D = 0
    -- ⟹ dot u_k curr = -μ * D
    have hD_eq : Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
        ((basis b).row km1) = D := rfl
    rw [hD_eq] at h
    linarith
  -- Now evaluate f at km1 and k.
  show f ⟨km1.val, hkm1_lt_i⟩ + f ⟨k.val, hki⟩ = D * _
  have hf_km1 : f ⟨km1.val, hkm1_lt_i⟩ =
      GramSchmidt.entry (coeffs b) i ⟨km1.val, hkm1_lt_n⟩ * D := by
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ ⟨km1.val, _⟩ *
        Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
          ((basis b).row ⟨km1.val, _⟩) = _
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ ⟨km1.val, hkm1_lt_n⟩ *
        Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
          ((basis b).row ⟨km1.val, hkm1_lt_n⟩) =
        GramSchmidt.entry (coeffs b) i ⟨km1.val, hkm1_lt_n⟩ * D
    have hi_eq : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
    have hkm1_eq : (⟨km1.val, hkm1_lt_n⟩ : Fin n) = km1 := Fin.ext rfl
    rw [hi_eq, hkm1_eq]
  have hf_k : f ⟨k.val, hki⟩ =
      GramSchmidt.entry (coeffs b) i k * (-μ * D) := by
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ ⟨k.val, _⟩ *
        Matrix.dot ((basis (Matrix.rowSwap b km1 k)).row k)
          ((basis b).row ⟨k.val, _⟩) = _
    have hi_eq : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
    have hk_eq : (⟨k.val, Nat.lt_trans hki i.isLt⟩ : Fin n) = k := Fin.ext rfl
    rw [hi_eq, hk_eq]
    rw [hdot_curr]
  rw [hf_km1, hf_k]
  ring

/-- Below the diagonal, the executable integral scaled coefficient is exactly
the Cramer determinant encoded by `scaledCoeffMatrix`. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_det
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  rw [scaledCoeffs_eq_scaledCoeffMatrix_bareiss]
  exact
    (HexMatrixMathlib.bareiss_eq_mathlib_det
        (GramSchmidt.scaledCoeffMatrix b i j hji)).trans
      (HexMatrixMathlib.det_eq (GramSchmidt.scaledCoeffMatrix b i j hji)).symm


/-- Conditional form of the leading Gram determinant identity. The remaining
unconditional fact is exactly the nonnegativity of leading Gram determinants:
once `0 ≤ det` is available, the public `Nat`-valued `gramDet` casts back to
the signed determinant. -/
theorem leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n)
    (hdet : 0 ≤ Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht)) :
    Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) =
      Int.ofNat (gramDet b t ht) := by
  rw [gramDet, HexMatrixMathlib.bareiss_eq_mathlib_det, ← HexMatrixMathlib.det_eq]
  exact (Int.toNat_of_nonneg hdet).symm

/-- The public `Nat` Gram determinant casts back to the signed determinant of
the leading integer Gram matrix. -/
theorem leadingGramMatrixInt_det_eq_gramDet_int
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n) :
    Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) =
      Int.ofNat (gramDet b t ht) :=
  leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg b t ht
    (leadingGramMatrixInt_det_nonneg b t ht)

/-- Mathlib-side unconditional diagonal synchronization for the public
scaled-coefficient matrix. The Mathlib-free core exposes the Nat-level version
and the conditional Int lift; the required nonnegativity of the Gram/Bareiss
diagonal slot is supplied here. -/
theorem scaledCoeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi)) := by
  let hk : i + 1 ≤ n := Nat.succ_le_of_lt hi
  rcases scaledCoeffs_diag_eq_zero_or_eq_leadingPrefix_bareiss b (StepWitness.ofGram b)
      i hi with hzero | hbareiss
  · have hnat := scaledCoeffs_diag_toNat (b := b) (StepWitness.ofGram b) i hi
    rw [hzero] at hnat
    simp at hnat
    rw [hzero, ← hnat]
    simp
  · apply scaledCoeffs_diag_of_nonneg b (StepWitness.ofGram b)
    rw [hbareiss]
    have hbareiss_eq :
        Matrix.bareiss
            (Matrix.leadingPrefix (Matrix.gramMatrix b) (i + 1) hk) =
          Matrix.det (GramSchmidt.leadingGramMatrixInt b (i + 1) hk) := by
      rw [← GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram]
      exact HexMatrixMathlib.bareiss_eq_det
        (GramSchmidt.leadingGramMatrixInt b (i + 1) hk)
    rw [hbareiss_eq]
    exact leadingGramMatrixInt_det_nonneg b (i + 1) hk

/-- Stage-B rational closed form for the strictly lower entries of
`scaledCoeffs`, packaged with a no-singular hypothesis for the σ-chain
singular-cascade consumer.

The hypothesis is unused: the unconditional Int-level identity
`scaledCoeffs_eq_scaledCoeffMatrix_det` already covers the singular branch
by routing through `scaledCoeffMatrix_det_eq_zero_of_singularStep_lt`. -/
theorem scaledCoeffs_lower_eq_det_scaledCoeffMatrix_of_no_singular
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (_h_nonsing :
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) =
      ((Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) : Int) : Rat) := by
  exact_mod_cast scaledCoeffs_eq_scaledCoeffMatrix_det b i j hji

/-- Stage-B rational closed form for the diagonal of `scaledCoeffs`,
packaged with a no-singular hypothesis for the σ-chain singular-cascade
consumer.

The hypothesis is unused: `scaledCoeffs_diag` already gives the
unconditional integer identification with `gramDet`, and the singular tail
slots are exactly the zero values the public `gramDet` returns once a
leading Gram prefix is singular. -/
theorem scaledCoeffs_diag_eq_gramDet_of_no_singular
    (b : Matrix Int n m) (i : Fin n)
    (_h_nonsing :
      (Matrix.noPivotLoop i.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    ((GramSchmidt.entry (scaledCoeffs b) i i : Int) : Rat) =
      ((gramDet b (i + 1) (Nat.lt_iff_add_one_le.mp i.isLt) : Int) : Rat) := by
  rw [scaledCoeffs_diag b i.val i.isLt]
  push_cast
  rfl

/-- The leading executable Gram determinants of a square upper-triangular
integer matrix with strictly positive diagonal are positive.

This theorem lives in `HexGramSchmidtMathlib`: its proof identifies the
executable `gramDet` with the Leibniz determinant of the leading Gram matrix
via the composition of `HexMatrixMathlib.bareiss_eq_mathlib_det` and
`HexMatrixMathlib.det_eq.symm`. -/
theorem gramDet_pos_of_upperTriangular_pos_diag
    {n : Nat} (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val -> M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i])
    (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet M k hk := by
  cases k with
  | zero =>
      omega
  | succ r =>
      have hrn : r < n := Nat.lt_of_succ_le hk
      have hlead :
          Matrix.gramMatrix (Matrix.leadingRows M (r + 1) hk) =
            Matrix.leadingPrefix (Matrix.gramMatrix M) (r + 1) hk := by
        apply Vector.ext
        intro i hi
        apply Vector.ext
        intro j hj
        let iFin : Fin (r + 1) := ⟨i, hi⟩
        let jFin : Fin (r + 1) := ⟨j, hj⟩
        let ii : Fin n := ⟨i, Nat.lt_of_lt_of_le hi hk⟩
        let jj : Fin n := ⟨j, Nat.lt_of_lt_of_le hj hk⟩
        have hrow_i :
            Matrix.row (Matrix.leadingRows M (r + 1) hk) iFin =
              Matrix.row M ii := by
          apply Vector.ext
          intro c hc
          simp [Matrix.row, Matrix.leadingRows, Matrix.ofFn, iFin, ii]
        have hrow_j :
            Matrix.row (Matrix.leadingRows M (r + 1) hk) jFin =
              Matrix.row M jj := by
          apply Vector.ext
          intro c hc
          simp [Matrix.row, Matrix.leadingRows, Matrix.ofFn, jFin, jj]
        have hdot :
            Matrix.dot (Matrix.row (Matrix.leadingRows M (r + 1) hk) iFin)
                (Matrix.row (Matrix.leadingRows M (r + 1) hk) jFin) =
              Matrix.dot (Matrix.row M ii) (Matrix.row M jj) := by
          rw [hrow_i, hrow_j]
        simpa [Matrix.gramMatrix, Matrix.leadingPrefix, Matrix.ofFn, iFin, jFin, ii, jj]
          using hdot
      have hdet_pos :
          0 < Matrix.det (GramSchmidt.leadingGramMatrixInt M (r + 1) hk) := by
        have hpos :=
          Matrix.det_gramMatrix_leadingRows_pos_of_upperTriangular_pos_diag M hzero hdiag
            (r + 1) hk
        rwa [hlead, ← GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram] at hpos
      have hdet_nat :
          Matrix.det (GramSchmidt.leadingGramMatrixInt M (r + 1) hk) =
            Int.ofNat (gramDet M (r + 1) hk) :=
        leadingGramMatrixInt_det_eq_gramDet_int M (r + 1) hk
      have hnat_int : 0 < Int.ofNat (gramDet M (r + 1) hk) := by
        simpa [hdet_nat] using hdet_pos
      exact Int.ofNat_lt.mp hnat_int


/-! ### Row-add determinant helper lemmas -/

/-- Entry-level expansion of `Matrix.rowAdd` for a rectangular matrix. -/
private theorem rowAdd_get_rect {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst r : Fin n') (c : R) (k : Fin m') :
    (Matrix.rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [Matrix.rowAdd]
  · simp [Matrix.rowAdd, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set dst (Vector.ofFn fun k => M[dst][k] + c * M[src][k]))[r] = M[r] :=
      (Vector.getElem_set_ne (xs := M)
        (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
        dst.isLt r.isLt hval)
    simpa [Matrix.rowAdd] using congrArg (fun row => row[k]) hrow

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
    Matrix.dot u v = Matrix.dot v u := by
  simpa [Matrix.dot, Hex.Vector.dotProduct] using
    foldl_dot_comm_int (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

/-- A row of `Matrix.rowAdd M src dst c` away from `dst` is unchanged. -/
private theorem rowAdd_row_eq_of_ne {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst r : Fin n') (c : R) (hr : r.val ≠ dst.val) :
    (Matrix.rowAdd M src dst c)[r] = M[r] :=
  Vector.getElem_set_ne (xs := M)
    (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
    dst.isLt r.isLt (fun heq => hr heq.symm)

/-- The row of `Matrix.rowAdd M src dst c` at index `dst` is the entry-wise
sum `M[dst] + c * M[src]`. -/
private theorem rowAdd_row_at {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst : Fin n') (c : R) :
    (Matrix.rowAdd M src dst c)[dst] =
      Vector.ofFn fun k => M[dst][k] + c * M[src][k] := by
  unfold Matrix.rowAdd
  simp

/-- Inductive helper for `dot_rowAdd_row_at_left`: distribution along a foldl. -/
private theorem foldl_dot_rowAdd_at {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m')
    (xs : List (Fin m')) (acc accX accY : Int) (hacc : acc = accX + c * accY) :
    xs.foldl (fun a i => a + (Matrix.rowAdd M src dst c)[dst][i] * w[i]) acc =
      xs.foldl (fun a i => a + M[dst][i] * w[i]) accX +
        c * xs.foldl (fun a i => a + M[src][i] * w[i]) accY := by
  induction xs generalizing acc accX accY with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      have hentry : (Matrix.rowAdd M src dst c)[dst][i] = M[dst][i] + c * M[src][i] := by
        rw [rowAdd_get_rect]
        simp
      rw [hentry, hacc]
      grind

/-- Distribute dot product on the left over the row produced by
`Matrix.rowAdd`: at index `dst`, the row is `M[dst] + c * M[src]` componentwise,
so dot with `w` distributes over the sum. -/
private theorem dot_rowAdd_row_at_left {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m') :
    Matrix.dot ((Matrix.rowAdd M src dst c)[dst]) w =
      Matrix.dot M[dst] w + c * Matrix.dot M[src] w := by
  simp only [Matrix.dot, Hex.Vector.dotProduct]
  exact foldl_dot_rowAdd_at M src dst c w (List.finRange m')
    0 0 0 (by show (0 : Int) = 0 + c * 0; grind)

/-- Symmetric form: dot product on the right with the modified row. -/
private theorem dot_rowAdd_row_at_right {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m') :
    Matrix.dot w ((Matrix.rowAdd M src dst c)[dst]) =
      Matrix.dot w M[dst] + c * Matrix.dot w M[src] := by
  rw [dot_comm_int w, dot_rowAdd_row_at_left, dot_comm_int w M[dst], dot_comm_int w M[src]]

/-- Determinant-level pivot identity for scaled Gram-Schmidt coefficients under
an elementary row addition. In the Cramer matrix computing `nu[k,j]`, replacing
row `k` by `row k + c * row j` changes the replaced last column linearly: the
new determinant is the old Cramer determinant plus `c` times the leading Gram
determinant. This formulation does not require the rational coefficient
denominator to be nonzero. -/
theorem scaledCoeffMatrix_rowAdd_pivot_det
    (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val) (c : Int) :
    Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk) =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
        c * Matrix.det
          (GramSchmidt.leadingGramMatrixInt b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  let t := j.val + 1
  let ht : t ≤ n := Nat.succ_le_of_lt j.isLt
  let last : Fin t := ⟨j.val, Nat.lt_succ_self j.val⟩
  let M := GramSchmidt.leadingGramMatrixInt b t ht
  let oldCol : Fin t → Int := fun p =>
    Matrix.dot (b.row (GramSchmidt.liftFinLE p ht)) (b.row k)
  let gramCol : Fin t → Int := fun p =>
    Matrix.dot (b.row (GramSchmidt.liftFinLE p ht)) (b.row j)
  have hnew :
      GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk =
        Matrix.colReplace M last (fun p => oldCol p + c * gramCol p) := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro q hq
    let p : Fin t := ⟨r, hr⟩
    let qf : Fin t := ⟨q, hq⟩
    have hp_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val := by
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_iff.mp hjk))
    have hp_row :
        (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
          b[GramSchmidt.liftFinLE p ht] :=
      rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE p ht) c hp_ne
    by_cases hqj : qf.val = j.val
    · have hqNat : q = j.val := by
        simpa [qf] using hqj
      have hq_last : qf = last := Fin.ext hqj
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn, hqNat, if_true]
      rw [if_pos (rfl : (⟨j.val, Nat.lt_succ_self j.val⟩ : Fin t) = last)]
      simp only [Matrix.row]
      change Matrix.dot ((Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht])
          ((Matrix.rowAdd b j k c)[k]) =
        oldCol p + c * gramCol p
      rw [hp_row]
      change Matrix.dot (b.row (GramSchmidt.liftFinLE p ht))
          ((Matrix.rowAdd b j k c)[k]) =
        oldCol p + c * gramCol p
      exact dot_rowAdd_row_at_right b j k c (b.row (GramSchmidt.liftFinLE p ht))
    · have hq_ne_last : qf ≠ last := by
        intro h
        exact hqj (congrArg Fin.val h)
      have hqNat : q ≠ j.val := by
        intro h
        exact hqj (by simpa [qf] using h)
      have hq_ne_k : (GramSchmidt.liftFinLE qf ht).val ≠ k.val := by
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le qf.isLt (Nat.succ_le_iff.mp hjk))
      have hq_row :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE qf ht] =
            b[GramSchmidt.liftFinLE qf ht] :=
        rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE qf ht) c hq_ne_k
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn, if_neg hqNat]
      rw [if_neg hq_ne_last]
      simp only [Matrix.row]
      rw [hp_row, hq_row]
      dsimp [M, GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row]
      rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  have hold :
      GramSchmidt.scaledCoeffMatrix b k j hjk =
        Matrix.colReplace M last oldCol := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro q hq
    let p : Fin t := ⟨r, hr⟩
    let qf : Fin t := ⟨q, hq⟩
    by_cases hqj : qf.val = j.val
    · have hqNat : q = j.val := by
        simpa [qf] using hqj
      have hq_last : qf = last := Fin.ext hqj
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn, hqNat, if_true]
      rw [if_pos (rfl : (⟨j.val, Nat.lt_succ_self j.val⟩ : Fin t) = last)]
    · have hq_ne_last : qf ≠ last := by
        intro h
        exact hqj (congrArg Fin.val h)
      have hqNat : q ≠ j.val := by
        intro h
        exact hqj (by simpa [qf] using h)
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn, if_neg hqNat]
      rw [if_neg hq_ne_last]
      dsimp [M, GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row]
      simp [Vector.getElem_ofFn]
  have hgram :
      Matrix.colReplace M last gramCol = M := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro q hq
    let p : Fin t := ⟨r, hr⟩
    let qf : Fin t := ⟨q, hq⟩
    by_cases hq_last : qf = last
    · have hq_lift : GramSchmidt.liftFinLE qf ht = j := by
        exact Fin.ext (by
          have hval := congrArg Fin.val hq_last
          simpa [last] using hval)
      simp only [M, gramCol, GramSchmidt.leadingGramMatrixInt, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn]
      rw [if_pos hq_last]
      rw [hq_lift]
    · simp only [M, gramCol, GramSchmidt.leadingGramMatrixInt, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn]
      rw [if_neg hq_last]
      simp [Matrix.row]
  calc
    Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk)
        = Matrix.det (Matrix.colReplace M last (fun p => oldCol p + c * gramCol p)) := by
          rw [hnew]
    _ = Matrix.det (Matrix.colReplace M last oldCol) +
          Matrix.det (Matrix.colReplace M last (fun p => c * gramCol p)) := by
          rw [Matrix.det_colReplace_add]
    _ = Matrix.det (Matrix.colReplace M last oldCol) +
          c * Matrix.det (Matrix.colReplace M last gramCol) := by
          rw [Matrix.det_colReplace_smul]
    _ = Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
          c * Matrix.det
            (GramSchmidt.leadingGramMatrixInt b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
          rw [← hold, hgram]

/-- When the modified row index `k` lies outside the leading `t`-prefix
(`t ≤ k.val`), the leading Gram matrix of `Matrix.rowAdd b j k c` agrees with
that of `b`. Internal support lemma for the row-add determinant theorem in
`HexGramSchmidtMathlib.Int`. -/
theorem leadingGramMatrixInt_rowAdd_outside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hkt : t ≤ k.val) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht =
      GramSchmidt.leadingGramMatrixInt b t ht := by
  -- Prove the matrices agree row-by-row using a stronger row-level identity:
  -- for all r : Fin n with r.val < t, the rows of `rowAdd b j k c` and `b`
  -- agree.
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  have hp_ne : (GramSchmidt.liftFinLE ⟨p, hp⟩ ht).val ≠ k.val :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hp hkt)
  have hq_ne : (GramSchmidt.liftFinLE ⟨q, hq⟩ ht).val ≠ k.val :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hq hkt)
  have hp_eq : (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE ⟨p, hp⟩ ht] =
      b[GramSchmidt.liftFinLE ⟨p, hp⟩ ht] :=
    rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE ⟨p, hp⟩ ht) c hp_ne
  have hq_eq : (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE ⟨q, hq⟩ ht] =
      b[GramSchmidt.liftFinLE ⟨q, hq⟩ ht] :=
    rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE ⟨q, hq⟩ ht) c hq_ne
  simp only [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row,
    Vector.getElem_ofFn, hp_eq, hq_eq]

/-- Entry-level structural identity for the leading Gram matrix of
`Matrix.rowAdd b j k c` when the modified row `k` lies inside the leading
`t`-prefix. The four cases (`p = k.val ∨ p ≠ k.val` × `q = k.val ∨ q ≠ k.val`)
are handled separately. -/
private theorem leadingGramMatrixInt_rowAdd_entry_inside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) (hkt : k.val < t)
    (p q : Fin t) :
    (GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht)[p][q] =
      (Matrix.colAdd
          (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht)
            ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)
          ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)[p][q] := by
  -- Abbreviations as Fin t.
  let jt : Fin t := ⟨j.val, Nat.lt_trans hjk hkt⟩
  let kt : Fin t := ⟨k.val, hkt⟩
  -- liftFinLE jt ht = j, liftFinLE kt ht = k as Fin n.
  have hjt_lift : GramSchmidt.liftFinLE jt ht = j := Fin.ext rfl
  have hkt_lift : GramSchmidt.liftFinLE kt ht = k := Fin.ext rfl
  -- The Gram matrix entry as a dot product of integer rows.
  have hM_entry : ∀ (a b' : Fin t),
      (GramSchmidt.leadingGramMatrixInt b t ht)[a][b'] =
        Matrix.dot (b[GramSchmidt.liftFinLE a ht]) (b[GramSchmidt.liftFinLE b' ht]) := by
    intro a b'
    simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row,
      Vector.getElem_ofFn]
  -- LHS is a dot product over `Matrix.rowAdd b j k c` rows.
  have hLHS :
      (GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht)[p][q] =
        Matrix.dot ((Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht])
          ((Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE q ht]) := by
    simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row,
      Vector.getElem_ofFn]
  -- RHS: the colAdd-rowAdd entry as a conditional.
  have hRHS :
      (Matrix.colAdd
          (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c) jt kt c)[p][q] =
        if q = kt then
          (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c)[p][q] +
            c * (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c)[p][jt]
        else (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c)[p][q] := by
    simp [Matrix.colAdd, Matrix.ofFn, Vector.getElem_ofFn]
  rw [hLHS, hRHS]
  -- Case split on `q = kt` and `p = kt`.
  by_cases hqk : q = kt
  · -- q = kt branch
    rw [if_pos hqk]
    rw [rowAdd_get_rect (GramSchmidt.leadingGramMatrixInt b t ht) jt kt p c q,
        rowAdd_get_rect (GramSchmidt.leadingGramMatrixInt b t ht) jt kt p c jt]
    -- The `b[·]` rewrites for `liftFinLE jt ht` and `liftFinLE kt ht`
    -- give `b[j]` and `b[k]` respectively. These survive even when direct
    -- `rw` fails on motive: we rewrite the matrix row indexings via
    -- `congrArg b.get` once and reuse.
    have hbjt_lift : b[GramSchmidt.liftFinLE jt ht] = b[j] :=
      congrArg b.get hjt_lift
    have hbkt_lift : b[GramSchmidt.liftFinLE kt ht] = b[k] :=
      congrArg b.get hkt_lift
    by_cases hpk : p = kt
    · -- p = kt, q = kt
      have hpn_k : GramSchmidt.liftFinLE p ht = k :=
        Fin.ext (Fin.val_eq_of_eq hpk : p.val = kt.val)
      have hqn_k : GramSchmidt.liftFinLE q ht = k :=
        Fin.ext (Fin.val_eq_of_eq hqk : q.val = kt.val)
      have hrowAdd_p :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hpn_k
      have hrowAdd_q :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE q ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hqn_k
      rw [hrowAdd_p, hrowAdd_q]
      rw [dot_rowAdd_row_at_left b j k c ((Matrix.rowAdd b j k c)[k])]
      have hrec_k :
          Matrix.dot b[k] ((Matrix.rowAdd b j k c)[k]) =
            Matrix.dot b[k] b[k] + c * Matrix.dot b[k] b[j] :=
        dot_rowAdd_row_at_right b j k c b[k]
      have hrec_j :
          Matrix.dot b[j] ((Matrix.rowAdd b j k c)[k]) =
            Matrix.dot b[j] b[k] + c * Matrix.dot b[j] b[j] :=
        dot_rowAdd_row_at_right b j k c b[j]
      rw [hrec_k, hrec_j]
      simp only [if_pos hpk]
      rw [hM_entry kt q, hM_entry jt q, hM_entry kt jt, hM_entry jt jt]
      have hb_q : b[GramSchmidt.liftFinLE q ht] = b[k] :=
        congrArg b.get hqn_k
      rw [hbjt_lift, hbkt_lift, hb_q]
      have hsym : Matrix.dot b[j] b[k] = Matrix.dot b[k] b[j] := dot_comm_int _ _
      rw [hsym]
    · -- p ≠ kt, q = kt
      have hpn_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val :=
        fun h => hpk (Fin.ext h)
      have hqn_k : GramSchmidt.liftFinLE q ht = k :=
        Fin.ext (Fin.val_eq_of_eq hqk : q.val = kt.val)
      have hrowAdd_q :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE q ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hqn_k
      have hb_q : b[GramSchmidt.liftFinLE q ht] = b[k] :=
        congrArg b.get hqn_k
      rw [hrowAdd_q]
      rw [rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE p ht) c hpn_ne]
      rw [dot_rowAdd_row_at_right b j k c (b[GramSchmidt.liftFinLE p ht])]
      simp only [if_neg hpk]
      rw [hM_entry p q, hM_entry p jt]
      rw [hbjt_lift, hb_q]
  · -- q ≠ kt branch
    rw [if_neg hqk]
    have hqn_ne : (GramSchmidt.liftFinLE q ht).val ≠ k.val :=
      fun h => hqk (Fin.ext h)
    rw [rowAdd_get_rect (GramSchmidt.leadingGramMatrixInt b t ht) jt kt p c q]
    rw [rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE q ht) c hqn_ne]
    have hbjt_lift : b[GramSchmidt.liftFinLE jt ht] = b[j] :=
      congrArg b.get hjt_lift
    have hbkt_lift : b[GramSchmidt.liftFinLE kt ht] = b[k] :=
      congrArg b.get hkt_lift
    by_cases hpk : p = kt
    · -- p = kt, q ≠ kt
      have hpn_k : GramSchmidt.liftFinLE p ht = k :=
        Fin.ext (Fin.val_eq_of_eq hpk : p.val = kt.val)
      have hrowAdd_p :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hpn_k
      rw [hrowAdd_p]
      rw [dot_rowAdd_row_at_left b j k c (b[GramSchmidt.liftFinLE q ht])]
      simp only [if_pos hpk]
      rw [hM_entry kt q, hM_entry jt q]
      rw [hbjt_lift, hbkt_lift]
    · -- p ≠ kt, q ≠ kt
      have hpn_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val :=
        fun h => hpk (Fin.ext h)
      rw [rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE p ht) c hpn_ne]
      simp only [if_neg hpk]
      rw [hM_entry p q]

/-- When the modified row index `k` lies inside the leading `t`-prefix
(`k.val < t`), the leading Gram matrix of `Matrix.rowAdd b j k c` agrees with
the row-and-column-add of the original leading Gram matrix at the lifted
`Fin t` indices `jt`, `kt`. Internal support lemma for the row-add
determinant theorem in `HexGramSchmidtMathlib.Int`. -/
theorem leadingGramMatrixInt_rowAdd_inside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) (hkt : k.val < t) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht =
      Matrix.colAdd
        (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht)
          ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)
        ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c := by
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  exact leadingGramMatrixInt_rowAdd_entry_inside b j k c t ht hjk hkt
    ⟨p, hp⟩ ⟨q, hq⟩


/-- The executable scaled-coefficient pivot entry changes predictably under
an earlier-row addition. This packages the Cramer/Bareiss pivot identity at
the public `scaledCoeffs` level so update callers need not unfold the
underlying determinant identity directly. -/
theorem scaledCoeffs_rowAdd_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k j =
      GramSchmidt.entry (scaledCoeffs b) k j +
        c * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  have hnew := scaledCoeffs_eq_scaledCoeffMatrix_det
    (b := Matrix.rowAdd b j k c) (i := k) (j := j) hjk
  have hold := scaledCoeffs_eq_scaledCoeffMatrix_det (b := b) (i := k) (j := j) hjk
  have hbridge := scaledCoeffMatrix_rowAdd_pivot_det (b := b) (j := j) (k := k) hjk c
  have hlead := leadingGramMatrixInt_det_eq_gramDet_int
    (b := b) (t := j.val + 1) (ht := Nat.succ_le_of_lt j.isLt)
  calc
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k j =
        Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk) := hnew
    _ =
        Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
          c * Matrix.det
            (GramSchmidt.leadingGramMatrixInt b (j.val + 1)
              (Nat.succ_le_of_lt j.isLt)) := hbridge
    _ =
        GramSchmidt.entry (scaledCoeffs b) k j +
          c * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
      rw [← hold, hlead]


/-- Adding a multiple of an earlier row to a later row leaves the leading
Gram determinant unchanged. The hypothesis `j.val < k.val` makes the source
row earlier than the destination row in the basis. -/
theorem gramDet_rowAdd_earlier
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) :
    gramDet (Matrix.rowAdd b j k c) t ht = gramDet b t ht := by
  unfold gramDet
  -- Reduce to the underlying Bareiss-determinant equality on `Int`.
  congr 1
  by_cases hkt : k.val < t
  · -- Inside case: bareiss = det, then det_rowAdd / det_colAdd preserve.
    rw [leadingGramMatrixInt_rowAdd_inside b j k c t ht hjk hkt]
    -- Identify `bareiss = det` via Mathlib's `Matrix.det ∘ matrixEquiv`,
    -- composing `bareiss_eq_mathlib_det` with `det_eq.symm` to keep the
    -- executable determinant surface visible to `det_colAdd` / `det_rowAdd`.
    have hbareiss_det : ∀ (M : Hex.Matrix Int t t),
        Hex.Matrix.bareiss M = Hex.Matrix.det M := fun M =>
      (HexMatrixMathlib.bareiss_eq_mathlib_det M).trans
        (HexMatrixMathlib.det_eq M).symm
    rw [hbareiss_det, hbareiss_det]
    -- Indices and inequality between `jt` and `kt` in `Fin t`.
    have hjt_ne_kt : (⟨j.val, Nat.lt_trans hjk hkt⟩ : Fin t) ≠ ⟨k.val, hkt⟩ := by
      intro h
      have hval : (⟨j.val, Nat.lt_trans hjk hkt⟩ : Fin t).val =
          (⟨k.val, hkt⟩ : Fin t).val :=
        congrArg Fin.val h
      exact Nat.ne_of_lt hjk hval
    rw [Matrix.det_colAdd _ _ _ _ hjt_ne_kt]
    rw [Matrix.det_rowAdd _ _ _ _ hjt_ne_kt]
  · -- Outside case: leading prefix unchanged.
    have hkt' : t ≤ k.val := Nat.le_of_not_lt hkt
    rw [leadingGramMatrixInt_rowAdd_outside b j k c t ht hkt']


/-! ### `scaledCoeffs` row-by-row updates under earlier-row addition

The three theorems below package the scaled-coefficient update under
`Matrix.rowAdd b j k c` with `j.val < k.val` at each below-diagonal column
position (left of the pivot, the row that is unchanged when not the
destination, and strictly between the source and the pivot column). They
mirror the pattern of `scaledCoeffs_rowAdd_pivot` and let the
`LLLState.sizeReduceColumn` proof-field discharges in `HexLLL/Basic.lean`
work against `rowAdd` directly, without reaching for the Mathlib-side
`scaledCoeffs_sizeReduce_*` wrappers in `HexGramSchmidt/Update.lean`. -/

private theorem intCast_rat_injective_for_rowAdd {a b : Int}
    (h : (a : Rat) = (b : Rat)) : a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by
    push_cast
    grind
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega

private theorem scaledCoeffs_eq_fin_of_lt (b : Matrix Int n m) (i j : Fin n)
    (hji : j.val < i.val) :
    ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) =
      (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt) : Rat) *
        GramSchmidt.entry (coeffs b) i j := by
  simpa using scaledCoeffs_eq (b := b) i.val j.val i.isLt hji

/-- Under `Matrix.rowAdd b j k c` with `l.val < j.val < k.val`, the
destination-row scaled coefficient at column `l` updates by the linear
combination `(scaledCoeffs b)[k][l] + c * (scaledCoeffs b)[j][l]`. -/
theorem scaledCoeffs_rowAdd_lower (b : Matrix Int n m) (l j k : Fin n)
    (hlj : l.val < j.val) (hjk : j.val < k.val) (c : Int) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l +
        c * GramSchmidt.entry (scaledCoeffs b) j l := by
  apply intCast_rat_injective_for_rowAdd
  have hlk : l.val < k.val := Nat.lt_trans hlj hjk
  have hnew := scaledCoeffs_eq_fin_of_lt (b := Matrix.rowAdd b j k c) k l hlk
  have holdk := scaledCoeffs_eq_fin_of_lt (b := b) k l hlk
  have holdj := scaledCoeffs_eq_fin_of_lt (b := b) j l hlj
  have hdet :
      gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
        gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
    gramDet_rowAdd_earlier b j k c (l.val + 1)
      (Nat.succ_le_of_lt l.isLt) hjk
  have hcoeff := coeffs_rowAdd_lower (b := b) l j k hlj hjk c
  calc
    ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l : Int) : Rat)
        =
          (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
              (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) k l := hnew
    _ =
          (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            (GramSchmidt.entry (coeffs b) k l +
              (c : Rat) * GramSchmidt.entry (coeffs b) j l) := by
          rw [hdet, hcoeff]
    _ =
          ((GramSchmidt.entry (scaledCoeffs b) k l +
            c * GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
          calc
            (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                (GramSchmidt.entry (coeffs b) k l +
                  (c : Rat) * GramSchmidt.entry (coeffs b) j l)
                =
                  (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                    GramSchmidt.entry (coeffs b) k l +
                    (c : Rat) *
                      ((gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
                        GramSchmidt.entry (coeffs b) j l) := by
                  grind
            _ =
                  ((GramSchmidt.entry (scaledCoeffs b) k l : Int) : Rat) +
                    (c : Rat) *
                      ((GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
                  rw [← holdk, ← holdj]
            _ =
                  ((GramSchmidt.entry (scaledCoeffs b) k l +
                    c * GramSchmidt.entry (scaledCoeffs b) j l : Int) : Rat) := by
                  grind

/-- Under `Matrix.rowAdd b j k c` with `j.val < k.val`, every row of
`scaledCoeffs` other than the destination row `k` is preserved. -/
theorem scaledCoeffs_rowAdd_other_row (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) (i : Fin n) (hik : i ≠ k) :
    (scaledCoeffs (Matrix.rowAdd b j k c)).row i = (scaledCoeffs b).row i := by
  apply Vector.ext
  intro col hcol
  let l : Fin n := ⟨col, hcol⟩
  change GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) i l =
    GramSchmidt.entry (scaledCoeffs b) i l
  by_cases hli : l.val < i.val
  · apply intCast_rat_injective_for_rowAdd
    have hnew := scaledCoeffs_eq_fin_of_lt (b := Matrix.rowAdd b j k c) i l hli
    have hold := scaledCoeffs_eq_fin_of_lt (b := b) i l hli
    have hdet :
        gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
          gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
      gramDet_rowAdd_earlier b j k c (l.val + 1)
        (Nat.succ_le_of_lt l.isLt) hjk
    have hrow := coeffs_rowAdd_other_row (b := b) j k c hjk i hik
    have hcoeff :
        GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) i l =
          GramSchmidt.entry (coeffs b) i l := by
      have hget := congrArg (fun row => row[l]) hrow
      simpa [GramSchmidt.entry] using hget
    calc
      ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) i l : Int) : Rat)
          =
            (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
                (Nat.succ_le_of_lt l.isLt) : Rat) *
              GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) i l := hnew
      _ =
            (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
              GramSchmidt.entry (coeffs b) i l := by
            rw [hdet, hcoeff]
      _ = ((GramSchmidt.entry (scaledCoeffs b) i l : Int) : Rat) := hold.symm
  · by_cases hil : i = l
    · subst l
      rw [← hil]
      rw [scaledCoeffs_diag, scaledCoeffs_diag]
      exact congrArg Int.ofNat
        (gramDet_rowAdd_earlier b j k c (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) hjk)
    · have hilv : i.val < l.val := by
        have hle : i.val ≤ l.val := Nat.le_of_not_lt hli
        exact Nat.lt_of_le_of_ne hle (fun h => hil (Fin.ext h))
      rw [scaledCoeffs_upper (Matrix.rowAdd b j k c) i.val l.val i.isLt l.isLt hilv,
        scaledCoeffs_upper b i.val l.val i.isLt l.isLt hilv]

/-- Under `Matrix.rowAdd b j k c` with `j.val < l.val < k.val`, the
destination-row scaled coefficient at column `l` between the source column
and the pivot is preserved. -/
theorem scaledCoeffs_rowAdd_above_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) (l : Fin n)
    (hjl : j.val < l.val) (hlk : l.val < k.val) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l =
      GramSchmidt.entry (scaledCoeffs b) k l := by
  apply intCast_rat_injective_for_rowAdd
  have hnew := scaledCoeffs_eq_fin_of_lt (b := Matrix.rowAdd b j k c) k l hlk
  have hold := scaledCoeffs_eq_fin_of_lt (b := b) k l hlk
  have hdet :
      gramDet (Matrix.rowAdd b j k c) (l.val + 1) (Nat.succ_le_of_lt l.isLt) =
        gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) :=
    gramDet_rowAdd_earlier b j k c (l.val + 1)
      (Nat.succ_le_of_lt l.isLt) hjk
  have hcoeff := coeffs_rowAdd_above_pivot (b := b) j l k hjl hlk c
  calc
    ((GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k l : Int) : Rat)
        =
          (gramDet (Matrix.rowAdd b j k c) (l.val + 1)
              (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs (Matrix.rowAdd b j k c)) k l := hnew
    _ =
          (gramDet b (l.val + 1) (Nat.succ_le_of_lt l.isLt) : Rat) *
            GramSchmidt.entry (coeffs b) k l := by
          rw [hdet, hcoeff]
    _ = ((GramSchmidt.entry (scaledCoeffs b) k l : Int) : Rat) := hold.symm


/-! ### Determinant-backed independence

These determinant-positivity lemmas for `gramDet` live in
`HexGramSchmidtMathlib` because their proofs identify `gramDet` with the
Leibniz determinant of the leading Gram matrix via the composition of
`HexMatrixMathlib.bareiss_eq_mathlib_det` and `HexMatrixMathlib.det_eq.symm`
(packaged here as `leadingGramMatrixInt_det_eq_gramDet_int`). Callers that
already have a determinant lemma for a special matrix family can produce the
public `independent` predicate stated over Mathlib-free computed data. -/

private theorem gramDet_pos_of_det_positive (b : Matrix Int n m)
    (hdet : ∀ k : Fin n, 0 < Matrix.det (Matrix.submatrix (Matrix.gramMatrix b) k))
    (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  cases k with
  | zero =>
      omega
  | succ r =>
      have hrn : r < n := Nat.lt_of_succ_le hk
      let last : Fin n := ⟨r, hrn⟩
      have hsub : 0 < Matrix.det (Matrix.submatrix (Matrix.gramMatrix b) last) :=
        hdet last
      have hsub_eq :
          Matrix.submatrix (Matrix.gramMatrix b) last =
            GramSchmidt.leadingGramMatrixInt b (r + 1) hk := by
        rw [Matrix.submatrix_eq_leadingPrefix]
        rw [GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram]
      have hdet_pos :
          0 < Matrix.det (GramSchmidt.leadingGramMatrixInt b (r + 1) hk) := by
        simpa [hsub_eq] using hsub
      have hdet_nat :
          Matrix.det (GramSchmidt.leadingGramMatrixInt b (r + 1) hk) =
            Int.ofNat (gramDet b (r + 1) hk) :=
        leadingGramMatrixInt_det_eq_gramDet_int b (r + 1) hk
      have hnat_int : 0 < Int.ofNat (gramDet b (r + 1) hk) := by
        simpa [hdet_nat] using hdet_pos
      exact Int.ofNat_lt.mp hnat_int

/-- A determinant-positive leading-Gram-prefix proof induces the executable
`gramDet` independence predicate. This is useful for callers that already
have determinant lemmas for special matrix families, while keeping the public
predicate stated over Mathlib-free computed data. -/
theorem independent_of_det_positive (b : Matrix Int n m)
    (hdet : ∀ k : Fin n, 0 < Matrix.det (Matrix.submatrix (Matrix.gramMatrix b) k)) :
    independent b := by
  intro k
  exact gramDet_pos_of_det_positive b hdet (k.val + 1) (Nat.succ_le_of_lt k.isLt)
    (Nat.succ_pos k.val)

theorem independent_one {n : Nat} : independent (1 : Matrix Int n n) := by
  exact independent_of_det_positive (1 : Matrix Int n n) (by
    intro k
    rw [Matrix.gramMatrix_one, Matrix.submatrix_one, Matrix.det_one]
    decide)


/-! ### Singular-prefix zero propagation for the Gram-Bareiss surface

When the no-pivot Bareiss loop on a Gram matrix records a singular step at
index `s`, the `(s+1)`-leading Gram prefix has zero determinant. By the
multiplicative succession `gramSchmidtNormProduct_succ`, the same vanishing
propagates to every larger prefix. This is the singular branch of the
`gramDetVecEntry_eq_leadingPrefix_bareiss` placeholder. -/


/-- From a partial no-pivot Bareiss pass on `M` recording a singular step at
index `s`, derive that the `s`-fueled prefix is non-singular, has reached
`step = s`, and has zero diagonal at `(s, s)`. This is the structural data
needed to invoke `BareissNoPivotInvariant` at the moment of singularity.

The matrix-entry equality is transferred from the final state to the prefix
state via `Matrix.noPivotLoop_diag_of_le_step`: subsequent no-pivot iterations
do not modify the diagonal at indices `≤ state.step`. -/
private theorem noPivotLoop_prefix_state_at_singular
    {n : Nat} (M : Matrix Int n n) (fuel s : Nat) (hs : s + 1 ≤ n)
    (h_sing : (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState M)).singularStep = some s) :
    (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).singularStep = none ∧
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s ∧
      (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState M)).matrix[
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)][
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)] = 0 := by
  set init := Matrix.noPivotInitialState M with hinit_def
  have h_init_sing : init.singularStep = none := rfl
  have h_init_step : init.step = 0 := rfl
  -- First derive `s < fuel` from the singular bound.
  have hsfuel : s < fuel := by
    have := noPivotLoop_singularStep_lt (n := n) fuel init h_init_sing s h_sing
    rw [h_init_step] at this
    omega
  -- Case analysis on whether the s-fueled prefix is already singular.
  rcases noPivotLoop_singular_inv (n := n) s init h_init_sing
    with h_none | ⟨k', h_sing_s, h_step_s, h_zero_s, h_klt⟩
  · -- s-fueled prefix is non-singular: derive .step = s and .matrix[s][s] = 0.
    have hS_step : (Matrix.noPivotLoop s init).step = s := by
      have h_room : init.step + s + 1 ≤ n := by rw [h_init_step]; omega
      have h_step := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        (n := n) s init h_init_sing h_room h_none
      rw [h_step, h_init_step]; omega
    refine ⟨h_none, hS_step, ?_⟩
    -- Apply singular_inv on the full pass to extract the zero diagonal.
    rcases noPivotLoop_singular_inv (n := n) fuel init h_init_sing
      with h_full_none | ⟨k, h_sing_full, h_step_full, h_zero_full, h_klt_full⟩
    · rw [h_full_none] at h_sing; nomatch h_sing
    · -- k.val = s from h_sing.
      have hk_eq : k.val = s := by
        rw [h_sing_full] at h_sing
        exact Option.some.inj h_sing
      -- Transfer the zero diagonal value from the full state back to the prefix state.
      have hsn : s < n := Nat.lt_of_succ_le hs
      have h_full_eq : Matrix.noPivotLoop (s + (fuel - s)) init =
          Matrix.noPivotLoop fuel init := by
        congr 1; omega
      have h_split : Matrix.noPivotLoop fuel init =
          Matrix.noPivotLoop (fuel - s) (Matrix.noPivotLoop s init) := by
        rw [← h_full_eq, Matrix.noPivotLoop_add s (fuel - s) init]
      have h_diag_preserved :
          (Matrix.noPivotLoop (fuel - s) (Matrix.noPivotLoop s init)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s init).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
        Matrix.noPivotLoop_diag_of_le_step (fuel - s)
          (Matrix.noPivotLoop s init) (⟨s, hsn⟩ : Fin n)
          (by rw [hS_step])
      have h_full_diag_eq :
          (Matrix.noPivotLoop fuel init).matrix[(⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s init).matrix[(⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] := by
        rw [h_split]; exact h_diag_preserved
      -- The full state's value at ⟨s, hsn⟩ equals 0 via h_zero_full at k = ⟨s, _⟩.
      have h_fin : k = (⟨s, hsn⟩ : Fin n) := Fin.ext hk_eq
      have h_full_zero :
          (Matrix.noPivotLoop fuel init).matrix[(⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] = 0 :=
        (matrix_diag_at_fin_eq (Matrix.noPivotLoop fuel init).matrix h_fin).symm.trans h_zero_full
      exact h_full_diag_eq.symm.trans h_full_zero
  · -- s-fueled prefix is already singular at some k'.val < s. Contradicts h_sing.
    have h_klt' : k'.val < s := by
      have := noPivotLoop_singularStep_lt (n := n) s init h_init_sing k'.val h_sing_s
      rw [h_init_step] at this
      omega
    -- The singular state persists.
    have h_persist :
        Matrix.noPivotLoop (s + (fuel - s)) init =
          Matrix.noPivotLoop s init :=
      noPivotLoop_extends_singularStep init s (fuel - s) k'
        h_sing_s h_step_s h_zero_s h_klt
    have h_fuel_eq : s + (fuel - s) = fuel := by omega
    rw [h_fuel_eq] at h_persist
    rw [h_persist] at h_sing
    rw [h_sing_s] at h_sing
    have hk'_eq : k'.val = s := Option.some.inj h_sing
    omega

/-- Specialization of `BareissNoPivotInvariant.trailing_eq` to the diagonal
corner: when the no-pivot Bareiss state has `step = k` for a free variable `k`,
its `(k, k)` matrix entry equals the determinant of the `(k + 1)`-leading
prefix of the source matrix. Stated with `k` as a free variable so that
`subst` can replace the let-bound projection with a fresh name. -/
private theorem bareissNoPivotInvariant_diag_eq_leadingPrefix_det
    {n : Nat} (M : Matrix Int n n) (state : Matrix.BareissState n) (k : Nat)
    (hinv : HexMatrixMathlib.BareissNoPivotInvariant M state)
    (hsk : k = state.step) (hk : k < n) :
    state.matrix[(⟨k, hk⟩ : Fin n)][(⟨k, hk⟩ : Fin n)] =
      Matrix.det (Matrix.leadingPrefix M (k + 1) (Nat.succ_le_of_lt hk)) := by
  subst hsk
  have h_trail :
      state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] =
        Matrix.det (Matrix.borderedMinor M state.step hk
          (⟨state.step, hk⟩ : Fin n) (⟨state.step, hk⟩ : Fin n)) :=
    hinv.trailing_eq hk (⟨state.step, hk⟩ : Fin n) (⟨state.step, hk⟩ : Fin n)
      (Nat.le_refl _) (Nat.le_refl _)
  rw [HexMatrixMathlib.borderedMinor_corner_eq_leadingPrefix M state.step hk] at h_trail
  exact h_trail

/-- Identification with the Mathlib leading-prefix determinant: from a partial
no-pivot Bareiss pass that records a singular step at index `s`, the
`(s+1)`-leading prefix of the source matrix has zero determinant (Hex's
`Matrix.det`). -/
private theorem leadingPrefix_det_eq_zero_of_noPivotLoop_singularStep
    {n : Nat} (M : Matrix Int n n) (fuel s : Nat) (hs : s + 1 ≤ n)
    (h_sing : (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState M)).singularStep = some s) :
    Matrix.det (Matrix.leadingPrefix M (s + 1) hs) = 0 := by
  obtain ⟨h_none, h_step, h_zero⟩ :=
    noPivotLoop_prefix_state_at_singular M fuel s hs h_sing
  -- Apply the noPivotLoop_invariant variant: S satisfies BareissNoPivotInvariant.
  have hinv_init : HexMatrixMathlib.BareissNoPivotInvariant M
      (Matrix.noPivotInitialState M) :=
    HexMatrixMathlib.bareissNoPivotInvariant_initial M
  have hinv_S : HexMatrixMathlib.BareissNoPivotInvariant M
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)) :=
    HexMatrixMathlib.noPivotLoop_invariant_of_singularStep_eq_none M s
      (Matrix.noPivotInitialState M) hinv_init h_none
  -- Use Nat.lt_of_succ_le hs as the bound throughout to match the helper's output type.
  -- Specialize the diagonal-corner helper: matrix[⟨s, _⟩][⟨s, _⟩] = det(leadingPrefix M (s+1) _).
  have h_diag_eq_lp :
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[(⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)][(⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)] =
        Matrix.det (Matrix.leadingPrefix M (s + 1) (Nat.succ_le_of_lt (Nat.lt_of_succ_le hs))) :=
    bareissNoPivotInvariant_diag_eq_leadingPrefix_det
      M (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)) s hinv_S
      h_step.symm (Nat.lt_of_succ_le hs)
  rw [h_zero] at h_diag_eq_lp
  -- h_diag_eq_lp : 0 = det(leadingPrefix M (s+1) (Nat.succ_le_of_lt ...)). The proof
  -- argument is definitionally equal to `hs`, so the goal matches up to proof irrelevance.
  exact h_diag_eq_lp.symm

/-- Multiplicative zero propagation for `gramSchmidtNormProduct`: if the
norm-product at some index `k₁` vanishes, every larger index's product also
vanishes. Proof is by induction on the gap via `gramSchmidtNormProduct_succ`. -/
private theorem gramSchmidtNormProduct_eq_zero_of_le {n m : Nat}
    (b : Matrix Int n m) (k₁ k₂ : Nat) (hk₂ : k₂ ≤ n) (hkk : k₁ ≤ k₂)
    (h₁ : gramSchmidtNormProduct b k₁ (Nat.le_trans hkk hk₂) = 0) :
    gramSchmidtNormProduct b k₂ hk₂ = 0 := by
  induction k₂ with
  | zero =>
      have : k₁ = 0 := Nat.le_zero.mp hkk
      subst this
      exact h₁
  | succ k₂' ih =>
      by_cases hcase : k₁ = k₂' + 1
      · subst hcase; exact h₁
      · have hkk' : k₁ ≤ k₂' := by omega
        have hk₂' : k₂' ≤ n := Nat.le_of_succ_le hk₂
        have h_prev : gramSchmidtNormProduct b k₂' hk₂' = 0 := by
          have h₁' : gramSchmidtNormProduct b k₁ (Nat.le_trans hkk' hk₂') = 0 := h₁
          exact ih hk₂' hkk' h₁'
        rw [gramSchmidtNormProduct_succ b k₂' hk₂, h_prev, Rat.zero_mul]

/-- Singular-branch zero propagation: if the partial-pass no-pivot Bareiss loop
on the full Gram matrix records a singular step at index `s` strictly before
slot `r + 1`, the public row-pivoted Bareiss determinant of the `(r + 1)`
leading Gram prefix is zero.

This is the supporting lemma needed by the singular branch of the
`gramDetVecEntry_eq_leadingPrefix_bareiss` placeholder: both sides vanish in
this case, and this lemma supplies the right-hand side. The proof composes the
new lemma `HexMatrixMathlib.noPivotLoop_invariant_of_singularStep_eq_none`
(to identify `det(leadingPrefix _ (s+1)) = 0` at the moment of singularity) with
the unconditional `gramDet_eq_prod_normSq_uncond` and the multiplicative
succession `gramSchmidtNormProduct_succ` to propagate zero from `s + 1` to
`r + 1`. -/
theorem leadingPrefix_gram_bareiss_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (r : Nat) (hr : r < n) (s : Nat)
    (h_sing : (Matrix.noPivotLoop r
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    Matrix.bareiss (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
        (Nat.succ_le_of_lt hr)) = 0 := by
  -- Step A: derive `s < r` from the partial-pass singular bound.
  have hsr : s < r := by
    have h := noPivotLoop_singularStep_lt (n := n) r
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
    change s < 0 + r at h
    omega
  have hs1 : s + 1 ≤ n := Nat.le_trans (Nat.succ_le_of_lt hsr) (Nat.le_of_lt hr)
  -- Step B: derive det(leadingPrefix (gramMatrix b) (s+1)) = 0 via the new lemma.
  have h_det_s1_zero :
      Matrix.det (Matrix.leadingPrefix (Matrix.gramMatrix b) (s + 1) hs1) = 0 :=
    leadingPrefix_det_eq_zero_of_noPivotLoop_singularStep
      (Matrix.gramMatrix b) r s hs1 h_sing
  -- Step C: convert to gramSchmidtNormProduct b (s+1) = 0.
  have h_lead_eq_s :
      GramSchmidt.leadingGramMatrixInt b (s + 1) hs1 =
        Matrix.leadingPrefix (Matrix.gramMatrix b) (s + 1) hs1 :=
    GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram b (s + 1) hs1
  have h_det_lead_s1_zero :
      Matrix.det (GramSchmidt.leadingGramMatrixInt b (s + 1) hs1) = 0 := by
    rw [h_lead_eq_s]; exact h_det_s1_zero
  have h_gd_s1_zero : gramDet b (s + 1) hs1 = 0 := by
    have hnat := leadingGramMatrixInt_det_eq_gramDet_int b (s + 1) hs1
    rw [h_det_lead_s1_zero] at hnat
    have hcast : Int.ofNat (gramDet b (s + 1) hs1) = Int.ofNat 0 := hnat.symm
    exact Int.ofNat.inj hcast
  have h_gd_s1_rat_zero : (gramDet b (s + 1) hs1 : Rat) = 0 := by
    rw [h_gd_s1_zero]; norm_cast
  have h_gsnp_s1_zero : gramSchmidtNormProduct b (s + 1) hs1 = 0 := by
    have := gramDet_eq_prod_normSq_uncond b (s + 1) hs1
    rw [this] at h_gd_s1_rat_zero
    exact h_gd_s1_rat_zero
  -- Step D: propagate to gramSchmidtNormProduct b (r+1) = 0.
  have hr1 : r + 1 ≤ n := Nat.succ_le_of_lt hr
  have hs1r1 : s + 1 ≤ r + 1 := Nat.succ_le_succ (Nat.le_of_lt hsr)
  have h_gsnp_r1_zero : gramSchmidtNormProduct b (r + 1) hr1 = 0 :=
    gramSchmidtNormProduct_eq_zero_of_le b (s + 1) (r + 1) hr1 hs1r1 h_gsnp_s1_zero
  -- Step E: back to gramDet b (r+1) = 0.
  have h_gd_r1_rat_zero : (gramDet b (r + 1) hr1 : Rat) = 0 := by
    rw [gramDet_eq_prod_normSq_uncond b (r + 1) hr1]; exact h_gsnp_r1_zero
  have h_gd_r1_zero : gramDet b (r + 1) hr1 = 0 := by
    have : ((gramDet b (r + 1) hr1 : Nat) : Rat) = (0 : Rat) := h_gd_r1_rat_zero
    exact_mod_cast this
  -- Step F: convert to det(leadingGramMatrixInt b (r+1)) = 0, then to bareiss.
  have h_det_lead_r1_zero :
      Matrix.det (GramSchmidt.leadingGramMatrixInt b (r + 1) hr1) = 0 := by
    have hnat := leadingGramMatrixInt_det_eq_gramDet_int b (r + 1) hr1
    rw [h_gd_r1_zero] at hnat
    simpa using hnat
  have h_det_prefix_r1_zero :
      Matrix.det (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1) hr1) = 0 := by
    have h_lead_eq_r :
        GramSchmidt.leadingGramMatrixInt b (r + 1) hr1 =
          Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1) hr1 :=
      GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram b (r + 1) hr1
    rw [← h_lead_eq_r]; exact h_det_lead_r1_zero
  rw [HexMatrixMathlib.bareiss_eq_det]
  exact h_det_prefix_r1_zero

/-- Capstone for the Gram determinant vector: the no-pivot
Bareiss pass over the full Gram matrix records, at slot `r + 1`, the same
leading-prefix determinant as the public row-pivoted Bareiss surface on that
prefix.

This theorem lives in `HexGramSchmidtMathlib` because the proof path for the
singular branch identifies the executable determinant with Mathlib's Leibniz
determinant. Mathlib-free callers should use the executable `gramDet` API
instead of depending on this Bareiss-facing statement. -/
theorem gramDetVecEntry_eq_leadingPrefix_bareiss
    (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ =
      (Matrix.bareiss
        (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
          (Nat.succ_le_of_lt hr))).toNat := by
  let GM := Matrix.gramMatrix b
  let init := Matrix.noPivotInitialState GM
  let data := Matrix.bareissNoPivotData GM
  let i : Fin n := ⟨r, hr⟩
  by_cases h_prefix :
      (Matrix.noPivotLoop r init).singularStep = none
  · have hdiag :=
      bareissNoPivotData_diag_eq_leadingPrefix_bareiss_of_prefix_nonsingular
        (b := b) r hr (by simpa [GM, init] using h_prefix)
    have h_step_r : (Matrix.noPivotLoop r init).step = r := by
      have h_room : init.step + r + 1 ≤ n := by
        simp [init, Matrix.noPivotInitialState]
        omega
      have h := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        r init rfl h_room h_prefix
      simpa [init, Matrix.noPivotInitialState] using h
    have h_entry_diag :
        gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (data.matrix[i][i]).toNat := by
      have h_split : r + (n - r) = n := by omega
      have h_full :
          Matrix.noPivotLoop n init =
            Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r init) := by
        simpa [h_split] using Matrix.noPivotLoop_add r (n - r) init
      rcases noPivotLoop_singular_inv (n := n) (n - r)
          (Matrix.noPivotLoop r init) h_prefix with h_none | h_sing
      · have hdata : data.singularStep = none := by
          simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full] using h_none
        simp [gramDetVecEntry, data, hdata, i]
        rfl
      · rcases h_sing with ⟨k, h_sing_full, h_step_full, h_zero_full, _hk_bound⟩
        have hdata : data.singularStep = some k.val := by
          simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full] using h_sing_full
        have hmono := noPivotLoop_step_monotone (n - r) (Matrix.noPivotLoop r init)
        have hr_le_k : r ≤ k.val := by
          rw [h_step_r, h_step_full] at hmono
          exact hmono
        by_cases hkr : k.val = r
        · have hlt : k.val < r + 1 := by omega
          have hdata_matrix :
              data.matrix[i][i] =
                (Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r init)).matrix[i][i] := by
            simp [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full]
          have hzero_i : data.matrix[i][i] = 0 := by
            have hi_eq : i = k := Fin.ext hkr.symm
            rw [hdata_matrix]
            simpa [hi_eq] using h_zero_full
          simp [gramDetVecEntry, data, hdata, i, hlt]
          simpa [data, i] using (congrArg Int.toNat hzero_i).symm
        · have hlt : ¬ k.val < r + 1 := by omega
          simp [gramDetVecEntry, data, hdata, i, hlt]
          rfl
    calc
      gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
          ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (data.matrix[i][i]).toNat := by
            simpa [data, GM, i] using h_entry_diag
      _ = (Matrix.bareiss
            (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
              (Nat.succ_le_of_lt hr))).toNat := by
            exact congrArg Int.toNat (by simpa [data, GM, i] using hdiag)
  · rcases noPivotLoop_singular_inv (n := n) r init rfl with h_none | h_sing
    · exact False.elim (h_prefix h_none)
    · rcases h_sing with ⟨k, h_sing_r, h_step_r, h_zero_r, h_klt⟩
      have hsr : k.val < r + 1 := by
        have h := noPivotLoop_singularStep_lt (n := n) r init rfl k.val h_sing_r
        simp [init, Matrix.noPivotInitialState] at h
        omega
      have h_full_eq :
          Matrix.noPivotLoop n init = Matrix.noPivotLoop r init := by
        have h_split : n = r + (n - r) := by omega
        have hext :=
          noPivotLoop_extends_singularStep init r (n - r) k
            h_sing_r h_step_r h_zero_r h_klt
        exact (congrArg (fun fuel => Matrix.noPivotLoop fuel init) h_split).trans hext
      have hdata : data.singularStep = some k.val := by
        simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full_eq] using h_sing_r
      have hleft :
          gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 := by
        simp [gramDetVecEntry, data, hdata, hsr]
      have hright :
          Matrix.bareiss
            (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
              (Nat.succ_le_of_lt hr)) = 0 :=
        leadingPrefix_gram_bareiss_eq_zero_of_singularStep_lt
          (b := b) r hr k.val (by simpa [GM, init] using h_sing_r)
      rw [hright]
      simpa [data, GM] using hleft


/-- Mathlib-side bridge wrapper for the Schur kernel singular cascade:
when the no-pivot Bareiss pass over the full Gram matrix records an
early singular step at column `s < j`, the scaled Gram-Schmidt
coefficient at any `(i, j)` with `j ≤ i` vanishes. Wraps the
Mathlib-free `getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt`
via the canonical `StepWitness.ofGram` instance. -/
theorem scaledCoeffs_lower_eq_zero_of_singularStep_lt
    {n m : Nat} (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (s : Nat) (hs : s < j.val)
    (h_sing : (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    GramSchmidt.entry (scaledCoeffs b) i j = 0 := by
  rw [scaledCoeffs_entry_eq_getArrayEntry]
  exact getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
    b (StepWitness.ofGram b) i.val j.val i.isLt (Nat.le_of_lt hji) s hs h_sing

/-- Unconditional rational closed form for the strictly lower entries of
`scaledCoeffs`: the executable integer scaled coefficient agrees with the
Leibniz determinant of the Cramer minor `scaledCoeffMatrix b i j hji`
regardless of whether the no-pivot Bareiss pass over `gramMatrix b`
reaches column `j` without a singular step. The non-singular branch
delegates to `scaledCoeffs_lower_eq_det_scaledCoeffMatrix_of_no_singular`;
the singular branch composes
`scaledCoeffs_lower_eq_zero_of_singularStep_lt` (LHS = 0) with
`scaledCoeffMatrix_det_eq_zero_of_singularStep_lt` (RHS = 0). -/
theorem scaledCoeffs_lower_eq_det_scaledCoeffMatrix
    {n m : Nat} (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    ((GramSchmidt.entry (scaledCoeffs b) i j : Int) : Rat) =
      ((Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) : Int) : Rat) := by
  cases h_sing : (Matrix.noPivotLoop j.val
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep with
  | none =>
      exact scaledCoeffs_lower_eq_det_scaledCoeffMatrix_of_no_singular b i j hji h_sing
  | some s =>
      have hsj : s < j.val := by
        have h := Hex.GramSchmidt.Int.noPivotLoop_singularStep_lt j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
        change s < 0 + j.val at h
        omega
      have h_lhs : GramSchmidt.entry (scaledCoeffs b) i j = 0 :=
        scaledCoeffs_lower_eq_zero_of_singularStep_lt b i j hji s hsj h_sing
      have h_det : Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) = 0 :=
        scaledCoeffMatrix_det_eq_zero_of_singularStep_lt b i j hji s h_sing
      rw [h_lhs, h_det]

end Int
end GramSchmidt
end Hex
