module

public import HexGramSchmidt.Int
public import HexMatrixMathlib.Determinant

public section

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
private theorem dot_prefixCombination_right_eq_zero
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
private theorem originalProjectionCoords_dot_eq
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
    apply dot_prefixCombination_right_eq_zero
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
    apply dot_prefixCombination_right_eq_zero
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
`originalProjectionCoords_dot_eq`; the downstream Cramer
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
    originalProjectionCoords_dot_eq
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

/-- The `k`-leading Gram determinant equals, as a rational, the product of the
squared Gram-Schmidt norms of the first `k` basis vectors
(`gramSchmidtNormProduct b k`). Public wrapper over
`gramDet_eq_prod_normSq_core`. -/
theorem gramDet_eq_prod_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk :=
  gramDet_eq_prod_normSq_core b hli k hk

/-- For an independent integer matrix `b`, every nonempty leading Gram
determinant is strictly positive (`0 < k ≤ n`). Public wrapper over
`gramDet_pos_core`. -/
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

/-- The squared norm of the `k`-th Gram-Schmidt basis vector is the ratio of
consecutive leading Gram determinants `d_{k+1} / d_k`, the standard telescoping
identity. Public wrapper over `basis_normSq_core`. -/
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
    apply dot_prefixCombination_right_eq_zero
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
private theorem dot_castIntRow_castIntRow_eq
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
    (dot_castIntRow_castIntRow_eq
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
      apply dot_prefixCombination_right_eq_zero
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

end Int
end GramSchmidt
end Hex
