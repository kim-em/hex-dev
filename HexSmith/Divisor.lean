/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmith.Contracts
public import HexDeterminant.Gram

public section

/-! Determinantal divisors, defined independently of the Smith algorithm. -/

namespace Hex.Matrix

/-- Canonical row/column choices for `k × k` minors. -/
noncomputable def minorSelections (n m k : Nat) :
    List (Vector (Fin n) k × Vector (Fin m) k) :=
  (selectedColumnTuples k n).flatMap fun rows =>
    (selectedColumnTuples k m).map fun cols => (rows, cols)

/-- Absolute determinant attached to one selected row/column pair. -/
noncomputable def minorValue (A : Matrix Int n m)
    (selection : Vector (Fin n) k × Vector (Fin m) k) : Nat :=
  (det (selectedSubmatrix A selection.1 selection.2)).natAbs

/-- The natural gcd of the determinants of all `k × k` minors. Row and
column selections are enumerated in the canonical strictly increasing order
provided by `selectedColumnTuples`; the definition therefore contains no
reference to `snf`. The empty minor has determinant one.

Direct evaluation enumerates all `k × k` minors and is exponential in the
matrix dimensions. This is a specification surface for uniqueness proofs,
not the executable way to obtain invariant factors; use `invariantFactors`
for computation. -/
noncomputable def detDivisor (A : Matrix Int n m) (k : Nat) : Nat :=
  (minorSelections n m k).foldl (fun g selection =>
    Nat.gcd g (minorValue A selection)) 0

private theorem foldl_gcd_dvd_acc {R : Type} (xs : List R) (f : R → Nat)
    (acc : Nat) : xs.foldl (fun g x => Nat.gcd g (f x)) acc ∣ acc := by
  induction xs generalizing acc with
  | nil => exact Nat.dvd_refl acc
  | cons x xs ih =>
      exact Nat.dvd_trans (ih (Nat.gcd acc (f x))) (Nat.gcd_dvd_left acc (f x))

private theorem foldl_gcd_dvd_mem {R : Type} (xs : List R) (f : R → Nat)
    (acc : Nat) {x : R} (hx : x ∈ xs) :
    xs.foldl (fun g x => Nat.gcd g (f x)) acc ∣ f x := by
  induction xs generalizing acc with
  | nil => cases hx
  | cons y ys ih =>
      rw [List.mem_cons] at hx
      rcases hx with hxy | hx
      · subst x
        exact Nat.dvd_trans (foldl_gcd_dvd_acc ys f (Nat.gcd acc (f y)))
          (Nat.gcd_dvd_right acc (f y))
      · exact ih (Nat.gcd acc (f y)) hx

private theorem dvd_foldl_gcd {R : Type} (d : Nat) (xs : List R) (f : R → Nat)
    (acc : Nat) (hacc : d ∣ acc) (hall : ∀ x ∈ xs, d ∣ f x) :
    d ∣ xs.foldl (fun g x => Nat.gcd g (f x)) acc := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
      apply ih (Nat.gcd acc (f x))
      · exact Nat.dvd_gcd hacc (hall x (by simp))
      · intro y hy
        exact hall y (List.mem_cons_of_mem x hy)

private theorem foldl_gcd_eq_zero {R : Type} (xs : List R) (f : R → Nat)
    (hall : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun g x => Nat.gcd g (f x)) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, hall x (by simp), Nat.gcd_zero_right]
      apply ih
      intro y hy
      exact hall y (List.mem_cons_of_mem x hy)

/-- A pair of canonical row and column selections occurs in the combined
minor-selection enumeration. -/
theorem minorSelections_mem (rows : Vector (Fin n) k) (cols : Vector (Fin m) k)
    (hrows : rows ∈ selectedColumnTuples k n)
    (hcols : cols ∈ selectedColumnTuples k m) :
    (rows, cols) ∈ minorSelections n m k := by
  simp only [minorSelections, List.mem_flatMap, List.mem_map]
  exact ⟨rows, hrows, cols, hcols, rfl⟩

set_option maxHeartbeats 800000 in
/-- The determinantal divisor divides every canonically selected minor. -/
theorem detDivisor_dvd_minor (A : Matrix Int n m) (k : Nat)
    (rows : Vector (Fin n) k) (cols : Vector (Fin m) k)
    (hrows : rows ∈ selectedColumnTuples k n)
    (hcols : cols ∈ selectedColumnTuples k m) :
    detDivisor A k ∣ (det (selectedSubmatrix A rows cols)).natAbs := by
  change (minorSelections n m k).foldl
      (fun g selection => Nat.gcd g (minorValue A selection)) 0 ∣
    minorValue A (rows, cols)
  exact foldl_gcd_dvd_mem (minorSelections n m k) (minorValue A) 0
    (minorSelections_mem rows cols hrows hcols)

/-- A natural number dividing every selected minor divides the determinantal
divisor. -/
theorem dvd_detDivisor (A : Matrix Int n m) (k d : Nat)
    (h : ∀ rows ∈ selectedColumnTuples k n,
      ∀ cols ∈ selectedColumnTuples k m,
        d ∣ (det (selectedSubmatrix A rows cols)).natAbs) :
    d ∣ detDivisor A k := by
  unfold detDivisor
  apply dvd_foldl_gcd d (minorSelections n m k)
    (minorValue A) 0
  · exact Nat.dvd_zero d
  · intro selection hselection
    rw [minorSelections, List.mem_flatMap] at hselection
    rcases hselection with ⟨rows, hrows, hcols⟩
    rw [List.mem_map] at hcols
    rcases hcols with ⟨cols, hcols, rfl⟩
    exact h rows hrows cols hcols

/-- If every canonically selected `k × k` minor vanishes, so does the
determinantal divisor. -/
theorem detDivisor_eq_zero (A : Matrix Int n m) (k : Nat)
    (h : ∀ rows ∈ selectedColumnTuples k n,
      ∀ cols ∈ selectedColumnTuples k m,
        det (selectedSubmatrix A rows cols) = 0) :
    detDivisor A k = 0 := by
  unfold detDivisor
  apply foldl_gcd_eq_zero
  intro selection hselection
  rw [minorSelections, List.mem_flatMap] at hselection
  rcases hselection with ⟨rows, hrows, hcols⟩
  rw [List.mem_map] at hcols
  rcases hcols with ⟨cols, hcols, rfl⟩
  unfold minorValue
  rw [h rows hrows cols hcols, Int.natAbs_zero]

private theorem dvd_foldl_add {R : Type} (d : Int) (xs : List R)
    (f : R → Int) (acc : Int) (hacc : d ∣ acc)
    (hall : ∀ x ∈ xs, d ∣ f x) :
    d ∣ xs.foldl (fun total x => total + f x) acc := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
      apply ih (acc + f x)
      · exact Int.dvd_add hacc (hall x (by simp))
      · intro y hy
        exact hall y (List.mem_cons_of_mem x hy)

private theorem int_dvd_foldl_add {R : Type} (d : Int) (xs : List R)
    (f : R → Int) (hall : ∀ x ∈ xs, d ∣ f x) :
    d ∣ xs.foldl (fun total x => total + f x) 0 :=
  dvd_foldl_add d xs f 0 (Int.dvd_zero d) hall

private theorem ofNat_dvd {d : Nat} {x : Int}
    (h : d ∣ x.natAbs) : (Int.ofNat d) ∣ x := by
  apply Int.natAbs_dvd_natAbs.mp
  simpa using h

private theorem dvd_natAbs {d : Nat} {x : Int}
    (h : (Int.ofNat d) ∣ x) : d ∣ x.natAbs := by
  have := Int.natAbs_dvd_natAbs.mpr h
  simpa using this

private theorem IsSNF.diag_dvd_of_le {A : Matrix Int n m} {S : SmithData n m}
    (h : IsSNF A S) {i j : Nat} (hi : i < S.rank) (hj : j < S.rank)
    (hij : i ≤ j) :
    S.diag[(⟨i, hi⟩ : Fin S.rank)] ∣ S.diag[(⟨j, hj⟩ : Fin S.rank)] := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact Int.dvd_refl _
  | succ j ih =>
      by_cases hij' : i = j + 1
      · subst i
        exact Int.dvd_refl _
      · have hi_le_j : i ≤ j := by omega
        exact Int.dvd_trans (ih (by omega) hi_le_j)
          (h.chain j (by omega))

/-- Folding a vector prefix agrees with folding its finite index range. -/
theorem foldl_take_eq_finFoldl (d : Vector Int r) (k : Nat)
    (hk : k ≤ r) :
    (d.take k).foldl (· * ·) 1 =
      Fin.foldl k (fun acc i => acc * d[(⟨i.val, by omega⟩ : Fin r)]) 1 := by
  rw [Fin.foldl_eq_finRange_foldl]
  rw [← List.foldl_map]
  rw [← Vector.foldl_toList]
  apply congrArg (fun xs : List Int => xs.foldl (· * ·) 1)
  apply List.ext_getElem
  · simp [Nat.min_eq_left hk]
  · intro i hi h'i
    simp at hi h'i
    rw [List.getElem_map, List.getElem_finRange]
    change (d.take k)[i] = d[i]
    exact Vector.getElem_take hi

private theorem foldl_mul_dvd {R : Type} (xs : List R) (f g : R → Int)
    (a b : Int) (hab : a ∣ b) (hfg : ∀ x ∈ xs, f x ∣ g x) :
    xs.foldl (fun acc x => acc * f x) a ∣
      xs.foldl (fun acc x => acc * g x) b := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons x xs ih =>
      apply ih (a * f x) (b * g x)
      · exact Int.mul_dvd_mul hab (hfg x (by simp))
      · intro y hy
        exact hfg y (List.mem_cons_of_mem x hy)

private theorem finFoldl_mul_dvd (f g : Fin k → Int)
    (hfg : ∀ i, f i ∣ g i) :
    Fin.foldl k (fun acc i => acc * f i) 1 ∣
      Fin.foldl k (fun acc i => acc * g i) 1 := by
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  apply foldl_mul_dvd (List.finRange k) f g 1 1 (Int.dvd_refl 1)
  intro i _hi
  exact hfg i

private theorem IsSNF.prefix_dvd_detProduct {A : Matrix Int n m}
    {S : SmithData n m} (h : IsSNF A S) (k : Nat) (hk : k ≤ S.rank)
    (rows : Vector (Fin n) k) (cols : Vector (Fin m) k)
    (hrows : rows ∈ selectedColumnTuples k n)
    (perm : Vector (Fin k) k) :
    (S.diag.take k).foldl (· * ·) 1 ∣
      detProduct (selectedSubmatrix (diagMatrix S.diag n m) rows cols) perm := by
  rw [foldl_take_eq_finFoldl S.diag k hk]
  unfold detProduct
  apply finFoldl_mul_dvd
  intro i
  simp only [getElem_pair_eq_nested]
  rw [getElem_selectedSubmatrix, getElem_diagMatrix]
  split
  next hentry =>
    exact h.diag_dvd_of_le (by omega) hentry.2
      (index_le_of_strictlyIncreasing rows
        ((mem_selectedColumnTuples_iff rows).mp hrows) i)
  next _ => exact Int.dvd_zero _

private theorem IsSNF.prefix_dvd_minor {A : Matrix Int n m}
    {S : SmithData n m} (h : IsSNF A S) (k : Nat) (hk : k ≤ S.rank)
    (rows : Vector (Fin n) k) (cols : Vector (Fin m) k)
    (hrows : rows ∈ selectedColumnTuples k n) :
    ((S.diag.take k).foldl (· * ·) 1).natAbs ∣
      (det (selectedSubmatrix (diagMatrix S.diag n m) rows cols)).natAbs := by
  apply Int.natAbs_dvd_natAbs.mpr
  unfold det
  apply int_dvd_foldl_add
  intro perm _hperm
  apply Int.dvd_mul_of_dvd_right
  exact h.prefix_dvd_detProduct k hk rows cols hrows perm

private theorem leadingMinor_diag_eq_foldl (d : Vector Int r) (k n m : Nat)
    (hkr : k ≤ r) (hkn : k ≤ n) (hkm : k ≤ m) :
    det (selectedSubmatrix (diagMatrix d n m)
      (firstColumns k n hkn) (firstColumns k m hkm)) =
      (d.take k).foldl (· * ·) 1 := by
  rw [det_upperTriangular_eq_foldl_diag]
  · rw [foldl_take_eq_finFoldl d k hkr, Fin.foldl_eq_finRange_foldl]
    apply List.foldl_congr
    intro acc i _hi
    simp only [getElem_selectedSubmatrix, getElem_firstColumns]
    rw [getElem_diagMatrix]
    split <;> simp_all; omega
  · intro i j hji
    simp only [getElem_selectedSubmatrix, getElem_firstColumns]
    apply diagMatrix_apply_of_ne
    simp only []
    omega

/-- On the represented part of a Smith diagonal, the determinantal divisor
is the absolute product of the corresponding leading invariant factors. -/
theorem IsSNF.detDivisor_diag_eq {A : Matrix Int n m} {S : SmithData n m}
    (h : IsSNF A S) (k : Nat) (hk : k ≤ S.rank) :
    detDivisor (diagMatrix S.diag n m) k =
      ((S.diag.take k).foldl (· * ·) 1).natAbs := by
  apply Nat.dvd_antisymm
  · have hdvd := detDivisor_dvd_minor (diagMatrix S.diag n m) k
      (firstColumns k n (Nat.le_trans hk h.rank_le_n))
      (firstColumns k m (Nat.le_trans hk h.rank_le_m))
      (firstColumns_mem_selectedColumnTuples k n (Nat.le_trans hk h.rank_le_n))
      (firstColumns_mem_selectedColumnTuples k m (Nat.le_trans hk h.rank_le_m))
    rw [leadingMinor_diag_eq_foldl S.diag k n m hk
      (Nat.le_trans hk h.rank_le_n) (Nat.le_trans hk h.rank_le_m)] at hdvd
    exact hdvd
  · apply dvd_detDivisor
    intro rows hrows cols _hcols
    exact h.prefix_dvd_minor k hk rows cols hrows

/-- Minors larger than a represented diagonal vector all vanish. -/
theorem detDivisor_diag_eq_zero (d : Vector Int r) (n m k : Nat) (hk : r < k) :
    detDivisor (diagMatrix d n m) k = 0 := by
  unfold detDivisor
  apply foldl_gcd_eq_zero
  intro selection hselection
  rw [minorSelections, List.mem_flatMap] at hselection
  rcases hselection with ⟨rows, hrows, hcols⟩
  rw [List.mem_map] at hcols
  rcases hcols with ⟨cols, _hcols, rfl⟩
  unfold minorValue
  have hzero : det (selectedSubmatrix (diagMatrix d n m) rows cols) = 0 :=
      det_eq_zero_of_row_zero _ (⟨r, hk⟩ : Fin k) (by
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_zero]
    have hge := index_le_of_strictlyIncreasing rows
      ((mem_selectedColumnTuples_iff rows).mp hrows)
      (⟨r, hk⟩ : Fin k)
    exact (getElem_selectedSubmatrix (diagMatrix d n m) rows cols
      (⟨r, hk⟩ : Fin k) (⟨j, hj⟩ : Fin k)).trans
        (diagMatrix_apply_of_ge d rows[(⟨r, hk⟩ : Fin k)]
          cols[(⟨j, hj⟩ : Fin k)] hge))
  simp [hzero]

/-- Left multiplication can only enlarge the ideal generated by the
`k × k` minors. -/
theorem detDivisor_dvd_mul_left (P : Matrix Int q n) (A : Matrix Int n m)
    (k : Nat) : detDivisor A k ∣ detDivisor (P * A) k := by
  apply dvd_detDivisor
  intro rows hrows cols hcols
  apply dvd_natAbs
  rw [det_minor_mul]
  apply int_dvd_foldl_add
  intro middle hmiddle
  apply Int.dvd_mul_of_dvd_left
  exact ofNat_dvd
    (detDivisor_dvd_minor A k middle cols hmiddle hcols)

/-- Right multiplication can only enlarge the ideal generated by the
`k × k` minors. -/
theorem detDivisor_dvd_mul_right (A : Matrix Int n m) (Q : Matrix Int m q)
    (k : Nat) : detDivisor A k ∣ detDivisor (A * Q) k := by
  apply dvd_detDivisor
  intro rows hrows cols hcols
  apply dvd_natAbs
  rw [det_minor_mul]
  apply int_dvd_foldl_add
  intro middle hmiddle
  apply Int.dvd_mul_of_dvd_right
  exact ofNat_dvd
    (detDivisor_dvd_minor A k rows middle hrows hmiddle)

/-- Multiplication on the left by a matrix with a recorded right inverse
preserves every determinantal divisor. -/
theorem detDivisor_mul_left_eq (P Pinv : Matrix Int n n)
    (hP : P * Pinv = Matrix.identity n) (A : Matrix Int n m) (k : Nat) :
    detDivisor (P * A) k = detDivisor A k := by
  apply Nat.dvd_antisymm
  · have h := detDivisor_dvd_mul_left Pinv (P * A) k
    have hrev := mul_eq_one_comm hP
    rw [← Matrix.mul_assoc, hrev, Matrix.identity_mul] at h
    exact h
  · exact detDivisor_dvd_mul_left P A k

/-- Multiplication on the right by a matrix with a recorded right inverse
preserves every determinantal divisor. -/
theorem detDivisor_mul_right_eq (A : Matrix Int n m) (Q Qinv : Matrix Int m m)
    (hQ : Q * Qinv = Matrix.identity m) (k : Nat) :
    detDivisor (A * Q) k = detDivisor A k := by
  apply Nat.dvd_antisymm
  · have h := detDivisor_dvd_mul_right (A * Q) Qinv k
    rw [Matrix.mul_assoc, hQ, Matrix.mul_identity] at h
    exact h
  · exact detDivisor_dvd_mul_right A Q k

/-- Determinantal divisors characterize every Smith form: within the rank
they are prefix products of the invariant factors, and above the rank they
vanish. -/
theorem IsSNF.detDivisor_eq {A : Matrix Int n m} {S : SmithData n m}
    (h : IsSNF A S) (k : Nat) :
    detDivisor A k =
      if k ≤ S.rank then ((S.diag.take k).foldl (· * ·) 1).natAbs else 0 := by
  have hleft := detDivisor_mul_left_eq S.left S.leftInv h.left_inv A k
  have hright := detDivisor_mul_right_eq (S.left * A) S.right S.rightInv
    h.right_inv k
  have hform : detDivisor (diagMatrix S.diag n m) k = detDivisor A k := by
    rw [← h.mul_eq]
    exact Eq.trans hright hleft
  rw [← hform]
  split
  next hk => exact h.detDivisor_diag_eq k hk
  next hk => exact detDivisor_diag_eq_zero S.diag n m k (Nat.lt_of_not_ge hk)

/-- The zeroth determinantal divisor is the empty-minor determinant, one. -/
@[simp]
theorem detDivisor_zero (A : Matrix Int n m) : detDivisor A 0 = 1 := by
  simp [detDivisor, minorValue, minorSelections, selectedColumnTuples,
    selectedColumnTuplesUpTo]
  have hz : selectedSubmatrix A #v[] #v[] =
      (Matrix.identity (R := Int) 0) := by
    apply Matrix.ext_getElem
    intro i
    exact i.elim0
  rw [hz, det_identity]
  rfl

end Hex.Matrix
