/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareiss.Kernel
public import HexMatrixMathlib.Literal
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

/-!
Soundness of the kernel determinant certificate: a passing `checkDetList` on
the rows of a Mathlib matrix determines `Matrix.det`, and a passing
`checkDetRat` determines it for a rational matrix through its row-scaled
integer form.

The row list is identified with the Mathlib matrix through `ofLists` of the
shared literal layer (`HexMatrixMathlib.Literal`), so the kernel never
evaluates an entry through `Matrix.of`/`vecCons` inside the arithmetic.

The proof follows the certificate: the swaps are transpositions, each
negating the determinant (`det_permute`, `sign_swap`); the transform `L` is
lower triangular with nonzero diagonal and the product `L · σA` is upper
triangular, so their determinants are the products of their diagonals
(`det_of_isLowerTriangular`, `det_of_isUpperTriangular`); `det_mul` and the
value identity give `(∏ lᵢ) · d = (∏ lᵢ) · det A`, and `∏ lᵢ ≠ 0` cancels.
A left kernel vector gives `det A = 0` by `exists_vecMul_eq_zero_iff`.
-/

open Matrix

namespace HexMatrixMathlib

open Hex.Matrix Hex.Matrix.DetWitness

/-! # The checker's primitives -/

private theorem intMul_eq (a b : Int) : Int.mul a b = a * b := rfl
private theorem intAdd_eq (a b : Int) : Int.add a b = a + b := rfl
private theorem intNeg_eq (a : Int) : Int.neg a = -a := rfl

theorem nthRow_eq_getD (A : List (List Int)) (i : Nat) : nthRow A i = A.getD i [] := by
  induction A generalizing i with
  | nil => simp [nthRow]
  | cons a as ih =>
    cases i with
    | zero => simp [nthRow]
    | succ i => simp only [nthRow, List.getD_cons_succ, ih]

theorem nthInt_eq_getD (a : List Int) (j : Nat) : nthInt a j = a.getD j 0 := by
  induction a generalizing j with
  | nil => simp [nthInt]
  | cons x xs ih =>
    cases j with
    | zero => simp [nthInt]
    | succ j => simp only [nthInt, List.getD_cons_succ, ih]

theorem replaceRow_length (A : List (List Int)) (i : Nat) (r : List Int) :
    (replaceRow A i r).length = A.length := by
  induction A generalizing i with
  | nil => simp [replaceRow]
  | cons a as ih =>
    cases i with
    | zero => simp [replaceRow]
    | succ i => simp [replaceRow, ih]

theorem replaceRow_getD (A : List (List Int)) (i : Nat) (r : List Int) (k : Nat) (hi : i < A.length) :
    (replaceRow A i r).getD k [] = if k = i then r else A.getD k [] := by
  induction A generalizing i k with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => cases k <;> simp [replaceRow]
    | succ i =>
      cases k with
      | zero => simp [replaceRow]
      | succ k =>
        simp only [replaceRow, List.getD_cons_succ]
        rw [ih i k (by simpa using hi)]
        simp

theorem swapRows_length (a b : Nat) (A : List (List Int)) :
    (swapRows a b A).length = A.length := by
  simp [swapRows, replaceRow_length]

theorem swapRows_getD (a b : Nat) (A : List (List Int)) (ha : a < A.length) (hb : b < A.length)
    (k : Nat) : (swapRows a b A).getD k [] =
      A.getD (if k = a then b else if k = b then a else k) [] := by
  unfold swapRows
  rw [replaceRow_getD _ _ _ _ (by rw [replaceRow_length]; exact hb), replaceRow_getD _ _ _ _ ha,
    nthRow_eq_getD, nthRow_eq_getD]
  by_cases hka : k = a
  · subst hka
    by_cases hkb : k = b
    · subst hkb; simp
    · simp [hkb]
  · by_cases hkb : k = b
    · subst hkb; simp [hka]
    · simp [hka, hkb]

theorem applySwaps_length (s : List (Nat × Nat)) (A : List (List Int)) :
    (applySwaps s A).length = A.length := by
  induction s generalizing A with
  | nil => rfl
  | cons p s ih => obtain ⟨a, b⟩ := p; simp [applySwaps, ih, swapRows_length]

theorem swapsOk_cons (n a b : Nat) (s : List (Nat × Nat)) (h : swapsOk n ((a, b) :: s) = true) :
    a < n ∧ b < n ∧ a ≠ b ∧ swapsOk n s = true := by
  simp only [swapsOk, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨ha, hb⟩, hab⟩, hs⟩ := h
  exact ⟨ha, hb, Nat.ne_of_beq_eq_false hab, hs⟩

theorem signOf_eq (s : List (Nat × Nat)) : signOf s = (-1) ^ s.length := by
  induction s with
  | nil => rfl
  | cons _ s ih => simp [signOf, intNeg_eq, ih, pow_succ]

theorem rowsLen_iff (m : Nat) (L : List (List Int)) :
    rowsLen m L = true ↔ ∀ r ∈ L, r.length = m := by
  induction L with
  | nil => simp [rowsLen]
  | cons r L ih => simp [rowsLen, ih]

theorem dotInt_eq_sum (a b : List Int) (r : Nat) (h : a.length ≤ r) :
    dotInt a b = ∑ k : Fin r, a.getD k 0 * b.getD k 0 := by
  induction a generalizing b r with
  | nil => simp [dotInt]
  | cons x xs ih =>
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by simp at h; omega⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
    cases b with
    | nil => simp [dotInt]
    | cons y ys =>
      simp only [dotInt, intAdd_eq, intMul_eq, List.getD_cons_zero, List.getD_cons_succ]
      rw [ih ys r (by simpa using h)]

theorem column_length (j : Nat) (A : List (List Int)) : (column j A).length = A.length := by
  induction A with
  | nil => rfl
  | cons r rs ih => simp [column, ih]

theorem column_getD (j : Nat) (A : List (List Int)) (k : Nat) :
    (column j A).getD k 0 = (A.getD k []).getD j 0 := by
  induction A generalizing k with
  | nil => simp [column]
  | cons r rs ih =>
    cases k with
    | zero => simp [column, nthInt_eq_getD]
    | succ k => simp only [column, List.getD_cons_succ, ih]

theorem columnsFrom_length (A : List (List Int)) (j k : Nat) : (columnsFrom A j k).length = k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [columnsFrom, ih]

theorem columnsFrom_getD (A : List (List Int)) (j k l : Nat) (hl : l < k) :
    (columnsFrom A j k).getD l [] = column (j + l) A := by
  induction k generalizing j l with
  | zero => omega
  | succ k ih =>
    cases l with
    | zero => simp [columnsFrom]
    | succ l =>
      simp only [columnsFrom, List.getD_cons_succ]
      rw [ih (j + 1) l (by omega)]
      congr 1
      omega

theorem columns_length (m : Nat) (A : List (List Int)) : (columns m A).length = m :=
  columnsFrom_length A 0 m

theorem columns_getD (m : Nat) (A : List (List Int)) (l : Nat) (hl : l < m) :
    (columns m A).getD l [] = column l A := by
  simpa [columns] using columnsFrom_getD A 0 m l hl

theorem zeroDots_iff (t : List Int) (cs : List (List Int)) :
    zeroDots t cs = true ↔ ∀ c ∈ cs, dotInt t c = 0 := by
  induction cs with
  | nil => simp [zeroDots]
  | cons c cs ih => simp [zeroDots, ih]

theorem anyNonzero_iff (v : List Int) : anyNonzero v = true ↔ ∃ a ∈ v, a ≠ 0 := by
  induction v with
  | nil => simp [anyNonzero]
  | cons a as ih => simp [anyNonzero, ih]

theorem triangularCheck_spec (d : Int) :
    ∀ (done : List (List Int)) (i : Nat) (ts cs : List (List Int)) (pl pu : Int),
      triangularCheck d done i ts cs pl pu = true →
      ts.length = cs.length ∧
      (∀ k, k < ts.length →
        (ts.getD k []).length = i + k + 1 ∧ nthInt (ts.getD k []) (i + k) ≠ 0 ∧
        (∀ c ∈ done, dotInt (ts.getD k []) c = 0) ∧
        ∀ k', k' < k → dotInt (ts.getD k []) (cs.getD k' []) = 0) ∧
      pl * (List.ofFn fun k : Fin ts.length => nthInt (ts.getD k []) (i + k)).prod * d =
        pu * (List.ofFn fun k : Fin ts.length => dotInt (ts.getD k []) (cs.getD k [])).prod := by
  intro done i ts
  induction ts generalizing done i with
  | nil =>
    intro cs pl pu h
    cases cs with
    | nil =>
      simp only [triangularCheck, intMul_eq, decide_eq_true_eq] at h
      simpa using h
    | cons c cs => simp [triangularCheck] at h
  | cons t ts ih =>
    intro cs pl pu h
    cases cs with
    | nil => simp [triangularCheck] at h
    | cons c cs =>
      simp only [triangularCheck, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true',
        decide_eq_false_iff_not] at h
      obtain ⟨⟨⟨hlen, hl⟩, hz⟩, hrest⟩ := h
      obtain ⟨hcslen, hrows, hprod⟩ := ih (c :: done) (i + 1) cs _ _ hrest
      refine ⟨by simpa using hcslen, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero =>
          exact ⟨by simpa using hlen, by simpa using hl,
            fun c' hc' => (zeroDots_iff _ _).mp hz c' hc', fun k' hk' => absurd hk' (Nat.not_lt_zero _)⟩
        | succ k =>
          obtain ⟨h1, h2, h3, h4⟩ := hrows k (by simpa using hk)
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [show i + 1 + k + 1 = i + (k + 1) + 1 by omega] using h1
          · simpa [show i + 1 + k = i + (k + 1) by omega] using h2
          · intro c' hc'
            exact h3 c' (List.mem_cons_of_mem _ hc')
          · intro k' hk'
            cases k' with
            | zero => simpa using h3 c (List.mem_cons_self ..)
            | succ k' => simpa using h4 k' (by omega)
      · rw [List.length_cons, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
        simp only [Fin.val_zero, List.getD_cons_zero, Nat.add_zero, Fin.val_succ,
          List.getD_cons_succ]
        have e : (fun k : Fin ts.length => nthInt (ts.getD k []) (i + (k + 1))) =
            fun k : Fin ts.length => nthInt (ts.getD k []) (i + 1 + k) := by
          funext k
          congr 1
          omega
        rw [e]
        rw [intMul_eq, intMul_eq] at hprod
        linear_combination hprod

/-! # Row swaps -/

theorem ofLists_swapRows (n : Nat) (L : List (List Int)) (hL : L.length = n) (a b : Fin n) :
    ofLists n n (swapRows a b L) = (ofLists n n L).submatrix (Equiv.swap a b) id := by
  ext i j
  rw [Matrix.submatrix_apply, id, ofLists_apply, ofLists_apply,
    swapRows_getD _ _ _ (by omega) (by omega), Equiv.swap_apply_def]
  by_cases hia : (i : Nat) = a
  · have : i = a := Fin.ext hia
    subst this
    simp
  · have hia' : i ≠ a := fun h => hia (congrArg Fin.val h)
    by_cases hib : (i : Nat) = b
    · have : i = b := Fin.ext hib
      subst this
      simp [hia, hia']
    · have hib' : i ≠ b := fun h => hib (congrArg Fin.val h)
      simp [hia, hib, hia', hib']

theorem det_ofLists_applySwaps (n : Nat) (s : List (Nat × Nat)) (L : List (List Int))
    (hL : L.length = n) (hs : swapsOk n s = true) :
    (ofLists n n (applySwaps s L)).det = signOf s * (ofLists n n L).det := by
  induction s generalizing L with
  | nil => simp [applySwaps, signOf]
  | cons p s ih =>
    obtain ⟨a, b⟩ := p
    obtain ⟨ha, hb, hab, hs'⟩ := swapsOk_cons n a b s hs
    rw [applySwaps, ih _ (by rw [swapRows_length]; exact hL) hs',
      ofLists_swapRows n L hL ⟨a, ha⟩ ⟨b, hb⟩, Matrix.det_permute,
      Equiv.Perm.sign_swap (by simpa [Fin.ext_iff] using hab), signOf]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, intNeg_eq]
    ring

/-! # Soundness -/

/-- A passing kernel check determines the determinant of the row list's matrix. -/
theorem det_eq_of_checkList (n : Nat) (L : List (List Int)) (c : DetWitness)
    (h : checkDetList n L c = true) : (ofLists n n L).det = c.value := by
  cases c with
  | triangular swaps T d =>
    simp only [checkDetList, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨hLlen, _⟩, hswaps⟩, htri⟩ := h
    show _ = d
    set P := applySwaps swaps L with hP
    have hdetP : (ofLists n n P).det = signOf swaps * (ofLists n n L).det :=
      det_ofLists_applySwaps n swaps L hLlen hswaps
    obtain ⟨hTlen, hrows, hprod⟩ :=
      triangularCheck_spec d [] 0 T (columns n P) 1 (signOf swaps) htri
    rw [columns_length] at hTlen
    subst hTlen
    let Lm : Matrix (Fin T.length) (Fin T.length) ℤ := Matrix.of fun i k => (T.getD i []).getD k 0
    let Pm := ofLists T.length T.length P
    have hU : ∀ i j : Fin T.length, (Lm * Pm) i j = dotInt (T.getD i []) (column j P) := by
      intro i j
      rw [Matrix.mul_apply, dotInt_eq_sum _ _ T.length (by rw [(hrows i i.isLt).1]; omega)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Lm, Pm, Matrix.of_apply, ofLists_apply, column_getD]
    have hlower : Lm.IsLowerTriangular := by
      intro i j hij
      have hij : (i : Nat) < j := by simpa using hij
      simp only [Lm, Matrix.of_apply]
      apply getD_eq_default'
      rw [(hrows i i.isLt).1]
      omega
    have hupper : (Lm * Pm).IsUpperTriangular := by
      intro i j hij
      have hij : (j : Nat) < i := by simpa using hij
      rw [hU]
      have := (hrows i i.isLt).2.2.2 j hij
      rwa [columns_getD _ P j j.isLt] at this
    have hdetL : Lm.det = ∏ i, Lm i i := Matrix.det_of_isLowerTriangular Lm hlower
    have hdetU : (Lm * Pm).det = ∏ i, (Lm * Pm) i i := Matrix.det_of_isUpperTriangular hupper
    have hl0 : (∏ i, Lm i i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => by
      have := (hrows i i.isLt).2.1
      rwa [nthInt_eq_getD, Nat.zero_add] at this
    have hsign : signOf swaps * signOf swaps = 1 := by
      rw [signOf_eq, ← mul_pow]
      norm_num
    have hprodL : (List.ofFn fun k : Fin T.length => nthInt (T.getD k []) (0 + k)).prod =
        ∏ i, Lm i i := by
      rw [List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => by simp [Lm, nthInt_eq_getD]
    have hprodU : (List.ofFn fun k : Fin T.length =>
        dotInt (T.getD k []) ((columns T.length P).getD k [])).prod = ∏ i, (Lm * Pm) i i := by
      rw [List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => by rw [hU, columns_getD _ P i i.isLt]
    rw [hprodL, hprodU, one_mul] at hprod
    have key : (∏ i, Lm i i) * d = (∏ i, Lm i i) * (ofLists T.length T.length L).det := by
      rw [hprod, ← hdetU, Matrix.det_mul, hdetL, hdetP]
      linear_combination (∏ i, Lm i i) * (ofLists T.length T.length L).det * hsign
    exact (mul_left_cancel₀ hl0 key).symm
  | singular v =>
    simp only [checkDetList, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨hLlen, _⟩, hvlen⟩, hnz⟩, hz⟩ := h
    show _ = 0
    let w : Fin n → ℤ := fun i => v.getD i 0
    have hw : w ≠ 0 := by
      obtain ⟨a, ha, ha0⟩ := (anyNonzero_iff v).mp hnz
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
      intro h0
      have := congrFun h0 ⟨k, by omega⟩
      simp only [w, Pi.zero_apply] at this
      rw [getD_eq_getElem' _ _ _ hk] at this
      exact ha0 this
    have hmul : w ᵥ* ofLists n n L = 0 := by
      funext j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
      have hmem : column j L ∈ columns n L := by
        rw [← columns_getD n L j j.isLt, getD_eq_getElem' _ _ _ (by rw [columns_length]; exact j.isLt)]
        exact List.getElem_mem _
      have := (zeroDots_iff v _).mp hz (column j L) hmem
      rw [dotInt_eq_sum v (column j L) n (by omega)] at this
      simp only [column_getD] at this
      simpa [ofLists_apply, w] using this
    exact Matrix.exists_vecMul_eq_zero_iff.mp ⟨w, hw, hmul⟩

/-- `det_eq_of_checkList` for a matrix identified with its row list; the
tactic supplies `hA` by `rfl` for a vector chain. -/
theorem det_eq_of_checkList' {n : Nat} (A : Matrix (Fin n) (Fin n) ℤ) (L : List (List Int))
    (c : DetWitness) (hA : A = ofLists n n L) (h : checkDetList n L c = true) :
    A.det = c.value :=
  hA ▸ det_eq_of_checkList n L c h

/-! # Rational rows -/

private theorem natMul_eq (a b : Nat) : Nat.mul a b = a * b := rfl

theorem scaledRow_spec (k : Nat) (q : List Rat) (b : List Int) (h : scaledRow k q b = true) :
    ∀ j, (k : ℚ) * q.getD j 0 = (b.getD j 0 : ℚ) := by
  induction q generalizing b with
  | nil =>
    cases b with
    | nil => simp
    | cons _ _ => simp [scaledRow] at h
  | cons x xs ih =>
    cases b with
    | nil => simp [scaledRow] at h
    | cons y ys =>
      simp only [scaledRow, Bool.and_eq_true, decide_eq_true_eq] at h
      have h1 : (k : ℚ) * x = (y : ℚ) := h.1
      intro j
      cases j with
      | zero => simpa using h1
      | succ j => simpa using ih ys h.2 j

theorem scaledRows_spec (s : List Nat) (A : List (List Rat)) (B : List (List Int))
    (h : scaledRows s A B = true) :
    ∀ i, 0 < s.getD i 1 ∧ ∀ j, (s.getD i 1 : ℚ) * (A.getD i []).getD j 0 = ((B.getD i []).getD j 0 : ℚ) := by
  induction s generalizing A B with
  | nil =>
    cases A with
    | nil =>
      cases B with
      | nil => simp
      | cons _ _ => simp [scaledRows] at h
    | cons _ _ => simp [scaledRows] at h
  | cons k ks ih =>
    cases A with
    | nil => simp [scaledRows] at h
    | cons q qs =>
      cases B with
      | nil => simp [scaledRows] at h
      | cons b bs =>
        simp only [scaledRows, Bool.and_eq_true, Nat.blt_eq] at h
        obtain ⟨⟨hk, hrow⟩, hrest⟩ := h
        intro i
        cases i with
        | zero => exact ⟨by simpa using hk, fun j => by simpa using scaledRow_spec k q b hrow j⟩
        | succ i => simpa using ih qs bs hrest i

theorem prodNat_cast (s : List Nat) (r : Nat) (hs : s.length = r) :
    (prodNat s : ℚ) = ∏ i : Fin r, (s.getD i 1 : ℚ) := by
  subst hs
  induction s with
  | nil => simp [prodNat]
  | cons k ks ih =>
    rw [List.length_cons, Fin.prod_univ_succ]
    simp only [prodNat, natMul_eq, Nat.cast_mul, Fin.val_zero, List.getD_cons_zero, Fin.val_succ,
      List.getD_cons_succ, ih]

/-- A passing rational check determines the determinant of the rational row
list's matrix. -/
theorem det_eq_of_checkRat (n : Nat) (A : List (List Rat)) (s : List Nat) (B : List (List Int))
    (c : DetWitness) (v : Rat) (h : checkDetRat n A s B c v = true) : (ofLists n n A).det = v := by
  simp only [checkDetRat, Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨_, hslen⟩, hsc⟩, hB⟩, hv⟩ := h
  have hv : v * (prodNat s : ℚ) = (c.value : ℚ) := hv
  have hrows := scaledRows_spec s A B hsc
  have hdetB := det_eq_of_checkList n B c hB
  let D : Matrix (Fin n) (Fin n) ℚ := Matrix.diagonal fun i : Fin n => (s.getD i 1 : ℚ)
  have hDA : D * ofLists n n A = (ofLists n n B).map (Int.cast : ℤ → ℚ) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.map_apply, ofLists_apply, ofLists_apply]
    exact (hrows i).2 j
  have h1 : (∏ i : Fin n, (s.getD i 1 : ℚ)) * (ofLists n n A).det = (c.value : ℚ) := by
    have := congrArg Matrix.det hDA
    simp only [Matrix.det_mul, Matrix.det_diagonal, D] at this
    rwa [← Int.cast_det, hdetB] at this
  have hs0 : (∏ i : Fin n, (s.getD i 1 : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (hrows i).1.ne'
  rw [prodNat_cast s n hslen] at hv
  apply mul_left_cancel₀ hs0
  rw [h1, ← hv, mul_comm]

/-- `det_eq_of_checkRat` for a matrix identified with its row list. -/
theorem det_eq_of_checkRat' {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (L : List (List Rat))
    (s : List Nat) (B : List (List Int)) (c : DetWitness) (v : Rat) (hA : A = ofLists n n L)
    (h : checkDetRat n L s B c v = true) : A.det = v :=
  hA ▸ det_eq_of_checkRat n L s B c v h

end HexMatrixMathlib
