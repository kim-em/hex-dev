/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Polynomial
public import HexRankMathlib.Modular
public import HexRankMathlib.Kernel
public import HexMatrixMathlib.Literal
public import Mathlib.Data.List.GetD

public section

namespace HexMatrixMathlib.PolyWitness

open Hex.Matrix.PolyWitness

variable {R : Type*} [CommRing R]

private theorem intAdd (a b : Int) : Int.add a b = a + b := rfl
private theorem intMul (a b : Int) : Int.mul a b = a * b := rfl
private theorem intSub (a b : Int) : Int.sub a b = a - b := rfl

/-- Evaluate ascending integer coefficients at a ring element. -/
@[expose] def eval (x : R) : List Int → R
  | [] => 0
  | a :: as => (a : R) + x * eval x as

@[simp] theorem eval_nil (x : R) : eval x [] = 0 := rfl

@[simp] theorem eval_cons (x : R) (a : Int) (as : List Int) :
    eval x (a :: as) = (a : R) + x * eval x as := rfl

theorem eval_add (x : R) (a b : List Int) :
    eval x (add a b) = eval x a + eval x b := by
  induction a generalizing b with
  | nil => simp [add]
  | cons a as ih =>
    cases b with
    | nil => simp [add]
    | cons b bs => simp only [add, eval_cons, ih, intAdd]; push_cast; ring

theorem eval_scale (x : R) (a : Int) (b : List Int) :
    eval x (scale a b) = (a : R) * eval x b := by
  induction b with
  | nil => simp [scale]
  | cons b bs ih => simp only [scale, eval_cons, ih, intMul]; push_cast; ring

theorem eval_mul (x : R) (a b : List Int) :
    eval x (mul a b) = eval x a * eval x b := by
  induction a with
  | nil => simp [mul]
  | cons a as ih =>
    simp only [mul, eval_add, eval_scale, eval_cons, Int.cast_zero, zero_add, ih]
    ring

theorem map_eval {S : Type*} [CommRing S] (φ : R →+* S) (x : R) (a : List Int) :
    φ (eval x a) = eval (φ x) a := by
  induction a with
  | nil => simp
  | cons a as ih => simp [ih]

private theorem cast_zero (M : Nat) (hM : (M : R) = 0) (a : Int)
    (ha : Int.emod a (Int.ofNat M) = 0) : (a : R) = 0 := by
  have ha' : a % (M : Int) = 0 := ha
  have h := congrArg (Int.cast : Int → R) (Int.emod_add_mul_ediv a (Int.ofNat M))
  simpa [ha', hM] using h.symm

theorem zeroMod_sound (x : R) (M : Nat) (hM : (M : R) = 0) (a : List Int)
    (h : zeroMod M a = true) : eval x a = 0 := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [zeroMod, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [cast_zero M hM a h.1, ih h.2]

/-- A coefficient check modulo the characteristic implies equality in the ring. -/
theorem eqMod_sound (x : R) (M : Nat) (hM : (M : R) = 0) (a b : List Int)
    (h : eqMod M a b = true) : eval x a = eval x b := by
  induction a generalizing b with
  | nil => exact (zeroMod_sound x M hM b h).symm
  | cons a as ih =>
    cases b with
    | nil =>
      simp only [eqMod, Bool.and_eq_true, decide_eq_true_eq] at h
      simp [cast_zero M hM a h.1, ih [] h.2]
    | cons b bs =>
      simp only [eqMod, Bool.and_eq_true, decide_eq_true_eq] at h
      have hab : (a : R) = (b : R) := by
        have := cast_zero M hM (Int.sub a b) h.1
        exact sub_eq_zero.mp (by simpa only [intSub, Int.cast_sub] using this)
      simp [hab, ih bs h.2]

theorem nth_eq_getD {α : Type} (zero : α) (a : List α) (i : Nat) :
    nth zero a i = a.getD i zero := by
  induction a generalizing i with
  | nil => simp [nth]
  | cons a as ih => cases i <;> simp [nth, ih]

theorem eval_dot (x : R) (a b : List (List Int)) :
    eval x (dot a b) = ∑ i : Fin a.length, eval x a[i] * eval x (b.getD i []) := by
  induction a generalizing b with
  | nil => simp [dot]
  | cons a as ih =>
    cases b with
    | nil => simp [dot]
    | cons b bs => simp [dot, eval_add, eval_mul, Fin.sum_univ_succ, ih]

theorem eval_dot_sum (x : R) (a b : List (List Int)) (r : Nat) (ha : a.length = r) :
    eval x (dot a b) = ∑ i : Fin r, eval x (a.getD i []) * eval x (b.getD i []) := by
  subst ha
  rw [eval_dot]
  exact Finset.sum_congr rfl fun i _ => by rw [getD_eq_getElem' _ _ _ i.isLt]; rfl

theorem checkDot_sound (x : R) (M : Nat) (hM : (M : R) = 0)
    (f v : List Int) (hf : eval x f = 0) (a b : List (List Int)) (q : List Int)
    (h : checkDot M f v a b q = true) : eval x (dot a b) = eval x v := by
  have := eqMod_sound x M hM _ _ h
  simpa [eval_add, eval_mul, hf] using this

theorem zeroDots_sound (x : R) (M : Nat) (hM : (M : R) = 0)
    (f : List Int) (hf : eval x f = 0) (a : List (List Int))
    (bs : List (List (List Int))) (qs : List (List Int))
    (h : zeroDots M f a bs qs = true) :
    ∀ j, eval x (dot a (bs.getD j [])) = 0 := by
  induction bs generalizing qs with
  | nil => intro j; simp [dot]
  | cons b bs ih =>
    cases qs with
    | nil => simp [zeroDots] at h
    | cons q qs =>
      simp only [zeroDots, Bool.and_eq_true] at h
      intro j
      cases j with
      | zero => simpa using checkDot_sound x M hM f [] hf a b q h.1
      | succ j => simpa using ih qs h.2 j

theorem lowerCheck_sound (x : R) (M : Nat) (hM : (M : R) = 0)
    (f : List Int) (hf : eval x f = 0)
    (as bs qs : List (List (List Int))) (h : lowerCheck M f as bs qs = true) :
    as.length = bs.length ∧ ∀ (i : Nat) (hi : i < as.length),
      eval x (dot as[i] (bs.getD i [])) = 1 ∧
        ∀ j, i < j → eval x (dot as[i] (bs.getD j [])) = 0 := by
  induction as generalizing bs qs with
  | nil =>
    cases bs <;> cases qs <;> simp_all [lowerCheck]
  | cons a as ih =>
    cases bs with
    | nil => simp [lowerCheck] at h
    | cons b bs =>
      cases qs with
      | nil => simp [lowerCheck] at h
      | cons q qs =>
        cases q with
        | nil => simp [lowerCheck] at h
        | cons q qr =>
          simp only [lowerCheck, Bool.and_eq_true] at h
          obtain ⟨⟨hd, hz⟩, ht⟩ := h
          obtain ⟨hlen, hrest⟩ := ih bs qs ht
          refine ⟨by simpa using hlen, fun i hi => ?_⟩
          cases i with
          | zero =>
            refine ⟨by simpa using checkDot_sound x M hM f [1] hf a b q hd, fun j hj => ?_⟩
            obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            simpa using zeroDots_sound x M hM f hf a bs qr hz j
          | succ i =>
            obtain ⟨h1, h2⟩ := hrest i (by simpa using hi)
            refine ⟨by simpa using h1, fun j hj => ?_⟩
            obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            simpa using h2 j (by omega)

theorem eval_dot_comm (x : R) (a b : List (List Int)) :
    eval x (dot a b) = eval x (dot b a) := by
  induction a generalizing b with
  | nil => simp [dot]
  | cons a as ih =>
    cases b with
    | nil => simp [dot]
    | cons b bs => simp [dot, eval_add, eval_mul, mul_comm, ih]

theorem rowCheck_sound (x : R) (f : List Int) (hf : eval x f = 0)
    (d : Int) (z a : List (List Int)) (pt : List (List (List Int))) (q : List (List Int))
    (h : rowCheck f d z a pt q = true) :
    ∀ j, (d : R) * eval x (a.getD j []) = eval x (dot z (pt.getD j [])) := by
  induction a generalizing pt q with
  | nil => cases pt <;> cases q <;> simp_all [rowCheck, dot]
  | cons a as ih =>
    cases pt with
    | nil => simp [rowCheck] at h
    | cons p pt =>
      cases q with
      | nil => simp [rowCheck] at h
      | cons q qs =>
        simp only [rowCheck, Bool.and_eq_true] at h
        intro j
        cases j with
        | zero =>
          have := eqMod_sound x 0 (by simp) _ _ h.1
          simpa [eval_scale, eval_add, eval_mul, hf] using this
        | succ j => simpa using ih pt qs h.2 j

theorem rowsCheck_sound (f : List Int) (d : Int) (rows : List Nat)
    (pt : List (List (List Int))) (i : Nat) (A z q : List (List (List Int)))
    (h : rowsCheck f d rows pt i A z q = true) (t : Nat) (ht : t < A.length) :
    Hex.Matrix.RankWitness.memNat (i + t) rows = true ∨
      ∃ z q, rowCheck f d z A[t] pt q = true := by
  induction A generalizing i z q t with
  | nil => simp at ht
  | cons a as ih =>
    cases hm : Hex.Matrix.RankWitness.memNat i rows with
    | true =>
      simp [rowsCheck, hm] at h
      cases t with
      | zero => exact Or.inl (by simpa using hm)
      | succ t =>
        have := ih (i + 1) z q h t (by simpa using ht)
        rwa [Nat.add_assoc, Nat.add_comm 1 t] at this
    | false =>
      simp [rowsCheck, hm] at h
      cases z with
      | nil => simp at h
      | cons z zs =>
        cases q with
        | nil => simp at h
        | cons q qs =>
          simp only [Bool.and_eq_true] at h
          cases t with
          | zero => exact Or.inr ⟨z, q, h.1⟩
          | succ t =>
            have := ih (i + 1) zs qs h.2 t (by simpa using ht)
            rwa [Nat.add_assoc, Nat.add_comm 1 t] at this

/-- Interpret polynomial rows in a ring with a chosen generator. -/
@[expose] def ofPolys (x : R) (n m : Nat) (A : List (List (List Int))) :
    Matrix (Fin n) (Fin m) R := ofLists n m (A.map (List.map (eval x)))

theorem ofPolys_apply (x : R) (n m : Nat) (A : List (List (List Int)))
    (i : Fin n) (j : Fin m) :
    ofPolys x n m A i j = eval x ((A.getD i []).getD j []) := by
  rw [ofPolys, ofLists_apply]
  have hrows : (A.map (List.map (eval x))).getD i [] = (A.getD i []).map (eval x) :=
    List.getD_map A [] (List.map (eval x))
  rw [hrows]
  exact List.getD_map (A.getD i []) [] (eval x)

/-- The list checker is sound for any characteristic-zero domain and any
homomorphism to a nontrivial modular ring. The chosen generator satisfies
the integer polynomial in the source ring. -/
theorem rank_eq_of_check [IsDomain R] [CharZero R] {S : Type*} [CommRing S]
    [Nontrivial S] (φ : R →+* S) (x : R) (n m : Nat) (f : List Int)
    (L : List (List (List Int))) (c : Hex.Matrix.PolyWitness)
    (hf : eval x f = 0) (hM : (c.modulus : S) = 0)
    (h : Hex.Matrix.checkRankPoly n m f L c = true) :
    (ofPolys x n m L).rank = c.rank := by
  classical
  simp only [Hex.Matrix.checkRankPoly, Bool.and_eq_true, Nat.beq_eq,
    decide_eq_true_eq, and_assoc] at h
  obtain ⟨hLen, _, _, _, _, hrowsLen, hcolsLen, hrows, hcols, hd, hlow, hup⟩ := h
  have hrowsLt := (HexMatrixMathlib.allLt_iff _ _).mp hrows
  have hcolsLt := (HexMatrixMathlib.allLt_iff _ _).mp hcols
  let r := c.rank
  have hrowsMem : ∀ k : Fin r, c.rows.getD k 0 ∈ c.rows := fun k => by
    rw [getD_eq_getElem' _ _ _ (by omega)]
    exact List.getElem_mem _
  have hcolsMem : ∀ k : Fin r, c.cols.getD k 0 ∈ c.cols := fun k => by
    rw [getD_eq_getElem' _ _ _ (by omega)]
    exact List.getElem_mem _
  let rowF : Fin r → Fin n := fun k => ⟨c.rows.getD k 0, hrowsLt _ (hrowsMem k)⟩
  let colF : Fin r → Fin m := fun k => ⟨c.cols.getD k 0, hcolsLt _ (hcolsMem k)⟩
  let A := ofPolys x n m L
  let V : Matrix (Fin r) (Fin r) S := fun k j => eval (φ x) ((c.vt.getD j []).getD k [])
  have hfs : eval (φ x) f = 0 := by rw [← map_eval, hf, map_zero]
  obtain ⟨_, hspec⟩ := lowerCheck_sound (φ x) c.modulus hM f hfs _ _ _ hlow
  have hblen : (block L c.rows c.cols).length = r := by simp [block, hrowsLen, r]
  have hmul : ∀ i j : Fin r, ((A.submatrix rowF colF).map φ * V) i j =
      eval (φ x) (dot ((block L c.rows c.cols)[i.val]'(by omega)) (c.vt.getD j [])) := by
    intro i j
    rw [Matrix.mul_apply, eval_dot_sum _ _ _ r (by simp [block, hcolsLen, r])]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [block, List.getElem_map]
    rw [getD_eq_getElem' _ _ _ (by simp; omega), List.getElem_map]
    simp only [nth_eq_getD, Matrix.map_apply, Matrix.submatrix_apply, A, ofPolys_apply, V,
      rowF, colF, map_eval]
    rw [getD_eq_getElem' c.rows _ _ (by omega), getD_eq_getElem' c.cols _ _ (by omega)]
  have hdiag : ∀ i, ((A.submatrix rowF colF).map φ * V) i i = 1 := fun i => by
    rw [hmul]
    exact (hspec i (by omega)).1
  have htri : ((A.submatrix rowF colF).map φ * V).IsLowerTriangular := by
    intro i j hij
    rw [hmul]
    exact (hspec i (by omega)).2 j (by simpa using hij)
  have hpt : ∀ j : Fin m, (pivotCols m L c.rows).getD j [] =
      c.rows.map fun i => (L.getD i []).getD j [] := by
    intro j
    rw [getD_eq_getElem' _ _ _ (by simp [pivotCols])]
    simp [pivotCols, nth_eq_getD]
  have key : ∀ i : Fin n, ∃ w : Fin r → R,
      ∀ j : Fin m, (c.denom : R) * A i j = ∑ l, w l * A (rowF l) j := by
    intro i
    rcases rowsCheck_sound f c.denom c.rows _ 0 L c.z c.upperQuot hup i (by omega) with
      hmem | ⟨z, q, hz⟩
    · rw [Nat.zero_add, HexMatrixMathlib.memNat_iff] at hmem
      obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp hmem
      let k0 : Fin r := ⟨k, by omega⟩
      have hrowFk : rowF k0 = i := by
        apply Fin.ext
        show c.rows.getD k 0 = i
        rw [getD_eq_getElem' _ _ _ hk, hki]
      refine ⟨fun l => if l = k0 then (c.denom : R) else 0, fun j => ?_⟩
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hrowFk]
    · refine ⟨fun l => eval x (z.getD l []), fun j => ?_⟩
      have hzj := rowCheck_sound x f hf c.denom z _ _ q hz j
      rw [eval_dot_comm, hpt, eval_dot_sum _ _ _ r (by simp [hrowsLen, r])] at hzj
      rw [show A i j = eval x ((L.getD i []).getD j []) from ofPolys_apply x n m L i j]
      rw [getD_eq_getElem' L i [] (by omega), hzj]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [getD_eq_getElem' _ _ _ (by simp; omega), List.getElem_map]
      simp only [A, ofPolys_apply, rowF]
      rw [getD_eq_getElem' c.rows _ _ (by omega), mul_comm]
  let W : Matrix (Fin n) (Fin r) R := fun i l => Classical.choose (key i) l
  have hW : (c.denom : R) • A = W * A.submatrix rowF id := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, W]
    exact Classical.choose_spec (key i) j
  exact rank_eq_of_modular φ A rowF colF V (c.denom : R) W
    (by exact_mod_cast hd) htri hdiag hW

end HexMatrixMathlib.PolyWitness
