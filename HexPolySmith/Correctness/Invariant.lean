/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmith.Divisor
public import HexPolySmith.Structure
import HexMatrix.ElementaryAlgebra

public section

/-! Correctness invariants for the polynomial Smith loop. -/

namespace Hex.PolyMatrix

universe u

open Hex

/-- The optional transforms represent the current work matrix and carry the
explicit right inverses promised by `SmithData`. -/
@[expose] def TransformValid {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (s : LoopState F n m) : Prop :=
  match s.transforms with
  | none => True
  | some t =>
      t.left * A * t.right = s.work
        ∧ t.left * t.leftInv = Matrix.identity n
        ∧ t.right * t.rightInv = Matrix.identity m

theorem transformValid_none {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (work : Matrix (DensePoly F) n m)
    (pivot : Nat) :
    TransformValid A ({ work, pivot, transforms := none } : LoopState F n m) := by
  trivial

/-- Multiplication commutes with replacing a pair of rows. -/
theorem pairRows_mul {R : Type u} [Lean.Grind.CommRing R] {n m k : Nat}
    (A : Matrix R n m) (B : Matrix R m k) (i j : Fin n) (E : Matrix R 2 2)
    (hij : i ≠ j) :
    pairRows A i j E * B = pairRows (A * B) i j E := by
  apply Matrix.ext_getElem
  intro r c
  rw [Matrix.getElem_mul]
  by_cases hri : r = i
  · subst r
    rw [pairRows_left _ _ _ _ hij, Matrix.getElem_mul, Matrix.getElem_mul]
    have hrow : Matrix.row (pairRows A i j E) i =
        Vector.ofFn fun q => E[(0, 0)] * A[i][q] + E[(0, 1)] * A[j][q] := by
      ext q hq
      rw [Vector.getElem_ofFn]
      change (pairRows A i j E)[i][(⟨q, hq⟩ : Fin m)] = _
      exact pairRows_left A i j E hij (⟨q, hq⟩ : Fin m)
    have hsplit : (Vector.ofFn fun q : Fin m =>
        E[(0, 0)] * A[i][q] + E[(0, 1)] * A[j][q]) =
        E[(0, 0)] • A[i] + E[(0, 1)] • A[j] := by
      ext q hq
      rw [Vector.getElem_ofFn, Vector.getElem_add, Vector.getElem_smul,
        Vector.getElem_smul]
      rfl
    rw [hrow, hsplit, Vector.dotProduct_add_left,
      Vector.dotProduct_smul_left, Vector.dotProduct_smul_left]
    rfl
  · by_cases hrj : r = j
    · subst r
      rw [pairRows_right, Matrix.getElem_mul, Matrix.getElem_mul]
      have hrow : Matrix.row (pairRows A i j E) j =
          Vector.ofFn fun q => E[(1, 0)] * A[i][q] + E[(1, 1)] * A[j][q] := by
        ext q hq
        rw [Vector.getElem_ofFn]
        change (pairRows A i j E)[j][(⟨q, hq⟩ : Fin m)] = _
        exact pairRows_right A i j E (⟨q, hq⟩ : Fin m)
      have hsplit : (Vector.ofFn fun q : Fin m =>
          E[(1, 0)] * A[i][q] + E[(1, 1)] * A[j][q]) =
          E[(1, 0)] • A[i] + E[(1, 1)] • A[j] := by
        ext q hq
        rw [Vector.getElem_ofFn, Vector.getElem_add, Vector.getElem_smul,
          Vector.getElem_smul]
        rfl
      rw [hrow, hsplit, Vector.dotProduct_add_left,
        Vector.dotProduct_smul_left, Vector.dotProduct_smul_left]
      rfl
    · rw [pairRows_other (A * B) i j r E hri hrj]
      have hrow : Matrix.row (pairRows A i j E) r = Matrix.row A r := by
        ext q hq
        change (pairRows A i j E)[r][(⟨q, hq⟩ : Fin m)] = _
        exact pairRows_other A i j r E hri hrj (⟨q, hq⟩ : Fin m)
      rw [hrow, Matrix.getElem_mul]

/-- Multiplication commutes with replacing a pair of columns. -/
theorem mul_pairCols {R : Type u} [Lean.Grind.CommRing R] {n m k : Nat}
    (A : Matrix R n m) (B : Matrix R m k) (i j : Fin k) (E : Matrix R 2 2)
    (hij : i ≠ j) :
    A * pairCols B i j E = pairCols (A * B) i j E := by
  apply Matrix.ext_getElem
  intro r c
  rw [Matrix.getElem_mul]
  by_cases hci : c = i
  · subst c
    rw [pairCols_left _ _ _ _ hij, Matrix.getElem_mul, Matrix.getElem_mul]
    have hcol : Matrix.col (pairCols B i j E) i =
        Vector.ofFn fun q => E[(0, 0)] * B[q][i] + E[(0, 1)] * B[q][j] := by
      ext q hq
      simp only [Matrix.col, Vector.getElem_ofFn]
      rw [Matrix.getElem_pair_eq_nested]
      exact pairCols_left B i j E hij (⟨q, hq⟩ : Fin m)
    have hsplit : (Vector.ofFn fun q : Fin m =>
        E[(0, 0)] * B[q][i] + E[(0, 1)] * B[q][j]) =
        E[(0, 0)] • Matrix.col B i + E[(0, 1)] • Matrix.col B j := by
      ext q hq
      rw [Vector.getElem_ofFn, Vector.getElem_add, Vector.getElem_smul,
        Vector.getElem_smul]
      simp only [Matrix.col, Vector.getElem_ofFn]
      rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested]
      change E[(0, 0)] * B[(⟨q, hq⟩ : Fin m)][i] +
        E[(0, 1)] * B[(⟨q, hq⟩ : Fin m)][j] =
        E[(0, 0)] * B[(⟨q, hq⟩ : Fin m)][i] +
        E[(0, 1)] * B[(⟨q, hq⟩ : Fin m)][j]
      rfl
    rw [hcol, hsplit, Vector.dotProduct_add_right,
      Vector.dotProduct_smul_right, Vector.dotProduct_smul_right]
    rfl
  · by_cases hcj : c = j
    · subst c
      rw [pairCols_right, Matrix.getElem_mul, Matrix.getElem_mul]
      have hcol : Matrix.col (pairCols B i j E) j =
          Vector.ofFn fun q => E[(1, 0)] * B[q][i] + E[(1, 1)] * B[q][j] := by
        ext q hq
        simp only [Matrix.col, Vector.getElem_ofFn]
        rw [Matrix.getElem_pair_eq_nested]
        exact pairCols_right B i j E (⟨q, hq⟩ : Fin m)
      have hsplit : (Vector.ofFn fun q : Fin m =>
          E[(1, 0)] * B[q][i] + E[(1, 1)] * B[q][j]) =
          E[(1, 0)] • Matrix.col B i + E[(1, 1)] • Matrix.col B j := by
        ext q hq
        rw [Vector.getElem_ofFn, Vector.getElem_add, Vector.getElem_smul,
          Vector.getElem_smul]
        simp only [Matrix.col, Vector.getElem_ofFn]
        rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested]
        change E[(1, 0)] * B[(⟨q, hq⟩ : Fin m)][i] +
          E[(1, 1)] * B[(⟨q, hq⟩ : Fin m)][j] =
          E[(1, 0)] * B[(⟨q, hq⟩ : Fin m)][i] +
          E[(1, 1)] * B[(⟨q, hq⟩ : Fin m)][j]
        rfl
      rw [hcol, hsplit, Vector.dotProduct_add_right,
        Vector.dotProduct_smul_right, Vector.dotProduct_smul_right]
      rfl
    · rw [pairCols_other (A * B) i j c E hci hcj]
      have hcol : Matrix.col (pairCols B i j E) c = Matrix.col B c := by
        ext q hq
        simp only [Matrix.col, Vector.getElem_ofFn]
        rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested]
        exact pairCols_other B i j c E hci hcj (⟨q, hq⟩ : Fin m)
      rw [hcol, Matrix.getElem_mul]

/-- Multiplication commutes with swapping columns of the right factor. -/
theorem mul_colSwap {R : Type u} [Lean.Grind.CommRing R] {n m k : Nat}
    (A : Matrix R n m) (B : Matrix R m k) (i j : Fin k) :
    A * B.colSwap i j = (A * B).colSwap i j := by
  apply Matrix.ext_getElem
  intro r c
  rw [Matrix.getElem_mul, Matrix.getElem_colSwap]
  by_cases hcj : c = j
  · rw [ite_eq_left hcj]
    subst c
    rw [Matrix.col_colSwap_right, Matrix.getElem_mul]
  · rw [ite_eq_right hcj]
    by_cases hci : c = i
    · rw [ite_eq_left hci]
      subst c
      rw [Matrix.col_colSwap_left, Matrix.getElem_mul]
    · rw [ite_eq_right hci, Matrix.col_colSwap_of_ne _ hci hcj,
        Matrix.getElem_mul]

/-- Multiplication commutes with scaling a column of the right factor. -/
theorem mul_colScale {R : Type u} [Lean.Grind.CommRing R] {n m k : Nat}
    (A : Matrix R n m) (B : Matrix R m k) (j : Fin k) (c : R) :
    A * B.colScale j c = (A * B).colScale j c := by
  apply Matrix.ext_getElem
  intro r q
  rw [Matrix.getElem_mul, Matrix.getElem_colScale]
  by_cases hqj : q = j
  · rw [ite_eq_left hqj]
    subst q
    rw [Matrix.col_colScale_self]
    have hcol : (Vector.ofFn fun i : Fin m => c * B[i][j]) =
        c • Matrix.col B j := by
      ext i hi
      rw [Vector.getElem_ofFn, Vector.getElem_smul]
      simp only [Matrix.col, Vector.getElem_ofFn,
        Matrix.getElem_pair_eq_nested]
      rfl
    rw [hcol, Vector.dotProduct_smul_right, Matrix.getElem_mul]
  · rw [ite_eq_right hqj, Matrix.col_colScale_of_ne _ _ hqj,
      Matrix.getElem_mul]

private theorem rowSwap_colSwap_identity {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (i j : Fin n) :
    ((Matrix.identity (R := R) n).colSwap i j).rowSwap i j = Matrix.identity n := by
  have hbridge : (Matrix.identity (R := R) n).colSwap i j =
      (Matrix.identity (R := R) n).rowSwap i j := by
    apply Matrix.ext_getElem
    intro r c
    have hid (a b : Fin n) :
        ((Matrix.identity (R := R) n).getRow a)[b] =
          if a = b then (1 : R) else 0 := Matrix.getElem_identity a b
    by_cases hij : i = j
    · subst j
      rw [Matrix.getElem_colSwap]
      by_cases hci : c = i <;> by_cases hri : r = i <;>
        simp_all
    have hji : j ≠ i := Ne.symm hij
    rw [Matrix.getElem_colSwap, Matrix.getElem_rowSwap]
    by_cases hrj : r = j <;> by_cases hri : r = i <;>
      by_cases hcj : c = j <;> by_cases hci : c = i <;>
        simp_all <;> grind
  rw [hbridge, Matrix.rowSwap_rowSwap]

private theorem rowScale_colScale_identity {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (i : Fin n) (c cinv : R) (hc : c * cinv = 1) :
    ((Matrix.identity (R := R) n).colScale i cinv).rowScale i c =
      Matrix.identity n := by
  have hbridge : (Matrix.identity (R := R) n).colScale i cinv =
      (Matrix.identity (R := R) n).rowScale i cinv := by
    apply Matrix.ext_getElem
    intro r q
    have hid (a b : Fin n) :
        ((Matrix.identity (R := R) n).getRow a)[b] =
          if a = b then (1 : R) else 0 := Matrix.getElem_identity a b
    rw [Matrix.getElem_colScale, Matrix.getElem_rowScale]
    by_cases hri : r = i
    · subst r
      by_cases hqi : q = i
      · subst q; simp [hid]
      · have hiq : i ≠ q := Ne.symm hqi
        simp [hqi, hiq, hid]
        grind
    · have hir : i ≠ r := Ne.symm hri
      by_cases hqi : q = i
      · subst q; simp [hri, hid]
        grind
      · simp [hri, hqi, hid]
  rw [hbridge]
  apply Matrix.ext_getElem
  intro r q
  have hid (a b : Fin n) :
      ((Matrix.identity (R := R) n).getRow a)[b] =
        if a = b then (1 : R) else 0 := Matrix.getElem_identity a b
  rw [Matrix.getElem_rowScale]
  by_cases hri : r = i
  · rw [ite_eq_left hri]
    subst r
    rw [Matrix.getElem_rowScale, ite_eq_left rfl]
    rw [Matrix.getElem_identity]
    by_cases hqi : q = i
    · subst q
      simp only [ite_true]
      grind
    · have hiq : i ≠ q := Ne.symm hqi
      simp [hiq]
      grind
  · rw [ite_eq_right hri, Matrix.getElem_rowScale, ite_eq_right hri]

private theorem rowAdd_colAdd_identity {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (src dst : Fin n) (c : R) (hsd : src ≠ dst) :
    ((Matrix.identity (R := R) n).colAdd dst src (-c)).rowAdd src dst c =
      Matrix.identity n := by
  have hbridge : (Matrix.identity (R := R) n).colAdd dst src (-c) =
      (Matrix.identity (R := R) n).rowAdd src dst (-c) := by
    apply Matrix.ext_getElem
    intro r q
    have hid (a b : Fin n) :
        ((Matrix.identity (R := R) n).getRow a)[b] =
          if a = b then (1 : R) else 0 := Matrix.getElem_identity a b
    have hds : dst ≠ src := Ne.symm hsd
    rw [Matrix.getElem_colAdd, Matrix.getElem_rowAdd]
    by_cases hrd : r = dst <;> by_cases hqs : q = src <;>
      by_cases hrs : r = src <;> by_cases hqd : q = dst <;>
        simp_all
    all_goals grind
  rw [hbridge]
  exact Matrix.rowAdd_rowAdd_neg_left (Matrix.identity (R := R) n) c hsd

private theorem leftUpdate_swap {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} {L Linv : Matrix R n n} (i j : Fin n)
    (h : L * Linv = Matrix.identity n) :
    L.rowSwap i j * Linv.colSwap i j = Matrix.identity n := by
  calc
    L.rowSwap i j * Linv.colSwap i j =
        ((Matrix.identity (R := R) n).colSwap i j).rowSwap i j := by
      rw [Matrix.rowSwap_mul, mul_colSwap, h]
    _ = Matrix.identity n := rowSwap_colSwap_identity i j

private theorem leftUpdate_scale {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} {L Linv : Matrix R n n} (i : Fin n) (c cinv : R)
    (hc : c * cinv = 1) (h : L * Linv = Matrix.identity n) :
    L.rowScale i c * Linv.colScale i cinv = Matrix.identity n := by
  calc
    L.rowScale i c * Linv.colScale i cinv =
        ((Matrix.identity (R := R) n).colScale i cinv).rowScale i c := by
      rw [Matrix.rowScale_mul, mul_colScale, h]
    _ = Matrix.identity n := rowScale_colScale_identity i c cinv hc

private theorem leftUpdate_add {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} {L Linv : Matrix R n n} (src dst : Fin n) (c : R)
    (hsd : src ≠ dst) (h : L * Linv = Matrix.identity n) :
    L.rowAdd src dst c * Linv.colAdd dst src (-c) = Matrix.identity n := by
  calc
    L.rowAdd src dst c * Linv.colAdd dst src (-c) =
        ((Matrix.identity (R := R) n).colAdd dst src (-c)).rowAdd src dst c := by
      rw [Matrix.rowAdd_mul, Matrix.mul_colAdd, h]
    _ = Matrix.identity n := rowAdd_colAdd_identity src dst c hsd

private theorem pairRows_comp {R : Type u} [Lean.Grind.CommRing R]
    {n m : Nat} (A : Matrix R n m) (i j : Fin n) (E G : Matrix R 2 2)
    (hij : i ≠ j) :
    pairRows (pairRows A i j G) i j E = pairRows A i j (E * G) := by
  apply Matrix.ext_getElem
  intro r c
  have hentry (M : Matrix R 2 2) (a b : Fin 2) : M[(a, b)] = M[a][b] :=
    Matrix.getElem_pair_eq_nested M a b
  have hmul (a b : Fin 2) :
      (E * G)[a][b] = E[a][0] * G[0][b] + E[a][1] * G[1][b] := by
    rw [Matrix.getElem_mul]
    have hfin : List.finRange 2 = [(0 : Fin 2), (1 : Fin 2)] := by rfl
    rw [Vector.dotProduct, hfin]
    simp only [List.foldl_cons, List.foldl_nil, Matrix.getElem_row,
      Matrix.getElem_col]
    grind
  have he00 := hentry E 0 0
  have he01 := hentry E 0 1
  have he10 := hentry E 1 0
  have he11 := hentry E 1 1
  have hg00 := hentry G 0 0
  have hg01 := hentry G 0 1
  have hg10 := hentry G 1 0
  have hg11 := hentry G 1 1
  have heg00 := hentry (E * G) 0 0
  have heg01 := hentry (E * G) 0 1
  have heg10 := hentry (E * G) 1 0
  have heg11 := hentry (E * G) 1 1
  have hm00 := hmul 0 0
  have hm01 := hmul 0 1
  have hm10 := hmul 1 0
  have hm11 := hmul 1 1
  have hen00 : E[(0, 0)] = E[0][0] := rfl
  have hen01 : E[(0, 1)] = E[0][1] := rfl
  have hen10 : E[(1, 0)] = E[1][0] := rfl
  have hen11 : E[(1, 1)] = E[1][1] := rfl
  have hgn00 : G[(0, 0)] = G[0][0] := rfl
  have hgn01 : G[(0, 1)] = G[0][1] := rfl
  have hgn10 : G[(1, 0)] = G[1][0] := rfl
  have hgn11 : G[(1, 1)] = G[1][1] := rfl
  have hegn00 : (E * G)[(0, 0)] = (E * G)[0][0] := rfl
  have hegn01 : (E * G)[(0, 1)] = (E * G)[0][1] := rfl
  have hegn10 : (E * G)[(1, 0)] = (E * G)[1][0] := rfl
  have hegn11 : (E * G)[(1, 1)] = (E * G)[1][1] := rfl
  clear hentry hmul
  by_cases hri : r = i
  · subst r
    rw [pairRows_left _ _ _ _ hij, pairRows_left _ _ _ _ hij,
      pairRows_right, pairRows_left _ _ _ _ hij]
    rw [heg00, heg01, he00, he01, hg00, hg01, hg10, hg11, hm00, hm01]
    clear he00 he01 he10 he11 hg00 hg01 hg10 hg11 heg00 heg01 heg10 heg11
      hm00 hm01 hm10 hm11 hen00 hen01 hen10 hen11 hgn00 hgn01 hgn10 hgn11
      hegn00 hegn01 hegn10 hegn11
    grind
  · by_cases hrj : r = j
    · subst r
      rw [pairRows_right, pairRows_left _ _ _ _ hij,
        pairRows_right, pairRows_right]
      rw [heg10, heg11, he10, he11, hg00, hg01, hg10, hg11, hm10, hm11]
      clear he00 he01 he10 he11 hg00 hg01 hg10 hg11 heg00 heg01 heg10 heg11
        hm00 hm01 hm10 hm11 hen00 hen01 hen10 hen11 hgn00 hgn01 hgn10 hgn11
        hegn00 hegn01 hegn10 hegn11
      grind
    · rw [pairRows_other _ _ _ _ _ hri hrj,
        pairRows_other _ _ _ _ _ hri hrj,
        pairRows_other _ _ _ _ _ hri hrj]

private theorem pairRows_identity {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (i j : Fin n) (hij : i ≠ j) :
    pairRows (Matrix.identity (R := R) n) i j (Matrix.identity 2) =
      Matrix.identity n := by
  apply Matrix.ext_getElem
  intro r c
  have hentry (M : Matrix R 2 2) (a b : Fin 2) : M[(a, b)] = M[a][b] :=
    Matrix.getElem_pair_eq_nested M a b
  have hid2 (a b : Fin 2) :
      (Matrix.identity (R := R) 2)[a][b] = if a = b then 1 else 0 :=
    Matrix.getElem_identity a b
  have hi00 := hentry (Matrix.identity (R := R) 2) 0 0
  have hi01 := hentry (Matrix.identity (R := R) 2) 0 1
  have hi10 := hentry (Matrix.identity (R := R) 2) 1 0
  have hi11 := hentry (Matrix.identity (R := R) 2) 1 1
  have hd00 := hid2 0 0
  have hd01 := hid2 0 1
  have hd10 := hid2 1 0
  have hd11 := hid2 1 1
  have hin00 : (Matrix.identity (R := R) 2)[(0, 0)] =
      (Matrix.identity (R := R) 2)[0][0] := rfl
  have hin01 : (Matrix.identity (R := R) 2)[(0, 1)] =
      (Matrix.identity (R := R) 2)[0][1] := rfl
  have hin10 : (Matrix.identity (R := R) 2)[(1, 0)] =
      (Matrix.identity (R := R) 2)[1][0] := rfl
  have hin11 : (Matrix.identity (R := R) 2)[(1, 1)] =
      (Matrix.identity (R := R) 2)[1][1] := rfl
  clear hentry hid2
  by_cases hri : r = i
  · subst r
    rw [pairRows_left _ _ _ _ hij]
    rw [hi00, hi01, hd00, hd01]
    clear hi00 hi01 hi10 hi11 hd00 hd01 hd10 hd11 hin00 hin01 hin10 hin11
    grind
  · by_cases hrj : r = j
    · subst r
      rw [pairRows_right]
      rw [hi10, hi11, hd10, hd11]
      clear hi00 hi01 hi10 hi11 hd00 hd01 hd10 hd11 hin00 hin01 hin10 hin11
      grind
    · rw [pairRows_other _ _ _ _ _ hri hrj]

private theorem identity_pairCols_transpose {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (i j : Fin n) (E : Matrix R 2 2) (hij : i ≠ j) :
    pairCols (Matrix.identity (R := R) n) i j E.transpose =
      pairRows (Matrix.identity (R := R) n) i j E := by
  apply Matrix.ext_getElem
  intro r c
  have hentry2 (M : Matrix R 2 2) (a b : Fin 2) : M[(a, b)] = M[a][b] :=
    Matrix.getElem_pair_eq_nested M a b
  have hentryN (M : Matrix R n n) (a b : Fin n) : M[(a, b)] = M[a][b] :=
    Matrix.getElem_pair_eq_nested M a b
  have hid (a b : Fin n) :
      (Matrix.identity (R := R) n)[a][b] = if a = b then 1 else 0 :=
    Matrix.getElem_identity a b
  have hidPair (a b : Fin n) :
      (Matrix.identity (R := R) n)[(a, b)] = if a = b then 1 else 0 := by
    rw [hentryN, hid]
  clear hentryN
  have ht (a b : Fin 2) : E.transpose[a][b] = E[b][a] :=
    Matrix.getElem_transpose E a b
  have het00 := hentry2 E.transpose 0 0
  have het01 := hentry2 E.transpose 0 1
  have het10 := hentry2 E.transpose 1 0
  have het11 := hentry2 E.transpose 1 1
  have he00 := hentry2 E 0 0
  have he01 := hentry2 E 0 1
  have he10 := hentry2 E 1 0
  have he11 := hentry2 E 1 1
  have ht00 := ht 0 0
  have ht01 := ht 0 1
  have ht10 := ht 1 0
  have ht11 := ht 1 1
  have hp00 : E.transpose[((0 : Fin 2), (0 : Fin 2))] =
      E[((0 : Fin 2), (0 : Fin 2))] := (het00.trans ht00).trans he00.symm
  have hp01 : E.transpose[((0 : Fin 2), (1 : Fin 2))] =
      E[((1 : Fin 2), (0 : Fin 2))] := (het01.trans ht01).trans he10.symm
  have hp10 : E.transpose[((1 : Fin 2), (0 : Fin 2))] =
      E[((0 : Fin 2), (1 : Fin 2))] := (het10.trans ht10).trans he01.symm
  have hp11 : E.transpose[((1 : Fin 2), (1 : Fin 2))] =
      E[((1 : Fin 2), (1 : Fin 2))] := (het11.trans ht11).trans he11.symm
  have hpn00 : E.transpose[(0, 0)] = E[(0, 0)] := by
    calc E.transpose[(0, 0)] = E.transpose[((0 : Fin 2), (0 : Fin 2))] := rfl
      _ = E[((0 : Fin 2), (0 : Fin 2))] := hp00
      _ = E[(0, 0)] := rfl
  have hpn01 : E.transpose[(0, 1)] = E[(1, 0)] := by
    calc E.transpose[(0, 1)] = E.transpose[((0 : Fin 2), (1 : Fin 2))] := rfl
      _ = E[((1 : Fin 2), (0 : Fin 2))] := hp01
      _ = E[(1, 0)] := rfl
  have hpn10 : E.transpose[(1, 0)] = E[(0, 1)] := by
    calc E.transpose[(1, 0)] = E.transpose[((1 : Fin 2), (0 : Fin 2))] := rfl
      _ = E[((0 : Fin 2), (1 : Fin 2))] := hp10
      _ = E[(0, 1)] := rfl
  have hpn11 : E.transpose[(1, 1)] = E[(1, 1)] := by
    calc E.transpose[(1, 1)] = E.transpose[((1 : Fin 2), (1 : Fin 2))] := rfl
      _ = E[((1 : Fin 2), (1 : Fin 2))] := hp11
      _ = E[(1, 1)] := rfl
  clear hentry2 ht het00 het01 het10 het11 he00 he01 he10 he11 ht00 ht01 ht10 ht11
  by_cases hri : r = i
  · subst r
    rw [pairRows_left _ _ _ _ hij]
    by_cases hci : c = i
    · subst c
      rw [pairCols_left _ _ _ _ hij, hp00, hp01]
      simp only [hid]
      clear hp00 hp01 hp10 hp11 hpn00 hpn01 hpn10 hpn11
      grind
    · by_cases hcj : c = j
      · subst c
        rw [pairCols_right, hp10, hp11]
        simp only [hid]
        clear hp00 hp01 hp10 hp11 hpn00 hpn01 hpn10 hpn11
        grind
      · rw [pairCols_other _ _ _ _ _ hci hcj]
        simp only [hid]
        clear hp00 hp01 hp10 hp11 hpn00 hpn01 hpn10 hpn11
        grind
  · by_cases hrj : r = j
    · subst r
      rw [pairRows_right]
      by_cases hci : c = i
      · subst c
        rw [pairCols_left _ _ _ _ hij, hp00, hp01]
        simp only [hid]
        clear hp00 hp01 hp10 hp11 hpn00 hpn01 hpn10 hpn11
        grind
      · by_cases hcj : c = j
        · subst c
          rw [pairCols_right, hp10, hp11]
          simp only [hid]
          clear hp00 hp01 hp10 hp11 hpn00 hpn01 hpn10 hpn11
          grind
        · rw [pairCols_other _ _ _ _ _ hci hcj]
          simp only [hid]
          clear hp00 hp01 hp10 hp11 hpn00 hpn01 hpn10 hpn11
          grind
    · rw [pairRows_other _ _ _ _ _ hri hrj]
      by_cases hci : c = i
      · subst c
        rw [pairCols_left _ _ _ _ hij, hp00, hp01]
        simp only [hid]
        clear hp00 hp01 hp10 hp11 hpn00 hpn01 hpn10 hpn11
        grind
      · by_cases hcj : c = j
        · subst c
          rw [pairCols_right, hp10, hp11]
          simp only [hid]
          clear hp00 hp01 hp10 hp11 hpn00 hpn01 hpn10 hpn11
          grind
        · rw [pairCols_other _ _ _ _ _ hci hcj]

private theorem pairRows_pairCols_identity {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} {L Linv : Matrix R n n} (i j : Fin n) (E Einv : Matrix R 2 2)
    (hij : i ≠ j) (hE : E * Einv = Matrix.identity 2)
    (hL : L * Linv = Matrix.identity n) :
    pairRows L i j E * pairCols Linv i j Einv.transpose = Matrix.identity n := by
  calc
    pairRows L i j E * pairCols Linv i j Einv.transpose =
        pairRows (pairCols (L * Linv) i j Einv.transpose) i j E := by
      rw [pairRows_mul _ _ _ _ _ hij, mul_pairCols _ _ _ _ _ hij]
    _ = pairRows (pairRows (Matrix.identity (R := R) n) i j Einv) i j E := by
      rw [hL, identity_pairCols_transpose i j Einv hij]
    _ = pairRows (Matrix.identity (R := R) n) i j (E * Einv) :=
      pairRows_comp _ i j E Einv hij
    _ = Matrix.identity n := by rw [hE]; exact pairRows_identity i j hij

theorem transformValid_swapRows {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {A : Matrix (DensePoly F) n m} {s : LoopState F n m}
    (i j : Fin n) (h : TransformValid A s) : TransformValid A (swapRows s i j) := by
  unfold TransformValid at h ⊢
  cases ht : s.transforms
  · simp [swapRows, mapTransforms, ht]
  · simp only [swapRows, mapTransforms, ht, Option.map_some]
    simp only [ht] at h
    rcases h with ⟨heq, hleft, hright⟩
    refine ⟨?_, leftUpdate_swap i j hleft, hright⟩
    rw [Matrix.rowSwap_mul, Matrix.rowSwap_mul, heq]

theorem transformValid_swapCols {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {A : Matrix (DensePoly F) n m} {s : LoopState F n m}
    (i j : Fin m) (h : TransformValid A s) : TransformValid A (swapCols s i j) := by
  unfold TransformValid at h ⊢
  cases ht : s.transforms
  · simp [swapCols, mapTransforms, ht]
  · simp only [swapCols, mapTransforms, ht, Option.map_some]
    simp only [ht] at h
    rcases h with ⟨heq, hleft, hright⟩
    refine ⟨?_, hleft, ?_⟩
    · rw [mul_colSwap, heq]
    · apply Matrix.mul_eq_one_comm
      apply leftUpdate_swap
      exact Matrix.mul_eq_one_comm hright

theorem transformValid_scaleRow {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {A : Matrix (DensePoly F) n m} {s : LoopState F n m}
    (i : Fin n) (c cinv : DensePoly F) (hc : c * cinv = 1)
    (h : TransformValid A s) : TransformValid A (scaleRow s i c cinv) := by
  unfold TransformValid at h ⊢
  cases ht : s.transforms
  · simp [scaleRow, mapTransforms, ht]
  · simp only [scaleRow, mapTransforms, ht, Option.map_some]
    simp only [ht] at h
    rcases h with ⟨heq, hleft, hright⟩
    refine ⟨?_, leftUpdate_scale i c cinv hc hleft, hright⟩
    rw [Matrix.rowScale_mul, Matrix.rowScale_mul, heq]

private theorem polyNeg_eq_neg {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (c : DensePoly F) : polyNeg c = -c := by
  unfold polyNeg
  change (0 : DensePoly F) - c = -c
  rfl

theorem transformValid_addRow {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {A : Matrix (DensePoly F) n m} {s : LoopState F n m}
    (src dst : Fin n) (c : DensePoly F) (hsd : src ≠ dst)
    (h : TransformValid A s) : TransformValid A (addRow s src dst c) := by
  unfold TransformValid at h ⊢
  cases ht : s.transforms
  · simp [addRow, mapTransforms, ht]
  · simp only [addRow, mapTransforms, ht, Option.map_some]
    simp only [ht] at h
    rcases h with ⟨heq, hleft, hright⟩
    refine ⟨?_, ?_, hright⟩
    · rw [Matrix.rowAdd_mul, Matrix.rowAdd_mul, heq]
    · rw [polyNeg_eq_neg]
      exact leftUpdate_add src dst c hsd hleft

theorem transformValid_addCol {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {A : Matrix (DensePoly F) n m} {s : LoopState F n m}
    (src dst : Fin m) (c : DensePoly F) (hsd : src ≠ dst)
    (h : TransformValid A s) : TransformValid A (addCol s src dst c) := by
  unfold TransformValid at h ⊢
  cases ht : s.transforms
  · simp [addCol, mapTransforms, ht]
  · simp only [addCol, mapTransforms, ht, Option.map_some]
    simp only [ht] at h
    rcases h with ⟨heq, hleft, hright⟩
    refine ⟨?_, hleft, ?_⟩
    · rw [Matrix.mul_colAdd, heq]
    · apply Matrix.mul_eq_one_comm
      rw [polyNeg_eq_neg]
      have hu := leftUpdate_add dst src (-c) (Ne.symm hsd)
        (Matrix.mul_eq_one_comm hright)
      have hnn : -(-c) = c := by grind
      rw [hnn] at hu
      exact hu

theorem transformValid_bezoutRows {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    {s : LoopState F n m} (i j : Fin n) (a b : DensePoly F) (hij : i ≠ j)
    (h : TransformValid A s) :
    TransformValid A (bezoutRows s i j (pairStep a b)) := by
  unfold TransformValid at h ⊢
  cases ht : s.transforms
  · simp [bezoutRows, mapTransforms, ht]
  · simp only [bezoutRows, mapTransforms, ht, Option.map_some]
    simp only [ht] at h
    rcases h with ⟨heq, hleft, hright⟩
    refine ⟨?_, ?_, hright⟩
    · rw [pairRows_mul _ _ _ _ _ hij, pairRows_mul _ _ _ _ _ hij, heq]
    · exact pairRows_pairCols_identity i j (pairStep a b).forward
        (pairStep a b).inverse hij (pairStep_forward_inverse _ _) hleft

theorem transformValid_bezoutCols {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    {s : LoopState F n m} (i j : Fin m) (a b : DensePoly F) (hij : i ≠ j)
    (h : TransformValid A s) :
    TransformValid A (bezoutCols s i j (pairStep a b)) := by
  unfold TransformValid at h ⊢
  cases ht : s.transforms
  · simp [bezoutCols, mapTransforms, ht]
  · simp only [bezoutCols, mapTransforms, ht, Option.map_some]
    simp only [ht] at h
    rcases h with ⟨heq, hleft, hright⟩
    refine ⟨?_, hleft, ?_⟩
    · rw [mul_pairCols _ _ _ _ _ hij, heq]
    · apply Matrix.mul_eq_one_comm
      exact pairRows_pairCols_identity i j (pairStep a b).inverse.transpose
        (pairStep a b).forward.transpose hij
        (by
          rw [← Matrix.transpose_mul_of_mul_comm, pairStep_forward_inverse,
            Matrix.transpose_identity])
        (Matrix.mul_eq_one_comm hright)

theorem transformValid_clearColumnScan {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    (ik : Fin n) (jk : Fin m) (is : List (Fin n)) {s : LoopState F n m}
    (h : TransformValid A s) : TransformValid A (clearColumnScan ik jk s is).state := by
  induction is generalizing s with
  | nil => exact h
  | cons i is ih =>
      rw [clearColumnScan]
      split
      · exact ih h
      · rename_i hik
        dsimp only
        split
        · exact ih h
        · split
          · apply ih
            apply transformValid_addRow ik i _ (Ne.symm hik)
            exact h
          · exact transformValid_bezoutRows ik i _ _ (Ne.symm hik) h

theorem transformValid_clearRowScan {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    (ik : Fin n) (jk : Fin m) (js : List (Fin m)) {s : LoopState F n m}
    (h : TransformValid A s) : TransformValid A (clearRowScan ik jk s js).state := by
  induction js generalizing s with
  | nil => exact h
  | cons j js ih =>
      rw [clearRowScan]
      split
      · exact ih h
      · rename_i hjk
        dsimp only
        split
        · exact ih h
        · split
          · apply ih
            apply transformValid_addCol jk j _ (Ne.symm hjk)
            exact h
          · exact transformValid_bezoutCols jk j _ _ (Ne.symm hjk) h

theorem transformValid_normalizePivot {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    {s : LoopState F n m} (k : Nat) (hkN : k < n) (hkM : k < m)
    (hp : s.work[((⟨k, hkN⟩ : Fin n), (⟨k, hkM⟩ : Fin m))] ≠ 0)
    (h : TransformValid A s) :
    TransformValid A (normalizePivot s k hkN hkM) := by
  unfold normalizePivot
  apply transformValid_scaleRow
  · rw [DensePoly.C_mul_C]
    apply congrArg DensePoly.C
    have hpSize : 0 < s.work[((⟨k, hkN⟩ : Fin n),
        (⟨k, hkM⟩ : Fin m))].size := by
      apply Nat.pos_of_ne_zero
      intro hs
      exact hp ((DensePoly.size_eq_zero_iff _).mp hs)
    have hlc := DensePoly.leadingCoeff_ne_zero_of_pos_size
      s.work[((⟨k, hkN⟩ : Fin n), (⟨k, hkM⟩ : Fin m))] hpSize
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.one_mul,
      Lean.Grind.Field.inv_mul_cancel hlc]
  · exact h

theorem transformValid_blockStep {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    {s : LoopState F n m} (ik i : Fin n) (jk j : Fin m)
    (hki : i ≠ ik) (hkj : jk ≠ j) (h : TransformValid A s) :
    TransformValid A (blockStep s ik i jk j) := by
  unfold blockStep
  apply transformValid_bezoutCols jk j _ _ hkj
  apply transformValid_addRow i ik polyOne hki
  exact h

theorem transformValid_smithStage {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    (s : LoopState F n m) (ik : Fin n) (jk : Fin m)
    (hp : s.work[(ik, jk)] ≠ 0) (h : TransformValid A s) :
    TransformValid A (smithStage s ik jk hp) := by
  generalize hsiz : s.work[(ik, jk)].size = N
  induction N using Nat.strongRecOn generalizing s with
  | _ N ih =>
    rw [smithStage]
    let col := clearColumnScan ik jk s (List.finRange n)
    split
    · rename_i hc
      apply ih col.state.work[(ik, jk)].size
      · rw [← hsiz]
        exact clearColumnScan_drop ik jk s (List.finRange n) hp hc
      · exact transformValid_clearColumnScan ik jk (List.finRange n) h
      · rfl
    · rename_i hc
      let row := clearRowScan ik jk col.state (List.finRange m)
      dsimp only
      split
      · rename_i hr
        apply ih row.state.work[(ik, jk)].size
        · rw [← hsiz]
          have hc0 : col.dropped = false := bool_eq_false hc
          have hcolEq := clearColumnScan_row ik jk jk s (List.finRange n) hc0
          calc
            row.state.work[(ik, jk)].size < col.state.work[(ik, jk)].size :=
              clearRowScan_drop ik jk col.state (List.finRange m)
                (clearColumnScan_pivot_ne_zero ik jk s (List.finRange n) hp) hr
            _ = s.work[(ik, jk)].size := congrArg DensePoly.size hcolEq
        · apply transformValid_clearRowScan ik jk (List.finRange m)
          exact transformValid_clearColumnScan ik jk (List.finRange n) h
        · rfl
      · rename_i hr
        split
        · exact transformValid_clearRowScan ik jk (List.finRange m)
            (transformValid_clearColumnScan ik jk (List.finRange n) h)
        · rename_i q hb
          have hq := badBlock_some hb
          have hki : q.1 ≠ ik := by omega
          have hkj : jk ≠ q.2 := by omega
          have hc0 : col.dropped = false := bool_eq_false hc
          have hr0 : row.dropped = false := bool_eq_false hr
          have hpCol := clearColumnScan_pivot_ne_zero
            ik jk s (List.finRange n) hp
          have hcol0 : col.state.work[(q.1, jk)] = 0 :=
            clearColumnScan_zero ik q.1 jk s (List.finRange n) hp
              (List.nodup_finRange n) hki (List.mem_finRange q.1) hc0
          have hcol : row.state.work[(q.1, jk)] = 0 := by
            rw [clearRowScan_column ik q.1 jk col.state (List.finRange m) hr0]
            exact hcol0
          have hrow : row.state.work[(ik, q.2)] = 0 :=
            clearRowScan_zero ik jk q.2 col.state (List.finRange m) hpCol
              (List.nodup_finRange m) (Ne.symm hkj) (List.mem_finRange q.2) hr0
          have hpRow := clearRowScan_pivot_ne_zero
            ik jk col.state (List.finRange m) hpCol
          apply ih (blockStep row.state ik q.1 jk q.2).work[(ik, jk)].size
          · rw [← hsiz]
            have hnot : ¬row.state.work[(ik, jk)] ∣ row.state.work[q] := by
              intro hd
              have hz := DensePoly.mod_eq_zero_of_dvd _ _ hd
              rw [hz] at hq
              exact Bool.noConfusion hq.2.2
            rw [blockStep_pivot row.state ik q.1 jk q.2 hkj hcol hrow]
            have hcolEq := clearColumnScan_row ik jk jk s (List.finRange n) hc0
            have hrowEq := clearRowScan_column ik ik jk col.state (List.finRange m) hr0
            calc
              (pairStep row.state.work[(ik, jk)] row.state.work[q]).pivot.size <
                  row.state.work[(ik, jk)].size := pairStep_pivot_size_lt_left hpRow hnot
              _ = col.state.work[(ik, jk)].size := congrArg DensePoly.size hrowEq
              _ = s.work[(ik, jk)].size := congrArg DensePoly.size hcolEq
          · apply transformValid_blockStep ik q.1 jk q.2 hki hkj
            exact transformValid_clearRowScan ik jk (List.finRange m)
              (transformValid_clearColumnScan ik jk (List.finRange n) h)
          · rfl

private theorem trailingColFold_none {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat)
    (i : Fin n) (js : List (Fin m)) (best : Option (Fin n × Fin m))
    (hnone : js.foldl (trailingColStep A k i) best = none) :
    best = none ∧ ∀ j ∈ js, k ≤ j.val → A[(i, j)] = 0 := by
  induction js generalizing best with
  | nil => exact ⟨hnone, by simp⟩
  | cons j js ih =>
      simp only [List.foldl_cons] at hnone
      have ht := ih (trailingColStep A k i best j) hnone
      have hstep := ht.1
      have hbest : best = none := by
        cases hb : best with
        | none => rfl
        | some q =>
            exfalso
            unfold trailingColStep at hstep
            split at hstep
            · rw [hb] at hstep
              contradiction
            · split at hstep
              · rw [hb] at hstep
                contradiction
              · dsimp only at hstep
                rw [hb] at hstep
                split at hstep
                · simp_all
                · split at hstep <;> simp_all
      refine ⟨hbest, ?_⟩
      intro q hq hkq
      rcases List.mem_cons.mp hq with rfl | hq
      · have hknot : ¬q.val < k := by omega
        have hz : A[(i, q)].isZero = true := by
          by_cases hz : A[(i, q)].isZero = true
          · exact hz
          · have hz0 := bool_eq_false hz
            simp [trailingColStep, hknot, hbest] at hstep
            rw [Matrix.getElem_pair_eq_nested] at hz
            exact False.elim (hz hstep)
        exact (DensePoly.size_eq_zero_iff _).mp
          ((DensePoly.isZero_eq_true_iff _).mp hz)
      · exact ht.2 q hq hkq

private theorem trailingRowFold_none {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat)
    (is : List (Fin n)) (best : Option (Fin n × Fin m))
    (hnone : is.foldl (trailingRowStep A k) best = none) :
    best = none ∧ ∀ i ∈ is, k ≤ i.val → ∀ j : Fin m, k ≤ j.val → A[(i, j)] = 0 := by
  induction is generalizing best with
  | nil => exact ⟨hnone, by simp⟩
  | cons i is ih =>
      simp only [List.foldl_cons] at hnone
      have ht := ih (trailingRowStep A k best i) hnone
      have hstep := ht.1
      have hbest : best = none := by
        unfold trailingRowStep at hstep
        split at hstep
        · exact hstep
        · exact (trailingColFold_none A k i (List.finRange m) best hstep).1
      refine ⟨hbest, ?_⟩
      intro r hr hkr j hkj
      rcases List.mem_cons.mp hr with rfl | hr
      · unfold trailingRowStep at hstep
        rw [ite_eq_right (by omega)] at hstep
        exact (trailingColFold_none A k _ (List.finRange m) best hstep).2
          j (List.mem_finRange j) hkj
      · exact ht.2 r hr hkr j hkj

theorem trailingMin_none_zero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat)
    (hnone : trailingMin A k = none) (i : Fin n) (j : Fin m)
    (hi : k ≤ i.val) (hj : k ≤ j.val) : A[(i, j)] = 0 := by
  unfold trailingMin at hnone
  exact (trailingRowFold_none A k (List.finRange n) none hnone).2
    i (List.mem_finRange i) hi j hj

private theorem trailingCols_bounds {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat)
    (i : Fin n) (hi : k ≤ i.val) (js : List (Fin m))
    (best : Option (Fin n × Fin m))
    (hbest : ∀ q, best = some q → k ≤ q.1.val ∧ k ≤ q.2.val) :
    ∀ q,
      (js.foldl (fun best j =>
        if j.val < k then best else
          let p := A[(i, j)]
          if p.isZero then best else
            match best with
            | none => some (i, j)
            | some q => if p.size < A[q].size then some (i, j) else best) best) = some q →
      k ≤ q.1.val ∧ k ≤ q.2.val := by
  induction js generalizing best with
  | nil => exact hbest
  | cons j js ih =>
      simp only [List.foldl_cons]
      apply ih
      intro q hq
      split at hq
      · exact hbest q hq
      · rename_i hj
        split at hq
        · exact hbest q hq
        · cases hb : best
          · simp only [hb] at hq
            cases Option.some.inj hq
            exact ⟨hi, Nat.le_of_not_gt hj⟩
          · simp only [hb] at hq
            split at hq
            · cases Option.some.inj hq
              exact ⟨hi, Nat.le_of_not_gt hj⟩
            · exact hbest q (hb.trans hq)

theorem trailingMin_bounds {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat)
    {q : Fin n × Fin m} (h : trailingMin A k = some q) :
    k ≤ q.1.val ∧ k ≤ q.2.val := by
  unfold trailingMin at h
  have hrows : ∀ (is : List (Fin n)) (best : Option (Fin n × Fin m)),
      (∀ q, best = some q → k ≤ q.1.val ∧ k ≤ q.2.val) →
      ∀ q,
        (is.foldl (fun best i =>
          if i.val < k then best else
            (List.finRange m).foldl (fun best j =>
              if j.val < k then best else
                let p := A[(i, j)]
                if p.isZero then best else
                  match best with
                  | none => some (i, j)
                  | some q => if p.size < A[q].size then some (i, j) else best) best) best) =
            some q → k ≤ q.1.val ∧ k ≤ q.2.val := by
    intro is
    induction is with
    | nil => intro best hbest q hq; exact hbest q hq
    | cons i is ih =>
        intro best hbest q hq
        simp only [List.foldl_cons] at hq
        apply ih _ ?_ q hq
        split
        · exact hbest
        · rename_i hi
          exact trailingCols_bounds A k i (by omega) (List.finRange m) best hbest
  exact hrows (List.finRange n) none (by simp) q h

private theorem trailingCols_nonzero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat)
    (i : Fin n) (js : List (Fin m)) (best : Option (Fin n × Fin m))
    (hbest : ∀ q, best = some q → A[q] ≠ 0) :
    ∀ q,
      (js.foldl (fun best j =>
        if j.val < k then best else
          let p := A[(i, j)]
          if p.isZero then best else
            match best with
            | none => some (i, j)
            | some q => if p.size < A[q].size then some (i, j) else best) best) = some q →
      A[q] ≠ 0 := by
  induction js generalizing best with
  | nil => exact hbest
  | cons j js ih =>
      simp only [List.foldl_cons]
      apply ih
      intro q hq
      split at hq
      · exact hbest q hq
      · split at hq
        · exact hbest q hq
        · rename_i hz
          have hp : A[(i, j)] ≠ 0 := by
            intro hp0
            rw [hp0] at hz
            have hzpos := (DensePoly.isZero_eq_false_iff (0 : DensePoly F)).mp
              (bool_eq_false hz)
            simp at hzpos
          cases hb : best
          · simp only [hb] at hq
            exact Option.some.inj hq ▸ hp
          · simp only [hb] at hq
            split at hq
            · exact Option.some.inj hq ▸ hp
            · exact hbest q (hb.trans hq)

theorem trailingMin_nonzero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat)
    {q : Fin n × Fin m} (h : trailingMin A k = some q) : A[q] ≠ 0 := by
  unfold trailingMin at h
  have hrows : ∀ (is : List (Fin n)) (best : Option (Fin n × Fin m)),
      (∀ q, best = some q → A[q] ≠ 0) →
      ∀ q,
        (is.foldl (fun best i =>
          if i.val < k then best else
            (List.finRange m).foldl (fun best j =>
              if j.val < k then best else
                let p := A[(i, j)]
                if p.isZero then best else
                  match best with
                  | none => some (i, j)
                  | some q => if p.size < A[q].size then some (i, j) else best) best) best) =
            some q → A[q] ≠ 0 := by
    intro is
    induction is with
    | nil => intro best hbest q hq; exact hbest q hq
    | cons i is ih =>
        intro best hbest q hq
        simp only [List.foldl_cons] at hq
        apply ih _ ?_ q hq
        by_cases hik : i.val < k
        · rw [ite_eq_left hik]
          exact hbest
        · rw [ite_eq_right hik]
          exact trailingCols_nonzero A k i (List.finRange m) best hbest
  exact hrows (List.finRange n) none (by simp) q h

theorem badBlock_none_dvd {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m)
    (ik : Fin n) (jk : Fin m) (h : badBlock A ik jk = none)
    (i : Fin n) (j : Fin m) (hi : ik.val < i.val) (hj : jk.val < j.val) :
    A[(ik, jk)] ∣ A[(i, j)] := by
  unfold badBlock at h
  have hrow := (List.findSome?_eq_none_iff.mp h) i (by simp)
  unfold badBlockRow at hrow
  have hcol := (List.findSome?_eq_none_iff.mp hrow) j (by simp)
  unfold badBlockEntry at hcol
  have hz : (A[(i, j)] % A[(ik, jk)]).isZero = true := by
    cases hb : (A[(i, j)] % A[(ik, jk)]).isZero <;> simp_all
  apply DensePoly.dvd_of_mod_eq_zero
  exact (DensePoly.size_eq_zero_iff _).mp ((DensePoly.isZero_eq_true_iff _).mp hz)

theorem clearColumnScan_drop_monic {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (ik : Fin n) (jk : Fin m)
    (s : LoopState F n m) (is : List (Fin n))
    (hp : s.work[(ik, jk)] ≠ 0)
    (hd : (clearColumnScan ik jk s is).dropped = true) :
    (clearColumnScan ik jk s is).state.work[(ik, jk)].Monic := by
  induction is generalizing s with
  | nil => simp [clearColumnScan] at hd
  | cons i is ih =>
      rw [clearColumnScan] at hd ⊢
      split
      · rename_i hik
        simp only [hik] at hd
        exact ih _ hp hd
      · rename_i hik
        simp only [hik] at hd
        dsimp only at hd ⊢
        split
        · rename_i hz
          simp only [hz] at hd
          exact ih _ hp hd
        · rename_i hz
          simp only [hz] at hd
          split
          · rename_i hm
            simp only [hm] at hd
            apply ih _
            · rw [addRow_keeps_pivot _ _ _ _ _ (Ne.symm hik)]
              exact hp
            · exact hd
          · rename_i hm
            rw [bezoutRows_pivot _ _ _ _ (Ne.symm hik)]
            rcases pairStep_pivot_shape s.work[(ik, jk)] s.work[(i, jk)] with hz | hm
            · exact False.elim (pairStep_pivot_ne_zero_left hp hz)
            · exact hm

theorem clearRowScan_drop_monic {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (ik : Fin n) (jk : Fin m)
    (s : LoopState F n m) (js : List (Fin m))
    (hp : s.work[(ik, jk)] ≠ 0)
    (hd : (clearRowScan ik jk s js).dropped = true) :
    (clearRowScan ik jk s js).state.work[(ik, jk)].Monic := by
  induction js generalizing s with
  | nil => simp [clearRowScan] at hd
  | cons j js ih =>
      rw [clearRowScan] at hd ⊢
      split
      · rename_i hjk
        simp only [hjk] at hd
        exact ih _ hp hd
      · rename_i hjk
        simp only [hjk] at hd
        dsimp only at hd ⊢
        split
        · rename_i hz
          simp only [hz] at hd
          exact ih _ hp hd
        · rename_i hz
          simp only [hz] at hd
          split
          · rename_i hm
            simp only [hm] at hd
            apply ih _
            · rw [addCol_keeps_pivot _ _ _ _ _ (Ne.symm hjk)]
              exact hp
            · exact hd
          · rename_i hm
            rw [bezoutCols_pivot _ _ _ _ (Ne.symm hjk)]
            rcases pairStep_pivot_shape s.work[(ik, jk)] s.work[(ik, j)] with hz | hm
            · exact False.elim (pairStep_pivot_ne_zero_left hp hz)
            · exact hm

/-- The canonical-shape facts established by one completed Smith stage. -/
structure StageShape {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (ik : Fin n) (jk : Fin m) : Prop where
  pivot_ne : s.work[(ik, jk)] ≠ 0
  pivot_monic : s.work[(ik, jk)].Monic
  column_zero : ∀ i : Fin n, i ≠ ik → s.work[(i, jk)] = 0
  row_zero : ∀ j : Fin m, j ≠ jk → s.work[(ik, j)] = 0
  trailing_dvd : ∀ (i : Fin n) (j : Fin m), ik.val < i.val → jk.val < j.val →
    s.work[(ik, jk)] ∣ s.work[(i, j)]

/-- Canonical shape of every pivot strictly before `k`. Besides isolation and
monicity, each earlier pivot divides the southeast block rooted at itself. -/
structure PrefixShape {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) (k : Nat) : Prop where
  le_rows : k ≤ n
  le_cols : k ≤ m
  monic : ∀ (d : Nat) (_hd : d < k) (hdn : d < n) (hdm : d < m),
    A[((⟨d, hdn⟩ : Fin n), (⟨d, hdm⟩ : Fin m))].Monic
  row_zero : ∀ (d : Nat) (_hd : d < k) (hdn : d < n) (_hdm : d < m)
    (j : Fin m), j.val ≠ d → A[((⟨d, hdn⟩ : Fin n), j)] = 0
  col_zero : ∀ (d : Nat) (_hd : d < k) (_hdn : d < n) (hdm : d < m)
    (i : Fin n), i.val ≠ d → A[(i, (⟨d, hdm⟩ : Fin m))] = 0
  future_dvd : ∀ (d : Nat) (_hd : d < k) (hdn : d < n) (hdm : d < m)
    (i : Fin n) (j : Fin m), d ≤ i.val → d ≤ j.val →
      A[((⟨d, hdn⟩ : Fin n), (⟨d, hdm⟩ : Fin m))] ∣ A[(i, j)]

theorem prefixShape_zero {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) : PrefixShape A 0 := by
  refine ⟨Nat.zero_le n, Nat.zero_le m, ?_, ?_, ?_, ?_⟩ <;>
    intro d hd <;> omega

private theorem poly_dvd_add {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {d a b : DensePoly F} (ha : d ∣ a) (hb : d ∣ b) : d ∣ a + b := by
  rcases ha with ⟨x, rfl⟩
  rcases hb with ⟨y, rfl⟩
  refine ⟨x + y, ?_⟩
  rw [DensePoly.mul_add_right_poly]

private theorem poly_dvd_mul_left {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {d a : DensePoly F} (c : DensePoly F) (ha : d ∣ a) :
    d ∣ c * a := by
  rcases ha with ⟨x, rfl⟩
  refine ⟨c * x, ?_⟩
  rw [← DensePoly.mul_assoc_poly, DensePoly.mul_comm_poly c d,
    DensePoly.mul_assoc_poly]

theorem prefixShape_rowScale {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m} {k : Nat}
    (h : PrefixShape A k) (i : Fin n) (c : DensePoly F) (hik : k ≤ i.val) :
    PrefixShape (A.rowScale i c) k := by
  refine ⟨h.le_rows, h.le_cols, ?_, ?_, ?_, ?_⟩
  · intro d hd hdn hdm
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale, ite_eq_right]
    · simpa only [Matrix.getElem_pair_eq_nested] using h.monic d hd hdn hdm
    · intro heq
      have heq' : d = i.val := by simpa using congrArg Fin.val heq
      omega
  · intro d hd hdn hdm j hj
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale, ite_eq_right]
    · simpa only [Matrix.getElem_pair_eq_nested] using h.row_zero d hd hdn hdm j hj
    · intro heq
      have heq' : d = i.val := by simpa using congrArg Fin.val heq
      omega
  · intro d hd hdn hdm r hr
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale]
    by_cases hri : r = i
    · rw [ite_eq_left hri]
      have hz := h.col_zero d hd hdn hdm i (by omega)
      rw [Matrix.getElem_pair_eq_nested] at hz
      rw [hz]
      exact Lean.Grind.Semiring.mul_zero c
    · rw [ite_eq_right hri]
      simpa only [Matrix.getElem_pair_eq_nested] using h.col_zero d hd hdn hdm r hr
  · intro d hd hdn hdm r j hdr hdj
    have hdi : (⟨d, hdn⟩ : Fin n) ≠ i := by
      intro heq
      have heq' : d = i.val := by simpa using congrArg Fin.val heq
      omega
    have hdiag : (A.rowScale i c)[
        ((⟨d, hdn⟩ : Fin n), (⟨d, hdm⟩ : Fin m))] =
        A[((⟨d, hdn⟩ : Fin n), (⟨d, hdm⟩ : Fin m))] := by
      rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale, ite_eq_right hdi]
      exact (Matrix.getElem_pair_eq_nested A ⟨d, hdn⟩ ⟨d, hdm⟩).symm
    rw [hdiag]
    rw [Matrix.getElem_pair_eq_nested A (⟨d, hdn⟩ : Fin n) (⟨d, hdm⟩ : Fin m),
      Matrix.getElem_pair_eq_nested (A.rowScale i c) r j]
    rw [Matrix.getElem_rowScale]
    by_cases hri : r = i
    · rw [ite_eq_left hri]
      apply poly_dvd_mul_left c
      simpa only [Matrix.getElem_pair_eq_nested] using
        h.future_dvd d hd hdn hdm i j (by omega) hdj
    · rw [ite_eq_right hri]
      simpa only [Matrix.getElem_pair_eq_nested] using
        h.future_dvd d hd hdn hdm r j hdr hdj

theorem prefixShape_rowAdd {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m} {k : Nat}
    (h : PrefixShape A k) (src dst : Fin n) (c : DensePoly F)
    (hsrc : k ≤ src.val) (hdst : k ≤ dst.val) :
    PrefixShape (A.rowAdd src dst c) k := by
  refine ⟨h.le_rows, h.le_cols, ?_, ?_, ?_, ?_⟩
  · intro d hd hdn hdm
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd, ite_eq_right]
    · simpa only [Matrix.getElem_pair_eq_nested] using h.monic d hd hdn hdm
    · intro heq
      have heq' : d = dst.val := by simpa using congrArg Fin.val heq
      omega
  · intro d hd hdn hdm j hj
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd, ite_eq_right]
    · simpa only [Matrix.getElem_pair_eq_nested] using h.row_zero d hd hdn hdm j hj
    · intro heq
      have heq' : d = dst.val := by simpa using congrArg Fin.val heq
      omega
  · intro d hd hdn hdm r hr
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd]
    by_cases hrd : r = dst
    · rw [ite_eq_left hrd]
      have hzDst := h.col_zero d hd hdn hdm dst (by omega)
      have hzSrc := h.col_zero d hd hdn hdm src (by omega)
      rw [Matrix.getElem_pair_eq_nested] at hzDst hzSrc
      rw [hzDst, hzSrc]
      grind
    · rw [ite_eq_right hrd]
      simpa only [Matrix.getElem_pair_eq_nested] using h.col_zero d hd hdn hdm r hr
  · intro d hd hdn hdm r j hdr hdj
    have hdd : (⟨d, hdn⟩ : Fin n) ≠ dst := by
      intro heq
      have heq' : d = dst.val := by simpa using congrArg Fin.val heq
      omega
    have hdiag : (A.rowAdd src dst c)[
        ((⟨d, hdn⟩ : Fin n), (⟨d, hdm⟩ : Fin m))] =
        A[((⟨d, hdn⟩ : Fin n), (⟨d, hdm⟩ : Fin m))] := by
      rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd, ite_eq_right hdd]
      exact (Matrix.getElem_pair_eq_nested A ⟨d, hdn⟩ ⟨d, hdm⟩).symm
    rw [hdiag]
    rw [Matrix.getElem_pair_eq_nested A (⟨d, hdn⟩ : Fin n) (⟨d, hdm⟩ : Fin m),
      Matrix.getElem_pair_eq_nested (A.rowAdd src dst c) r j,
      Matrix.getElem_rowAdd]
    by_cases hrd : r = dst
    · rw [ite_eq_left hrd]
      apply poly_dvd_add
      · simpa only [Matrix.getElem_pair_eq_nested] using
          h.future_dvd d hd hdn hdm dst j (by omega) hdj
      · apply poly_dvd_mul_left c
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.future_dvd d hd hdn hdm src j (by omega) hdj
    · rw [ite_eq_right hrd]
      simpa only [Matrix.getElem_pair_eq_nested] using
        h.future_dvd d hd hdn hdm r j hdr hdj

theorem prefixShape_rowSwap {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m} {k : Nat}
    (h : PrefixShape A k) (a b : Fin n) (ha : k ≤ a.val) (hb : k ≤ b.val) :
    PrefixShape (A.rowSwap a b) k := by
  refine ⟨h.le_rows, h.le_cols, ?_, ?_, ?_, ?_⟩
  · intro d hd hdn hdm
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowSwap]
    have hda : (⟨d, hdn⟩ : Fin n) ≠ a := by
      intro heq
      have heq' : d = a.val := by simpa using congrArg Fin.val heq
      omega
    have hdb : (⟨d, hdn⟩ : Fin n) ≠ b := by
      intro heq
      have heq' : d = b.val := by simpa using congrArg Fin.val heq
      omega
    rw [ite_eq_right hda, ite_eq_right hdb]
    simpa only [Matrix.getElem_pair_eq_nested] using h.monic d hd hdn hdm
  · intro d hd hdn hdm j hj
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowSwap]
    have hda : (⟨d, hdn⟩ : Fin n) ≠ a := by
      intro heq
      have heq' : d = a.val := by simpa using congrArg Fin.val heq
      omega
    have hdb : (⟨d, hdn⟩ : Fin n) ≠ b := by
      intro heq
      have heq' : d = b.val := by simpa using congrArg Fin.val heq
      omega
    rw [ite_eq_right hda, ite_eq_right hdb]
    simpa only [Matrix.getElem_pair_eq_nested] using h.row_zero d hd hdn hdm j hj
  · intro d hd hdn hdm r hr
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowSwap]
    by_cases hra : r = a
    · rw [ite_eq_left hra]
      split
      · simpa only [Matrix.getElem_pair_eq_nested] using
          h.col_zero d hd hdn hdm a (by omega)
      · simpa only [Matrix.getElem_pair_eq_nested] using
          h.col_zero d hd hdn hdm b (by omega)
    · rw [ite_eq_right hra]
      by_cases hrb : r = b
      · rw [ite_eq_left hrb]
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.col_zero d hd hdn hdm a (by omega)
      · rw [ite_eq_right hrb]
        simpa only [Matrix.getElem_pair_eq_nested] using h.col_zero d hd hdn hdm r hr
  · intro d hd hdn hdm r j hdr hdj
    have hda : (⟨d, hdn⟩ : Fin n) ≠ a := by
      intro heq
      have heq' : d = a.val := by simpa using congrArg Fin.val heq
      omega
    have hdb : (⟨d, hdn⟩ : Fin n) ≠ b := by
      intro heq
      have heq' : d = b.val := by simpa using congrArg Fin.val heq
      omega
    have hdiag : (A.rowSwap a b)[
        ((⟨d, hdn⟩ : Fin n), (⟨d, hdm⟩ : Fin m))] =
        A[((⟨d, hdn⟩ : Fin n), (⟨d, hdm⟩ : Fin m))] := by
      rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowSwap,
        ite_eq_right hda, ite_eq_right hdb]
      exact (Matrix.getElem_pair_eq_nested A ⟨d, hdn⟩ ⟨d, hdm⟩).symm
    rw [hdiag]
    rw [Matrix.getElem_pair_eq_nested A (⟨d, hdn⟩ : Fin n) (⟨d, hdm⟩ : Fin m),
      Matrix.getElem_pair_eq_nested (A.rowSwap a b) r j, Matrix.getElem_rowSwap]
    by_cases hra : r = a
    · rw [ite_eq_left hra]
      split
      · simpa only [Matrix.getElem_pair_eq_nested] using
          h.future_dvd d hd hdn hdm a j (by omega) hdj
      · simpa only [Matrix.getElem_pair_eq_nested] using
          h.future_dvd d hd hdn hdm b j (by omega) hdj
    · rw [ite_eq_right hra]
      by_cases hrb : r = b
      · rw [ite_eq_left hrb]
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.future_dvd d hd hdn hdm a j (by omega) hdj
      · rw [ite_eq_right hrb]
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.future_dvd d hd hdn hdm r j hdr hdj

theorem prefixShape_transpose {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m} {k : Nat}
    (h : PrefixShape A k) : PrefixShape A.transpose k := by
  refine ⟨h.le_cols, h.le_rows, ?_, ?_, ?_, ?_⟩
  · intro d hd hdm hdn
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_transpose,
      ← Matrix.getElem_pair_eq_nested]
    exact h.monic d hd hdn hdm
  · intro d hd hdm hdn i hi
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_transpose,
      ← Matrix.getElem_pair_eq_nested]
    exact h.col_zero d hd hdn hdm i hi
  · intro d hd hdm hdn j hj
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_transpose,
      ← Matrix.getElem_pair_eq_nested]
    exact h.row_zero d hd hdn hdm j hj
  · intro d hd hdm hdn j i hdj hdi
    rw [Matrix.getElem_pair_eq_nested A.transpose (⟨d, hdm⟩ : Fin m)
        (⟨d, hdn⟩ : Fin n), Matrix.getElem_transpose,
      ← Matrix.getElem_pair_eq_nested A (⟨d, hdn⟩ : Fin n) (⟨d, hdm⟩ : Fin m),
      Matrix.getElem_pair_eq_nested A.transpose j i, Matrix.getElem_transpose,
      ← Matrix.getElem_pair_eq_nested A i j]
    exact h.future_dvd d hd hdn hdm i j hdi hdj

theorem prefixShape_colScale {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m} {k : Nat}
    (h : PrefixShape A k) (j : Fin m) (c : DensePoly F) (hjk : k ≤ j.val) :
    PrefixShape (A.colScale j c) k := by
  have ht := prefixShape_rowScale (prefixShape_transpose h) j c hjk
  have hb := prefixShape_transpose ht
  have heq : (A.transpose.rowScale j c).transpose = A.colScale j c := by
    rw [← Matrix.transpose_colScale, Matrix.transpose_transpose]
  rw [heq] at hb
  exact hb

theorem prefixShape_colAdd {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m} {k : Nat}
    (h : PrefixShape A k) (src dst : Fin m) (c : DensePoly F)
    (hsrc : k ≤ src.val) (hdst : k ≤ dst.val) :
    PrefixShape (A.colAdd src dst c) k := by
  have ht := prefixShape_rowAdd (prefixShape_transpose h) src dst c hsrc hdst
  have hb := prefixShape_transpose ht
  have heq : (A.transpose.rowAdd src dst c).transpose = A.colAdd src dst c := by
    rw [← Matrix.transpose_colAdd, Matrix.transpose_transpose]
  rw [heq] at hb
  exact hb

theorem prefixShape_colSwap {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m} {k : Nat}
    (h : PrefixShape A k) (a b : Fin m) (ha : k ≤ a.val) (hb : k ≤ b.val) :
    PrefixShape (A.colSwap a b) k := by
  have ht := prefixShape_rowSwap (prefixShape_transpose h) a b ha hb
  have hback := prefixShape_transpose ht
  have heq : (A.transpose.rowSwap a b).transpose = A.colSwap a b := by
    rw [← Matrix.transpose_colSwap, Matrix.transpose_transpose]
  rw [heq] at hback
  exact hback

theorem prefixShape_pairRows {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m} {k : Nat}
    (h : PrefixShape A k) (a b : Fin n) (E : Matrix (DensePoly F) 2 2)
    (ha : k ≤ a.val) (hb : k ≤ b.val) (hab : a ≠ b) :
    PrefixShape (pairRows A a b E) k := by
  refine ⟨h.le_rows, h.le_cols, ?_, ?_, ?_, ?_⟩
  · intro d hd hdn hdm
    have hda : (⟨d, hdn⟩ : Fin n) ≠ a := by
      intro heq
      have heq' : d = a.val := by simpa using congrArg Fin.val heq
      omega
    have hdb : (⟨d, hdn⟩ : Fin n) ≠ b := by
      intro heq
      have heq' : d = b.val := by simpa using congrArg Fin.val heq
      omega
    rw [Matrix.getElem_pair_eq_nested,
      pairRows_other A a b ⟨d, hdn⟩ E hda hdb]
    simpa only [Matrix.getElem_pair_eq_nested] using h.monic d hd hdn hdm
  · intro d hd hdn hdm j hj
    have hda : (⟨d, hdn⟩ : Fin n) ≠ a := by
      intro heq
      have heq' : d = a.val := by simpa using congrArg Fin.val heq
      omega
    have hdb : (⟨d, hdn⟩ : Fin n) ≠ b := by
      intro heq
      have heq' : d = b.val := by simpa using congrArg Fin.val heq
      omega
    rw [Matrix.getElem_pair_eq_nested,
      pairRows_other A a b ⟨d, hdn⟩ E hda hdb]
    simpa only [Matrix.getElem_pair_eq_nested] using h.row_zero d hd hdn hdm j hj
  · intro d hd hdn hdm r hr
    rw [Matrix.getElem_pair_eq_nested]
    by_cases hra : r = a
    · subst r
      rw [pairRows_left A a b E hab]
      have hza := h.col_zero d hd hdn hdm a (by omega)
      have hzb := h.col_zero d hd hdn hdm b (by omega)
      rw [Matrix.getElem_pair_eq_nested] at hza hzb
      rw [hza, hzb]
      grind
    · by_cases hrb : r = b
      · subst r
        rw [pairRows_right]
        have hza := h.col_zero d hd hdn hdm a (by omega)
        have hzb := h.col_zero d hd hdn hdm b (by omega)
        rw [Matrix.getElem_pair_eq_nested] at hza hzb
        rw [hza, hzb]
        grind
      · rw [pairRows_other A a b r E hra hrb]
        simpa only [Matrix.getElem_pair_eq_nested] using h.col_zero d hd hdn hdm r hr
  · intro d hd hdn hdm r j hdr hdj
    have hda : (⟨d, hdn⟩ : Fin n) ≠ a := by
      intro heq
      have heq' : d = a.val := by simpa using congrArg Fin.val heq
      omega
    have hdb : (⟨d, hdn⟩ : Fin n) ≠ b := by
      intro heq
      have heq' : d = b.val := by simpa using congrArg Fin.val heq
      omega
    have hdiag : (pairRows A a b E)[
        ((⟨d, hdn⟩ : Fin n), (⟨d, hdm⟩ : Fin m))] =
        A[((⟨d, hdn⟩ : Fin n), (⟨d, hdm⟩ : Fin m))] := by
      rw [Matrix.getElem_pair_eq_nested,
        pairRows_other A a b ⟨d, hdn⟩ E hda hdb]
      exact (Matrix.getElem_pair_eq_nested A ⟨d, hdn⟩ ⟨d, hdm⟩).symm
    rw [hdiag, Matrix.getElem_pair_eq_nested A ⟨d, hdn⟩ ⟨d, hdm⟩,
      Matrix.getElem_pair_eq_nested (pairRows A a b E) r j]
    by_cases hra : r = a
    · subst r
      rw [pairRows_left A a b E hab]
      apply poly_dvd_add
      · apply poly_dvd_mul_left
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.future_dvd d hd hdn hdm a j (by omega) hdj
      · apply poly_dvd_mul_left
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.future_dvd d hd hdn hdm b j (by omega) hdj
    · by_cases hrb : r = b
      · subst r
        rw [pairRows_right]
        apply poly_dvd_add
        · apply poly_dvd_mul_left
          simpa only [Matrix.getElem_pair_eq_nested] using
            h.future_dvd d hd hdn hdm a j (by omega) hdj
        · apply poly_dvd_mul_left
          simpa only [Matrix.getElem_pair_eq_nested] using
            h.future_dvd d hd hdn hdm b j (by omega) hdj
      · rw [pairRows_other A a b r E hra hrb]
        simpa only [Matrix.getElem_pair_eq_nested] using
          h.future_dvd d hd hdn hdm r j hdr hdj

theorem transpose_pairCols {R : Type u} [Zero R] [Add R] [Mul R]
    {n m : Nat} (A : Matrix R n m) (i j : Fin m) (E : Matrix R 2 2)
    (hij : i ≠ j) :
    (pairCols A i j E).transpose = pairRows A.transpose i j E := by
  apply Matrix.ext_getElem
  intro r c
  rw [Matrix.getElem_transpose]
  by_cases hri : r = i
  · subst r
    rw [pairCols_left A i j E hij, pairRows_left A.transpose i j E hij]
    simp only [Matrix.getElem_transpose]
  · by_cases hrj : r = j
    · subst r
      rw [pairCols_right, pairRows_right]
      simp only [Matrix.getElem_transpose]
    · rw [pairCols_other A i j r E hri hrj,
        pairRows_other A.transpose i j r E hri hrj]
      simp only [Matrix.getElem_transpose]

theorem prefixShape_pairCols {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m} {k : Nat}
    (h : PrefixShape A k) (a b : Fin m) (E : Matrix (DensePoly F) 2 2)
    (ha : k ≤ a.val) (hb : k ≤ b.val) (hab : a ≠ b) :
    PrefixShape (pairCols A a b E) k := by
  have ht := prefixShape_pairRows (prefixShape_transpose h) a b E ha hb hab
  have hback := prefixShape_transpose ht
  have heq : (pairRows A.transpose a b E).transpose = pairCols A a b E := by
    rw [← transpose_pairCols A a b E hab, Matrix.transpose_transpose]
  rw [heq] at hback
  exact hback

theorem prefixShape_swapRows {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} {k : Nat}
    (h : PrefixShape s.work k) (a b : Fin n) (ha : k ≤ a.val) (hb : k ≤ b.val) :
    PrefixShape (swapRows s a b).work k := prefixShape_rowSwap h a b ha hb

theorem prefixShape_swapCols {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} {k : Nat}
    (h : PrefixShape s.work k) (a b : Fin m) (ha : k ≤ a.val) (hb : k ≤ b.val) :
    PrefixShape (swapCols s a b).work k := prefixShape_colSwap h a b ha hb

theorem prefixShape_scaleRowState {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} {k : Nat}
    (h : PrefixShape s.work k) (i : Fin n) (c cinv : DensePoly F) (hi : k ≤ i.val) :
    PrefixShape (scaleRow s i c cinv).work k := prefixShape_rowScale h i c hi

theorem prefixShape_addRowState {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} {k : Nat}
    (h : PrefixShape s.work k) (src dst : Fin n) (c : DensePoly F)
    (hsrc : k ≤ src.val) (hdst : k ≤ dst.val) :
    PrefixShape (addRow s src dst c).work k :=
  prefixShape_rowAdd h src dst c hsrc hdst

theorem prefixShape_addColState {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} {k : Nat}
    (h : PrefixShape s.work k) (src dst : Fin m) (c : DensePoly F)
    (hsrc : k ≤ src.val) (hdst : k ≤ dst.val) :
    PrefixShape (addCol s src dst c).work k :=
  prefixShape_colAdd h src dst c hsrc hdst

theorem prefixShape_bezoutRows {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} {k : Nat}
    (h : PrefixShape s.work k) (a b : Fin n) (e : PairStep F)
    (ha : k ≤ a.val) (hb : k ≤ b.val) (hab : a ≠ b) :
    PrefixShape (bezoutRows s a b e).work k :=
  prefixShape_pairRows h a b e.forward ha hb hab

theorem prefixShape_bezoutCols {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} {k : Nat}
    (h : PrefixShape s.work k) (a b : Fin m) (e : PairStep F)
    (ha : k ≤ a.val) (hb : k ≤ b.val) (hab : a ≠ b) :
    PrefixShape (bezoutCols s a b e).work k :=
  prefixShape_pairCols h a b e.forward ha hb hab

theorem prefixShape_clearColumnScan {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (ik : Fin n) (jk : Fin m) {k : Nat}
    (hik : ik.val = k) (hjk : jk.val = k) (is : List (Fin n))
    {s : LoopState F n m} (h : PrefixShape s.work k) :
    PrefixShape (clearColumnScan ik jk s is).state.work k := by
  induction is generalizing s with
  | nil => exact h
  | cons i is ih =>
      rw [clearColumnScan]
      split
      · exact ih h
      · rename_i hi
        dsimp only
        split
        · exact ih h
        · rename_i hz
          have hki : k ≤ i.val := by
            by_cases hki : k ≤ i.val
            · exact hki
            · exfalso
              have hid : i.val < k := by omega
              have hdn : i.val < n := i.isLt
              have hdm : i.val < m := by omega
              have hentry := h.row_zero i.val hid hdn hdm jk (by omega)
              rw [hentry] at hz
              have hzpos := (DensePoly.isZero_eq_false_iff (0 : DensePoly F)).mp
                (bool_eq_false hz)
              rw [DensePoly.size_zero] at hzpos
              omega
          split
          · exact ih (prefixShape_addRowState h ik i _ (by omega) hki)
          · exact prefixShape_bezoutRows h ik i _ (by omega) hki (Ne.symm hi)

theorem prefixShape_clearRowScan {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (ik : Fin n) (jk : Fin m) {k : Nat}
    (hik : ik.val = k) (hjk : jk.val = k) (js : List (Fin m))
    {s : LoopState F n m} (h : PrefixShape s.work k) :
    PrefixShape (clearRowScan ik jk s js).state.work k := by
  induction js generalizing s with
  | nil => exact h
  | cons j js ih =>
      rw [clearRowScan]
      split
      · exact ih h
      · rename_i hj
        dsimp only
        split
        · exact ih h
        · rename_i hz
          have hkj : k ≤ j.val := by
            by_cases hkj : k ≤ j.val
            · exact hkj
            · exfalso
              have hjd : j.val < k := by omega
              have hdn : j.val < n := by omega
              have hdm : j.val < m := j.isLt
              have hentry := h.col_zero j.val hjd hdn hdm ik (by omega)
              rw [hentry] at hz
              have hzpos := (DensePoly.isZero_eq_false_iff (0 : DensePoly F)).mp
                (bool_eq_false hz)
              rw [DensePoly.size_zero] at hzpos
              omega
          split
          · exact ih (prefixShape_addColState h jk j _ (by omega) hkj)
          · exact prefixShape_bezoutCols h jk j _ (by omega) hkj (Ne.symm hj)

theorem prefixShape_normalizePivot {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} {k : Nat}
    (hkN : k < n) (hkM : k < m) (h : PrefixShape s.work k) :
    PrefixShape (normalizePivot s k hkN hkM).work k := by
  unfold normalizePivot
  exact prefixShape_scaleRowState h (⟨k, hkN⟩ : Fin n) _ _ (Nat.le_refl k)

theorem prefixShape_blockStep {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} {k : Nat}
    (h : PrefixShape s.work k) (ik i : Fin n) (jk j : Fin m)
    (hik : ik.val = k) (hjk : jk.val = k) (hi : k ≤ i.val) (hj : k ≤ j.val)
    (hjne : jk ≠ j) : PrefixShape (blockStep s ik i jk j).work k := by
  unfold blockStep
  apply prefixShape_bezoutCols
  · exact prefixShape_addRowState h i ik polyOne hi (by omega)
  · omega
  · exact hj
  · exact hjne

theorem prefixShape_smithStage {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (ik : Fin n) (jk : Fin m)
    {k : Nat} (hik : ik.val = k) (hjk : jk.val = k)
    (hp : s.work[(ik, jk)] ≠ 0) (h : PrefixShape s.work k) :
    PrefixShape (smithStage s ik jk hp).work k := by
  induction s, hp using smithStage.induct ik jk with
  | case1 s hp col hc ih =>
      rw [smithStage]
      change (clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      simp [hc]
      exact ih (prefixShape_clearColumnScan ik jk hik hjk (List.finRange n) h)
  | case2 s hp col hc row hr ih =>
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change (clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
        (List.finRange m)).dropped = true at hr
      simp [hc, hr]
      exact ih (prefixShape_clearRowScan ik jk hik hjk (List.finRange m)
        (prefixShape_clearColumnScan ik jk hik hjk (List.finRange n) h))
  | case3 s hp col hc row hr hb =>
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change ¬(clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
        (List.finRange m)).dropped = true at hr
      change badBlock
        (clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
          (List.finRange m)).state.work ik jk = none at hb
      simp [hc, hr]
      split
      · exact prefixShape_clearRowScan ik jk hik hjk (List.finRange m)
          (prefixShape_clearColumnScan ik jk hik hjk (List.finRange n) h)
      · simp_all
  | case4 s hp col hc row hr q hb hc0 hr0 hq hki hkj hpCol hcol0 hcol hrow
      hnot hpRow hpBlock ih =>
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change ¬(clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
        (List.finRange m)).dropped = true at hr
      change badBlock
        (clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
          (List.finRange m)).state.work ik jk = some q at hb
      simp [hc, hr]
      split
      · simp_all
      · rename_i q' hb'
        have hqq : q' = q := by simp_all
        subst q'
        apply ih
        apply prefixShape_blockStep
        · exact prefixShape_clearRowScan ik jk hik hjk (List.finRange m)
            (prefixShape_clearColumnScan ik jk hik hjk (List.finRange n) h)
        · exact hik
        · exact hjk
        · omega
        · omega
        · exact hkj

theorem prefixShape_smithStageSafe {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (ik : Fin n) (jk : Fin m)
    {k : Nat} (hik : ik.val = k) (hjk : jk.val = k) (h : PrefixShape s.work k) :
    PrefixShape (smithStageSafe s ik jk).work k := by
  unfold smithStageSafe
  split
  · exact h
  · exact prefixShape_smithStage _ _ _ hik hjk _ h

theorem PrefixShape.extend {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} {k : Nat}
    (h : PrefixShape s.work k) (ik : Fin n) (jk : Fin m)
    (hik : ik.val = k) (hjk : jk.val = k) (hs : StageShape s ik jk) :
    PrefixShape s.work (k + 1) := by
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro d hd hdn hdm
    by_cases hdk : d < k
    · exact h.monic d hdk hdn hdm
    · have hdeq : d = k := by omega
      subst d
      have hin : (⟨k, hdn⟩ : Fin n) = ik := Fin.ext (by simpa using hik.symm)
      have him : (⟨k, hdm⟩ : Fin m) = jk := Fin.ext (by simpa using hjk.symm)
      simpa [hin, him] using hs.pivot_monic
  · intro d hd hdn hdm j hj
    by_cases hdk : d < k
    · exact h.row_zero d hdk hdn hdm j hj
    · have hdeq : d = k := by omega
      subst d
      have hin : (⟨k, hdn⟩ : Fin n) = ik := Fin.ext (by simpa using hik.symm)
      have hjne : j ≠ jk := by
        intro heq
        apply hj
        simpa [heq] using hjk
      simpa [hin] using hs.row_zero j hjne
  · intro d hd hdn hdm i hi
    by_cases hdk : d < k
    · exact h.col_zero d hdk hdn hdm i hi
    · have hdeq : d = k := by omega
      subst d
      have him : (⟨k, hdm⟩ : Fin m) = jk := Fin.ext (by simpa using hjk.symm)
      have hine : i ≠ ik := by
        intro heq
        apply hi
        simpa [heq] using hik
      simpa [him] using hs.column_zero i hine
  · intro d hd hdn hdm i j hdi hdj
    by_cases hdk : d < k
    · exact h.future_dvd d hdk hdn hdm i j hdi hdj
    · have hdeq : d = k := by omega
      subst d
      have hin : (⟨k, hdn⟩ : Fin n) = ik := Fin.ext (by simpa using hik.symm)
      have him : (⟨k, hdm⟩ : Fin m) = jk := Fin.ext (by simpa using hjk.symm)
      rw [hin, him]
      by_cases hiEq : i = ik
      · subst i
        by_cases hjEq : j = jk
        · subst j
          exact ⟨1, (DensePoly.mul_one_right_poly _).symm⟩
        · rw [hs.row_zero j hjEq]
          exact ⟨0, (Lean.Grind.Semiring.mul_zero _).symm⟩
      · by_cases hjEq : j = jk
        · subst j
          rw [hs.column_zero i hiEq]
          exact ⟨0, (Lean.Grind.Semiring.mul_zero _).symm⟩
        · apply hs.trailing_dvd i j
          · have hine : i.val ≠ k := by
              intro heq
              exact hiEq (Fin.ext (by omega))
            omega
          · have hjne : j.val ≠ k := by
              intro heq
              exact hjEq (Fin.ext (by omega))
            omega
end Hex.PolyMatrix
