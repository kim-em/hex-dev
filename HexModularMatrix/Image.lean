/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ring
public import HexDeterminant.Laplace
public import HexMatrix.ElementaryAlgebra

public section

/-! Modular determinants by elimination below each pivot. -/

namespace Hex.Matrix

variable {m : Nat} [ZMod64.Bounds m]

namespace DetImage

/-- A unit in the first column, with its checked inverse. -/
structure Pivot (A : Matrix (ZMod64 m) (n + 1) (n + 1)) where
  row : Fin (n + 1)
  inverse : ZMod64 m
  mul_inverse : A[(row, (0 : Fin (n + 1)))] * inverse = 1

/-- Search the whole pivot column for a unit, in row order. -/
def pivot? (A : Matrix (ZMod64 m) (n + 1) (n + 1)) : Option (Pivot A) :=
  Fin.foldl (n + 1) (fun found i =>
    match found with
    | some p => some p
    | none =>
      match h : ZMod64.inv? A[(i, (0 : Fin (n + 1)))] with
      | none => none
      | some b => some ⟨i, b, ZMod64.inv?_eq_some h⟩) none

/-- Eliminate one entry below the first pivot. -/
@[expose]
def clearRow (A : Matrix (ZMod64 m) (n + 1) (n + 1))
    (b : ZMod64 m) (i : Fin n) : Matrix (ZMod64 m) (n + 1) (n + 1) :=
  A.rowAdd 0 i.succ (-A[(i.succ, (0 : Fin (n + 1)))] * b)

/-- Eliminate below the first pivot using a linear fold over the matrix buffer. -/
@[expose]
def clear (A : Matrix (ZMod64 m) (n + 1) (n + 1)) (b : ZMod64 m) :=
  Fin.foldl n (fun A i => clearRow A b i) A

private theorem clearRow_pivot (A : Matrix (ZMod64 m) (n + 1) (n + 1))
    (b : ZMod64 m) (i : Fin n) : (clearRow A b i)[(0 : Fin (n + 1))][(0 : Fin (n + 1))] = A[(0 : Fin (n + 1))][(0 : Fin (n + 1))] := by
  simp only [clearRow, getElem_rowAdd]
  simp [Fin.ext_iff]

private theorem clearRows_pivot (xs : List (Fin n))
    (A : Matrix (ZMod64 m) (n + 1) (n + 1)) (b : ZMod64 m) :
    (xs.foldl (fun A i => clearRow A b i) A)[(0 : Fin (n + 1))][(0 : Fin (n + 1))] = A[(0 : Fin (n + 1))][(0 : Fin (n + 1))] := by
  induction xs generalizing A with
  | nil => rfl
  | cons i xs ih => rw [List.foldl_cons, ih, clearRow_pivot]

private theorem clearRows_det (xs : List (Fin n))
    (A : Matrix (ZMod64 m) (n + 1) (n + 1)) (b : ZMod64 m) :
    det (xs.foldl (fun A i => clearRow A b i) A) = det A := by
  induction xs generalizing A with
  | nil => rfl
  | cons i xs ih =>
    rw [List.foldl_cons, ih, clearRow, det_rowAdd]
    simp [Fin.ext_iff]

private theorem clearRows_column (xs : List (Fin n))
    (A : Matrix (ZMod64 m) (n + 1) (n + 1)) (b : ZMod64 m)
    (hb : A[(0 : Fin (n + 1))][(0 : Fin (n + 1))] * b = 1) (i : Fin n) :
    (xs.foldl (fun A i => clearRow A b i) A)[i.succ][(0 : Fin (n + 1))] =
      if i ∈ xs then (0 : ZMod64 m) else A[i.succ][(0 : Fin (n + 1))] := by
  induction xs generalizing A with
  | nil => simp
  | cons j xs ih =>
    rw [List.foldl_cons, ih _ (by rw [clearRow_pivot]; exact hb)]
    by_cases hi : i ∈ xs
    · simp [hi]
    · simp only [hi, ↓reduceIte, List.mem_cons]
      simp only [clearRow, getElem_rowAdd, getElem_pair_eq_nested]
      by_cases hij : i = j
      · subst j
        simp only [↓reduceIte, true_or]
        grind only
      · simp [hij]

/-- Elimination preserves the determinant and pivot, and clears its column. -/
theorem clear_spec (A : Matrix (ZMod64 m) (n + 1) (n + 1))
    (b : ZMod64 m) (hb : A[(0 : Fin (n + 1))][(0 : Fin (n + 1))] * b = 1) :
    det (clear A b) = det A ∧ (clear A b)[(0 : Fin (n + 1))][(0 : Fin (n + 1))] = A[(0 : Fin (n + 1))][(0 : Fin (n + 1))] ∧
      ∀ i : Fin n, (clear A b)[i.succ][(0 : Fin (n + 1))] = 0 := by
  simp only [clear, Fin.foldl_eq_finRange_foldl]
  exact ⟨clearRows_det _ A b, clearRows_pivot _ A b,
    fun i => by simpa using clearRows_column (List.finRange n) A b hb i⟩

/-- A cleared first column factors the determinant into pivot and trailing minor. -/
theorem det_column (A : Matrix (ZMod64 m) (n + 1) (n + 1))
    (hz : ∀ i : Fin n, A[i.succ][(0 : Fin (n + 1))] = 0) :
    det A = A[(0 : Fin (n + 1))][(0 : Fin (n + 1))] * det (A.deleteRowCol 0 0) := by
  rw [det_eq_finFoldl_laplace_col A 0, Fin.foldl_succ]
  have hs : ∀ i : Fin n, A[i.succ][(0 : Fin (n + 1))] * cofactor A i.succ 0 = 0 := by
    intro i
    rw [hz i]
    grind only
  simp only [Fin.foldl_eq_finRange_foldl]
  rw [List.foldl_add_eq_self (List.finRange n)
    (fun i => A[i.succ][(0 : Fin (n + 1))] * cofactor A i.succ 0)
    ((0 : ZMod64 m) + A[(0 : Fin (n + 1))][(0 : Fin (n + 1))] * cofactor A 0 0) (fun i _ => hs i)]
  simp [cofactor, cofactorSign]

end DetImage

/-- Compute a modular determinant by elimination below unit pivots. An all-zero
pivot column returns `some 0`; a nonzero column without a unit returns `none`.
No primality assumption is required. -/
@[expose]
def detMod? : {n : Nat} → Matrix (ZMod64 m) n n → Option (ZMod64 m)
  | 0, _ => some 1
  | n + 1, A =>
    if ∀ i : Fin (n + 1), A[(i, (0 : Fin (n + 1)))] = 0 then some 0
    else
      match DetImage.pivot? A with
      | none => none
      | some p =>
        let B := A.rowSwap 0 p.row
        let a := B[((0 : Fin (n + 1)), (0 : Fin (n + 1)))]
        let C := DetImage.clear B p.inverse
        (detMod? (C.deleteRowCol 0 0)).map fun d =>
          if p.row = 0 then a * d else -(a * d)

/-- Every successful modular image equals the Leibniz determinant. -/
theorem detMod?_eq {n : Nat} {A : Matrix (ZMod64 m) n n} {d : ZMod64 m}
    (h : detMod? A = some d) : det A = d := by
  induction n generalizing d with
  | zero =>
    simp only [detMod?, Option.some.injEq] at h
    subst d
    simp [det, permutationVectors, detTerm, detSign, detProduct, inversionCount]
  | succ n ih =>
    unfold detMod? at h
    split at h
    · rename_i hz
      cases h
      rw [DetImage.det_column A (fun i => by simpa using hz i.succ)]
      have ha : A[(0 : Fin (n + 1))][(0 : Fin (n + 1))] = 0 := by simpa using hz 0
      rw [ha]
      grind only
    · split at h
      · contradiction
      · rename_i p hp
        dsimp only at h
        obtain ⟨e, he, hd⟩ := Option.map_eq_some_iff.mp h
        have hb : (A.rowSwap 0 p.row)[(0 : Fin (n + 1))][(0 : Fin (n + 1))] * p.inverse = 1 := by
          have hentry : (A.rowSwap 0 p.row)[(0 : Fin (n + 1))][(0 : Fin (n + 1))] =
              A[p.row][(0 : Fin (n + 1))] := by
            rw [getElem_rowSwap]
            split <;> simp_all only [↓reduceIte]
          rw [hentry]
          simpa only [getElem_pair_eq_nested] using p.mul_inverse
        obtain ⟨hdet, hpivot, hzero⟩ := DetImage.clear_spec (A.rowSwap 0 p.row) p.inverse hb
        have hfactor := DetImage.det_column (DetImage.clear (A.rowSwap 0 p.row) p.inverse) hzero
        rw [hdet, hpivot, ih he] at hfactor
        by_cases hr : p.row = 0
        · simp only [hr, ↓reduceIte, getElem_pair_eq_nested, rowSwap_self] at hd hfactor
          exact hfactor.trans hd
        · have hswap := det_rowSwap A 0 p.row (Ne.symm hr)
          simp only [hr, ↓reduceIte, getElem_pair_eq_nested] at hd
          rw [hswap] at hfactor
          simpa only [Lean.Grind.AddCommGroup.neg_neg] using
            (congrArg (fun x : ZMod64 m => -x) hfactor).trans hd

/-- Reducing an integer matrix and successfully eliminating it returns the
integer determinant modulo the same modulus, including composite moduli. -/
theorem detMod?_reduce {n : Nat} (A : Matrix Int n n) {d : ZMod64 m}
    (h : detMod? (A.mapEntries (ZMod64.intCast m)) = some d) :
    det A % (m : Int) = (d.toNat : Int) % (m : Int) := by
  have heq := detMod?_eq h
  rw [det_mapEntries A (ZMod64.intCast m)
    (Lean.Grind.Ring.intCast_zero) (Lean.Grind.Ring.intCast_one)
    (Lean.Grind.Ring.intCast_add) (Lean.Grind.Ring.intCast_mul)] at heq
  have hnat := congrArg (fun a : ZMod64 m => (a.toNat : Int)) heq
  rw [ZMod64.toNat_intCast] at hnat
  rw [← hnat, Int.emod_emod]

end Hex.Matrix
