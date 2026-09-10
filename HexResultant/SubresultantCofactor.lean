/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.BrownTraub
import all HexResultant.BrownTraub
import HexBasic.Fold

public section

/-!
Determinantal Bezout cofactors for generalized subresultants.

The coefficient minors in `SubresultantMinor` use their final row to select
one output coefficient.  Replacing a column by the final coordinate vector
removes that selector row and leaves an integral cofactor independent of the
selected coefficient.  Grouping the cofactors belonging to the two Sylvester
blocks gives the two polynomial transformation rows developed here.
-/

namespace Hex

universe u v

namespace DensePoly
namespace Subresultant

section Base

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]

/-- One column cofactor in a generalized coefficient matrix. -/
@[expose]
def columnCofactorAt (df dg J : Nat) (f g : DensePoly R)
    (j : Fin ((df - J) + (dg - J))) : R :=
  SubresultantMinor.lastCofactor (coeffMatrixAt df dg J 0 f g) j

/-- Accumulate the left-block cofactor monomials over selected columns. -/
@[expose]
def cofactorUCols (df dg J : Nat) (f g : DensePoly R) :
    List (Fin ((df - J) + (dg - J))) → DensePoly R
  | [] => 0
  | j :: js =>
      if j.val < dg - J then
        monomial (dg - J - 1 - j.val) (columnCofactorAt df dg J f g j) +
          cofactorUCols df dg J f g js
      else
        cofactorUCols df dg J f g js

/-- Accumulate the right-block cofactor monomials over selected columns. -/
@[expose]
def cofactorVCols (df dg J : Nat) (f g : DensePoly R) :
    List (Fin ((df - J) + (dg - J))) → DensePoly R
  | [] => 0
  | j :: js =>
      if dg - J ≤ j.val then
        monomial (df - J - 1 - (j.val - (dg - J)))
            (columnCofactorAt df dg J f g j) +
          cofactorVCols df dg J f g js
      else
        cofactorVCols df dg J f g js

/-- Sum the polynomial contribution of each selected Sylvester column. -/
@[expose]
def cofactorRowCols (df dg J : Nat) (f g : DensePoly R) :
    List (Fin ((df - J) + (dg - J))) → DensePoly R
  | [] => 0
  | j :: js =>
      (if j.val < dg - J then
        monomial (dg - J - 1 - j.val) (columnCofactorAt df dg J f g j) * f
      else
        monomial (df - J - 1 - (j.val - (dg - J)))
          (columnCofactorAt df dg J f g j) * g) +
        cofactorRowCols df dg J f g js

/-- Scalar final-row Laplace terms over selected Sylvester columns. -/
@[expose]
def cofactorScalarCols (df dg J l : Nat) (f g : DensePoly R) :
    List (Fin ((df - J) + (dg - J))) → R
  | [] => 0
  | j :: js =>
      (if j.val < dg - J then
        coeffInt f
            (Int.ofNat l - Int.ofNat (dg - J - 1) + Int.ofNat j.val) *
          columnCofactorAt df dg J f g j
      else
        coeffInt g
            (Int.ofNat l - Int.ofNat (df - J - 1) +
              Int.ofNat (j.val - (dg - J))) *
          columnCofactorAt df dg J f g j) +
        cofactorScalarCols df dg J l f g js

/-- Reconstruct a bounded polynomial from a selected interval of coefficient
columns, listed in descending monomial order. -/
@[expose]
def blockCols (start count total : Nat) (p : DensePoly R) :
    List (Fin total) → DensePoly R
  | [] => 0
  | j :: js =>
      (if start ≤ j.val ∧ j.val < start + count then
        monomial (count - 1 - (j.val - start))
          (p.coeff (count - 1 - (j.val - start)))
      else 0) + blockCols start count total p js

/-- Polynomial contribution of bounded left and right coefficient vectors. -/
@[expose]
def bezoutCols (df dg J : Nat) (u v f g : DensePoly R) :
    List (Fin ((df - J) + (dg - J))) → DensePoly R
  | [] => 0
  | j :: js =>
      (if j.val < dg - J then
        monomial (dg - J - 1 - j.val) (u.coeff (dg - J - 1 - j.val)) * f
      else
        monomial (df - J - 1 - (j.val - (dg - J)))
          (v.coeff (df - J - 1 - (j.val - (dg - J)))) * g) +
        bezoutCols df dg J u v f g js

/-- The bounded coefficient vector in Sylvester-column order. -/
@[expose]
def bezoutVector (df dg J : Nat) (u v : DensePoly R) :
    Vector R ((df - J) + (dg - J)) :=
  Vector.ofFn fun j =>
    if j.val < dg - J then
      u.coeff (dg - J - 1 - j.val)
    else
      v.coeff (df - J - 1 - (j.val - (dg - J)))

/-- The cofactor polynomial contributed by the left (`f`) block at explicit
formal degrees. -/
@[expose]
def cofactorUAt (df dg J : Nat) (f g : DensePoly R) : DensePoly R :=
  cofactorUCols df dg J f g (List.finRange ((df - J) + (dg - J)))

/-- The cofactor polynomial contributed by the right (`g`) block at explicit
formal degrees. -/
@[expose]
def cofactorVAt (df dg J : Nat) (f g : DensePoly R) : DensePoly R :=
  cofactorVCols df dg J f g (List.finRange ((df - J) + (dg - J)))

/-- The left Bezout cofactor of the `J`-th generalized subresultant. -/
@[expose]
def cofactorU (J : Nat) (f g : DensePoly R) : DensePoly R :=
  cofactorUAt (formalDegree f) (formalDegree g) J f g

/-- The right Bezout cofactor of the `J`-th generalized subresultant. -/
@[expose]
def cofactorV (J : Nat) (f g : DensePoly R) : DensePoly R :=
  cofactorVAt (formalDegree f) (formalDegree g) J f g

/-- Column cofactors do not depend on the selected output coefficient, since
that coefficient changes only the deleted final row. -/
theorem columnCofactorAt_eq (df dg J l : Nat) (f g : DensePoly R)
    (j : Fin ((df - J) + (dg - J))) :
    columnCofactorAt df dg J f g j =
      SubresultantMinor.lastCofactor (coeffMatrixAt df dg J l f g) j := by
  unfold columnCofactorAt
  apply SubresultantMinor.lastCofactor_congr
  intro i k hi
  unfold coeffMatrixAt
  have hlast : i.val ≠ (df - J) + (dg - J) - 1 := by omega
  simp [hlast]

/-- The two accumulated cofactor blocks multiply back to the sum of their
individual Sylvester-column contributions. -/
theorem cofactorCols_mul (df dg J : Nat) (f g : DensePoly R)
    (cols : List (Fin ((df - J) + (dg - J)))) :
    cofactorUCols df dg J f g cols * f +
        cofactorVCols df dg J f g cols * g =
      cofactorRowCols df dg J f g cols := by
  induction cols with
  | nil =>
      simp only [cofactorUCols, cofactorVCols, cofactorRowCols]
      rw [zero_mul, zero_mul, add_zero_poly]
  | cons j js ih =>
      by_cases hj : j.val < dg - J
      · have hj' : ¬dg - J ≤ j.val := by omega
        simp only [cofactorUCols, cofactorVCols, cofactorRowCols,
          ite_eq_left hj, ite_eq_right hj']
        rw [mul_add_left_poly, add_assoc_poly, ih]
      · have hj' : dg - J ≤ j.val := by omega
        simp only [cofactorUCols, cofactorVCols, cofactorRowCols,
          ite_eq_right hj, ite_eq_left hj']
        rw [mul_add_left_poly]
        calc
          cofactorUCols df dg J f g js * f +
              (monomial (df - J - 1 - (j.val - (dg - J)))
                (columnCofactorAt df dg J f g j) * g +
                cofactorVCols df dg J f g js * g) =
              monomial (df - J - 1 - (j.val - (dg - J)))
                  (columnCofactorAt df dg J f g j) * g +
                (cofactorUCols df dg J f g js * f +
                  cofactorVCols df dg J f g js * g) := by
                    rw [← add_assoc_poly, add_comm_poly
                      (cofactorUCols df dg J f g js * f)]
                    rw [add_assoc_poly]
          _ = _ := by rw [ih]

/-- Multiplying by a scalar monomial shifts a scalar multiple of the right
factor. -/
private theorem monomial_mul_eq_shift (e : Nat) (c : R) (p : DensePoly R) :
    monomial e c * p = shift e (scale c p) := by
  have hmono : monomial e c = scale c (monomial e 1) := by
    apply ext_coeff
    intro k
    rw [coeff_monomial, coeff_scale_semiring, coeff_monomial]
    by_cases hke : k = e
    · simp [hke]
      grind
    · simp [hke]
      exact (Lean.Grind.Semiring.mul_zero c).symm
  rw [hmono, ← scale_mul, monomial_one_mul_poly_eq_shift]
  apply ext_coeff
  intro k
  by_cases hke : k < e
  · simp [hke]
    exact Lean.Grind.Semiring.mul_zero c
  · simp [hke]

/-- Coefficient form of scalar-monomial multiplication, using the same
integer-index convention as a generalized coefficient matrix. -/
private theorem coeff_monomial_mul (e : Nat) (c : R) (p : DensePoly R)
    (l : Nat) :
    (monomial e c * p).coeff l =
      c * coeffInt p (Int.ofNat l - Int.ofNat e) := by
  rw [monomial_mul_eq_shift, coeff_shift_scale_semiring]
  unfold coeffInt
  by_cases hle : l < e
  · have hneg : Int.ofNat l - Int.ofNat e < 0 :=
      Int.sub_neg_of_lt (Int.ofNat_lt.mpr hle)
    rw [ite_eq_left hle, ite_eq_left hneg, Lean.Grind.Semiring.mul_zero]
    rfl
  · have hleInt : Int.ofNat e ≤ Int.ofNat l :=
      Int.ofNat_le.mpr (Nat.le_of_not_gt hle)
    have hnneg : ¬Int.ofNat l - Int.ofNat e < 0 :=
      Int.not_lt.mpr (Int.sub_nonneg_of_le hleInt)
    rw [ite_eq_right hle, ite_eq_right hnneg]
    have hnat := Int.toNat_sub l e
    change (Int.ofNat l - Int.ofNat e).toNat = l - e at hnat
    rw [hnat]

omit [DecidableEq R] in
private theorem foldl_add_eq_foldr {A : Type v} (xs : List A) (h : A → R)
    (a : R) :
    xs.foldl (fun acc x => acc + h x) a =
      a + xs.foldr (fun x acc => h x + acc) 0 := by
  induction xs generalizing a with
  | nil =>
      simp only [List.foldl_nil, List.foldr_nil]
      grind
  | cons x xs ih =>
      simp only [List.foldl_cons, List.foldr_cons]
      rw [ih]
      grind

/-- Each column inside the block contributes one reversed coefficient of `p`
at its own index, and columns outside the block contribute nothing. -/
private theorem coeff_blockCols (start count total : Nat) (p : DensePoly R)
    (cols : List (Fin total)) (k : Nat) :
    (blockCols start count total p cols).coeff k =
      cols.foldr
        (fun j acc =>
          (if start ≤ j.val ∧ j.val < start + count then
            if k = count - 1 - (j.val - start) then
              p.coeff (count - 1 - (j.val - start))
            else 0
          else 0) + acc)
        0 := by
  induction cols with
  | nil => simp [blockCols]
  | cons j js ih =>
      simp only [blockCols, List.foldr_cons]
      rw [coeff_add_semiring, ih]
      by_cases hj : start ≤ j.val ∧ j.val < start + count
      · rw [ite_eq_left hj, ite_eq_left hj, coeff_monomial]
        by_cases hk : k = count - 1 - (j.val - start)
        · rw [ite_eq_left hk, ite_eq_left hk]
        · rw [ite_eq_right hk, ite_eq_right hk]
          rfl
      · rw [ite_eq_right hj, ite_eq_right hj, coeff_zero]

/-- A full interval of reversed coefficient columns reconstructs the bounded
polynomial. -/
theorem blockCols_finRange (start count total : Nat) (p : DensePoly R)
    (hfit : start + count ≤ total) (hsize : p.size ≤ count) :
    blockCols start count total p (List.finRange total) = p := by
  apply ext_coeff
  intro k
  rw [coeff_blockCols]
  let term : Fin total → R := fun j =>
    if start ≤ j.val ∧ j.val < start + count then
      if k = count - 1 - (j.val - start) then
        p.coeff (count - 1 - (j.val - start))
      else 0
    else 0
  have hfold := foldl_add_eq_foldr (R := R) (List.finRange total) term 0
  have hfold' :
      (List.finRange total).foldr (fun j acc => term j + acc) 0 =
        (List.finRange total).foldl (fun acc j => acc + term j) 0 := by
    grind
  change (List.finRange total).foldr (fun j acc => term j + acc) 0 = p.coeff k
  rw [hfold']
  by_cases hk : k < count
  · let q : Fin total := ⟨start + (count - 1 - k), by omega⟩
    calc
      (List.finRange total).foldl (fun acc j => acc + term j) 0 =
          (List.finRange total).foldl
            (fun acc j => acc + if j = q then p.coeff k else 0) 0 := by
              apply List.foldl_congr
              intro acc j _hj
              congr 1
              dsimp only [term, q]
              by_cases hjq : j = ⟨start + (count - 1 - k), by omega⟩
              · subst j
                simp only [reduceIte]
                rw [ite_eq_left (by omega), ite_eq_left (by omega)]
                congr 1
                omega
              · rw [ite_eq_right hjq]
                by_cases hjblock : start ≤ j.val ∧ j.val < start + count
                · rw [ite_eq_left hjblock]
                  rw [ite_eq_right]
                  intro heq
                  apply hjq
                  apply Fin.ext
                  symm
                  have hdle : j.val - start ≤ count - 1 := by omega
                  have hsplit : start + (j.val - start) = j.val := by omega
                  calc
                    start + (count - 1 - k) =
                        start + (count - 1 -
                          (count - 1 - (j.val - start))) := by rw [heq]
                    _ = start + (j.val - start) := by
                      rw [Nat.sub_sub_self hdle]
                    _ = j.val := hsplit
                · rw [ite_eq_right hjblock]
      _ = 0 + p.coeff k := by
        exact List.foldl_add_single (List.finRange total) 0 q
          (fun _ => p.coeff k) (List.mem_finRange q) (List.nodup_finRange total)
      _ = p.coeff k := by grind
  · have hpzero : p.coeff k = 0 :=
      coeff_eq_zero_of_size_le p (by omega)
    have hterm : ∀ j, j ∈ List.finRange total → term j = 0 := by
      intro j _hj
      dsimp only [term]
      by_cases hjblock : start ≤ j.val ∧ j.val < start + count
      · rw [ite_eq_left hjblock, ite_eq_right (by omega)]
      · rw [ite_eq_right hjblock]
    rw [List.foldl_add_eq_self _ term 0 hterm, hpzero]

/-- The two reconstructed coefficient blocks multiply to their per-column
Bezout contributions. -/
theorem blockCols_mul (df dg J : Nat) (u v f g : DensePoly R)
    (cols : List (Fin ((df - J) + (dg - J)))) :
    blockCols 0 (dg - J) ((df - J) + (dg - J)) u cols * f +
        blockCols (dg - J) (df - J) ((df - J) + (dg - J)) v cols * g =
      bezoutCols df dg J u v f g cols := by
  induction cols with
  | nil =>
      simp only [blockCols, bezoutCols]
      rw [zero_mul, zero_mul, add_zero_poly]
  | cons j js ih =>
      by_cases hj : j.val < dg - J
      · have hleft : 0 ≤ j.val ∧ j.val < 0 + (dg - J) := by omega
        have hright : ¬(dg - J ≤ j.val ∧ j.val < dg - J + (df - J)) := by
          omega
        simp only [blockCols, bezoutCols, ite_eq_left hj, ite_eq_left hleft,
          ite_eq_right hright]
        rw [add_comm_poly (0 : DensePoly R), add_zero_poly]
        rw [mul_add_left_poly, add_assoc_poly, ih]
        simp only [Nat.sub_zero]
      · have hleft : ¬(0 ≤ j.val ∧ j.val < 0 + (dg - J)) := by omega
        have hright : dg - J ≤ j.val ∧
            j.val < dg - J + (df - J) := by
          have hjfin := j.isLt
          omega
        simp only [blockCols, bezoutCols, ite_eq_right hj, ite_eq_right hleft,
          ite_eq_left hright]
        rw [add_comm_poly (0 : DensePoly R)
          (blockCols 0 (dg - J) (df - J + (dg - J)) u js), add_zero_poly,
          mul_add_left_poly]
        calc
          blockCols 0 (dg - J) (df - J + (dg - J)) u js * f +
              (monomial (df - J - 1 - (j.val - (dg - J)))
                  (v.coeff (df - J - 1 - (j.val - (dg - J)))) * g +
                blockCols (dg - J) (df - J) (df - J + (dg - J)) v js * g) =
              monomial (df - J - 1 - (j.val - (dg - J)))
                    (v.coeff (df - J - 1 - (j.val - (dg - J)))) * g +
                (blockCols 0 (dg - J) (df - J + (dg - J)) u js * f +
                  blockCols (dg - J) (df - J) (df - J + (dg - J)) v js * g) := by
                    rw [← add_assoc_poly, add_comm_poly
                      (blockCols 0 (dg - J) (df - J + (dg - J)) u js * f)]
                    rw [add_assoc_poly]
          _ = _ := by rw [ih]

/-- Full bounded column lists reconstruct the original Bezout polynomial. -/
theorem bezoutCols_finRange (df dg J : Nat) (u v f g : DensePoly R)
    (hu : u.size ≤ dg - J) (hv : v.size ≤ df - J) :
    bezoutCols df dg J u v f g
        (List.finRange ((df - J) + (dg - J))) =
      u * f + v * g := by
  rw [← blockCols_mul]
  rw [blockCols_finRange 0 (dg - J) ((df - J) + (dg - J)) u
      (by omega) hu]
  rw [blockCols_finRange (dg - J) (df - J)
      ((df - J) + (dg - J)) v (by omega) hv]

/-- Coefficients of bounded Bezout columns are matrix-row products with the
bounded coefficient vector. -/
theorem coeff_bezoutCols (df dg J l : Nat) (u v f g : DensePoly R)
    (hcount : 0 < (df - J) + (dg - J))
    (cols : List (Fin ((df - J) + (dg - J)))) :
    (bezoutCols df dg J u v f g cols).coeff l =
      cols.foldr
        (fun j acc =>
          coeffMatrixAt df dg J l f g
              ⟨(df - J) + (dg - J) - 1, by omega⟩ j *
            (bezoutVector df dg J u v)[j] + acc)
        0 := by
  induction cols with
  | nil => simp [bezoutCols]
  | cons j js ih =>
      simp only [bezoutCols, List.foldr_cons]
      rw [coeff_add_semiring, ih]
      unfold coeffMatrixAt bezoutVector
      simp only [Fin.getElem_fin, Vector.getElem_ofFn]
      by_cases hj : j.val < dg - J
      · simp only [ite_eq_left hj, ite_eq_left True.intro, coeff_monomial_mul]
        have hle : j.val ≤ dg - J - 1 := by omega
        have hcast : Int.ofNat (dg - J - 1 - j.val) =
            Int.ofNat (dg - J - 1) - Int.ofNat j.val :=
          Int.ofNat_sub hle
        rw [hcast]
        grind
      · simp only [ite_eq_right hj, ite_eq_left True.intro, coeff_monomial_mul]
        have hbound : j.val - (dg - J) ≤ df - J - 1 := by
          have hjfin := j.isLt
          omega
        have hcast :
            Int.ofNat (df - J - 1 - (j.val - (dg - J))) =
              Int.ofNat (df - J - 1) - Int.ofNat (j.val - (dg - J)) :=
          Int.ofNat_sub hbound
        rw [hcast]
        grind

/-- Every row of a generalized coefficient matrix is the final row of the
matrix at some other requested coefficient: the non-final rows are shifted
polynomial coefficients, and the final row is selected by `ell` itself.  This
lets a single final-row Laplace identity cover the whole matrix. -/
private theorem coeffMatrixAt_row_eq_last (df dg J ell : Nat)
    (f g : DensePoly R) (hJ : J < dg)
    (hcount : 0 < (df - J) + (dg - J))
    (i : Fin ((df - J) + (dg - J))) :
    let l := if i.val = (df - J) + (dg - J) - 1 then ell
      else df + (dg - J) - 1 - i.val
    ∀ j,
      coeffMatrixAt df dg J ell f g i j =
        coeffMatrixAt df dg J l f g
          ⟨(df - J) + (dg - J) - 1, by omega⟩ j := by
  let last : Fin ((df - J) + (dg - J)) :=
    ⟨(df - J) + (dg - J) - 1, by omega⟩
  by_cases hi : i.val = (df - J) + (dg - J) - 1
  · have hieq : i = last := Fin.ext hi
    subst i
    simp only [ite_eq_left hi]
    intro j
    rfl
  · simp only [ite_eq_right hi]
    intro j
    unfold coeffMatrixAt
    by_cases hj : j.val < dg - J
    · simp only [ite_eq_left hj, ite_eq_right hi, ite_eq_left True.intro]
      congr 2
      have hleft : 0 < dg - J := by omega
      have hibound : i.val ≤ df + (dg - J) - 1 := by
        have hiFin := i.isLt
        omega
      have hsub : Int.ofNat (df + (dg - J) - 1 - i.val) =
          Int.ofNat (df + (dg - J) - 1) - Int.ofNat i.val :=
        Int.ofNat_sub hibound
      have hsplitNat : df + (dg - J) - 1 = df + (dg - J - 1) := by omega
      have hsplit := congrArg Int.ofNat hsplitNat
      have hadd : Int.ofNat (df + (dg - J - 1)) =
          Int.ofNat df + Int.ofNat (dg - J - 1) := Int.natCast_add _ _
      rw [hsub, hsplit, hadd]
      grind
    · simp only [ite_eq_right hj, ite_eq_right hi, ite_eq_left True.intro]
      congr 2
      have hright : 0 < df - J := by
        have hiFin := j.isLt
        omega
      have hiboundLeft : i.val ≤ df + (dg - J) - 1 := by
        have hiFin := i.isLt
        omega
      have hibound : i.val ≤ dg + (df - J) - 1 := by
        have hiFin := i.isLt
        omega
      have hbaseNat : df + (dg - J) - 1 = dg + (df - J) - 1 := by omega
      have hbase := congrArg Int.ofNat hbaseNat
      have hleftSub : Int.ofNat (df + (dg - J) - 1 - i.val) =
          Int.ofNat (df + (dg - J) - 1) - Int.ofNat i.val :=
        Int.ofNat_sub hiboundLeft
      have hsplitNat : dg + (df - J) - 1 = dg + (df - J - 1) := by omega
      have hsplit := congrArg Int.ofNat hsplitNat
      have hadd : Int.ofNat (dg + (df - J - 1)) =
          Int.ofNat dg + Int.ofNat (df - J - 1) := Int.natCast_add _ _
      rw [hleftSub, hbase, hsplit, hadd]
      grind

/-- A bounded Bezout syzygy gives a kernel vector for every generalized
coefficient matrix of the same index. -/
theorem coeffMatrixAt_mul_bezoutVector_eq_zero
    (df dg J ell : Nat) (u v f g : DensePoly R)
    (hJ : J < dg)
    (hcount : 0 < (df - J) + (dg - J))
    (hu : u.size ≤ dg - J) (hv : v.size ≤ df - J)
    (hzero : u * f + v * g = 0) :
    SubresultantMinor.toMatrix (coeffMatrixAt df dg J ell f g) *
        bezoutVector df dg J u v = 0 := by
  apply Vector.ext
  intro i hi
  let ii : Fin ((df - J) + (dg - J)) := ⟨i, hi⟩
  let l := if ii.val = (df - J) + (dg - J) - 1 then ell
    else df + (dg - J) - 1 - ii.val
  let term : Fin ((df - J) + (dg - J)) → R := fun j =>
    coeffMatrixAt df dg J ell f g ii j *
      (bezoutVector df dg J u v)[j]
  let lastTerm : Fin ((df - J) + (dg - J)) → R := fun j =>
    coeffMatrixAt df dg J l f g
        ⟨(df - J) + (dg - J) - 1, by omega⟩ j *
      (bezoutVector df dg J u v)[j]
  have hrow := coeffMatrixAt_row_eq_last df dg J ell f g hJ hcount ii
  have hterm (j : Fin ((df - J) + (dg - J))) : term j = lastTerm j := by
    dsimp only [term, lastTerm]
    rw [hrow j]
  have hcoeff := coeff_bezoutCols df dg J l u v f g hcount
    (List.finRange ((df - J) + (dg - J)))
  rw [bezoutCols_finRange df dg J u v f g hu hv, hzero, coeff_zero] at hcoeff
  have hlastFold :
      (List.finRange ((df - J) + (dg - J))).foldl
          (fun acc j => acc + lastTerm j) 0 = 0 := by
    have hfold := foldl_add_eq_foldr (R := R)
      (List.finRange ((df - J) + (dg - J))) lastTerm 0
    change (0 : R) =
      (List.finRange ((df - J) + (dg - J))).foldr
        (fun j acc => lastTerm j + acc) 0 at hcoeff
    grind
  have hfoldEq :
      (List.finRange ((df - J) + (dg - J))).foldl
          (fun acc j => acc + term j) 0 =
        (List.finRange ((df - J) + (dg - J))).foldl
          (fun acc j => acc + lastTerm j) 0 := by
    apply List.foldl_congr
    intro acc j _hj
    rw [hterm j]
  change
    (SubresultantMinor.toMatrix (coeffMatrixAt df dg J ell f g) *
      bezoutVector df dg J u v)[ii] = (0 : Vector R ((df - J) + (dg - J)))[ii]
  rw [Matrix.getElem_mulVec]
  unfold Vector.dotProduct
  simp only [Matrix.getElem_row, SubresultantMinor.toMatrix_get]
  change (List.finRange ((df - J) + (dg - J))).foldl
      (fun acc j => acc + term j) 0 = _
  rw [hfoldEq, hlastFold]
  simp only [Fin.getElem_fin, Vector.getElem_zero]

/-- A nonzero generalized coefficient minor makes bounded Bezout
representations unique. -/
theorem bounded_bezout_unique [Div R] [ExactDivLaws R]
    (df dg J ell : Nat) (f g u v : DensePoly R)
    (hJ : J < dg) (hdet : coeffMinorAt df dg J ell f g ≠ 0)
    (hu : u.size ≤ dg - J) (hv : v.size ≤ df - J)
    (hzero : u * f + v * g = 0) :
    u = 0 ∧ v = 0 := by
  have hcount : 0 < (df - J) + (dg - J) := by omega
  have hmul := coeffMatrixAt_mul_bezoutVector_eq_zero
    df dg J ell u v f g hJ hcount hu hv hzero
  have hkernel := SubresultantMinor.vector_eq_zero_of_mul_eq_zero
    (coeffMatrixAt df dg J ell f g) hcount hdet
    (bezoutVector df dg J u v) hmul
  constructor
  · apply ext_coeff
    intro k
    rw [coeff_zero]
    by_cases hk : k < dg - J
    · let j : Fin ((df - J) + (dg - J)) :=
        ⟨dg - J - 1 - k, by omega⟩
      have hj := hkernel j
      unfold bezoutVector at hj
      simp only [Fin.getElem_fin, Vector.getElem_ofFn] at hj
      rw [ite_eq_left (by dsimp [j]; omega)] at hj
      have hle : k ≤ dg - J - 1 := by omega
      have hindex : dg - J - 1 - (dg - J - 1 - k) = k :=
        Nat.sub_sub_self hle
      simpa only [j, hindex] using hj
    · exact coeff_eq_zero_of_size_le u (by omega)
  · apply ext_coeff
    intro k
    rw [coeff_zero]
    by_cases hk : k < df - J
    · let j : Fin ((df - J) + (dg - J)) :=
        ⟨(dg - J) + (df - J - 1 - k), by omega⟩
      have hj := hkernel j
      unfold bezoutVector at hj
      simp only [Fin.getElem_fin, Vector.getElem_ofFn] at hj
      rw [ite_eq_right (by dsimp [j]; omega)] at hj
      have hle : k ≤ df - J - 1 := by omega
      have hindex :
          df - J - 1 -
              ((dg - J + (df - J - 1 - k)) - (dg - J)) = k := by
        rw [Nat.add_sub_cancel_left]
        exact Nat.sub_sub_self hle
      simpa only [j, hindex] using hj
    · exact coeff_eq_zero_of_size_le v (by omega)

/-- Vanishing above index `n` bounds the normalized size by `n`. This is the
size-bound entry point for the cofactor columns below. -/
private theorem size_le_of_coeff_zero_above (p : DensePoly R) (n : Nat)
    (hzero : ∀ k, n ≤ k → p.coeff k = 0) : p.size ≤ n := by
  by_cases hle : p.size ≤ n
  · exact hle
  · have hpos : 0 < p.size := by omega
    have hlast : n ≤ p.size - 1 := by omega
    exact False.elim
      ((coeff_last_ne_zero_of_pos_size p hpos) (hzero _ hlast))

/-- A difference of dense polynomials is bounded by the larger operand
size. -/
theorem size_sub_le_max (p q : DensePoly R) :
    (p - q).size ≤ Nat.max p.size q.size := by
  apply size_le_of_coeff_zero_above
  intro k hk
  have hp : p.size ≤ k :=
    Nat.le_trans (Nat.le_max_left _ _) hk
  have hq : q.size ≤ k :=
    Nat.le_trans (Nat.le_max_right _ _) hk
  rw [coeff_sub_ring, coeff_eq_zero_of_size_le p hp,
    coeff_eq_zero_of_size_le q hq]
  grind

/-- The `f`-side cofactor accumulates only monomials below `dg - J`, so it
stays inside the `g` block's column budget. -/
private theorem cofactorUCols_size_le (df dg J : Nat) (f g : DensePoly R)
    (cols : List (Fin ((df - J) + (dg - J)))) :
    (cofactorUCols df dg J f g cols).size ≤ dg - J := by
  apply size_le_of_coeff_zero_above
  intro k hk
  induction cols with
  | nil => rw [cofactorUCols, coeff_zero]
  | cons j js ih =>
      simp only [cofactorUCols]
      by_cases hj : j.val < dg - J
      · rw [ite_eq_left hj, coeff_add_semiring, coeff_monomial, ih]
        rw [ite_eq_right (by omega)]
        have hzero : (Zero.zero : R) = 0 := rfl
        rw [hzero]
        grind
      · rw [ite_eq_right hj]
        exact ih

/-- The `g`-side cofactor accumulates only monomials below `df - J`, so it
stays inside the `f` block's column budget. -/
private theorem cofactorVCols_size_le (df dg J : Nat) (f g : DensePoly R)
    (cols : List (Fin ((df - J) + (dg - J)))) :
    (cofactorVCols df dg J f g cols).size ≤ df - J := by
  apply size_le_of_coeff_zero_above
  intro k hk
  induction cols with
  | nil => rw [cofactorVCols, coeff_zero]
  | cons j js ih =>
      simp only [cofactorVCols]
      by_cases hj : dg - J ≤ j.val
      · rw [ite_eq_left hj, coeff_add_semiring, coeff_monomial, ih]
        rw [ite_eq_right (by omega)]
        have hzero : (Zero.zero : R) = 0 := rfl
        rw [hzero]
        grind
      · rw [ite_eq_right hj]
        exact ih

/-- Degree bound for the left determinantal cofactor block at explicit formal
degrees. -/
theorem cofactorUAt_size_le (df dg J : Nat) (f g : DensePoly R) :
    (cofactorUAt df dg J f g).size ≤ dg - J := by
  exact cofactorUCols_size_le df dg J f g _

/-- Degree bound for the right determinantal cofactor block at explicit formal
degrees. -/
theorem cofactorVAt_size_le (df dg J : Nat) (f g : DensePoly R) :
    (cofactorVAt df dg J f g).size ≤ df - J := by
  exact cofactorVCols_size_le df dg J f g _

/-- Degree bound for the canonical left cofactor at the actual formal
degrees. -/
theorem cofactorU_size_le (J : Nat) (f g : DensePoly R) :
    (cofactorU J f g).size ≤ formalDegree g - J := by
  exact cofactorUAt_size_le _ _ J f g

/-- Degree bound for the canonical right cofactor at the actual formal
degrees. -/
theorem cofactorV_size_le (J : Nat) (f g : DensePoly R) :
    (cofactorV J f g).size ≤ formalDegree f - J := by
  exact cofactorVAt_size_le _ _ J f g

/-- Each coefficient of the polynomial column sum is its scalar Laplace
column sum. -/
theorem coeff_cofactorRowCols (df dg J l : Nat) (f g : DensePoly R)
    (cols : List (Fin ((df - J) + (dg - J)))) :
    (cofactorRowCols df dg J f g cols).coeff l =
      cofactorScalarCols df dg J l f g cols := by
  induction cols with
  | nil =>
      simp [cofactorRowCols, cofactorScalarCols]
  | cons j js ih =>
      simp only [cofactorRowCols, cofactorScalarCols]
      rw [coeff_add_semiring, ih]
      by_cases hj : j.val < dg - J
      · rw [ite_eq_left hj, ite_eq_left hj, coeff_monomial_mul]
        have hle : j.val ≤ dg - J - 1 := by omega
        have hcast : Int.ofNat (dg - J - 1 - j.val) =
            Int.ofNat (dg - J - 1) - Int.ofNat j.val :=
          Int.ofNat_sub hle
        rw [hcast]
        grind
      · have hj' : dg - J ≤ j.val := by omega
        rw [ite_eq_right hj, ite_eq_right hj, coeff_monomial_mul]
        have hbound : j.val - (dg - J) ≤ df - J - 1 := by
          have hjfin := j.isLt
          omega
        have hcast :
            Int.ofNat (df - J - 1 - (j.val - (dg - J))) =
              Int.ofNat (df - J - 1) - Int.ofNat (j.val - (dg - J)) :=
          Int.ofNat_sub hbound
        rw [hcast]
        grind

/-- The scalar cofactor sum is the final-row Laplace sum of the coefficient
matrix. -/
theorem cofactorScalarCols_eq_laplace (df dg J l : Nat)
    (f g : DensePoly R) (hcount : 0 < (df - J) + (dg - J))
    (cols : List (Fin ((df - J) + (dg - J)))) :
    cofactorScalarCols df dg J l f g cols =
      cols.foldr
        (fun j acc =>
          coeffMatrixAt df dg J l f g
              ⟨(df - J) + (dg - J) - 1, by omega⟩ j *
            SubresultantMinor.lastCofactor
              (coeffMatrixAt df dg J l f g) j + acc)
        0 := by
  induction cols with
  | nil => rfl
  | cons j js ih =>
      simp only [cofactorScalarCols, List.foldr_cons]
      rw [← ih]
      rw [← columnCofactorAt_eq df dg J l f g j]
      unfold coeffMatrixAt
      by_cases hj : j.val < dg - J
      · simp only [ite_eq_left hj]
        rw [ite_eq_left True.intro]
      · simp only [ite_eq_right hj]
        rw [ite_eq_left True.intro]

/-- At positive matrix dimension, the full scalar cofactor sum is the
corresponding generalized coefficient minor. -/
theorem cofactorScalarCols_finRange (df dg J l : Nat) (f g : DensePoly R)
    (hcount : 0 < (df - J) + (dg - J)) :
    cofactorScalarCols df dg J l f g
        (List.finRange ((df - J) + (dg - J))) =
      coeffMinorAt df dg J l f g := by
  have hlap := SubresultantMinor.det_lastCofactor_of_pos
    (coeffMatrixAt df dg J l f g) hcount
  rw [cofactorScalarCols_eq_laplace df dg J l f g hcount]
  unfold coeffMinorAt
  rw [hlap]
  symm
  have hfold := foldl_add_eq_foldr (R := R)
    (List.finRange ((df - J) + (dg - J)))
    (fun j =>
      coeffMatrixAt df dg J l f g
          ⟨(df - J) + (dg - J) - 1, by omega⟩ j *
        SubresultantMinor.lastCofactor
          (coeffMatrixAt df dg J l f g) j)
    (0 : R)
  exact hfold.trans (by grind)

/-- The accumulated cofactor products have the generalized determinant as
every coefficient for which the coefficient matrix has positive dimension. -/
theorem coeff_cofactorAt_mul (df dg J l : Nat) (f g : DensePoly R)
    (hcount : 0 < (df - J) + (dg - J)) :
    (cofactorUAt df dg J f g * f + cofactorVAt df dg J f g * g).coeff l =
      coeffMinorAt df dg J l f g := by
  unfold cofactorUAt cofactorVAt
  rw [cofactorCols_mul, coeff_cofactorRowCols,
    cofactorScalarCols_finRange df dg J l f g hcount]

/-- The integer-indexed lookup vanishes above the normalized size, which is
what lets the cofactor rows be summed over a fixed integer window. -/
private theorem coeffInt_eq_zero_of_size_le (p : DensePoly R) (k : Int)
    (h : Int.ofNat p.size ≤ k) : coeffInt p k = 0 := by
  cases k with
  | ofNat n =>
      unfold coeffInt
      by_cases hneg : Int.ofNat n < 0
      · exact False.elim (Int.not_ofNat_neg n hneg)
      rw [ite_eq_right hneg]
      apply coeff_eq_zero_of_size_le
      exact Int.ofNat_le.mp h
  | negSucc n =>
      have hs : 0 ≤ Int.ofNat p.size := Int.natCast_nonneg _
      omega

/-- Coefficient minors above the requested subresultant degree vanish: in
the active range their selector row repeats an earlier Sylvester row, and
above that range the selector row is zero. -/
theorem coeffMinorAt_eq_zero_of_lt (df dg J l : Nat) (f g : DensePoly R)
    (hJ : J < dg) (hdg : dg ≤ df)
    (hf : f.size ≤ df + 1) (hg : g.size ≤ dg + 1)
    (hl : J < l) :
    coeffMinorAt df dg J l f g = 0 := by
  unfold coeffMinorAt
  have hcount : 0 < (df - J) + (dg - J) := by omega
  by_cases hrange : l < df + dg - J
  · let src : Fin ((df - J) + (dg - J)) :=
      ⟨df + dg - J - l - 1, by omega⟩
    let dst : Fin ((df - J) + (dg - J)) :=
      ⟨(df - J) + (dg - J) - 1, by omega⟩
    apply SubresultantMinor.det_eq_zero_of_row_eq
      (coeffMatrixAt df dg J l f g) src dst
    · intro hsd
      have hv := congrArg Fin.val hsd
      dsimp [src, dst] at hv
      omega
    · intro j
      have hsrc : src.val ≠ (df - J) + (dg - J) - 1 := by
        dsimp [src]
        omega
      have hdst : dst.val = (df - J) + (dg - J) - 1 := by rfl
      unfold coeffMatrixAt
      by_cases hj : j.val < dg - J
      · simp only [ite_eq_left hj, ite_eq_right hsrc, ite_eq_left hdst]
        congr 2
        dsimp [src, dst]
        omega
      · simp only [ite_eq_right hj, ite_eq_right hsrc, ite_eq_left hdst]
        congr 2
        dsimp [src, dst]
        omega
  · apply SubresultantMinor.det_lastRow_zero_of_pos
      (coeffMatrixAt df dg J l f g) hcount
    intro j
    unfold coeffMatrixAt
    by_cases hj : j.val < dg - J
    · simp only [ite_eq_left hj, ite_eq_left True.intro]
      apply coeffInt_eq_zero_of_size_le
      have hbase : dg - J - 1 ≤ l := by omega
      have hnat : f.size ≤ l - (dg - J - 1) + j.val := by omega
      calc
        Int.ofNat f.size ≤
            Int.ofNat (l - (dg - J - 1) + j.val) := Int.ofNat_le.mpr hnat
        _ = Int.ofNat l - Int.ofNat (dg - J - 1) + Int.ofNat j.val := by
          have hadd : Int.ofNat (l - (dg - J - 1) + j.val) =
              Int.ofNat (l - (dg - J - 1)) + Int.ofNat j.val :=
            Int.natCast_add _ _
          have hsub : Int.ofNat (l - (dg - J - 1)) =
              Int.ofNat l - Int.ofNat (dg - J - 1) :=
            Int.ofNat_sub hbase
          exact hadd.trans (congrArg (fun z => z + Int.ofNat j.val) hsub)
    · simp only [ite_eq_right hj, ite_eq_left True.intro]
      apply coeffInt_eq_zero_of_size_le
      have hbase : df - J - 1 ≤ l := by omega
      have hnat : g.size ≤
          l - (df - J - 1) + (j.val - (dg - J)) := by omega
      calc
        Int.ofNat g.size ≤ Int.ofNat
            (l - (df - J - 1) + (j.val - (dg - J))) := Int.ofNat_le.mpr hnat
        _ = Int.ofNat l - Int.ofNat (df - J - 1) +
            Int.ofNat (j.val - (dg - J)) := by
          have hadd :
              Int.ofNat (l - (df - J - 1) + (j.val - (dg - J))) =
                Int.ofNat (l - (df - J - 1)) +
                  Int.ofNat (j.val - (dg - J)) := Int.natCast_add _ _
          have hsub : Int.ofNat (l - (df - J - 1)) =
              Int.ofNat l - Int.ofNat (df - J - 1) :=
            Int.ofNat_sub hbase
          exact hadd.trans
            (congrArg (fun z => z + Int.ofNat (j.val - (dg - J))) hsub)

/-- The determinantal cofactors give an integral Bezout representation of a
generalized subresultant. -/
theorem cofactor_bezout (J : Nat) (f g : DensePoly R)
    (hgf : g.size ≤ f.size) (hJ : J < formalDegree g) :
    cofactorU J f g * f + cofactorV J f g * g = poly J f g := by
  apply ext_coeff
  intro l
  let df := formalDegree f
  let dg := formalDegree g
  have hdg : dg ≤ df := by
    dsimp only [df, dg, formalDegree]
    omega
  have hcount : 0 < (df - J) + (dg - J) := by omega
  unfold cofactorU cofactorV
  rw [coeff_cofactorAt_mul df dg J l f g hcount, coeff_poly]
  by_cases hl : l < J + 1
  · rw [ite_eq_left hl]
    rfl
  · rw [ite_eq_right hl]
    apply coeffMinorAt_eq_zero_of_lt
    · exact hJ
    · exact hdg
    · dsimp only [df, formalDegree]
      omega
    · dsimp only [dg, formalDegree]
      omega
    · omega

/-- Any bounded Bezout row for a scalar multiple of a nonzero subresultant is
that scalar multiple of the determinantal cofactor row. -/
theorem eq_scaled_cofactor [Div R] [ExactDivLaws R]
    (J : Nat) (d : R) (f g u v : DensePoly R)
    (hgf : g.size ≤ f.size) (hJ : J < formalDegree g)
    (hroot : poly J f g ≠ 0)
    (hu : u.size ≤ formalDegree g - J)
    (hv : v.size ≤ formalDegree f - J)
    (hrepr : u * f + v * g = scale d (poly J f g)) :
    u = scale d (cofactorU J f g) ∧
      v = scale d (cofactorV J f g) := by
  let df := formalDegree f
  let dg := formalDegree g
  let ell := (poly J f g).size - 1
  have hrootPos : 0 < (poly J f g).size := by
    by_cases hs : 0 < (poly J f g).size
    · exact hs
    · exact False.elim
        (hroot ((size_eq_zero_iff (poly J f g)).mp (by omega)))
  have hell : ell < J + 1 := by
    have hs := Subresultant.poly_size_le J f g
    dsimp only [ell]
    omega
  have hminor : coeffMinorAt df dg J ell f g ≠ 0 := by
    have hc := coeff_last_ne_zero_of_pos_size (poly J f g) hrootPos
    rw [coeff_poly, ite_eq_left hell] at hc
    have hzero : (Zero.zero : R) = 0 := rfl
    change coeffMinorAt df dg J ell f g ≠ (Zero.zero : R)
    simpa only [df, dg, ell, coeffMinor] using hc
  let du := u - scale d (cofactorU J f g)
  let dv := v - scale d (cofactorV J f g)
  have hscaleU : (scale d (cofactorU J f g)).size ≤ dg - J := by
    rw [scale_eq_scaleImpl]
    exact Nat.le_trans (size_scaleImpl_le _ _) (cofactorU_size_le J f g)
  have hscaleV : (scale d (cofactorV J f g)).size ≤ df - J := by
    rw [scale_eq_scaleImpl]
    exact Nat.le_trans (size_scaleImpl_le _ _) (cofactorV_size_le J f g)
  have hdu : du.size ≤ dg - J := by
    exact Nat.le_trans (size_sub_le_max _ _)
      (Nat.max_le.mpr ⟨by simpa only [dg] using hu, hscaleU⟩)
  have hdv : dv.size ≤ df - J := by
    exact Nat.le_trans (size_sub_le_max _ _)
      (Nat.max_le.mpr ⟨by simpa only [df] using hv, hscaleV⟩)
  have hcanon := cofactor_bezout J f g hgf hJ
  have hzero : du * f + dv * g = 0 := by
    dsimp only [du, dv]
    have hdistU : (u - scale d (cofactorU J f g)) * f =
        u * f - scale d (cofactorU J f g) * f := by grind
    have hdistV : (v - scale d (cofactorV J f g)) * g =
        v * g - scale d (cofactorV J f g) * g := by grind
    rw [hdistU, hdistV, ← scale_mul, ← scale_mul]
    have hrearr :
        u * f - scale d (cofactorU J f g * f) +
            (v * g - scale d (cofactorV J f g * g)) =
          (u * f + v * g) -
            (scale d (cofactorU J f g * f) +
              scale d (cofactorV J f g * g)) := by grind
    rw [hrearr, ← scale_add]
    rw [hcanon, hrepr]
    grind
  have huniq := bounded_bezout_unique df dg J ell f g du dv hJ hminor
    hdu hdv hzero
  constructor
  · dsimp only [du] at huniq
    grind
  · dsimp only [dv] at huniq
    grind

end Base

end Subresultant
end DensePoly
end Hex
