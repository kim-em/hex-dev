/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.FractionPoly

public section

/-!
Coefficient-indexed generalized Sylvester minors.

This module is proof infrastructure for Brown exactness.  It deliberately uses
finite functions rather than `Hex.Matrix`: `hex-resultant` remains dependent
only on `hex-poly`.  The determinant is a local Laplace recursion, and the
subresultant polynomial is assembled from its scalar coefficient minors.
-/

namespace Hex

universe u

namespace SubresultantMinor

/-- A proof-only square coefficient family. -/
abbrev Square (R : Type u) (n : Nat) := Fin n → Fin n → R

/-- Embed an index while skipping one position. -/
@[expose]
def skipIndex {n : Nat} (j : Fin (n + 1)) (k : Fin n) : Fin (n + 1) :=
  if h : k.val < j.val then
    ⟨k.val, by omega⟩
  else
    ⟨k.val + 1, by omega⟩

/-- Remove the first row and one selected column. -/
@[expose]
def deleteFirst {R : Type u} {n : Nat} (M : Square R (n + 1))
    (j : Fin (n + 1)) : Square R n :=
  fun i k => M i.succ (skipIndex j k)

/-- The alternating sign in a first-row Laplace expansion. -/
@[expose]
def sign {R : Type u} [Zero R] [One R] [Sub R] (j : Nat) : R :=
  if j % 2 = 0 then 1 else 0 - 1

/-- Local proof-only determinant, defined by first-row Laplace expansion.
Its factorial recursion is not an executable resultant algorithm. -/
@[expose]
def det {R : Type u} [Zero R] [One R] [Add R] [Sub R] [Mul R] :
    {n : Nat} → Square R n → R
  | 0, _ => 1
  | n + 1, M =>
      (List.finRange (n + 1)).foldl
        (fun acc j =>
          acc + sign j.val * M ⟨0, by omega⟩ j * det (deleteFirst M j)) 0

@[simp, grind =]
theorem det_zero {R : Type u} [Zero R] [One R] [Add R] [Sub R] [Mul R]
    (M : Square R 0) : det M = 1 := by
  rfl

namespace Fraction

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
  [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]

omit [DecidableEq R] in
private theorem sign_map (j : Nat) :
    Hex.Fraction.ofCoeff (sign (R := R) j) =
      sign (R := Hex.Fraction R) j := by
  unfold sign
  by_cases h : j % 2 = 0
  · rw [if_pos h, if_pos h]
    exact Hex.Fraction.ofCoeff_one
  · rw [if_neg h, if_neg h, Hex.Fraction.ofCoeff_sub]
    change Hex.Fraction.ofCoeff (Zero.zero : R) -
        Hex.Fraction.ofCoeff (One.one : R) =
      (Zero.zero : Hex.Fraction R) - (One.one : Hex.Fraction R)
    rw [Hex.Fraction.ofCoeff_zero, Hex.Fraction.ofCoeff_one]

omit [DecidableEq R] in
/-- The coefficient embedding commutes with the local determinant. -/
theorem det_map {n : Nat} (M : Square R n) :
    det (fun i j => Hex.Fraction.ofCoeff (M i j)) =
      Hex.Fraction.ofCoeff (det M) := by
  induction n with
  | zero =>
      simp only [det]
      exact Hex.Fraction.ofCoeff_one.symm
  | succ n ih =>
      simp only [det]
      let row : Fin (n + 1) := ⟨0, by omega⟩
      let stepR := fun (acc : R) (j : Fin (n + 1)) =>
        acc + sign j.val * M row j * det (deleteFirst M j)
      let stepF := fun (acc : Hex.Fraction R) (j : Fin (n + 1)) =>
        acc + sign j.val * Hex.Fraction.ofCoeff (M row j) *
          det (deleteFirst (fun i k => Hex.Fraction.ofCoeff (M i k)) j)
      have hminor (j : Fin (n + 1)) :
          det (deleteFirst (fun i k => Hex.Fraction.ofCoeff (M i k)) j) =
            Hex.Fraction.ofCoeff (det (deleteFirst M j)) := by
        change det (fun i k => Hex.Fraction.ofCoeff ((deleteFirst M j) i k)) = _
        exact ih (deleteFirst M j)
      have hstep (acc : R) (j : Fin (n + 1)) :
          stepF (Hex.Fraction.ofCoeff acc) j =
            Hex.Fraction.ofCoeff (stepR acc j) := by
        unfold stepF stepR
        rw [hminor, ← sign_map, ← Hex.Fraction.ofCoeff_mul,
          ← Hex.Fraction.ofCoeff_mul, ← Hex.Fraction.ofCoeff_add]
      have hfold (xs : List (Fin (n + 1))) (acc : R) :
          xs.foldl stepF (Hex.Fraction.ofCoeff acc) =
            Hex.Fraction.ofCoeff (xs.foldl stepR acc) := by
        induction xs generalizing acc with
        | nil => rfl
        | cons j js hjs =>
            simp only [List.foldl_cons]
            rw [hstep, hjs]
      change (List.finRange (n + 1)).foldl stepF
          (Hex.Fraction.ofCoeff (Zero.zero : R)) = _
      exact hfold (List.finRange (n + 1)) (Zero.zero : R)

end Fraction
end SubresultantMinor

namespace DensePoly
namespace Subresultant

section Base

variable {R : Type u} [Zero R] [DecidableEq R]

/-- Read a coefficient at an integer index, returning zero below index zero. -/
@[expose]
def coeffInt (p : DensePoly R) (i : Int) : R :=
  if i < 0 then 0 else p.coeff i.toNat

/-- Integer-indexed coefficient lookup distributes over polynomial addition. -/
theorem coeffInt_add {S : Type u} [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (t : Int) :
    coeffInt (p + q) t = coeffInt p t + coeffInt q t := by
  by_cases ht : t < 0
  · unfold coeffInt
    rw [if_pos ht, if_pos ht, if_pos ht]
    grind
  · unfold coeffInt
    rw [if_neg ht, if_neg ht, if_neg ht, coeff_add_semiring]

/-- Default formal degree: zero and nonzero constants both have degree zero. -/
@[expose]
def formalDegree (p : DensePoly R) : Nat :=
  p.size - 1

/-- Scalar coefficient matrix at explicit formal degrees.  Keeping the degree
parameters separate makes coefficient embeddings definitionally
dimension-preserving. -/
@[expose]
def coeffMatrixAt (df dg J l : Nat) (f g : DensePoly R) :
    SubresultantMinor.Square R ((df - J) + (dg - J)) :=
  fun i j =>
    let left := dg - J
    let right := df - J
    let n := right + left
    if j.val < left then
      if i.val = n - 1 then
        coeffInt f (Int.ofNat l - Int.ofNat (left - 1) + Int.ofNat j.val)
      else
        coeffInt f (Int.ofNat df - Int.ofNat i.val + Int.ofNat j.val)
    else
      let jj := j.val - left
      if i.val = n - 1 then
        coeffInt g (Int.ofNat l - Int.ofNat (right - 1) + Int.ofNat jj)
      else
        coeffInt g (Int.ofNat dg - Int.ofNat i.val + Int.ofNat jj)

/-- One scalar coefficient minor at explicit formal degrees. -/
@[expose]
def coeffMinorAt [One R] [Add R] [Sub R] [Mul R]
    (df dg J l : Nat) (f g : DensePoly R) : R :=
  SubresultantMinor.det (coeffMatrixAt df dg J l f g)

/-- One scalar coefficient minor of the `J`-th generalized subresultant. -/
@[expose]
def coeffMinor [One R] [Add R] [Sub R] [Mul R]
    (J l : Nat) (f g : DensePoly R) : R :=
  coeffMinorAt (formalDegree f) (formalDegree g) J l f g

/-- Generalized Sylvester subresultant, assembled coefficientwise from scalar
minors.  Its degree is at most `J`. -/
@[expose]
def poly [One R] [Add R] [Sub R] [Mul R]
    (J : Nat) (f g : DensePoly R) : DensePoly R :=
  ofList ((List.range (J + 1)).map fun l => coeffMinor J l f g)

@[simp, grind =]
theorem coeff_poly [One R] [Add R] [Sub R] [Mul R]
    (J : Nat) (f g : DensePoly R) (l : Nat) :
    (poly J f g).coeff l =
      if l < J + 1 then coeffMinor J l f g else Zero.zero := by
  by_cases h : l < J + 1
  · simp [poly, h]
  · simp [poly, h]

/-- The coefficient construction stores no terms above subresultant index
`J`. -/
theorem poly_size_le [One R] [Add R] [Sub R] [Mul R]
    (J : Nat) (f g : DensePoly R) :
    (poly J f g).size ≤ J + 1 := by
  exact Nat.le_trans (size_ofList_le _)
    (by simp)

end Base

namespace Fraction

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
  [Div R] [ExactDivLaws R]
  [Hex.Fraction.NonzeroOne R]

@[simp]
theorem coeffInt_map (p : DensePoly R) (i : Int) :
    coeffInt (DensePoly.Fraction.map p) i =
      Hex.Fraction.ofCoeff (coeffInt p i) := by
  unfold coeffInt
  by_cases h : i < 0
  · rw [if_pos h, if_pos h]
    exact Hex.Fraction.ofCoeff_zero.symm
  · simp [h, DensePoly.Fraction.coeff_map]

@[simp]
theorem formalDegree_map (p : DensePoly R) :
    formalDegree (DensePoly.Fraction.map p) = formalDegree p := by
  simp [formalDegree]

/-- A coefficient minor at fixed formal degrees is preserved by the fraction
embedding. -/
theorem coeffMinorAt_map (df dg J l : Nat) (f g : DensePoly R) :
    coeffMinorAt df dg J l (DensePoly.Fraction.map f)
        (DensePoly.Fraction.map g) =
      Hex.Fraction.ofCoeff (coeffMinorAt df dg J l f g) := by
  unfold coeffMinorAt
  have hmatrix :
      coeffMatrixAt df dg J l (DensePoly.Fraction.map f)
          (DensePoly.Fraction.map g) =
        fun i j => Hex.Fraction.ofCoeff ((coeffMatrixAt df dg J l f g) i j) := by
    funext i j
    simp only [coeffMatrixAt]
    split <;> split <;> simp
  rw [hmatrix, SubresultantMinor.Fraction.det_map]

/-- Every generalized subresultant coefficient is preserved by the fraction
embedding. -/
theorem coeffMinor_map (J l : Nat) (f g : DensePoly R) :
    coeffMinor J l (DensePoly.Fraction.map f) (DensePoly.Fraction.map g) =
      Hex.Fraction.ofCoeff (coeffMinor J l f g) := by
  unfold coeffMinor
  rw [formalDegree_map, formalDegree_map]
  exact coeffMinorAt_map (formalDegree f) (formalDegree g) J l f g

/-- Generalized Sylvester subresultants commute with the polynomial
coefficient embedding.  In particular, every coefficient of the fraction
construction has an explicit base-ring image witness. -/
theorem poly_map (J : Nat) (f g : DensePoly R) :
    poly J (DensePoly.Fraction.map f) (DensePoly.Fraction.map g) =
      DensePoly.Fraction.map (poly J f g) := by
  apply ext_coeff
  intro l
  simp only [coeff_poly, DensePoly.Fraction.coeff_map]
  by_cases h : l < J + 1
  · rw [if_pos h, if_pos h, coeffMinor_map]
  · rw [if_neg h, if_neg h]
    exact Hex.Fraction.ofCoeff_zero.symm

/-- Coefficients of mapped generalized subresultants lie in the coefficient
embedding image. -/
theorem exists_coeff (J : Nat) (f g : DensePoly R) (l : Nat) :
    ∃ c : R,
      Hex.Fraction.ofCoeff c =
        (poly J (DensePoly.Fraction.map f) (DensePoly.Fraction.map g)).coeff l := by
  refine ⟨(poly J f g).coeff l, ?_⟩
  rw [poly_map, DensePoly.Fraction.coeff_map]

end Fraction
end Subresultant
end DensePoly
end Hex
