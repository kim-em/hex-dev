/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.DeterminantAlgebra
import all HexResultant.DeterminantAlgebra

public section

/-!
Consecutive-block transformations for the local resultant determinant.

The generalized Sylvester swap law exchanges its two consecutive coefficient
blocks.  This module realizes that exchange as adjacent column swaps, tracks
the determinant sign, and keeps the construction independent of the matrix
and determinant libraries.
-/

namespace Hex

universe u

namespace SubresultantMinor

/-- Reindex a square coefficient family along an equality of dimensions. -/
@[expose]
def castSquare {R : Type u} {n m : Nat} (h : n = m)
    (M : Square R n) : Square R m :=
  fun i j => M (Fin.cast h.symm i) (Fin.cast h.symm j)

@[simp, grind =]
theorem castSquare_rfl {R : Type u} {n : Nat} (M : Square R n) :
    castSquare rfl M = M := by
  rfl

@[simp, grind =]
theorem castSquare_apply {R : Type u} {n m : Nat} (h : n = m)
    (M : Square R n) (i j : Fin m) :
    castSquare h M i j = M (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  rfl

/-- Reindexing along a dimension equality does not change the local
determinant. -/
theorem det_castSquare {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (h : n = m) (M : Square R n) :
    det (castSquare h M) = det M := by
  subst m
  rfl

/-- Swap the columns at numeric positions `left` and `left + 1`. -/
@[expose]
def swapAt {R : Type u} {n : Nat} (M : Square R n) (left : Nat)
    (h : left + 1 < n) : Square R n :=
  fun i j =>
    if j.val = left then M i ⟨left + 1, h⟩
    else if j.val = left + 1 then M i ⟨left, by omega⟩
    else M i j

@[simp, grind =]
theorem swapAt_apply {R : Type u} {n : Nat} (M : Square R n)
    (left : Nat) (h : left + 1 < n) (i j : Fin n) :
    swapAt M left h i j =
      if j.val = left then M i ⟨left + 1, h⟩
      else if j.val = left + 1 then M i ⟨left, by omega⟩
      else M i j := by
  rfl

/-- A numeric adjacent-column swap negates the local determinant. -/
theorem det_swapAt {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R n) (left : Nat) (h : left + 1 < n) :
    det (swapAt M left h) = 0 - det M := by
  cases n with
  | zero => omega
  | succ n =>
      let left' : Fin n := ⟨left, by omega⟩
      have hmatrix : swapAt M left h = swapAdjacent M left' := by
        funext i j
        simp only [swapAt, swapAdjacent]
        by_cases hjl : j.val = left
        · rw [if_pos hjl]
          have hj : j = left'.castSucc := by
            apply Fin.ext
            exact hjl
          rw [if_pos hj]
          apply congrArg (M i)
          apply Fin.ext
          simp [left']
        · rw [if_neg hjl]
          have hjl' : j ≠ left'.castSucc := by
            intro hj
            exact hjl (congrArg Fin.val hj)
          rw [if_neg hjl']
          by_cases hjr : j.val = left + 1
          · rw [if_pos hjr]
            have hj : j = left'.succ := by
              apply Fin.ext
              simpa [left'] using hjr
            rw [if_pos hj]
            apply congrArg (M i)
            apply Fin.ext
            simp [left']
          · rw [if_neg hjr]
            have hjr' : j ≠ left'.succ := by
              intro hj
              apply hjr
              simpa [left'] using congrArg Fin.val hj
            rw [if_neg hjr']
      rw [hmatrix, det_swapAdjacent]

/-- Move the column at `start + count` to `start`, shifting the intervening
columns one position to the right. -/
@[expose]
def moveLeft {R : Type u} {n : Nat} (M : Square R n) (start : Nat) :
    (count : Nat) → start + count < n → Square R n
  | 0, _ => M
  | count + 1, h =>
      moveLeft (swapAt M (start + count) (by omega)) start count (by omega)

/-- Entrywise action of moving one column left across a consecutive range. -/
theorem moveLeft_apply {R : Type u} {n : Nat} (M : Square R n)
    (start count : Nat) (h : start + count < n) (i j : Fin n) :
    moveLeft M start count h i j =
      if j.val = start then M i ⟨start + count, h⟩
      else if start < j.val ∧ j.val ≤ start + count then
        M i ⟨j.val - 1, by omega⟩
      else M i j := by
  induction count generalizing M with
  | zero =>
      by_cases hs : j.val = start
      · have hj : j = ⟨start, by omega⟩ := Fin.ext hs
        subst j
        simp [moveLeft]
      · have hmid : ¬(start < j.val ∧ j.val ≤ start) := by omega
        simp [moveLeft, hs, hmid]
  | succ count ih =>
      rw [moveLeft, ih]
      by_cases hs : j.val = start
      · simp [hs, swapAt]
        apply congrArg (M i)
        apply Fin.ext
        simp [Nat.add_assoc]
      · by_cases hmid : start < j.val ∧ j.val ≤ start + count
        · have hnew : start < j.val ∧ j.val ≤ start + (count + 1) := by
            omega
          have hpredLeft : j.val - 1 ≠ start + count := by omega
          have hpredRight : j.val - 1 ≠ start + count + 1 := by omega
          simp [hs, hmid, hnew, swapAt, hpredLeft, hpredRight]
        · by_cases hend : j.val = start + count + 1
          · have hj : j = ⟨start + count + 1, by omega⟩ := Fin.ext hend
            subst j
            have hns : start + count + 1 ≠ start := by omega
            have hpos : start < start + count + 1 := by omega
            have hold : ¬(start + count + 1 ≤ start + count) := by omega
            have hnew : start + count + 1 ≤ start + (count + 1) := by omega
            simp [swapAt, hns, hpos, hold, hnew]
          · have hnew : ¬(start < j.val ∧ j.val ≤ start + (count + 1)) := by
              omega
            have hleft : j.val ≠ start + count := by
              intro heq
              apply hmid
              omega
            simp [hs, hmid, hend, hnew, swapAt, hleft]

/-- Moving a column left across `count` positions contributes the parity sign
of `count`. -/
theorem det_moveLeft {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R n) (start count : Nat) (h : start + count < n) :
    det (moveLeft M start count h) = sign (R := R) count * det M := by
  induction count generalizing M with
  | zero =>
      simp [moveLeft, sign] <;> grind
  | succ count ih =>
      rw [moveLeft, ih, det_swapAt, sign_succ]
      grind

/-- Rotate consecutive blocks of lengths `left` and `right` beginning at
`start`, changing `[A, B]` to `[B, A]`. -/
@[expose]
def rotateBlocks {R : Type u} {n : Nat} (M : Square R n)
    (start left : Nat) : (right : Nat) → start + left + right ≤ n → Square R n
  | 0, _ => M
  | right + 1, h =>
      rotateBlocks (moveLeft M start left (by omega)) (start + 1) left right
        (by omega)

/-- The column of the original matrix appearing at a given position after a
consecutive-block rotation. -/
@[expose]
def rotateIndex {n : Nat} (start left right : Nat)
    (h : start + left + right ≤ n) (j : Fin n) : Fin n :=
  if hj : start ≤ j.val ∧ j.val < start + right then
    ⟨j.val + left, by omega⟩
  else if hk : start + right ≤ j.val ∧
      j.val < start + right + left then
    ⟨j.val - right, by
      have := j.isLt
      omega⟩
  else j

/-- Entrywise action of rotating two consecutive column blocks. -/
theorem rotateBlocks_apply {R : Type u} {n : Nat} (M : Square R n)
    (start left right : Nat) (h : start + left + right ≤ n)
    (i j : Fin n) :
    rotateBlocks M start left right h i j =
      M i (rotateIndex start left right h j) := by
  induction right generalizing M start with
  | zero =>
      have hfirst : ¬(start ≤ j.val ∧ j.val < start) := by omega
      have hindex : rotateIndex start left 0 h j = j := by
        apply Fin.ext
        simp [rotateIndex, hfirst]
      simp [rotateBlocks, hindex]
  | succ right ih =>
      rw [rotateBlocks, ih]
      by_cases hstart : j.val = start
      · have hrecFirst :
            ¬(start + 1 ≤ j.val ∧ j.val < start + 1 + right) := by omega
        have hrecSecond :
            ¬(start + 1 + right ≤ j.val ∧
              j.val < start + 1 + right + left) := by omega
        have hfirst : start ≤ j.val ∧ j.val < start + (right + 1) := by
          omega
        have hrecIndex :
            rotateIndex (start + 1) left right (by omega) j = j := by
          apply Fin.ext
          simp [rotateIndex, hrecFirst, hrecSecond]
        let shifted : Fin n := ⟨start + left, by omega⟩
        have hfinalIndex :
            rotateIndex start left (right + 1) h j = shifted := by
          apply Fin.ext
          simp [rotateIndex, hstart, shifted]
        rw [hrecIndex, hfinalIndex, moveLeft_apply]
        rw [if_pos hstart]
      · by_cases hfirst : start ≤ j.val ∧ j.val < start + (right + 1)
        · have hrecFirst :
              start + 1 ≤ j.val ∧ j.val < start + 1 + right := by omega
          let shifted : Fin n := ⟨j.val + left, by omega⟩
          have hrecIndex :
              rotateIndex (start + 1) left right (by omega) j = shifted := by
            apply Fin.ext
            simp [rotateIndex, hrecFirst, shifted]
          have hfinalIndex :
              rotateIndex start left (right + 1) h j = shifted := by
            apply Fin.ext
            simp [rotateIndex, hfirst, shifted]
          have hshiftStart : shifted.val ≠ start := by
            simp [shifted]
            omega
          have hshiftMiddle :
              ¬(start < shifted.val ∧ shifted.val ≤ start + left) := by
            simp [shifted]
            omega
          rw [hrecIndex, hfinalIndex, moveLeft_apply]
          rw [if_neg hshiftStart, if_neg hshiftMiddle]
        · by_cases hsecond :
            start + (right + 1) ≤ j.val ∧
              j.val < start + (right + 1) + left
          · have hrecSecond :
                start + 1 + right ≤ j.val ∧
                  j.val < start + 1 + right + left := by omega
            have hrecFirst :
                ¬(start + 1 ≤ j.val ∧ j.val < start + 1 + right) := by
              omega
            let middle : Fin n := ⟨j.val - right, by
              have := j.isLt
              omega⟩
            let shifted : Fin n := ⟨j.val - (right + 1), by
              have := j.isLt
              omega⟩
            have hrecIndex :
                rotateIndex (start + 1) left right (by omega) j = middle := by
              apply Fin.ext
              simp [rotateIndex, hrecFirst, hrecSecond, middle]
            have hfinalIndex :
                rotateIndex start left (right + 1) h j = shifted := by
              apply Fin.ext
              simp [rotateIndex, hfirst, hsecond, shifted]
            have hlookup :
                start < j.val - right ∧
                  j.val - right ≤ start + left := by omega
            have hmiddleStart : middle.val ≠ start := by
              simp [middle]
              omega
            rw [hrecIndex, hfinalIndex, moveLeft_apply]
            rw [if_neg hmiddleStart, if_pos hlookup]
            apply congrArg (M i)
            apply Fin.ext
            simp [middle, shifted]
            omega
          · have hrecFirst :
                ¬(start + 1 ≤ j.val ∧
                  j.val < start + 1 + right) := by omega
            have hrecSecond :
                ¬(start + 1 + right ≤ j.val ∧
                  j.val < start + 1 + right + left) := by omega
            have hlookup :
                ¬(start < j.val ∧ j.val ≤ start + left) := by omega
            have hrecIndex :
                rotateIndex (start + 1) left right (by omega) j = j := by
              apply Fin.ext
              simp [rotateIndex, hrecFirst, hrecSecond]
            have hfinalIndex :
                rotateIndex start left (right + 1) h j = j := by
              apply Fin.ext
              simp [rotateIndex, hfirst, hsecond]
            rw [hrecIndex, hfinalIndex, moveLeft_apply]
            simp [hstart, hlookup]

/-- Rotating consecutive blocks contributes one adjacent swap for each pair
of columns drawn from opposite blocks. -/
theorem det_rotateBlocks {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R n) (start left right : Nat)
    (h : start + left + right ≤ n) :
    det (rotateBlocks M start left right h) =
      sign (R := R) (left * right) * det M := by
  induction right generalizing M start with
  | zero =>
      simp [rotateBlocks, sign] <;> grind
  | succ right ih =>
      rw [rotateBlocks, ih, det_moveLeft]
      have hsign := sign_add (R := R) (left * right) left
      rw [Nat.mul_succ, hsign]
      grind

end SubresultantMinor

namespace DensePoly
namespace Subresultant

section Swap

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]

/-- Rotating the two coefficient blocks of a generalized Sylvester matrix
produces the matrix with its polynomial inputs exchanged. -/
theorem coeffMatrixAt_rotate (df dg J l : Nat) (f g : DensePoly R) :
    SubresultantMinor.castSquare (by omega)
        (SubresultantMinor.rotateBlocks
          (coeffMatrixAt df dg J l f g) 0 (dg - J) (df - J) (by omega)) =
      coeffMatrixAt dg df J l g f := by
  funext i j
  simp only [SubresultantMinor.castSquare]
  rw [SubresultantMinor.rotateBlocks_apply]
  by_cases hj : j.val < df - J
  · let source : Fin ((df - J) + (dg - J)) :=
      ⟨j.val + (dg - J), by
        have := j.isLt
        omega⟩
    have hindex :
        SubresultantMinor.rotateIndex 0 (dg - J) (df - J)
            (show 0 + (dg - J) + (df - J) ≤
              (df - J) + (dg - J) by omega)
            (Fin.cast (show (dg - J) + (df - J) =
              (df - J) + (dg - J) by omega) j) = source := by
      apply Fin.ext
      simp [SubresultantMinor.rotateIndex, hj, source, Fin.cast]
    rw [hindex]
    have hright : ¬j.val + (dg - J) < dg - J := by omega
    have hsub : j.val + (dg - J) - (dg - J) = j.val := by omega
    have hrow :
        i.val = (df - J) + (dg - J) - 1 ↔
          i.val = (dg - J) + (df - J) - 1 := by omega
    simp [coeffMatrixAt, source, hj, hright, hsub, hrow, Fin.cast]
  · let source : Fin ((df - J) + (dg - J)) :=
      ⟨j.val - (df - J), by
        have := j.isLt
        omega⟩
    have hindex :
        SubresultantMinor.rotateIndex 0 (dg - J) (df - J)
            (show 0 + (dg - J) + (df - J) ≤
              (df - J) + (dg - J) by omega)
            (Fin.cast (show (dg - J) + (df - J) =
              (df - J) + (dg - J) by omega) j) = source := by
      apply Fin.ext
      have hlower : df ≤ j.val + J := by omega
      have hupper : j.val < (df - J) + (dg - J) := by
        have := j.isLt
        omega
      simp [SubresultantMinor.rotateIndex, hj, hlower, hupper, source,
        Fin.cast]
    rw [hindex]
    have hleft : j.val - (df - J) < dg - J := by omega
    have hrow :
        i.val = (df - J) + (dg - J) - 1 ↔
          i.val = (dg - J) + (df - J) - 1 := by omega
    simp [coeffMatrixAt, source, hj, hleft, hrow, Fin.cast]

/-- Exchanging the inputs of a fixed-degree coefficient minor contributes
the parity of the product of the two block lengths. -/
theorem coeffMinorAt_swap (df dg J l : Nat) (f g : DensePoly R) :
    coeffMinorAt df dg J l f g =
      SubresultantMinor.sign (R := R) ((df - J) * (dg - J)) *
        coeffMinorAt dg df J l g f := by
  have hswap :
      coeffMinorAt dg df J l g f =
        SubresultantMinor.sign (R := R) ((df - J) * (dg - J)) *
          coeffMinorAt df dg J l f g := by
    unfold coeffMinorAt
    rw [← coeffMatrixAt_rotate]
    rw [SubresultantMinor.det_castSquare,
      SubresultantMinor.det_rotateBlocks]
    congr 2
    exact Nat.mul_comm _ _
  rw [hswap, ← Lean.Grind.Semiring.mul_assoc,
    SubresultantMinor.sign_mul_self]
  grind

/-- Exchanging the inputs of a generalized coefficient minor contributes
the standard degree-product sign. -/
theorem coeffMinor_swap (J l : Nat) (f g : DensePoly R) :
    coeffMinor J l f g =
      SubresultantMinor.sign (R := R)
          ((formalDegree f - J) * (formalDegree g - J)) *
        coeffMinor J l g f := by
  unfold coeffMinor
  exact coeffMinorAt_swap (formalDegree f) (formalDegree g) J l f g

/-- Generalized Sylvester subresultants obey the standard input-swap sign
law. -/
theorem poly_swap (J : Nat) (f g : DensePoly R) :
    poly J f g =
      scale
        (SubresultantMinor.sign (R := R)
          ((formalDegree f - J) * (formalDegree g - J)))
        (poly J g f) := by
  apply ext_coeff
  intro l
  rw [coeff_scale_semiring]
  simp only [coeff_poly]
  by_cases hl : l < J + 1
  · rw [if_pos hl, if_pos hl, coeffMinor_swap]
  · rw [if_neg hl, if_neg hl]
    exact (Lean.Grind.Semiring.mul_zero _).symm

end Swap
end Subresultant
end DensePoly
end Hex
