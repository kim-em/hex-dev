/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank
public import HexMatrixMathlib.Algebra
public import HexDeterminantMathlib.Core
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

public section

/-!
Soundness of the rank checker for `Matrix.rank`.

A checked certificate transports to three identities about the Mathlib matrix
`matrixEquiv A`, and those identities force `Matrix.rank` to be the certified
rank over the domain itself (`checkRank_sound`) and after any injective ring
homomorphism into a domain (`checkRank_sound_map`).
-/

open Matrix

namespace HexMatrixMathlib

universe u v

variable {R : Type u} {n m : Nat}

/-- The executable identity matrix is Mathlib's. -/
theorem matrixEquiv_identity [Zero R] [One R] (k : Nat) :
    matrixEquiv (Hex.Matrix.identity (R := R) k) = (1 : Matrix (Fin k) (Fin k) R) := by
  ext i j
  rw [matrixEquiv_apply, Hex.Matrix.getElem_identity, Matrix.one_apply]

/-- The three identities of a checked certificate, on the Mathlib side. -/
theorem checkRank_iff_matrixEquiv [CommRing R] [DecidableEq R] (A : Hex.Matrix R n m)
    (c : Hex.Matrix.RankCert R n m) :
    Hex.Matrix.checkRank A c = true ↔
      c.denom ≠ 0 ∧
      (matrixEquiv A).submatrix c.rows.get c.cols.get * matrixEquiv c.adj =
        c.denom • (1 : Matrix (Fin c.rank) (Fin c.rank) R) ∧
      c.denom • matrixEquiv A =
        (matrixEquiv A).submatrix id c.cols.get *
          (matrixEquiv c.adj * (matrixEquiv A).submatrix c.rows.get id) := by
  rw [Hex.Matrix.checkRank_iff]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · rw [← matrixEquiv.injective.eq_iff, matrixEquiv_mul, matrixEquiv_smul,
      matrixEquiv_selectedSubmatrix, matrixEquiv_identity]
  · rw [← matrixEquiv.injective.eq_iff, matrixEquiv_mul, matrixEquiv_mul, matrixEquiv_smul,
      matrixEquiv_selectCols, matrixEquiv_selectRows]

/-- The three certificate identities force the rank: a nonsingular `r × r`
block bounds it below, and the all-column identity bounds it above. -/
theorem rank_eq_of_cert [CommRing R] [IsDomain R] {r : Nat} (M : Matrix (Fin n) (Fin m) R)
    (rows : Fin r → Fin n) (cols : Fin r → Fin m) (d : R) (adj : Matrix (Fin r) (Fin r) R)
    (hd : d ≠ 0) (h2 : M.submatrix rows cols * adj = d • 1)
    (h3 : d • M = M.submatrix id cols * (adj * M.submatrix rows id)) :
    M.rank = r := by
  apply le_antisymm
  · calc M.rank = (d • M).rank :=
          (rank_smul_of_mem_nonZeroDivisors M (mem_nonZeroDivisors_of_ne_zero hd)).symm
      _ ≤ (M.submatrix id cols).rank := by rw [h3]; exact rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin r) := rank_le_card_width _
      _ = r := Fintype.card_fin r
  · have hdet : (M.submatrix rows cols).det ≠ 0 := by
      intro h0
      have hdet := congrArg det h2
      rw [det_mul, det_smul, det_one, mul_one, h0, zero_mul, Fintype.card_fin] at hdet
      exact pow_ne_zero r hd hdet.symm
    calc r = Fintype.card (Fin r) := (Fintype.card_fin r).symm
      _ = (M.submatrix rows cols).rank := (rank_of_det_ne_zero hdet).symm
      _ ≤ M.rank := rank_submatrix_le _ _ _

/-- A checked certificate determines `Matrix.rank` over the domain. -/
theorem checkRank_sound [CommRing R] [IsDomain R] [DecidableEq R] {A : Hex.Matrix R n m}
    {c : Hex.Matrix.RankCert R n m} (h : Hex.Matrix.checkRank A c = true) :
    (matrixEquiv A).rank = c.rank := by
  obtain ⟨hd, h2, h3⟩ := (checkRank_iff_matrixEquiv A c).mp h
  exact rank_eq_of_cert _ _ _ _ _ hd h2 h3

/-- A checked certificate determines `Matrix.rank` after any injective ring
homomorphism into a domain. -/
theorem checkRank_sound_map {S : Type v} [CommRing R] [CommRing S] [IsDomain S] [DecidableEq R]
    (φ : R →+* S) (hφ : Function.Injective φ) {A : Hex.Matrix R n m}
    {c : Hex.Matrix.RankCert R n m} (h : Hex.Matrix.checkRank A c = true) :
    ((matrixEquiv A).map φ).rank = c.rank := by
  obtain ⟨hd, h2, h3⟩ := (checkRank_iff_matrixEquiv A c).mp h
  refine rank_eq_of_cert ((matrixEquiv A).map φ) c.rows.get c.cols.get (φ c.denom)
    ((matrixEquiv c.adj).map φ) ?_ ?_ ?_
  · intro h0
    exact hd (hφ (h0.trans (map_zero φ).symm))
  · have h2' := congrArg (fun M => M.map φ) h2
    simp only [Matrix.map_mul] at h2'
    rw [Matrix.submatrix_map, h2']
    ext i j
    by_cases hij : i = j <;> simp [hij]
  · have h3' := congrArg (fun M => M.map φ) h3
    simp only [Matrix.map_mul] at h3'
    rw [Matrix.submatrix_map, Matrix.submatrix_map, ← h3']
    ext i j
    simp

end HexMatrixMathlib
