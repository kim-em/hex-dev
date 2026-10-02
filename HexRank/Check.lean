/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Cert

public section

/-!
Mathlib-free soundness of the rank checker.

Over a nontrivial ring without zero divisors (`Hex.DomainLaws`), a checked
certificate of rank `r` has a nonzero `r × r` minor (`RankCert.det_ne_zero`)
and every `(r + 1) × (r + 1)` minor vanishes (`RankCert.det_succ_eq_zero`), so
`r` is the largest size of a nonzero minor. At `r = 0` the matrix is zero
(`RankCert.matrix_eq_zero`). Neither proof mentions a quotient operation or
how the certificate was produced.
-/

namespace Hex

universe u

/-- Powers of a nonzero element of a domain are nonzero. -/
theorem DomainLaws.pow_ne_zero {R : Type u} [Lean.Grind.CommRing R] [DomainLaws R]
    {d : R} (hd : d ≠ 0) : ∀ k : Nat, d ^ k ≠ 0
  | 0 => by
    rw [Lean.Grind.Semiring.pow_zero]
    exact DomainLaws.one_ne_zero
  | k + 1 => by
    rw [Lean.Grind.Semiring.pow_succ]
    intro h
    rcases DomainLaws.no_zero_div _ _ h with h0 | h0
    · exact DomainLaws.pow_ne_zero hd k h0
    · exact hd h0

/-- A product with a nonzero left factor vanishes only if the right factor
does. -/
theorem DomainLaws.eq_zero_of_mul_eq_zero {R : Type u} [Lean.Grind.CommRing R] [DomainLaws R]
    {d x : R} (hd : d ≠ 0) (h : d * x = 0) : x = 0 := by
  rcases DomainLaws.no_zero_div _ _ h with h0 | h0
  · exact absurd h0 hd
  · exact h0

namespace Matrix

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] [DomainLaws R] {n m : Nat}

/-- Lower bound: the selected block of a checked certificate is nonsingular. -/
theorem RankCert.det_ne_zero {A : Matrix R n m} {c : RankCert R n m}
    (h : checkRank A c = true) :
    det (selectedSubmatrix A c.rows c.cols) ≠ 0 := by
  obtain ⟨hd, h2, _⟩ := (checkRank_iff A c).mp h
  have hdet := congrArg det h2
  rw [det_mul, det_smul, det_identity, Lean.Grind.Semiring.mul_one] at hdet
  intro h0
  rw [h0, Lean.Grind.Semiring.zero_mul] at hdet
  exact DomainLaws.pow_ne_zero hd c.rank hdet.symm

/-- Upper bound: every minor one size larger than a checked certificate's rank
vanishes. -/
theorem RankCert.det_succ_eq_zero {A : Matrix R n m} {c : RankCert R n m}
    (h : checkRank A c = true)
    (rows : Vector (Fin n) (c.rank + 1)) (cols : Vector (Fin m) (c.rank + 1)) :
    det (selectedSubmatrix A rows cols) = 0 := by
  obtain ⟨hd, _, h3⟩ := (checkRank_iff A c).mp h
  have hscaled : c.denom ^ (c.rank + 1) * det (selectedSubmatrix A rows cols) = 0 := by
    rw [← det_smul, ← selectedSubmatrix_smul, h3, det_minor_mul,
      selectedColumnTuples_eq_nil_of_lt (Nat.lt_succ_self c.rank), List.foldl_nil]
  exact DomainLaws.eq_zero_of_mul_eq_zero (DomainLaws.pow_ne_zero hd _) hscaled

/-- A checked certificate of rank `0` certifies the zero matrix. -/
theorem RankCert.matrix_eq_zero {A : Matrix R n m} {c : RankCert R n m}
    (h : checkRank A c = true) (hr : c.rank = 0) : A = 0 := by
  obtain ⟨hd, _, h3⟩ := (checkRank_iff A c).mp h
  obtain ⟨r, rows, cols, d, adj⟩ := c
  subst hr
  apply ext_getElem
  intro i j
  have hij := congrArg (fun M : Matrix R n m => M[i][j]) h3
  simp only [smul_getElem, getElem_mul, getElem_zero] at hij ⊢
  have hzero : (row (selectCols A cols) i).dotProduct (col (adj * selectRows A rows) j) = 0 := by
    simp [Vector.dotProduct]
  rw [hzero] at hij
  exact DomainLaws.eq_zero_of_mul_eq_zero hd hij

end Matrix

end Hex
