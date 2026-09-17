/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Rank
public import HexRank.Check

public section

/-! Rational kernel numerators from a checked rank certificate. -/

namespace Hex.Matrix

variable {n m r k : Nat}

/-- Selected columns of a checked certificate are distinct. -/
theorem RankCert.cols_injective {A : Matrix Int n m} {c : RankCert Int n m}
    (h : checkRank A c = true) {i j : Fin c.rank} (hij : c.cols[i] = c.cols[j]) : i = j := by
  by_cases hn : i = j
  · exact hn
  exfalso
  apply RankCert.det_ne_zero h
  apply det_eq_zero_of_col_eq _ i j hn
  intro l
  simp only [getElem_selectedSubmatrix, hij]

/-- The selected-column list has no duplicates. -/
theorem RankCert.cols_nodup {A : Matrix Int n m} {c : RankCert Int n m}
    (h : checkRank A c = true) : c.cols.toList.Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  have hi' : i < c.rank := by simpa using hi
  have hj' : j < c.rank := by simpa using hj
  have he' : c.cols[(⟨i, hi'⟩ : Fin c.rank)] = c.cols[(⟨j, hj'⟩ : Fin c.rank)] := by
    simpa using he
  exact congrArg Fin.val (RankCert.cols_injective h he')

namespace Kernel

/-- Complement in increasing original-column order. -/
@[expose] def complement (J : Vector (Fin m) r) : List (Fin m) :=
  (List.finRange m).filter (fun j => decide (j ∉ J.toList))

/-- A distinct selection leaves exactly `m - r` free columns. -/
theorem complement_length (J : Vector (Fin m) r) (hJ : J.toList.Nodup) :
    (complement J).length = m - r := by
  have hp : ((List.finRange m).filter (fun j => decide (j ∈ J.toList))).Perm J.toList := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange m).filter _) hJ).mpr
    intro j
    simp
  have hh := (List.filter_append_perm (fun j => decide (j ∈ J.toList))
    (List.finRange m)).length_eq
  simp only [List.length_append, hp.length_eq, Vector.length_toList, List.length_finRange] at hh
  have he : (List.finRange m).filter (fun j => !decide (j ∈ J.toList)) = complement J := by
    simp [complement]
  rw [he] at hh
  omega

/-- Insert coordinates at a selected list of original positions. -/
def embedding (J : Vector (Fin m) r) : Matrix Int m r :=
  selectCols (Matrix.identity m) J

/-- Multiplication by an embedding selects the corresponding columns. -/
theorem mul_embedding (A : Matrix Int n m) (J : Vector (Fin m) r) :
    A * embedding J = selectCols A J := by
  apply ext_getElem
  intro i j
  have hc : col (embedding J) j = Vector.unit Int J[j] := by
    apply Vector.ext
    intro l hl
    change (col (embedding J) j)[(⟨l, hl⟩ : Fin m)] =
      (Vector.unit Int J[j])[(⟨l, hl⟩ : Fin m)]
    rw [getElem_col, embedding, getElem_selectCols, getElem_identity, Vector.getElem_unit]
    simp only [eq_comm]
    rfl
  rw [getElem_mul, hc, ← getElem_mulVec, mulVec_unit, getElem_col, getElem_selectCols]

/-- Selection commutes with multiplication on the left. -/
theorem selectCols_mul (A : Matrix Int n r) (B : Matrix Int r m)
    (J : Vector (Fin m) k) : selectCols (A * B) J = A * selectCols B J := by
  apply ext_getElem
  intro i j
  rw [getElem_selectCols, getElem_mul, getElem_mul]
  congr 1
  apply Vector.ext
  intro l hl
  change (col B J[j])[(⟨l, hl⟩ : Fin r)] =
    (col (selectCols B J) j)[(⟨l, hl⟩ : Fin r)]
  rw [getElem_col, getElem_col, getElem_selectCols]

/-- The numerator matrix expressed through coordinate embeddings. -/
def product (A : Matrix Int n m) (c : RankCert Int n m)
    (F : Vector (Fin m) (m - c.rank)) : Matrix Int m (m - c.rank) :=
  embedding c.cols * selectCols (c.adj * selectRows A c.rows) F -
    scale c.denom (embedding F)

/-- Multiplication respects integer scaling of the right factor. -/
theorem mul_scale (A : Matrix Int n r) (d : Int) (B : Matrix Int r m) :
    A * scale d B = scale d (A * B) := by
  apply ext_getElem
  intro i j
  rw [scale_eq_smul, scale_eq_smul, getElem_mul, smul_getElem, getElem_mul]
  have hc : col (d • B) j = d • col B j := by
    apply Vector.ext
    intro l hl
    change (col (d • B) j)[(⟨l, hl⟩ : Fin r)] = (d • col B j)[(⟨l, hl⟩ : Fin r)]
    rw [getElem_col, smul_getElem]
    change d * B[(⟨l, hl⟩ : Fin r)][j] = (d • col B j)[l]
    rw [Vector.getElem_smul]
    congr 1
    exact (getElem_col B j (⟨l, hl⟩ : Fin r)).symm
  rw [hc, Vector.dotProduct_smul_right]
  rfl

/-- The certificate's upper identity annihilates the embedded numerator matrix. -/
theorem product_annihilate {A : Matrix Int n m} {c : RankCert Int n m}
    (h : checkRank A c = true) (F : Vector (Fin m) (m - c.rank)) :
    A * product A c F = Matrix.zero n (m - c.rank) := by
  obtain ⟨_, _, hu⟩ := (checkRank_iff A c).mp h
  rw [product, mul_sub, ← mul_assoc, mul_embedding, ← selectCols_mul,
    ← hu, mul_scale, mul_embedding]
  apply ext_getElem
  intro i j
  rw [getElem_sub, getElem_selectCols, smul_getElem, scale_eq_smul,
    smul_getElem, getElem_selectCols]
  change _ - _ = (0 : Matrix Int n (m - c.rank))[i][j]
  rw [getElem_zero]
  omega

/-- Outside a selection its embedding has a zero row. -/
theorem embedding_row_zero (J : Vector (Fin m) r) (i : Fin m)
    (hi : i ∉ J.toList) : row (embedding J) i = 0 := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_zero]
  change (row (embedding J) i)[(⟨j, hj⟩ : Fin r)] = 0
  rw [getElem_row, embedding, getElem_selectCols, getElem_identity]
  have hn : i ≠ J[(⟨j, hj⟩ : Fin r)] := by
    intro he
    apply hi
    rw [he]
    exact Vector.mem_toList_iff.mpr (Vector.getElem_mem hj)
  rw [ite_eq_right hn]

/-- A free coordinate reads the negative denominator on its own column. -/
theorem product_free {A : Matrix Int n m} {c : RankCert Int n m}
    {F : Vector (Fin m) (m - c.rank)} (hF : F.toList = complement c.cols)
    (i j : Fin (m - c.rank)) :
    (product A c F)[F[i]][j] = if i = j then -c.denom else 0 := by
  have hmem : F[i] ∈ complement c.cols := by
    rw [← hF]
    exact Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt)
  have hi : F[i] ∉ c.cols.toList := by simpa [complement] using hmem
  have hn : F.toList.Nodup := by
    rw [hF]
    exact (List.nodup_finRange m).filter _
  have hij : F[i] = F[j] ↔ i = j := by
    constructor
    · intro he
      apply Fin.ext
      apply hn.eq_of_getElem_eq (by simp) (by simp)
      simpa using he
    · rintro rfl; rfl
  have hz := row_mul_eq_zero (embedding c.cols)
    (selectCols (c.adj * selectRows A c.rows) F) F[i]
    (embedding_row_zero c.cols F[i] hi)
  have he := congrArg (fun v : Vector Int (m - c.rank) => v[j]) hz
  rw [getElem_row] at he
  have he' : (embedding c.cols * selectCols (c.adj * selectRows A c.rows) F)[F[i]][j] = 0 := by
    simpa only [Fin.getElem_fin, Vector.getElem_zero] using he
  rw [product, getElem_sub, he', scale_eq_smul, smul_getElem,
    embedding, getElem_selectCols, getElem_identity]
  by_cases h : i = j
  · rw [ite_eq_left (hij.mpr h), ite_eq_left h]
    change 0 - c.denom * 1 = -c.denom
    omega
  · rw [ite_eq_right (fun he => h (hij.mp he)), ite_eq_right h]
    change 0 - c.denom * 0 = 0
    omega

/-- The pivot-coordinate block is `adj * A[rows, freeCols]`. -/
theorem product_pivot {A : Matrix Int n m} {c : RankCert Int n m}
    (hc : checkRank A c = true) {F : Vector (Fin m) (m - c.rank)}
    (hF : F.toList = complement c.cols) (i : Fin c.rank) (j : Fin (m - c.rank)) :
    (product A c F)[c.cols[i]][j] = (c.adj * selectRows A c.rows)[i][F[j]] := by
  have hr : row (embedding c.cols) c.cols[i] = row (Matrix.identity c.rank) i := by
    apply Vector.ext
    intro l hl
    change (row (embedding c.cols) c.cols[i])[(⟨l, hl⟩ : Fin c.rank)] =
      (row (Matrix.identity c.rank) i)[(⟨l, hl⟩ : Fin c.rank)]
    rw [getElem_row, getElem_row, embedding, getElem_selectCols,
      getElem_identity, getElem_identity]
    by_cases he : i = (⟨l, hl⟩ : Fin c.rank)
    · subst i; simp
    · rw [ite_eq_right he, ite_eq_right (fun h => he (c.cols_injective hc h))]
  have hm : F[j] ∈ complement c.cols := by
    rw [← hF]
    exact Vector.mem_toList_iff.mpr (Vector.getElem_mem j.isLt)
  have hf : F[j] ∉ c.cols.toList := by simpa [complement] using hm
  have he : c.cols[i] ≠ F[j] := by
    intro h
    apply hf
    rw [← h]
    exact Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt)
  rw [product, getElem_sub, getElem_mul, hr, ← getElem_mul,
    identity_mul, getElem_selectCols, scale_eq_smul, smul_getElem,
    embedding, getElem_selectCols, getElem_identity, ite_eq_right he]
  change _ - c.denom * 0 = _
  omega

/-- Scatter pivot rows of the coefficient matrix and the free diagonal into
original coordinates. Row lookups are computed once, outside the entry loop. -/
def numerator (A : Matrix Int n m) (c : RankCert Int n m)
    (F : Vector (Fin m) (m - c.rank)) : Matrix Int m (m - c.rank) :=
  let positions := Vector.ofFn fun i : Fin m =>
    (List.finRange c.rank).find? (fun k => decide (c.cols[k] = i))
  let T := selectCols (c.adj * selectRows A c.rows) F
  Matrix.ofFn fun i j =>
    match positions[i] with
    | some k => T[(k, j)]
    | none => if i = F[j] then -c.denom else 0

/-- The scatter implements the certificate product identity. -/
theorem numerator_eq_product {A : Matrix Int n m} {c : RankCert Int n m}
    (hc : checkRank A c = true) {F : Vector (Fin m) (m - c.rank)}
    (hF : F.toList = complement c.cols) : numerator A c F = product A c F := by
  apply ext_getElem
  intro i j
  rw [numerator, getElem_ofFn]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · rename_i k hk
    have hp := List.find?_some hk
    have he : c.cols[k] = i := by simpa using hp
    change (selectCols (c.adj * selectRows A c.rows) F)[(k, j)] = (product A c F)[i][j]
    subst i
    rw [product_pivot hc hF, getElem_pair_eq_nested, getElem_selectCols]
  · rename_i hn
    have hi : i ∉ c.cols.toList := by
      intro hm
      obtain ⟨k, hk, he⟩ := Vector.getElem_of_mem (Vector.mem_toList_iff.mp hm)
      have hh := List.find?_eq_none.mp hn (⟨k, hk⟩ : Fin c.rank) (List.mem_finRange _)
      exact hh (by simpa using he)
    have hz := row_mul_eq_zero (embedding c.cols)
      (selectCols (c.adj * selectRows A c.rows) F) i
      (embedding_row_zero c.cols i hi)
    have he : (embedding c.cols * selectCols (c.adj * selectRows A c.rows) F)[i][j] = 0 := by
      have hh := congrArg (fun v : Vector Int (m - c.rank) => v[j]) hz
      rw [getElem_row] at hh
      simpa only [Fin.getElem_fin, Vector.getElem_zero] using hh
    change (if i = F[j] then -c.denom else 0) = (product A c F)[i][j]
    rw [product, getElem_sub, he, scale_eq_smul, smul_getElem,
      embedding, getElem_selectCols, getElem_identity]
    by_cases hij : i = F[j]
    · rw [ite_eq_left hij, ite_eq_left hij]
      change -c.denom = 0 - c.denom * 1
      omega
    · rw [ite_eq_right hij, ite_eq_right hij]
      change 0 = 0 - c.denom * 0
      omega

end Kernel

/-- Integer numerators and a common denominator for a rational kernel basis. -/
structure Kernel (n m : Nat) where
  cert : RankCert Int n m
  freeCols : Vector (Fin m) (m - cert.rank)
  basis : Matrix Int m (m - cert.rank)

namespace Kernel

abbrev rank (K : Kernel n m) : Nat := K.cert.rank
abbrev denom (K : Kernel n m) : Int := K.cert.denom

/-- Construct the explicit basis from any checked certificate, preserving its scale. -/
def ofCert (A : Matrix Int n m) (c : RankCert Int n m) (h : checkRank A c = true) :
    Kernel n m :=
  let F : Vector (Fin m) (m - c.rank) :=
    ⟨(complement c.cols).toArray, by simp [complement_length c.cols (c.cols_nodup h)]⟩
  ⟨c, F, numerator A c F⟩

end Kernel

/-- Produce a checked rank certificate once and construct its rational kernel basis.
Modular-search failure propagates as `none`. -/
def kernel? (A : Matrix Int n m) (fuel : Nat) : Option (Kernel n m) :=
  match h : rankCert? A fuel with
  | none => none
  | some c => some (Kernel.ofCert A c (rankCert?_check h))

/-- A returned kernel carries a checked rank certificate. -/
theorem kernel?_check {A : Matrix Int n m} {fuel : Nat} {K : Kernel n m}
    (h : kernel? A fuel = some K) : checkRank A K.cert = true := by
  unfold kernel? at h
  split at h
  · contradiction
  · cases h
    exact rankCert?_check ‹_›

/-- Free columns enumerate the complement in original-column order. -/
theorem kernel?_freeCols {A : Matrix Int n m} {fuel : Nat} {K : Kernel n m}
    (h : kernel? A fuel = some K) : K.freeCols.toList = Kernel.complement K.cert.cols := by
  unfold kernel? at h
  split at h
  · contradiction
  · cases h
    simp [Kernel.ofCert]

/-- Integer numerator columns annihilate the input matrix. -/
theorem kernel?_annihilate {A : Matrix Int n m} {fuel : Nat} {K : Kernel n m}
    (h : kernel? A fuel = some K) : A * K.basis = Matrix.zero n (m - K.cert.rank) := by
  unfold kernel? at h
  split at h
  · contradiction
  · cases h
    dsimp only [Kernel.ofCert] at *
    rw [Kernel.numerator_eq_product (rankCert?_check ‹_›) (by simp)]
    exact Kernel.product_annihilate (rankCert?_check ‹_›) _

/-- Reading the free coordinates gives a nonzero scalar identity block. -/
theorem kernel?_free {A : Matrix Int n m} {fuel : Nat} {K : Kernel n m}
    (h : kernel? A fuel = some K) (i j : Fin (m - K.cert.rank)) :
    K.basis[K.freeCols[i]][j] = if i = j then -K.cert.denom else 0 := by
  unfold kernel? at h
  split at h
  · contradiction
  · cases h
    dsimp only [Kernel.ofCert] at *
    rw [Kernel.numerator_eq_product (rankCert?_check ‹_›) (by simp)]
    exact Kernel.product_free (by simp [Kernel.ofCert]) i j

/-- The selected coordinates are given by the certificate's coefficient matrix. -/
theorem kernel?_pivot {A : Matrix Int n m} {fuel : Nat} {K : Kernel n m}
    (h : kernel? A fuel = some K) (i : Fin K.cert.rank) (j : Fin (m - K.cert.rank)) :
    K.basis[K.cert.cols[i]][j] = (K.cert.adj * selectRows A K.cert.rows)[i][K.freeCols[j]] := by
  unfold kernel? at h
  split at h
  · contradiction
  · cases h
    dsimp only [Kernel.ofCert] at *
    rw [Kernel.numerator_eq_product (rankCert?_check ‹_›) (by simp)]
    exact Kernel.product_pivot (rankCert?_check ‹_›) (by simp [Kernel.ofCert]) i j

/-- The numerator columns have full column rank over the integers. -/
theorem kernel?_mulVec_eq_zero {A : Matrix Int n m} {fuel : Nat} {K : Kernel n m}
    (h : kernel? A fuel = some K) (z : Vector Int (m - K.cert.rank))
    (hz : K.basis.mulVec z = 0) : z = 0 := by
  have hd := ((checkRank_iff A K.cert).mp (kernel?_check h)).1
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_zero]
  let i : Fin (m - K.cert.rank) := ⟨k, hk⟩
  have hr : row K.basis K.freeCols[i] =
      (-K.cert.denom) • row (Matrix.identity (m - K.cert.rank)) i := by
    apply Vector.ext
    intro l hl
    change (row K.basis K.freeCols[i])[(⟨l, hl⟩ : Fin (m - K.cert.rank))] = _
    rw [getElem_row, kernel?_free h, Vector.getElem_smul]
    change (if i = (⟨l, hl⟩ : Fin (m - K.cert.rank)) then -K.cert.denom else 0) =
      -K.cert.denom * (row (Matrix.identity (m - K.cert.rank)) i)[(⟨l, hl⟩ : Fin (m - K.cert.rank))]
    rw [getElem_row, getElem_identity]
    split <;> omega
  have he : (K.basis.mulVec z)[K.freeCols[i]] = 0 := by
    rw [hz]
    simp only [Fin.getElem_fin, Vector.getElem_zero]
  change (K.basis * z)[K.freeCols[i]] = 0 at he
  rw [getElem_mulVec, hr, Vector.dotProduct_smul_left, ← getElem_mulVec, identity_mulVec] at he
  rcases Int.mul_eq_zero.mp he with he | he
  · exact False.elim (hd (by omega))
  · exact he

end Hex.Matrix
