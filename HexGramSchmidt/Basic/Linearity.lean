/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Basic.Kernel
import all HexGramSchmidt.Basic.Kernel

public section

namespace Hex
namespace GramSchmidt
/-! Linearity-of-source helpers for `subtractProjection` and
`reduceAgainstBasis`. These let later proofs pull the reconstruction
sum across the reduction. -/

private theorem foldl_dot_add_left
    (xs : List (Fin m)) (a b c : Vector Rat m) (accA accB : Rat) :
    xs.foldl (fun acc i => acc + (a + b)[i] * c[i]) (accA + accB) =
      xs.foldl (fun acc i => acc + a[i] * c[i]) accA +
        xs.foldl (fun acc i => acc + b[i] * c[i]) accB := by
  induction xs generalizing accA accB with
  | nil => simp
  | cons i xs ih =>
      have hentry : (a + b)[i] = a[i] + b[i] := by
        change (a + b)[i.val] = a[i.val] + b[i.val]
        rw [Vector.getElem_add]
      simp only [List.foldl_cons]
      have hstart :
          accA + accB + (a + b)[i] * c[i] =
            (accA + a[i] * c[i]) + (accB + b[i] * c[i]) := by
        rw [hentry]
        grind
      rw [hstart]
      exact ih (accA := accA + a[i] * c[i]) (accB := accB + b[i] * c[i])

/-- `dot_add_left` states left-additivity of the dot product. -/
private theorem dot_add_left (a b c : Vector Rat m) :
    (a + b).dotProduct c = a.dotProduct c + b.dotProduct c := by
  unfold Vector.dotProduct
  have hzero : (0 : Rat) + 0 = 0 := by grind
  simpa [hzero] using
    foldl_dot_add_left (xs := List.finRange m) (a := a) (b := b) (c := c)
      (accA := 0) (accB := 0)

/-- `foldl_dot_smul_left` states left-homogeneity of the dot-product fold. -/
private theorem foldl_dot_smul_left
    (xs : List (Fin m)) (s : Rat) (a c : Vector Rat m) (acc : Rat) :
    xs.foldl (fun acc i => acc + (s • a)[i] * c[i]) (s * acc) =
      s * xs.foldl (fun acc i => acc + a[i] * c[i]) acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons i xs ih =>
      have hentry : (s • a)[i] = s * a[i] := by
        change (s • a)[i.val] = s * a[i.val]
        rw [Vector.getElem_smul]; rfl
      simp only [List.foldl_cons]
      have hstart :
          s * acc + (s • a)[i] * c[i] =
            s * (acc + a[i] * c[i]) := by
        rw [hentry]; grind
      rw [hstart]
      exact ih (acc := acc + a[i] * c[i])

/-- `dot_smul_left` states left-homogeneity of the dot product. -/
private theorem dot_smul_left (s : Rat) (a c : Vector Rat m) :
    (s • a).dotProduct c = s * a.dotProduct c := by
  unfold Vector.dotProduct
  have hzero : s * (0 : Rat) = 0 := by grind
  simpa [hzero] using
    foldl_dot_smul_left (xs := List.finRange m) (s := s) (a := a) (c := c) (acc := 0)

/-- `projectionCoeff_add_left` states left-additivity of the projection coefficient. -/
private theorem projectionCoeff_add_left (a b c : Vector Rat m) :
    projectionCoeff (a + b) c = projectionCoeff a c + projectionCoeff b c := by
  unfold projectionCoeff
  by_cases hnorm : c.dotProduct c = 0
  · simp [hnorm]
    grind
  · simp [hnorm]
    rw [dot_add_left]
    grind

/-- `projectionCoeff_smul_left` states left-homogeneity of the projection coefficient. -/
private theorem projectionCoeff_smul_left (s : Rat) (a c : Vector Rat m) :
    projectionCoeff (s • a) c = s * projectionCoeff a c := by
  unfold projectionCoeff
  by_cases hnorm : c.dotProduct c = 0
  · simp [hnorm]
  · simp [hnorm]
    rw [dot_smul_left]
    grind

/-- `subtractProjection_add_left` states left-additivity of projection subtraction. -/
private theorem subtractProjection_add_left (a b c : Vector Rat m) :
    subtractProjection (a + b) c =
      subtractProjection a c + subtractProjection b c := by
  apply Vector.ext
  intro k hk
  unfold subtractProjection
  have hcoeff := projectionCoeff_add_left a b c
  have hentry_lhs :
      ((a + b) - projectionCoeff (a + b) c • c)[k] =
        a[k] + b[k] - projectionCoeff (a + b) c * c[k] := by
    rw [Vector.getElem_sub, Vector.getElem_add, Vector.getElem_smul]
    rfl
  have hentry_rhs :
      (a - projectionCoeff a c • c + (b - projectionCoeff b c • c))[k] =
        a[k] - projectionCoeff a c * c[k] +
          (b[k] - projectionCoeff b c * c[k]) := by
    rw [Vector.getElem_add, Vector.getElem_sub, Vector.getElem_sub,
      Vector.getElem_smul, Vector.getElem_smul]
    rfl
  rw [hentry_lhs, hentry_rhs, hcoeff]
  grind

/-- `subtractProjection_smul_left` states left-homogeneity of projection subtraction. -/
private theorem subtractProjection_smul_left (s : Rat) (a c : Vector Rat m) :
    subtractProjection (s • a) c = s • subtractProjection a c := by
  apply Vector.ext
  intro k hk
  unfold subtractProjection
  have hcoeff := projectionCoeff_smul_left s a c
  have hentry_lhs :
      (s • a - projectionCoeff (s • a) c • c)[k] =
        s * a[k] - projectionCoeff (s • a) c * c[k] := by
    rw [Vector.getElem_sub, Vector.getElem_smul, Vector.getElem_smul]
    rfl
  have hentry_rhs :
      (s • (a - projectionCoeff a c • c))[k] =
        s * (a[k] - projectionCoeff a c * c[k]) := by
    rw [Vector.getElem_smul, Vector.getElem_sub, Vector.getElem_smul]
    rfl
  rw [hentry_lhs, hentry_rhs, hcoeff]
  grind

/-- `reduceAgainstBasis_add_left` states left-additivity of basis reduction. -/
private theorem reduceAgainstBasis_add_left
    (basisRev : List (Vector Rat m)) (a b : Vector Rat m) :
    reduceAgainstBasis basisRev (a + b) =
      reduceAgainstBasis basisRev a + reduceAgainstBasis basisRev b := by
  induction basisRev generalizing a b with
  | nil => simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      rw [subtractProjection_add_left]
      change reduceAgainstBasis rest
          (subtractProjection a basisRow + subtractProjection b basisRow) =
        reduceAgainstBasis rest (subtractProjection a basisRow) +
          reduceAgainstBasis rest (subtractProjection b basisRow)
      exact ih (a := subtractProjection a basisRow) (b := subtractProjection b basisRow)

/-- `reduceAgainstBasis_smul_left` states left-homogeneity of basis reduction. -/
private theorem reduceAgainstBasis_smul_left
    (basisRev : List (Vector Rat m)) (s : Rat) (a : Vector Rat m) :
    reduceAgainstBasis basisRev (s • a) = s • reduceAgainstBasis basisRev a := by
  induction basisRev generalizing a with
  | nil => simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      rw [subtractProjection_smul_left]
      change reduceAgainstBasis rest (s • subtractProjection a basisRow) =
        s • reduceAgainstBasis rest (subtractProjection a basisRow)
      exact ih (a := subtractProjection a basisRow)

/-- `reduceAgainstBasis_append` states the append-decomposition of basis reduction. -/
private theorem reduceAgainstBasis_append
    (l₁ l₂ : List (Vector Rat m)) (row : Vector Rat m) :
    reduceAgainstBasis (l₁ ++ l₂) row =
      reduceAgainstBasis l₂ (reduceAgainstBasis l₁ row) := by
  unfold reduceAgainstBasis
  rw [List.foldl_append]

private theorem basisRows_get!_dot_eq_zero_of_list
    (rows : List (Vector Rat m)) (i j : Nat)
    (hi : i < rows.length) (hj : j < rows.length) (hij : i ≠ j) :
    (basisRows rows)[i]!.dotProduct (basisRows rows)[j]! = 0 := by
  have hilen : i < (basisRows rows).length := by simpa [basisRows_length]
  have hjlen : j < (basisRows rows).length := by simpa [basisRows_length]
  have hpair : (basisRows rows).Pairwise
      (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) :=
    basisRows_pairwise rows
  have hget_i : (basisRows rows)[i]! = (basisRows rows)[i] := by simp [hilen]
  have hget_j : (basisRows rows)[j]! = (basisRows rows)[j] := by simp [hjlen]
  by_cases hlt : i < j
  · have hrel :=
      (List.pairwise_iff_getElem.1 hpair) i j hilen hjlen hlt
    rw [hget_i, hget_j]
    exact hrel.1
  · have hji : j < i :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hij h.symm)
    have hrel :=
      (List.pairwise_iff_getElem.1 hpair) j i hjlen hilen hji
    rw [hget_i, hget_j]
    exact hrel.2

private theorem zero_add_vec (v : Vector Rat m) : (0 : Vector Rat m) + v = v := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_add, Vector.getElem_zero]
  grind

private theorem smul_zero_vec (s : Rat) : s • (0 : Vector Rat m) = 0 := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_smul, Vector.getElem_zero]
  show s * (0 : Rat) = 0
  grind

/-- Reducing a generated basis row against any later prefix that contains it
returns 0. -/
private theorem reduceAgainstBasis_basisRows_take_get!_eq_zero
    (rows : List (Vector Rat m)) (ℓ k : Nat)
    (hℓk : ℓ < k) (hk : k ≤ rows.length) :
    reduceAgainstBasis ((basisRows rows).take k).reverse
        (basisRows rows)[ℓ]! = 0 := by
  have hℓlen : ℓ < rows.length := Nat.lt_of_lt_of_le hℓk hk
  have hℓbasis : ℓ < (basisRows rows).length := by simpa [basisRows_length]
  have hkbasis : k ≤ (basisRows rows).length := by simpa [basisRows_length]
  -- The first ℓ+1 elements of take k are exactly take (ℓ+1).
  have htake_take :
      ((basisRows rows).take k).take (ℓ + 1) = (basisRows rows).take (ℓ + 1) := by
    rw [List.take_take]
    congr 1
    omega
  have hsplit :
      (basisRows rows).take k =
        (basisRows rows).take (ℓ + 1) ++
          ((basisRows rows).take k).drop (ℓ + 1) := by
    rw [← htake_take]
    exact (List.take_append_drop (ℓ + 1) ((basisRows rows).take k)).symm
  rw [hsplit, List.reverse_append, reduceAgainstBasis_append]
  -- Inner reduction: (basisRows rows)[ℓ]! is orthogonal to all elements in
  -- the drop-take part (those are basis rows at indices > ℓ).
  have hinner :
      reduceAgainstBasis (((basisRows rows).take k).drop (ℓ + 1)).reverse
          (basisRows rows)[ℓ]! = (basisRows rows)[ℓ]! := by
    apply reduceAgainstBasis_eq_self
    intro b hmem
    rw [List.mem_reverse] at hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hilen, hbget⟩ := hmem
    have hdroplen :
        (((basisRows rows).take k).drop (ℓ + 1)).length =
          ((basisRows rows).take k).length - (ℓ + 1) := by
      rw [List.length_drop]
    have htakelen : ((basisRows rows).take k).length = k := by
      rw [List.length_take]; omega
    rw [hdroplen, htakelen] at hilen
    have hidx_lt_basis : i + (ℓ + 1) < (basisRows rows).length := by
      have : k ≤ (basisRows rows).length := hkbasis
      omega
    have hidx_lt_take : i + (ℓ + 1) < ((basisRows rows).take k).length := by
      rw [htakelen]; omega
    -- Resolve b to (basisRows rows)[ℓ + 1 + i].
    have hidx_lt_basis' : ℓ + 1 + i < (basisRows rows).length := by
      have hcomm : ℓ + 1 + i = i + (ℓ + 1) := by omega
      rw [hcomm]; exact hidx_lt_basis
    have hbget' :
        b = (basisRows rows)[ℓ + 1 + i]'hidx_lt_basis' := by
      rw [← hbget, List.getElem_drop, List.getElem_take]
    have hbget!_eq :
        b = (basisRows rows)[ℓ + 1 + i]! := by
      rw [hbget']
      simp [hidx_lt_basis']
    rw [hbget!_eq]
    apply basisRows_get!_dot_eq_zero_of_list rows ℓ (ℓ + 1 + i) hℓlen
    · -- ℓ + 1 + i < rows.length
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    · omega
  rw [hinner]
  exact reduceAgainstBasis_basisRows_get!_succ_eq_zero rows ℓ hℓlen

/-- A `projectionCombination` whose basis rows all reduce to 0 against
`basisRev'` (and whose accumulator does too) reduces to 0 against `basisRev'`. -/
private theorem reduceAgainstBasis_projectionCombination_eq_zero
    (basisRev basisRev' : List (Vector Rat m)) (row acc : Vector Rat m)
    (hzero : ∀ b ∈ basisRev, reduceAgainstBasis basisRev' b = 0)
    (haccZero : reduceAgainstBasis basisRev' acc = 0) :
    reduceAgainstBasis basisRev' (projectionCombination row basisRev acc) = 0 := by
  induction basisRev generalizing acc with
  | nil =>
      simp [projectionCombination]
      exact haccZero
  | cons b rest ih =>
      show reduceAgainstBasis basisRev'
          (projectionCombination row (b :: rest) acc) = 0
      simp only [projectionCombination, List.foldl_cons]
      change reduceAgainstBasis basisRev'
          (projectionCombination row rest
            (acc + projectionCoeff row b • b)) = 0
      apply ih
      · intro b' hb'
        exact hzero b' (by simp [hb'])
      · rw [reduceAgainstBasis_add_left, haccZero, reduceAgainstBasis_smul_left,
          hzero b (by simp), smul_zero_vec, zero_add_vec]

/-- Reducing the source row `rows[j]!` against any later prefix returns 0:
the source row's basis-prefix decomposition lies entirely in the reduction
prefix, and the basis component vanishes by index. -/
private theorem reduceAgainstBasis_basisRows_take_source_eq_zero
    (rows : List (Vector Rat m)) (j k : Nat)
    (hjk : j < k) (hk : k ≤ rows.length) :
    reduceAgainstBasis ((basisRows rows).take k).reverse rows[j]! = 0 := by
  have hjlen : j < rows.length := Nat.lt_of_lt_of_le hjk hk
  have hjbasis : j < (basisRows rows).length := by simpa [basisRows_length]
  -- Reconstruction theorem for the source row.
  have hrec :=
    basisRows_get!_eq_reduceAgainstBasis_forward (rows := rows) (k := j) hjlen
  rw [hrec, reduceAgainstBasis_add_left]
  -- Basis-row component vanishes by Aux1 with ℓ = j.
  rw [reduceAgainstBasis_basisRows_take_get!_eq_zero rows j k hjk hk, zero_add_vec]
  -- ProjectionCombination component vanishes: each contributing basis row is
  -- at index < j < k, so reducing it gives 0.
  apply reduceAgainstBasis_projectionCombination_eq_zero
  · intro b hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hilen, hbget⟩ := hmem
    have htakelen : ((basisRows rows).take j).length = j := by
      rw [List.length_take]; omega
    rw [htakelen] at hilen
    have hi_lt_basis : i < (basisRows rows).length := by
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    have hbget' : b = (basisRows rows)[i]'hi_lt_basis := by
      rw [← hbget, List.getElem_take]
    have hbget!_eq : b = (basisRows rows)[i]! := by
      rw [hbget']; simp [hi_lt_basis]
    rw [hbget!_eq]
    apply reduceAgainstBasis_basisRows_take_get!_eq_zero rows i k _ hk
    omega
  · exact reduceAgainstBasis_zero_left _

/-- The first `i` Gram-Schmidt output rows depend only on the first `i` input
rows. -/
private theorem basisRows_take_eq
    (rows rows' : List (Vector Rat m)) (i : Nat)
    (hlen : rows'.length = rows.length)
    (hprefix : ∀ t, t < i → rows'[t]! = rows[t]!)
    (hi : i ≤ rows.length) :
    (basisRows rows').take i = (basisRows rows).take i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ≤ rows.length := Nat.le_of_succ_le hi
    have ihtake := ih (by
      intro t ht
      exact hprefix t (Nat.lt_trans ht (Nat.lt_succ_self i))) hi'
    have hi_lt : i < rows.length := hi
    have hi_lt_rows' : i < rows'.length := by rw [hlen]; exact hi_lt
    have hb1_len : (basisRows rows').length = rows.length := by
      rw [basisRows_length, hlen]
    have hb2_len : (basisRows rows).length = rows.length := basisRows_length rows
    have hi_lt_b1 : i < (basisRows rows').length := by rw [hb1_len]; exact hi_lt
    have hi_lt_b2 : i < (basisRows rows).length := by rw [hb2_len]; exact hi_lt
    rw [List.take_succ_eq_append_getElem hi_lt_b1,
        List.take_succ_eq_append_getElem hi_lt_b2,
        ihtake]
    congr 1
    have hge1 : (basisRows rows')[i] = (basisRows rows')[i]! :=
      (getElem!_pos _ i hi_lt_b1).symm
    have hge2 : (basisRows rows)[i] = (basisRows rows)[i]! :=
      (getElem!_pos _ i hi_lt_b2).symm
    rw [hge1, hge2]
    congr 1
    rw [basisRows_get!_eq_reduceAgainstBasis_take rows' i hi_lt_rows',
        basisRows_get!_eq_reduceAgainstBasis_take rows i hi_lt,
        ihtake,
        hprefix i (Nat.lt_succ_self i)]

private theorem basisRows_get!_eq_of_prefix
    (rows rows' : List (Vector Rat m)) (i : Nat)
    (hlen : rows'.length = rows.length)
    (hprefix : ∀ t, t ≤ i → rows'[t]! = rows[t]!)
    (hi : i < rows.length) :
    (basisRows rows')[i]! = (basisRows rows)[i]! := by
  have htake :=
    basisRows_take_eq rows rows' (i + 1) hlen
      (by
        intro t ht
        exact hprefix t (Nat.le_of_lt_succ ht))
      (Nat.succ_le_of_lt hi)
  have hb1_len : (basisRows rows').length = rows.length := by
    rw [basisRows_length, hlen]
  have hb2_len : (basisRows rows).length = rows.length := basisRows_length rows
  have hi_b1 : i < (basisRows rows').length := by rw [hb1_len]; exact hi
  have hi_b2 : i < (basisRows rows).length := by rw [hb2_len]; exact hi
  have hget :=
    congrArg (fun xs : List (Vector Rat m) => xs[i]?) htake
  simp [hi_b1, hi_b2] at hget
  simp [hget, hi_b1, hi_b2]

/-- Reducing the next source row against the prefix before its predecessor
leaves the old next basis row plus the predecessor projection term. -/
private theorem reduceAgainstBasis_basisRows_take_source_adjacent
    (rows : List (Vector Rat m)) (km1 k : Nat)
    (hkm1 : km1 + 1 = k) (hk : k < rows.length) :
    reduceAgainstBasis ((basisRows rows).take km1).reverse rows[k]! =
      (basisRows rows)[k]! +
        projectionCoeff rows[k]! (basisRows rows)[km1]! • (basisRows rows)[km1]! := by
  have hkm1_lt_k : km1 < k := by omega
  have hkm1_lt_rows : km1 < rows.length := Nat.lt_trans hkm1_lt_k hk
  have hbasis_k_len : k < (basisRows rows).length := by simpa [basisRows_length]
  have hbasis_km1_len : km1 < (basisRows rows).length := by
    simpa [basisRows_length] using hkm1_lt_rows
  have hrec :=
    basisRows_get!_eq_reduceAgainstBasis_forward (rows := rows) (k := k) hk
  have htake :
      (basisRows rows).take k =
        (basisRows rows).take km1 ++ [(basisRows rows)[km1]!] := by
    rw [← hkm1, List.take_succ_eq_append_getElem hbasis_km1_len]
    congr 1
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hbasis_km1_len]
  have hbasis_k :
      reduceAgainstBasis ((basisRows rows).take km1).reverse (basisRows rows)[k]! =
        (basisRows rows)[k]! := by
    apply reduceAgainstBasis_eq_self
    intro b hmem
    rw [List.mem_reverse] at hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨idx, hidx, hbget⟩ := hmem
    have htake_len : ((basisRows rows).take km1).length = km1 := by
      rw [List.length_take]
      omega
    have hidx_km1 : idx < km1 := by
      rw [htake_len] at hidx
      exact hidx
    have hidx_basis : idx < (basisRows rows).length := by
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    have hbget' : b = (basisRows rows)[idx]! := by
      rw [← hbget, List.getElem_take]
      simp [hidx_basis]
    rw [hbget']
    exact basisRows_get!_dot_eq_zero_of_list rows k idx hk
      (by omega) (by omega)
  have hproj_prefix :
      reduceAgainstBasis ((basisRows rows).take km1).reverse
        (projectionCombination rows[k]! ((basisRows rows).take km1) 0) = 0 := by
    apply reduceAgainstBasis_projectionCombination_eq_zero
    · intro b hmem
      rw [List.mem_iff_getElem] at hmem
      obtain ⟨idx, hidx, hbget⟩ := hmem
      have htake_len : ((basisRows rows).take km1).length = km1 := by
        rw [List.length_take]
        omega
      have hidx_km1 : idx < km1 := by
        rw [htake_len] at hidx
        exact hidx
      have hidx_basis : idx < (basisRows rows).length := by
        have : (basisRows rows).length = rows.length := basisRows_length rows
        omega
      have hbget' : b = (basisRows rows)[idx]! := by
        rw [← hbget, List.getElem_take]
        simp [hidx_basis]
      rw [hbget']
      apply reduceAgainstBasis_basisRows_take_get!_eq_zero rows idx km1 hidx_km1
      omega
    · exact reduceAgainstBasis_zero_left _
  have hbasis_km1 :
      reduceAgainstBasis ((basisRows rows).take km1).reverse (basisRows rows)[km1]! =
      (basisRows rows)[km1]! := by
    apply reduceAgainstBasis_eq_self
    intro b hmem
    rw [List.mem_reverse] at hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨idx, hidx, hbget⟩ := hmem
    have htake_len : ((basisRows rows).take km1).length = km1 := by
      rw [List.length_take]
      omega
    have hidx_km1 : idx < km1 := by
      rw [htake_len] at hidx
      exact hidx
    have hidx_basis : idx < (basisRows rows).length := by
      have : (basisRows rows).length = rows.length := basisRows_length rows
      omega
    have hbget' : b = (basisRows rows)[idx]! := by
      rw [← hbget, List.getElem_take]
      simp [hidx_basis]
    rw [hbget']
    exact basisRows_get!_dot_eq_zero_of_list rows km1 idx hkm1_lt_rows
      (by omega) (by omega)
  conv => lhs; rw [hrec]
  rw [htake, projectionCombination_append, projectionCombination_singleton]
  repeat rw [reduceAgainstBasis_add_left]
  rw [hbasis_k, hproj_prefix, reduceAgainstBasis_smul_left, hbasis_km1]
  apply Vector.ext
  intro idx hidx
  rw [Vector.getElem_add, Vector.getElem_add, Vector.getElem_zero]
  grind

/-- For `j < k < rows.length`, the first `i` basis rows produced by Gram-Schmidt
on `rows.set k (rows[k]! + c • rows[j]!)` agree with the first `i` basis rows
produced on `rows`. Proved jointly with the pointwise equality at index `i` by
ordinary induction: the inductive step rewrites `(basisRows _)[i]!` via
`basisRows_get!_eq_reduceAgainstBasis_take` against the equal prefix from the
inductive hypothesis, then either uses the unchanged-row case (`i ≠ k`) or
linearity plus `reduceAgainstBasis_basisRows_take_source_eq_zero` (`i = k`). -/
private theorem basisRows_take_set_rowAdd
    (rows : List (Vector Rat m)) (j k : Nat) (c : Rat)
    (hjk : j < k) (hk : k < rows.length) (i : Nat) (hi : i ≤ rows.length) :
    (basisRows (rows.set k (rows[k]! + c • rows[j]!))).take i =
      (basisRows rows).take i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ≤ rows.length := Nat.le_of_succ_le hi
    have ihtake := ih hi'
    have hi_lt : i < rows.length := hi
    have hrows'_len :
        (rows.set k (rows[k]! + c • rows[j]!)).length = rows.length := by simp
    have hi_lt_rows' : i < (rows.set k (rows[k]! + c • rows[j]!)).length := by
      rw [hrows'_len]; exact hi_lt
    have hb1_len :
        (basisRows (rows.set k (rows[k]! + c • rows[j]!))).length = rows.length := by
      rw [basisRows_length, hrows'_len]
    have hb2_len : (basisRows rows).length = rows.length := basisRows_length rows
    have hi_lt_b1 :
        i < (basisRows (rows.set k (rows[k]! + c • rows[j]!))).length := by
      rw [hb1_len]; exact hi_lt
    have hi_lt_b2 : i < (basisRows rows).length := by rw [hb2_len]; exact hi_lt
    rw [List.take_succ_eq_append_getElem hi_lt_b1,
        List.take_succ_eq_append_getElem hi_lt_b2,
        ihtake]
    congr 1
    -- Reduce `[(basisRows rows')[i]] = [(basisRows rows)[i]]` to `[i]!`-form.
    have hge1 :
        (basisRows (rows.set k (rows[k]! + c • rows[j]!)))[i] =
          (basisRows (rows.set k (rows[k]! + c • rows[j]!)))[i]! :=
      (getElem!_pos _ i hi_lt_b1).symm
    have hge2 : (basisRows rows)[i] = (basisRows rows)[i]! :=
      (getElem!_pos _ i hi_lt_b2).symm
    rw [hge1, hge2]
    congr 1
    rw [basisRows_get!_eq_reduceAgainstBasis_take
          (rows.set k (rows[k]! + c • rows[j]!)) i hi_lt_rows',
        basisRows_get!_eq_reduceAgainstBasis_take rows i hi_lt,
        ihtake]
    by_cases hik : i = k
    · -- Modified row: i = k.
      have hrows'_get_eq :
          (rows.set k (rows[k]! + c • rows[j]!))[i]! = rows[k]! + c • rows[j]! := by
        rw [hik]
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_self hk]
      rw [hrows'_get_eq, reduceAgainstBasis_add_left,
          reduceAgainstBasis_smul_left]
      have hsrc :
          reduceAgainstBasis ((basisRows rows).take i).reverse rows[j]! = 0 := by
        rw [hik]
        exact reduceAgainstBasis_basisRows_take_source_eq_zero rows j k hjk
            (Nat.le_of_lt hk)
      rw [hsrc]
      have hrhs_get :
          reduceAgainstBasis ((basisRows rows).take i).reverse rows[i]! =
            reduceAgainstBasis ((basisRows rows).take i).reverse rows[k]! := by
        rw [hik]
      rw [hrhs_get, smul_zero_vec]
      apply Vector.ext
      intro idx hidx
      rw [Vector.getElem_add, Vector.getElem_zero]
      grind
    · -- Unchanged row: i ≠ k.
      have hne : k ≠ i := Ne.symm hik
      have hrows'_get_eq :
          (rows.set k (rows[k]! + c • rows[j]!))[i]! = rows[i]! := by
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]
      rw [hrows'_get_eq]

/-- `basisRows` is invariant under replacing input row `k` by
`rows[k]! + c • rows[j]!` for `j < k < rows.length`. -/
private theorem basisRows_set_rowAdd
    (rows : List (Vector Rat m)) (j k : Nat) (c : Rat)
    (hjk : j < k) (hk : k < rows.length) :
    basisRows (rows.set k (rows[k]! + c • rows[j]!)) = basisRows rows := by
  have h :=
    basisRows_take_set_rowAdd rows j k c hjk hk rows.length (Nat.le_refl _)
  have hlen1 :
      (basisRows (rows.set k (rows[k]! + c • rows[j]!))).length = rows.length := by
    rw [basisRows_length, List.length_set]
  have hlen2 : (basisRows rows).length = rows.length := basisRows_length rows
  rw [List.take_of_length_le (Nat.le_of_eq hlen1),
      List.take_of_length_le (Nat.le_of_eq hlen2)] at h
  exact h

/-- `basisMatrix` is invariant under the executable row-add operation
`Matrix.rowAdd b src dst c` whenever `src.val < dst.val`. Wraps
`basisRows_set_rowAdd` through the `toList` representation. -/
private theorem basisMatrix_rowAdd
    (b : Matrix Rat n m) (src dst : Fin n) (c : Rat) (h : src.val < dst.val) :
    basisMatrix (Matrix.rowAdd b src dst c) = basisMatrix b := by
  unfold basisMatrix
  have hsrc_toList : b.toList[src.val]! = b[src] := by simp
  have hdst_toList : b.toList[dst.val]! = b[dst] := by simp
  have htoList :
      (Matrix.rowAdd b src dst c).toList =
        b.toList.set dst.val
          (b.toList[dst.val]! + c • b.toList[src.val]!) := by
    rw [Matrix.rowAdd_eq_set]
    rw [Vector.toList_set]
    congr 1
    rw [hsrc_toList, hdst_toList]
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_ofFn, Vector.getElem_add, Vector.getElem_smul]
    rfl
  rw [htoList, basisRows_set_rowAdd b.toList src.val dst.val c h
    (by rw [Vector.length_toList]; exact dst.isLt)]

/-- `rowSwap_toList_get!_of_lt`: reading `toList`/`get!` at an index `t` strictly
below both swapped positions `km1 < k` returns the same row as before the swap. -/
private theorem rowSwap_toList_get!_of_lt
    (b : Matrix Rat n m) (km1 k : Fin n) (t : Nat)
    (hkm1k : km1.val < k.val) (ht : t < km1.val) :
    (Matrix.rowSwap b km1 k).toList[t]! = b.toList[t]! := by
  have ht_n : t < n := Nat.lt_trans ht km1.isLt
  let r : Fin n := ⟨t, ht_n⟩
  have hrk : r ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    change t = k.val at hval
    omega
  have hrkm1 : r ≠ km1 := by
    intro h
    have hval := congrArg Fin.val h
    change t = km1.val at hval
    omega
  have hleft :
      (Matrix.rowSwap b km1 k).toList[t]! = (Matrix.rowSwap b km1 k).row r := by
    have hget :
        (Matrix.rowSwap b km1 k).toList[t]! =
          (Matrix.rowSwap b km1 k).toList[t]'(by simp [ht_n]) :=
      getElem!_pos _ t (by simp [ht_n])
    simpa [Matrix.row, Vector.getElem_toList, r] using hget
  have hright : b.toList[t]! = b.row r := by
    have hget : b.toList[t]! = b.toList[t]'(by simp [ht_n]) :=
      getElem!_pos _ t (by simp [ht_n])
    simpa [Matrix.row, Vector.getElem_toList, r] using hget
  rw [hleft, hright]
  apply Vector.ext
  intro idx hidx
  let cc : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b km1 k)[r][cc] = b[r][cc]
  rw [Matrix.getElem_rowSwap]
  simp [hrk, hrkm1]

/-- `rowSwap_toList_get!_left`: at the lower swapped index `km1`, the swapped matrix
reads back the original row stored at the upper index `k`. -/
private theorem rowSwap_toList_get!_left
    (b : Matrix Rat n m) (km1 k : Fin n) (hkm1k : km1.val ≠ k.val) :
    (Matrix.rowSwap b km1 k).toList[km1.val]! = b.toList[k.val]! := by
  have hleft :
      (Matrix.rowSwap b km1 k).toList[km1.val]! =
        (Matrix.rowSwap b km1 k).row km1 := by
    simp [Matrix.row]
  have hright : b.toList[k.val]! = b.row k := by
    simp [Matrix.row]
  rw [hleft, hright]
  have hne : km1 ≠ k := by
    intro h
    exact hkm1k (congrArg Fin.val h)
  apply Vector.ext
  intro idx hidx
  let cc : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b km1 k)[km1][cc] = b[k][cc]
  rw [Matrix.getElem_rowSwap]
  simp [hne]

/-- `rowSwap_toList_get!_right`: at the upper swapped index `k`, the swapped matrix
reads back the original row stored at the lower index `km1`. -/
private theorem rowSwap_toList_get!_right
    (b : Matrix Rat n m) (km1 k : Fin n) :
    (Matrix.rowSwap b km1 k).toList[k.val]! = b.toList[km1.val]! := by
  have hleft :
      (Matrix.rowSwap b km1 k).toList[k.val]! =
        (Matrix.rowSwap b km1 k).row k := by
    simp [Matrix.row]
  have hright : b.toList[km1.val]! = b.row km1 := by
    simp [Matrix.row]
  rw [hleft, hright]
  apply Vector.ext
  intro idx hidx
  let cc : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b km1 k)[k][cc] = b[km1][cc]
  rw [Matrix.getElem_rowSwap]
  simp

/-- `rowSwap_toList_get!_of_gt`: reading `toList`/`get!` at an index `t` strictly
above both swapped positions `km1 < k` returns the same row as before the swap. -/
private theorem rowSwap_toList_get!_of_gt
    (b : Matrix Rat n m) (km1 k : Fin n) (t : Nat)
    (hkm1k : km1.val < k.val) (ht_lt_n : t < n) (ht : k.val < t) :
    (Matrix.rowSwap b km1 k).toList[t]! = b.toList[t]! := by
  let r : Fin n := ⟨t, ht_lt_n⟩
  have hrk : r ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    change t = k.val at hval
    omega
  have hrkm1 : r ≠ km1 := by
    intro h
    have hval := congrArg Fin.val h
    change t = km1.val at hval
    omega
  have hleft :
      (Matrix.rowSwap b km1 k).toList[t]! = (Matrix.rowSwap b km1 k).row r := by
    have hget :
        (Matrix.rowSwap b km1 k).toList[t]! =
          (Matrix.rowSwap b km1 k).toList[t]'(by simp [ht_lt_n]) :=
      getElem!_pos _ t (by simp [ht_lt_n])
    simpa [Matrix.row, Vector.getElem_toList, r] using hget
  have hright : b.toList[t]! = b.row r := by
    have hget : b.toList[t]! = b.toList[t]'(by simp [ht_lt_n]) :=
      getElem!_pos _ t (by simp [ht_lt_n])
    simpa [Matrix.row, Vector.getElem_toList, r] using hget
  rw [hleft, hright]
  apply Vector.ext
  intro idx hidx
  let cc : Fin m := ⟨idx, hidx⟩
  change (Matrix.rowSwap b km1 k)[r][cc] = b[r][cc]
  rw [Matrix.getElem_rowSwap]
  simp [hrk, hrkm1]

/-- `basisMatrix_rowSwap`: swapping rows `km1` and `k` leaves the
`basisMatrix` row at any index `i` lying before `km1` unchanged. -/
private theorem basisMatrix_rowSwap
    (b : Matrix Rat n m) (km1 k i : Fin n)
    (hkm1k : km1.val < k.val) (hi : i.val < km1.val) :
    (basisMatrix (Matrix.rowSwap b km1 k)).row i = (basisMatrix b).row i := by
  rw [basisMatrix_row_eq_basisRows_get!, basisMatrix_row_eq_basisRows_get!]
  apply basisRows_get!_eq_of_prefix
  · simp
  · intro t ht
    exact rowSwap_toList_get!_of_lt b km1 k t hkm1k (Nat.lt_of_le_of_lt ht hi)
  · simp

/-- `basisMatrix_rowSwap_adjacent_prev`: after an adjacent swap (`km1 + 1 = k`),
the new `basisMatrix` row at `km1` is the original row `k` plus its projection
onto the original orthogonal row at `km1`. -/
private theorem basisMatrix_rowSwap_adjacent_prev
    (b : Matrix Rat n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    (basisMatrix (Matrix.rowSwap b km1 k)).row km1 =
      (basisMatrix b).row k +
        projectionCoeff (b.row k) ((basisMatrix b).row km1) • (basisMatrix b).row km1 := by
  rw [basisMatrix_row_eq_basisRows_get!, basisMatrix_row_eq_basisRows_get!,
    basisMatrix_row_eq_basisRows_get!]
  have hswap_row :
      (Matrix.rowSwap b km1 k).toList[km1.val]! = b.toList[k.val]! := by
    apply rowSwap_toList_get!_left
    omega
  have hprefix :
      ((basisRows (Matrix.rowSwap b km1 k).toList).take km1.val) =
        ((basisRows b.toList).take km1.val) := by
    apply basisRows_take_eq
    · simp
    · intro t ht
      exact rowSwap_toList_get!_of_lt b km1 k t (by omega) ht
    · simp
  have hlen_swap : (Matrix.rowSwap b km1 k).toList.length = b.toList.length := by simp
  have hkm1_lt_len : km1.val < b.toList.length := by simp [km1.isLt]
  have hkm1_lt_swap : km1.val < (Matrix.rowSwap b km1 k).toList.length := by
    rw [hlen_swap]; exact hkm1_lt_len
  rw [basisRows_get!_eq_reduceAgainstBasis_take
        (Matrix.rowSwap b km1 k).toList km1.val hkm1_lt_swap,
      hprefix, hswap_row]
  have hreduce :=
    reduceAgainstBasis_basisRows_take_source_adjacent
      (rows := b.toList) (km1 := km1.val) (k := k.val) hkm1 (by simp [k.isLt])
  simpa [Matrix.row] using hreduce

/-- `basisMatrix_rowSwap_adjacent_curr`: after an adjacent swap (`km1 + 1 = k`),
the new `basisMatrix` row at `k` is the original orthogonal row at `km1` minus
its projection onto the new orthogonal row produced at `km1`. -/
private theorem basisMatrix_rowSwap_adjacent_curr
    (b : Matrix Rat n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    (basisMatrix (Matrix.rowSwap b km1 k)).row k =
      (basisMatrix b).row km1 -
        projectionCoeff (b.row km1)
          ((basisMatrix b).row k +
            projectionCoeff (b.row k) ((basisMatrix b).row km1) •
              (basisMatrix b).row km1) •
          ((basisMatrix b).row k +
            projectionCoeff (b.row k) ((basisMatrix b).row km1) •
              (basisMatrix b).row km1) := by
  let prev := (basisMatrix b).row km1
  let curr := (basisMatrix b).row k
  let mu := projectionCoeff (b.row k) prev
  let swappedPrev := curr + mu • prev
  change (basisMatrix (Matrix.rowSwap b km1 k)).row k =
    prev - projectionCoeff (b.row km1) swappedPrev • swappedPrev
  rw [basisMatrix_row_eq_basisRows_get!]
  have hkm1k : km1.val < k.val := by omega
  have hk_lt_swap_len : k.val < (Matrix.rowSwap b km1 k).toList.length := by
    simp [k.isLt]
  have hkm1_lt_b_len : km1.val < b.toList.length := by simp [km1.isLt]
  rw [basisRows_get!_eq_reduceAgainstBasis_take
        (Matrix.rowSwap b km1 k).toList k.val hk_lt_swap_len]
  -- Replace the swapped source row at index k with the original row at km1.
  have hswap_row :
      (Matrix.rowSwap b km1 k).toList[k.val]! = b.toList[km1.val]! :=
    rowSwap_toList_get!_right b km1 k
  -- Decompose the prefix of length k = km1 + 1.
  have hkm1_lt_swap_basis :
      km1.val < (basisRows (Matrix.rowSwap b km1 k).toList).length := by
    simp [basisRows_length, km1.isLt]
  have htake_succ :
      (basisRows (Matrix.rowSwap b km1 k).toList).take k.val =
        (basisRows (Matrix.rowSwap b km1 k).toList).take km1.val ++
          [(basisRows (Matrix.rowSwap b km1 k).toList)[km1.val]!] := by
    rw [show k.val = km1.val + 1 from hkm1.symm,
      List.take_succ_eq_append_getElem hkm1_lt_swap_basis]
    congr 1
    simp [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hkm1_lt_swap_basis]
  -- The first km1 entries of `basisRows` agree before and after the swap.
  have hprefix :
      (basisRows (Matrix.rowSwap b km1 k).toList).take km1.val =
        (basisRows b.toList).take km1.val := by
    apply basisRows_take_eq
    · simp
    · intro t ht
      exact rowSwap_toList_get!_of_lt b km1 k t hkm1k ht
    · simp
  -- The km1-th entry of `basisRows` after the swap is `swappedPrev`.
  have hkm1_entry :
      (basisRows (Matrix.rowSwap b km1 k).toList)[km1.val]! = swappedPrev := by
    have hraw :=
      basisMatrix_rowSwap_adjacent_prev (b := b) (km1 := km1) (k := k) hkm1
    have hlhs :
        (basisRows (Matrix.rowSwap b km1 k).toList)[km1.val]! =
          (basisMatrix (Matrix.rowSwap b km1 k)).row km1 := by
      simp [basisMatrix, Matrix.row]
    rw [hlhs, hraw]
  rw [hswap_row, htake_succ, hprefix, hkm1_entry]
  -- Now apply `reduceAgainstBasis_append` to split off `swappedPrev`.
  have hreduce_split :
      reduceAgainstBasis (((basisRows b.toList).take km1.val ++ [swappedPrev]).reverse)
          b.toList[km1.val]! =
        reduceAgainstBasis ((basisRows b.toList).take km1.val).reverse
          (subtractProjection b.toList[km1.val]! swappedPrev) := by
    rw [List.reverse_append, reduceAgainstBasis_append]
    rfl
  rw [hreduce_split]
  -- Expand `subtractProjection` into row + (-proj) • swappedPrev and use linearity.
  have hsource_row : b.toList[km1.val]! = b.row km1 := by simp [Matrix.row]
  rw [hsource_row]
  have hsubP : ∀ u : Vector Rat m, subtractProjection (b.row km1) u =
      (b.row km1) + (- projectionCoeff (b.row km1) u) • u := by
    intro u
    apply Vector.ext
    intro idx hidx
    change ((b.row km1) - projectionCoeff (b.row km1) u • u)[idx] =
      ((b.row km1) + (- projectionCoeff (b.row km1) u) • u)[idx]
    rw [Vector.getElem_sub, Vector.getElem_smul, Vector.getElem_add, Vector.getElem_smul]
    change (b.row km1)[idx] - projectionCoeff (b.row km1) u * u[idx] =
      (b.row km1)[idx] + (- projectionCoeff (b.row km1) u) * u[idx]
    grind
  rw [hsubP swappedPrev, reduceAgainstBasis_add_left, reduceAgainstBasis_smul_left]
  -- Compute the (b.row km1) reduction → `prev`.
  have hreduce_row :
      reduceAgainstBasis ((basisRows b.toList).take km1.val).reverse (b.row km1) =
        prev := by
    have hrec :=
      basisRows_get!_eq_reduceAgainstBasis_take b.toList km1.val hkm1_lt_b_len
    have hbasis_km1 :
        (basisRows b.toList)[km1.val]! = (basisMatrix b).row km1 := by
      exact (basisMatrix_row_eq_basisRows_get! (b := b) km1.val km1.isLt).symm
    have hsrc_row : b.toList[km1.val]! = b.row km1 := by simp [Matrix.row]
    change reduceAgainstBasis _ (b.row km1) = (basisMatrix b).row km1
    rw [← hbasis_km1, hrec, hsrc_row]
  -- Show that `swappedPrev` is orthogonal to every row of `basisRows.take km1`,
  -- so the reduction is the identity on it.
  have hreduce_sP :
      reduceAgainstBasis ((basisRows b.toList).take km1.val).reverse swappedPrev =
        swappedPrev := by
    apply reduceAgainstBasis_eq_self
    intro other hother
    rw [List.mem_reverse] at hother
    rw [List.mem_iff_getElem] at hother
    obtain ⟨idx, hidx, hget⟩ := hother
    have htake_len :
        ((basisRows b.toList).take km1.val).length = km1.val := by
      rw [List.length_take]
      simp [basisRows_length]
    have hidx_km1 : idx < km1.val := by
      rw [htake_len] at hidx
      exact hidx
    have hidx_basis_len : idx < (basisRows b.toList).length := by
      simp only [basisRows_length, Vector.length_toList]
      omega
    have hother_get :
        other = (basisRows b.toList)[idx]! := by
      rw [← hget, List.getElem_take]
      simp [hidx_basis_len]
    rw [hother_get]
    -- dot swappedPrev (basisRows[idx]) = dot curr (basisRows[idx]) + mu * dot prev (basisRows[idx])
    -- Both inner products vanish by pairwise orthogonality.
    have hcurr_orth :
        curr.dotProduct (basisRows b.toList)[idx]! = 0 := by
      change ((basisMatrix b).row k).dotProduct _ = 0
      rw [basisMatrix_row_eq_basisRows_get!]
      exact basisRows_get!_dot_eq_zero_of_list b.toList k.val idx
        (by simp [k.isLt])
        (by simp only [Vector.length_toList]; omega)
        (by omega)
    have hprev_orth :
        prev.dotProduct (basisRows b.toList)[idx]! = 0 := by
      change ((basisMatrix b).row km1).dotProduct _ = 0
      rw [basisMatrix_row_eq_basisRows_get!]
      exact basisRows_get!_dot_eq_zero_of_list b.toList km1.val idx
        (by simp [km1.isLt])
        (by simp only [Vector.length_toList]; omega)
        (by omega)
    show (curr + mu • prev).dotProduct _ = 0
    rw [dot_add_left, dot_smul_left, hcurr_orth, hprev_orth]
    grind
  rw [hreduce_row, hreduce_sP]
  -- Combine: prev + (-proj) • swappedPrev = prev - proj • swappedPrev
  have hfinal : ∀ p : Vector Rat m, ∀ u : Vector Rat m, ∀ s : Rat,
      p + (- s) • u = p - s • u := by
    intro p u s
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_add, Vector.getElem_sub, Vector.getElem_smul, Vector.getElem_smul]
    change p[idx] + (- s) * u[idx] = p[idx] - s * u[idx]
    grind
  exact hfinal prev swappedPrev (projectionCoeff (b.row km1) swappedPrev)

/-- The "by-row" prefix sum: a row-indexed variant of `prefixCombination` that
takes the projection row directly rather than reading it through a coefficient
matrix. Defined via `foldl` over `List.finRange i` so the conversion to
`prefixCombination` is a pointwise function-level rewrite. -/
private def prefixSumByRow (row : Vector Rat m) (basis : Matrix Rat n m)
    (i : Nat) (hi : i ≤ n) : Vector Rat m :=
  (List.finRange i).foldl
    (fun acc j =>
      let jn : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩
      acc + projectionCoeff row (basis.row jn) • basis.row jn)
    0

/-- The strict row prefix containing rows `0` through `k - 1`. This is the
matrix shape naturally paired with `prefixSumByRow`. -/
private def strictPrefixRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n) :
    Matrix R k m :=
  Vector.ofFn fun j => M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩

/-- Extend coefficients on a strict prefix by a zero coefficient on the new
last row of the inclusive prefix. -/
private def extendStrictPrefixCoeff (c : Vector Rat k) : Vector Rat (k + 1) :=
  Vector.ofFn fun j =>
    if h : j.val < k then
      let jj : Fin k := ⟨j.val, h⟩
      c[jj]
    else
      0

/-- Coefficients witnessing `prefixSumByRow` as a row combination of the strict
row prefix. -/
private def projectionCoeffVector (row : Vector Rat m) (basis : Matrix Rat n m)
    (k : Nat) (hk : k ≤ n) : Vector Rat k :=
  Vector.ofFn fun j =>
    projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)

private theorem rowCombination_prefixRows_extendStrictPrefixCoeff
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat i) :
    Matrix.rowCombination (prefixRows M i hi) (extendStrictPrefixCoeff c) =
      Matrix.rowCombination (strictPrefixRows M i (Nat.le_of_lt hi)) c := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change
    (Matrix.mulVec (Matrix.transpose (prefixRows M i hi))
        (extendStrictPrefixCoeff c))[idxFin] =
      (Matrix.mulVec (Matrix.transpose (strictPrefixRows M i (Nat.le_of_lt hi)))
        c)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose (prefixRows M i hi))
          (extendStrictPrefixCoeff c))[idxFin] =
        (List.finRange (i + 1)).foldl
          (fun acc j =>
            acc +
              (M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hi)⟩)[idxFin] *
                (extendStrictPrefixCoeff c)[j])
          0 by
        unfold Matrix.mulVec Matrix.transpose Matrix.col Matrix.row Vector.dotProduct prefixRows
        simp [Matrix.row]]
  rw [show
      (Matrix.mulVec (Matrix.transpose (strictPrefixRows M i (Nat.le_of_lt hi)))
          c)[idxFin] =
        (List.finRange i).foldl
          (fun acc j =>
            acc +
              (M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt hi)⟩)[idxFin] *
                c[j])
          0 by
        unfold Matrix.mulVec Matrix.transpose Matrix.col Matrix.row Vector.dotProduct strictPrefixRows
        simp [Matrix.row]]
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  have hlast_not_lt : ¬i < i := Nat.lt_irrefl i
  simp [extendStrictPrefixCoeff, hlast_not_lt]
  grind

private theorem rowCombination_add_rat
    (M : Matrix Rat n m) (c d : Vector Rat n) :
    Matrix.rowCombination M (c + d) =
      Matrix.rowCombination M c + Matrix.rowCombination M d := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) (c + d))[idxFin] =
    (Matrix.rowCombination M c + Matrix.rowCombination M d)[idxFin]
  simp [Matrix.rowCombination, HMul.hMul, Matrix.mulVec, Matrix.transpose, Matrix.col,
    Matrix.row, Vector.dotProduct, Vector.getElem_add]
  have hfold :
      ∀ xs : List (Fin n), ∀ accC accD : Rat,
        xs.foldl
            (fun acc row =>
              acc + M[row.val][idxFin.val] * (c[row.val] + d[row.val]))
            (accC + accD) =
          xs.foldl (fun acc row => acc + M[row.val][idxFin.val] * c[row.val]) accC +
            xs.foldl (fun acc row => acc + M[row.val][idxFin.val] * d[row.val]) accD := by
    intro xs
    induction xs with
    | nil =>
        intro accC accD
        simp
    | cons row rows ih =>
        intro accC accD
        simp only [List.foldl_cons]
        have hstep :
            accC + accD + M[row.val][idxFin.val] * (c[row.val] + d[row.val]) =
              (accC + M[row.val][idxFin.val] * c[row.val]) +
                (accD + M[row.val][idxFin.val] * d[row.val]) := by
          grind
        rw [hstep]
        exact ih (accC + M[row.val][idxFin.val] * c[row.val])
          (accD + M[row.val][idxFin.val] * d[row.val])
  have h := hfold (List.finRange n) 0 0
  rw [show (0 : Rat) + 0 = 0 by grind] at h
  exact h

private theorem rowCombination_smul_rat
    (M : Matrix Rat n m) (a : Rat) (c : Vector Rat n) :
    Matrix.rowCombination M (a • c) =
      a • Matrix.rowCombination M c := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) (a • c))[idxFin] =
    (a • Matrix.rowCombination M c)[idxFin]
  simp [Matrix.rowCombination, HMul.hMul, Matrix.mulVec, Matrix.transpose, Matrix.col,
    Matrix.row, Vector.dotProduct, Vector.getElem_smul]
  have hfold :
      ∀ xs : List (Fin n), ∀ acc : Rat,
        xs.foldl
            (fun acc row => acc + M[row.val][idxFin.val] * (a * c[row.val]))
            (a * acc) =
          a * xs.foldl (fun acc row => acc + M[row.val][idxFin.val] * c[row.val]) acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp
    | cons row rows ih =>
        intro acc
        simp only [List.foldl_cons]
        have hstep :
            a * acc + M[row.val][idxFin.val] * (a * c[row.val]) =
              a * (acc + M[row.val][idxFin.val] * c[row.val]) := by
          grind
        rw [hstep]
        exact ih (acc + M[row.val][idxFin.val] * c[row.val])
  have key := hfold (List.finRange n) 0
  simp only [Rat.mul_zero] at key
  exact key

/-- `prefixSpan_add` says the rational prefix row-span is closed under vector addition. -/
private theorem prefixSpan_add
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) {u v : Vector Rat m}
    (hu : prefixSpan M i hi u) (hv : prefixSpan M i hi v) :
    prefixSpan M i hi (u + v) := by
  rcases hu with ⟨cu, hcu⟩
  rcases hv with ⟨cv, hcv⟩
  refine ⟨cu + cv, ?_⟩
  rw [rowCombination_add_rat, hcu, hcv]

/-- `prefixSpan_smul` says the rational prefix row-span is closed under scalar multiplication. -/
private theorem prefixSpan_smul
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (a : Rat) {u : Vector Rat m}
    (hu : prefixSpan M i hi u) :
    prefixSpan M i hi (a • u) := by
  rcases hu with ⟨cu, hcu⟩
  refine ⟨a • cu, ?_⟩
  rw [rowCombination_smul_rat, hcu]

/-- `prefixSpan_sub` says the rational prefix row-span is closed under vector subtraction. -/
private theorem prefixSpan_sub
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) {u v : Vector Rat m}
    (hu : prefixSpan M i hi u) (hv : prefixSpan M i hi v) :
    prefixSpan M i hi (u - v) := by
  have hneg : prefixSpan M i hi ((-1 : Rat) • v) :=
    prefixSpan_smul M i hi (-1) hv
  have hadd := prefixSpan_add M i hi hu hneg
  have hsub : u + (-1 : Rat) • v = u - v := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_add, Vector.getElem_smul, Vector.getElem_sub]
    change u[idx] + (-1 : Rat) * v[idx] = u[idx] - v[idx]
    grind
  simpa [← hsub] using hadd

/-- `dot_add_right` gives additivity of the rational dot product in its right argument. -/
private theorem dot_add_right (a b c : Vector Rat m) :
    a.dotProduct (b + c) = a.dotProduct b + a.dotProduct c := by
  rw [dot_comm_rat, dot_add_left, dot_comm_rat b a, dot_comm_rat c a]

/-- `dot_smul_right` pulls a rational scalar out of the right argument of the dot product. -/
private theorem dot_smul_right (s : Rat) (a b : Vector Rat m) :
    a.dotProduct (s • b) = s * a.dotProduct b := by
  rw [dot_comm_rat, dot_smul_left, dot_comm_rat b a]

/-- `dot_sub_right` gives subtractivity of the rational dot product in its right argument. -/
private theorem dot_sub_right (a b c : Vector Rat m) :
    a.dotProduct (b - c) = a.dotProduct b - a.dotProduct c := by
  have hsub : b - c = b + (-1 : Rat) • c := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_sub, Vector.getElem_add, Vector.getElem_smul]
    change b[idx] - c[idx] = b[idx] + (-1 : Rat) * c[idx]
    grind
  rw [hsub, dot_add_right, dot_smul_right]
  grind

/-- `dot_zero_right` says the rational dot product with a zero right argument is zero. -/
private theorem dot_zero_right (a : Vector Rat m) :
    a.dotProduct 0 = 0 := by
  unfold Vector.dotProduct
  change (List.finRange m).foldl
      (fun acc i => acc + a[i] * (0 : Vector Rat m)[i]) 0 = 0
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hterm : a[i] * (0 : Vector Rat m)[i] = 0 := by
        change a[i] * (0 : Vector Rat m)[i.val] = 0
        rw [Vector.getElem_zero]
        grind
      rw [hterm, show (0 : Rat) + 0 = 0 by grind]
      exact ih

private def unitCoeff (j : Fin n) : Vector Rat n :=
  Vector.ofFn fun k => if k = j then 1 else 0

private theorem foldl_add_eq_acc_rat
    {α : Type} (xs : List α) (f : α → Rat) (acc : Rat)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hacc : acc + (0 : Rat) = acc := by grind
      rw [hacc]
      exact ih acc hxs

private theorem foldl_indicator_mul_unique_rat
    (xs : List (Fin n)) (i : Fin n) (f : Fin n → Rat)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : Rat) :
    xs.foldl (fun acc l => acc + f l * (if l = i then (1 : Rat) else 0)) acc =
      acc + f i := by
  induction xs generalizing acc with
  | nil =>
      exact absurd hi List.not_mem_nil
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hix | hitail
      · subst i
        rw [if_pos rfl]
        have hxs_zero :
            ∀ y ∈ xs, f y * (if y = x then (1 : Rat) else 0) = 0 := by
          intro y hy
          have hyx : y ≠ x := by
            intro heq
            exact (List.nodup_cons.mp hnodup).1 (heq ▸ hy)
          rw [if_neg hyx]
          grind
        have hfold :=
          foldl_add_eq_acc_rat xs
            (fun l => f l * (if l = x then (1 : Rat) else 0))
            (acc + f x * 1) hxs_zero
        have hfold' :
            xs.foldl (fun acc l => acc + f l * (if l = x then (1 : Rat) else 0))
                (acc + f x * 1) =
              acc + f x * 1 := hfold
        rw [hfold']
        grind
      · have hxi : x ≠ i := by
          intro h
          subst i
          exact (List.nodup_cons.mp hnodup).1 hitail
        rw [if_neg hxi]
        have hzero : f x * (0 : Rat) = 0 := by grind
        rw [hzero]
        have hacc : acc + (0 : Rat) = acc := by grind
        rw [hacc]
        exact ih hitail (List.nodup_cons.mp hnodup).2 acc

private theorem rowCombination_prefixRows_unitCoeff
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (j : Fin (i + 1)) :
    Matrix.rowCombination (prefixRows M i hi) (unitCoeff j) =
      (prefixRows M i hi).row j := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change
    (Matrix.mulVec (Matrix.transpose (prefixRows M i hi)) (unitCoeff j))[idxFin] =
      ((prefixRows M i hi).row j)[idxFin]
  simp [HMul.hMul, Matrix.mulVec, Matrix.transpose, Matrix.col,
    Matrix.row, Vector.dotProduct, unitCoeff]
  have h :=
    foldl_indicator_mul_unique_rat
      (xs := List.finRange (i + 1)) (i := j)
      (f := fun row : Fin (i + 1) => (prefixRows M i hi)[row.val][idxFin.val])
      (hi := List.mem_finRange j) (hnodup := List.nodup_finRange (i + 1)) (acc := 0)
  rw [show (0 : Rat) + (prefixRows M i hi)[j.val][idxFin.val] =
      (prefixRows M i hi)[j.val][idxFin.val] by grind] at h
  exact h

private theorem prefixSpan_row
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (j : Fin (i + 1)) :
    prefixSpan M i hi ((prefixRows M i hi).row j) := by
  exact ⟨unitCoeff j, rowCombination_prefixRows_unitCoeff M i hi j⟩

private theorem rowCombination_eq_foldl_rows
    (M : Matrix Rat n m) (c : Vector Rat n) :
    Matrix.rowCombination M c =
      (List.finRange n).foldl (fun acc j => acc + c[j] • M.row j) 0 := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) c)[idxFin] =
    ((List.finRange n).foldl (fun acc j => acc + c[j] • M.row j) 0)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose M) c)[idxFin] =
        (List.finRange n).foldl
          (fun acc j => acc + M[j.val][idxFin.val] * c[j])
          0 by
        unfold Matrix.mulVec Matrix.transpose Matrix.col Matrix.row Vector.dotProduct
        simp]
  have hfold :
      ∀ xs : List (Fin n), ∀ accL : Rat, ∀ accR : Vector Rat m,
        accL = accR[idxFin] →
        xs.foldl (fun acc j => acc + M[j.val][idxFin.val] * c[j]) accL =
          (xs.foldl (fun acc j => acc + c[j] • M.row j) accR)[idxFin] := by
    intro xs
    induction xs with
    | nil =>
        intro accL accR hacc
        simp [hacc]
    | cons j rest ih =>
        intro accL accR hacc
        simp only [List.foldl_cons]
        apply ih
        change accL + M[j.val][idxFin.val] * c[j] =
          (accR + c[j] • M.row j)[idxFin.val]
        rw [Vector.getElem_add, Vector.getElem_smul, hacc]
        change accR[idx] + M[j.val][idx] * c[j] =
          accR[idx] + c[j] * M[j.val][idx]
        grind
  exact hfold (List.finRange n) 0 0 (by simp [Vector.getElem_zero])

private theorem dot_eq_zero_of_prefixSpan
    (M : Matrix Rat n m) (i : Nat) (hi : i < n)
    (u v : Vector Rat m)
    (hspan : prefixSpan M i hi v)
    (horth : ∀ j : Fin (i + 1), u.dotProduct ((prefixRows M i hi).row j) = 0) :
    u.dotProduct v = 0 := by
  rcases hspan with ⟨c, hc⟩
  rw [← hc, rowCombination_eq_foldl_rows]
  have hfold :
      ∀ xs : List (Fin (i + 1)), ∀ acc : Vector Rat m,
        u.dotProduct acc = 0 →
          u.dotProduct
            (xs.foldl
              (fun acc j => acc + c[j] • (prefixRows M i hi).row j) acc) = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons j rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        rw [dot_add_right, dot_smul_right, hacc, horth j]
        grind
  exact hfold (List.finRange (i + 1)) 0 (dot_zero_right u)

/-- `v`.normSq is nonnegative for a rational vector, since it is the
self-dot-product, a sum of squares (via `foldl_dot_self_start_le`). -/
private theorem rat_normSq_nonneg (v : Vector Rat m) :
    0 ≤ v.normSq := by
  simpa [Vector.normSq, Vector.dotProduct] using
    foldl_dot_self_start_le (xs := List.finRange m) (v := v)
      (acc := 0) (by decide)

/-- Pythagorean split: when `acc` is orthogonal to `row`, the squared norm of
`acc + c • row` expands to `acc.normSq + c * c * row`..normSq -/
private theorem normSq_add_smul
    (acc row : Vector Rat m) (c : Rat)
    (horth : acc.dotProduct row = 0) :
    (acc + c • row).normSq =
      acc.normSq + c * c * row.normSq := by
  change (acc + c • row).dotProduct (acc + c • row) =
    acc.dotProduct acc + c * c * row.dotProduct row
  rw [dot_add_left, dot_add_right acc acc (c • row), dot_smul_right, dot_smul_left,
    dot_add_right row acc (c • row), dot_smul_right, horth]
  have horth' : row.dotProduct acc = 0 := by
    rw [dot_comm_rat]
    exact horth
  rw [horth']
  grind

/-- A left fold summing `f` over `xs` factors its starting accumulator out:
`xs.foldl (· + f ·) acc = acc + xs.foldl (· + f ·) 0`. -/
private theorem foldl_rat_sum_start {α : Type v}
    (xs : List α) (f : α → Rat) (acc : Rat) :
    xs.foldl (fun total x => total + f x) acc =
      acc + xs.foldl (fun total x => total + f x) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
      grind
  | cons x xs ih =>
    simp only [List.foldl_cons]
    calc
      xs.foldl (fun total x => total + f x) (acc + f x) =
          (acc + f x) + xs.foldl (fun total x => total + f x) 0 := ih (acc + f x)
      _ = acc + ((0 + f x) + xs.foldl (fun total x => total + f x) 0) := by grind
      _ = acc + xs.foldl (fun total x => total + f x) (0 + f x) := by
          rw [ih (0 + f x)]

/-- Orthogonal-expansion of a folded row combination: when the listed rows are
pairwise orthogonal and `acc` is orthogonal to each, the squared norm of the
fold splits as `acc`.normSq plus the fold of weighted squared norms
`coeffs[i] * coeffs[i] * (rows.row i)`..normSq -/
private theorem foldl_orthogonal_expansion_normSq
    (xs : List (Fin n)) (rows : Matrix Rat n m) (coeffs : Vector Rat n)
    (acc : Vector Rat m)
    (hnodup : xs.Nodup)
    (hacc : ∀ i ∈ xs, acc.dotProduct (rows.row i) = 0)
    (horth : ∀ i ∈ xs, ∀ j ∈ xs, i ≠ j →
      (rows.row i).dotProduct (rows.row j) = 0) :
    Vector.normSq
        (xs.foldl (fun acc i => acc + coeffs[i] • rows.row i) acc) =
      acc.normSq +
        xs.foldl
          (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
      grind
  | cons i rest ih =>
    simp only [List.foldl_cons]
    have hnodup_tail : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hi_not_mem : i ∉ rest := (List.nodup_cons.mp hnodup).1
    let acc' := acc + coeffs[i] • rows.row i
    have hacc' : ∀ j ∈ rest, acc'.dotProduct (rows.row j) = 0 := by
      intro j hj
      have hij : i ≠ j := by
        intro h
        subst h
        exact hi_not_mem hj
      have hrow : (rows.row i).dotProduct (rows.row j) = 0 :=
        horth i (by simp) j (by simp [hj]) hij
      simp only [acc']
      rw [dot_add_left, dot_smul_left, hacc j (by simp [hj]), hrow]
      grind
    have horth' : ∀ a ∈ rest, ∀ b ∈ rest, a ≠ b →
        (rows.row a).dotProduct (rows.row b) = 0 := by
      intro a ha b hb hab
      exact horth a (by simp [ha]) b (by simp [hb]) hab
    rw [ih (acc := acc') hnodup_tail hacc' horth',
      normSq_add_smul acc (rows.row i) coeffs[i] (hacc i (by simp))]
    rw [foldl_rat_sum_start rest
      (fun j => coeffs[j] * coeffs[j] * (rows.row j).normSq)
      (0 + coeffs[i] * coeffs[i] * (rows.row i).normSq)]
    grind

/-- The `acc = 0` case of `foldl_orthogonal_expansion_normSq`: for pairwise
orthogonal rows the squared norm of the full row combination equals the fold of
`coeffs[i] * coeffs[i] * (rows.row i)`.normSq over `List.finRange n`. -/
private theorem foldl_orthogonal_expansion_normSq_zero
    (rows : Matrix Rat n m) (coeffs : Vector Rat n)
    (horth : ∀ i j : Fin n, i ≠ j →
      (rows.row i).dotProduct (rows.row j) = 0) :
    Vector.normSq
        ((List.finRange n).foldl (fun acc i => acc + coeffs[i] • rows.row i) 0) =
      (List.finRange n).foldl
        (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 := by
  have hacc : ∀ i ∈ List.finRange n, (0 : Vector Rat m).dotProduct (rows.row i) = 0 := by
    intro i _hi
    rw [dot_comm_rat]
    exact dot_zero_right (rows.row i)
  have horth' : ∀ i ∈ List.finRange n, ∀ j ∈ List.finRange n, i ≠ j →
      (rows.row i).dotProduct (rows.row j) = 0 := by
    intro i _hi j _hj hij
    exact horth i j hij
  have h :=
    foldl_orthogonal_expansion_normSq (xs := List.finRange n)
      (rows := rows) (coeffs := coeffs) (acc := (0 : Vector Rat m))
      (List.nodup_finRange n) hacc horth'
  have hzero : (0 : Vector Rat m).normSq = 0 := by
    have hfold :
        ∀ xs : List (Fin m), ∀ acc : Rat,
          xs.foldl (fun acc _ => acc + 0) acc = acc := by
      intro xs
      induction xs with
      | nil =>
          intro acc
          simp
      | cons _ rest ih =>
          intro acc
          simp only [List.foldl_cons]
          have hacc : acc + 0 = acc := by grind
          rw [hacc]
          exact ih acc
    simpa [Vector.normSq, Vector.dotProduct] using
      hfold (List.finRange m) 0
  rw [hzero] at h
  have hzero_add :
      (0 : Rat) +
          (List.finRange n).foldl
            (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 =
        (List.finRange n).foldl
            (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 := by
    grind
  rw [hzero_add] at h
  exact h

/-- The weighted-squared-norm fold `xs.foldl (· + coeffs[i] * coeffs[i] *
(rows.row i).normSq) 0` is nonnegative, being a sum of nonnegative
terms. -/
private theorem foldl_orthogonal_weighted_nonneg
    (xs : List (Fin n)) (rows : Matrix Rat n m) (coeffs : Vector Rat n) :
    0 ≤ xs.foldl
      (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 := by
  induction xs with
  | nil =>
      simp
  | cons i rest ih =>
      simp only [List.foldl_cons]
      rw [foldl_rat_sum_start rest
        (fun j => coeffs[j] * coeffs[j] * (rows.row j).normSq)
        (0 + coeffs[i] * coeffs[i] * (rows.row i).normSq)]
      have hterm : 0 ≤ coeffs[i] * coeffs[i] * (rows.row i).normSq :=
        Rat.mul_nonneg (rat_mul_self_nonneg coeffs[i]) (rat_normSq_nonneg (rows.row i))
      exact Rat.add_nonneg (by grind) ih

/-- If `k ∈ xs` and its coefficient square is at least `1`, the
weighted-squared-norm fold over `xs` is at least `(rows.row k)`.normSq,
the single term contributed by `k`. -/
private theorem foldl_orthogonal_weighted_normSq_ge
    (xs : List (Fin n)) (rows : Matrix Rat n m) (coeffs : Vector Rat n)
    (k : Fin n) (hk : k ∈ xs)
    (hcoeff : 1 ≤ coeffs[k] * coeffs[k]) :
    (rows.row k).normSq ≤
      xs.foldl
        (fun total i => total + coeffs[i] * coeffs[i] * (rows.row i).normSq) 0 := by
  induction xs with
  | nil =>
      cases hk
  | cons i rest ih =>
      simp only [List.foldl_cons]
      simp only [List.mem_cons] at hk
      have hterm_nonneg :
          0 ≤ coeffs[i] * coeffs[i] * (rows.row i).normSq := by
        exact Rat.mul_nonneg (rat_mul_self_nonneg coeffs[i]) (rat_normSq_nonneg (rows.row i))
      cases hk with
      | inl hik =>
          subst hik
          rw [foldl_rat_sum_start rest
            (fun j => coeffs[j] * coeffs[j] * (rows.row j).normSq)
            (0 + coeffs[k] * coeffs[k] * (rows.row k).normSq)]
          have hrow_nonneg : 0 ≤ (rows.row k).normSq :=
            rat_normSq_nonneg (rows.row k)
          have hfirst :
              (rows.row k).normSq ≤
                coeffs[k] * coeffs[k] * (rows.row k).normSq := by
            have hdelta_nonneg : 0 ≤ (coeffs[k] * coeffs[k] - 1) *
                (rows.row k).normSq :=
              Rat.mul_nonneg (by grind) hrow_nonneg
            have hsplit :
                coeffs[k] * coeffs[k] * (rows.row k).normSq =
                  (rows.row k).normSq +
                    (coeffs[k] * coeffs[k] - 1) * (rows.row k).normSq := by
              grind
            calc
              (rows.row k).normSq ≤
                  (rows.row k).normSq +
                    (coeffs[k] * coeffs[k] - 1) * (rows.row k).normSq := by
                    grind
              _ = coeffs[k] * coeffs[k] * (rows.row k).normSq := hsplit.symm
          have htail_nonneg :
              0 ≤ rest.foldl
                (fun total j => total + coeffs[j] * coeffs[j] * (rows.row j).normSq) 0 := by
            exact foldl_orthogonal_weighted_nonneg rest rows coeffs
          exact Rat.le_trans hfirst (by grind)
      | inr htail =>
          have htail_le := ih htail
          rw [foldl_rat_sum_start rest
            (fun j => coeffs[j] * coeffs[j] * (rows.row j).normSq)
            (0 + coeffs[i] * coeffs[i] * (rows.row i).normSq)]
          exact Rat.le_trans htail_le (by grind)

/-- Orthogonal row-combination lower bound. If the rows of `rows` are pairwise
orthogonal and the coefficient at `k` has square at least `1`, then the squared
norm of the whole row combination is at least the squared norm of row `k`. -/
theorem rowCombination_normSq_ge_of_orthogonal_coeff_sq_ge_one
    (rows : Matrix Rat n m) (coeffs : Vector Rat n) (k : Fin n)
    (horth : ∀ i j : Fin n, i ≠ j →
      (rows.row i).dotProduct (rows.row j) = 0)
    (hcoeff : 1 ≤ coeffs[k] * coeffs[k]) :
    (rows.row k).normSq ≤ (Matrix.rowCombination rows coeffs).normSq := by
  rw [rowCombination_eq_foldl_rows, foldl_orthogonal_expansion_normSq_zero rows coeffs horth]
  exact foldl_orthogonal_weighted_normSq_ge (xs := List.finRange n)
    (rows := rows) (coeffs := coeffs) k (by simp) hcoeff

/-- A nonzero integer coefficient has rational square at least `1`. -/
theorem one_le_intCast_mul_self_of_ne_zero (z : Int) (hz : z ≠ 0) :
    (1 : Rat) ≤ ((z : Rat) * (z : Rat)) := by
  cases z with
  | ofNat n =>
      cases n with
      | zero =>
          exact False.elim (hz rfl)
      | succ n =>
          let a : Rat := ((Nat.succ n : Nat) : Rat)
          have hge : (1 : Rat) ≤ a := by
            have hnat : 1 ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
            dsimp [a]
            exact_mod_cast hnat
          have hnonneg : (0 : Rat) ≤ a := by
            exact Rat.le_trans (by decide) hge
          have hsum_nonneg : 0 ≤ a + 1 := by grind
          have hprod_nonneg : 0 ≤ (a - 1) * (a + 1) :=
            Rat.mul_nonneg (by grind) hsum_nonneg
          have hsplit : a * a = 1 + (a - 1) * (a + 1) := by grind
          change (1 : Rat) ≤ a * a
          rw [hsplit]
          grind
  | negSucc n =>
      have hpos :
          (1 : Rat) ≤ (((Nat.succ n : Nat) : Rat) * ((Nat.succ n : Nat) : Rat)) := by
        let a : Rat := ((Nat.succ n : Nat) : Rat)
        have hge : (1 : Rat) ≤ a := by
          have hnat : 1 ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
          dsimp [a]
          exact_mod_cast hnat
        have hnonneg : (0 : Rat) ≤ a := by
          exact Rat.le_trans (by decide) hge
        have hsum_nonneg : 0 ≤ a + 1 := by grind
        have hprod_nonneg : 0 ≤ (a - 1) * (a + 1) :=
          Rat.mul_nonneg (by grind) hsum_nonneg
        have hsplit : a * a = 1 + (a - 1) * (a + 1) := by grind
        change (1 : Rat) ≤ a * a
        rw [hsplit]
        grind
      change (1 : Rat) ≤ (-(↑(Nat.succ n) : Rat)) * (-(↑(Nat.succ n) : Rat))
      have hsq :
          (-(↑(Nat.succ n) : Rat)) * (-(↑(Nat.succ n) : Rat)) =
            (↑(Nat.succ n) : Rat) * (↑(Nat.succ n) : Rat) := by
        grind
      rw [hsq]
      exact hpos

private theorem eq_zero_of_prefixSpan
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (v : Vector Rat m)
    (hspan : prefixSpan M i hi v)
    (horth : ∀ j : Fin (i + 1), v.dotProduct ((prefixRows M i hi).row j) = 0) :
    v = 0 := by
  have hself : v.dotProduct v = 0 :=
    dot_eq_zero_of_prefixSpan M i hi v v hspan horth
  apply Vector.ext
  intro idx hidx
  rw [Vector.getElem_zero]
  exact dot_self_eq_zero_get v hself ⟨idx, hidx⟩

/-- If two residuals reconstruct the same source row modulo the same prefix
span and are both orthogonal to that prefix, they are equal. This is the
local uniqueness principle used by suffix row-swap proofs after translating
equal generated prefixes into equal `prefixSpan` predicates. -/
private theorem residual_eq_of_same_prefixSpan
    (M : Matrix Rat n m) (i : Nat) (hi : i < n)
    (row r s : Vector Rat m)
    (hrspan : prefixSpan M i hi (row - r))
    (hsspan : prefixSpan M i hi (row - s))
    (hrorth : ∀ j : Fin (i + 1), r.dotProduct ((prefixRows M i hi).row j) = 0)
    (hsorth : ∀ j : Fin (i + 1), s.dotProduct ((prefixRows M i hi).row j) = 0) :
    r = s := by
  have hspanDiff :
      prefixSpan M i hi ((row - s) - (row - r)) :=
    prefixSpan_sub M i hi hsspan hrspan
  have hdiff_eq : (row - s) - (row - r) = r - s := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_sub, Vector.getElem_sub, Vector.getElem_sub]
    grind
  have hspan : prefixSpan M i hi (r - s) := by
    simpa [hdiff_eq] using hspanDiff
  have horth : ∀ j : Fin (i + 1),
      (r - s).dotProduct ((prefixRows M i hi).row j) = 0 := by
    intro j
    rw [dot_comm_rat (r - s) ((prefixRows M i hi).row j), dot_sub_right]
    rw [dot_comm_rat ((prefixRows M i hi).row j) r,
      dot_comm_rat ((prefixRows M i hi).row j) s, hrorth j, hsorth j]
    grind
  have hzero := eq_zero_of_prefixSpan M i hi (r - s) hspan horth
  apply Vector.ext
  intro idx hidx
  have hz := congrArg (fun v : Vector Rat m => v[(⟨idx, hidx⟩ : Fin m)]) hzero
  change (r - s)[idx] = (0 : Vector Rat m)[idx] at hz
  rw [Vector.getElem_sub, Vector.getElem_zero] at hz
  grind

/-- Residual uniqueness across two prefix bases with the same span. The
second residual only needs to reconstruct modulo `B`; the span equality and
orthogonality transport move it to `A`, where `residual_eq_of_same_prefixSpan`
applies. -/
private theorem residual_eq_of_equiv_prefixSpan
    (A B : Matrix Rat n m) (i : Nat) (hi : i < n)
    (row r s : Vector Rat m)
    (hrspan : prefixSpan A i hi (row - r))
    (hsspan : prefixSpan B i hi (row - s))
    (hB_to_A : ∀ v : Vector Rat m, prefixSpan B i hi v → prefixSpan A i hi v)
    (hA_rows_to_B :
      ∀ j : Fin (i + 1), prefixSpan B i hi ((prefixRows A i hi).row j))
    (hrorth : ∀ j : Fin (i + 1), r.dotProduct ((prefixRows A i hi).row j) = 0)
    (hsorth : ∀ j : Fin (i + 1), s.dotProduct ((prefixRows B i hi).row j) = 0) :
    r = s := by
  apply residual_eq_of_same_prefixSpan A i hi row r s hrspan (hB_to_A _ hsspan) hrorth
  intro j
  exact dot_eq_zero_of_prefixSpan B i hi s ((prefixRows A i hi).row j)
    (hA_rows_to_B j) hsorth

/-- `prefixSpan_zero` states that the zero vector is contained in every prefix span, providing the base case for prefix-span closure arguments. -/
private theorem prefixSpan_zero
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) :
    prefixSpan M i hi 0 := by
  let j : Fin (i + 1) := ⟨0, Nat.succ_pos i⟩
  have hz := prefixSpan_smul M i hi 0 (prefixSpan_row M i hi j)
  have hzero : (0 : Rat) • (prefixRows M i hi).row j = 0 := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_smul, Vector.getElem_zero]
    change (0 : Rat) * ((prefixRows M i hi).row j)[idx] = 0
    grind
  simpa [hzero] using hz

/-- `prefixSpan_rowCombination` states that any row combination of prefix rows already in another prefix span remains in that prefix span. -/
private theorem prefixSpan_rowCombination
    (A B : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat (i + 1))
    (hrows : ∀ j : Fin (i + 1), prefixSpan B i hi ((prefixRows A i hi).row j)) :
    prefixSpan B i hi (Matrix.rowCombination (prefixRows A i hi) c) := by
  rw [rowCombination_eq_foldl_rows]
  have hfold :
      ∀ xs : List (Fin (i + 1)), ∀ acc : Vector Rat m,
        prefixSpan B i hi acc →
          prefixSpan B i hi
            (xs.foldl
              (fun acc j => acc + c[j] • (prefixRows A i hi).row j) acc) := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons j rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        exact prefixSpan_add B i hi hacc
          (prefixSpan_smul B i hi c[j] (hrows j))
  exact hfold (List.finRange (i + 1)) 0 (prefixSpan_zero B i hi)

/-- `strictPrefixRows_succ_eq_prefixRows` identifies the strict prefix of length `i + 1` with the inclusive prefix through row `i`. -/
private theorem strictPrefixRows_succ_eq_prefixRows
    (M : Matrix Rat n m) (i : Nat) (hi : i + 1 < n) :
    strictPrefixRows M (i + 1) (Nat.le_of_lt hi) =
      prefixRows M i (Nat.lt_of_succ_lt hi) := by
  apply Vector.ext
  intro row hrow
  apply Vector.ext
  intro col hcol
  rfl

/-- `prefixSpan_mono_succ` lifts prefix-span membership across one successor step in the prefix length. -/
private theorem prefixSpan_mono_succ
    (M : Matrix Rat n m) (i : Nat) (hi : i + 1 < n) {v : Vector Rat m}
    (hv : prefixSpan M i (Nat.lt_of_succ_lt hi) v) :
    prefixSpan M (i + 1) hi v := by
  rcases hv with ⟨c, hc⟩
  refine ⟨extendStrictPrefixCoeff c, ?_⟩
  rw [rowCombination_prefixRows_extendStrictPrefixCoeff,
    strictPrefixRows_succ_eq_prefixRows (hi := hi)]
  exact hc

/-- `prefixSpan_mono_le` lifts prefix-span membership along any ordered pair of prefix indices. -/
private theorem prefixSpan_mono_le
    (M : Matrix Rat n m) {j i : Nat} (hj : j < n) (hi : i < n) (hji : j ≤ i)
    {v : Vector Rat m} (hv : prefixSpan M j hj v) :
    prefixSpan M i hi v := by
  induction hji with
  | refl =>
      exact hv
  | step hji ih =>
      exact prefixSpan_mono_succ M _ hi (ih (Nat.lt_of_succ_lt hi))

/-- `prefixSpan_matrix_row` records that each matrix row belongs to the prefix span ending at that row. -/
private theorem prefixSpan_matrix_row
    (M : Matrix Rat n m) (j : Fin n) :
    prefixSpan M j.val j.isLt (M.row j) := by
  let last : Fin (j.val + 1) := ⟨j.val, Nat.lt_succ_self j.val⟩
  simpa [prefixRows, Matrix.row] using prefixSpan_row M j.val j.isLt last

private theorem prefixRows_rowSwap_row_mem_prefixSpan
    (b : Matrix Rat n m) (km1 k : Fin n) (i : Nat) (hi : i < n)
    (hkm1k : km1.val < k.val) (hki : k.val ≤ i) (j : Fin (i + 1)) :
    prefixSpan b i hi ((prefixRows (Matrix.rowSwap b km1 k) i hi).row j) := by
  let r : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hi)⟩
  have hkm1_ne_k : km1 ≠ k := by
    intro h
    exact Nat.ne_of_lt hkm1k (congrArg Fin.val h)
  by_cases hjkm1 : r = km1
  · have hrow :
        (prefixRows (Matrix.rowSwap b km1 k) i hi).row j = b.row k := by
      apply Vector.ext
      intro col hcol
      let c : Fin m := ⟨col, hcol⟩
      simp [prefixRows, Matrix.row]
      change (Matrix.rowSwap b km1 k)[r][c] = b[k][c]
      rw [Matrix.getElem_rowSwap]
      simp [hjkm1, hkm1_ne_k]
    rw [hrow]
    exact prefixSpan_mono_le b k.isLt hi hki (prefixSpan_matrix_row b k)
  · by_cases hjk : r = k
    · have hkm1_le_i : km1.val ≤ i := by
        omega
      have hrow :
          (prefixRows (Matrix.rowSwap b km1 k) i hi).row j = b.row km1 := by
        apply Vector.ext
        intro col hcol
        let c : Fin m := ⟨col, hcol⟩
        simp [prefixRows, Matrix.row]
        change (Matrix.rowSwap b km1 k)[r][c] = b[km1][c]
        rw [Matrix.getElem_rowSwap]
        simp [hjk]
      rw [hrow]
      exact prefixSpan_mono_le b km1.isLt hi hkm1_le_i (prefixSpan_matrix_row b km1)
    · have hrle : r.val ≤ i := Nat.le_of_lt_succ j.isLt
      have hrow :
          (prefixRows (Matrix.rowSwap b km1 k) i hi).row j = b.row r := by
        apply Vector.ext
        intro col hcol
        let c : Fin m := ⟨col, hcol⟩
        simp [prefixRows, Matrix.row, r]
        change (Matrix.rowSwap b km1 k)[r][c] = b[r][c]
        rw [Matrix.getElem_rowSwap]
        simp [hjk, hjkm1]
      rw [hrow]
      exact prefixSpan_mono_le b r.isLt hi hrle (prefixSpan_matrix_row b r)

private theorem prefixSpan_rowSwap_adjacent_at_or_after
    (b : Matrix Rat n m) (km1 k : Fin n) (i : Nat) (hi : i < n)
    (hkm1 : km1.val + 1 = k.val) (hki : k.val ≤ i) (v : Vector Rat m) :
    prefixSpan (Matrix.rowSwap b km1 k) i hi v ↔ prefixSpan b i hi v := by
  constructor
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      prefixSpan_rowCombination
        (A := Matrix.rowSwap b km1 k) (B := b) (i := i) (hi := hi) c
        (by
          intro j
          exact prefixRows_rowSwap_row_mem_prefixSpan
            (b := b) (km1 := km1) (k := k) (i := i) (hi := hi)
            (by omega) hki j)
    rwa [hc] at hspan
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      prefixSpan_rowCombination
        (A := b) (B := Matrix.rowSwap b km1 k) (i := i) (hi := hi) c
        (by
          intro j
          have hrowspan :=
            prefixRows_rowSwap_row_mem_prefixSpan
              (b := Matrix.rowSwap b km1 k) (km1 := km1) (k := k)
              (i := i) (hi := hi) (by omega) hki j
          have hswap_swap : Matrix.rowSwap (Matrix.rowSwap b km1 k) km1 k = b := by
            exact Matrix.rowSwap_rowSwap b km1 k
          simpa [hswap_swap] using hrowspan)
    rwa [hc] at hspan

private theorem prefixSpan_strictPrefix_rowCombination
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat i) :
    prefixSpan M i hi
      (Matrix.rowCombination (strictPrefixRows M i (Nat.le_of_lt hi)) c) := by
  cases i with
  | zero =>
      have hcomb :
          Matrix.rowCombination (strictPrefixRows M 0 (Nat.le_of_lt hi)) c = 0 := by
        rw [rowCombination_eq_foldl_rows]
        simp
      simpa [hcomb] using prefixSpan_zero M 0 hi
  | succ k =>
      have hk : k < n := Nat.lt_of_succ_lt hi
      rw [strictPrefixRows_succ_eq_prefixRows (M := M) (i := k) (hi := hi)]
      have hspan :
          prefixSpan M k hk
            (Matrix.rowCombination (prefixRows M k hk) c) := by
        apply prefixSpan_rowCombination
        intro row
        have hself :=
          prefixSpan_matrix_row M (⟨row.val, Nat.lt_trans row.isLt hi⟩ : Fin n)
        have hmono :=
          prefixSpan_mono_le M (Nat.lt_trans row.isLt hi) hk
            (Nat.le_of_lt_succ row.isLt) hself
        have htarget :
            M.row (⟨row.val, Nat.lt_trans row.isLt hi⟩ : Fin n) =
              (prefixRows M k hk).row row := by
          apply Vector.ext
          intro col hcol
          simp [prefixRows, Matrix.row]
        rw [htarget] at hmono
        exact hmono
      exact prefixSpan_mono_succ M k hi hspan

private theorem prefixSpan_strictRowCombination
    (A B : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat i)
    (hrows : ∀ j : Fin i,
      prefixSpan B i hi ((strictPrefixRows A i (Nat.le_of_lt hi)).row j)) :
    prefixSpan B i hi
      (Matrix.rowCombination (strictPrefixRows A i (Nat.le_of_lt hi)) c) := by
  rw [rowCombination_eq_foldl_rows]
  have hfold :
      ∀ xs : List (Fin i), ∀ acc : Vector Rat m,
        prefixSpan B i hi acc →
          prefixSpan B i hi
            (xs.foldl
              (fun acc j => acc + c[j] • (strictPrefixRows A i (Nat.le_of_lt hi)).row j)
              acc) := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons j rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        exact prefixSpan_add B i hi hacc
          (prefixSpan_smul B i hi c[j] (hrows j))
  exact hfold (List.finRange i) 0 (prefixSpan_zero B i hi)

private theorem foldl_projectionCoeff_rowCombination_comm
    (xs : List (Fin k)) (row : Vector Rat m) (basis : Matrix Rat n m)
    (hk : k ≤ n) (idx : Fin m) (acc : Rat) :
    xs.foldl
        (fun acc j =>
          acc +
            (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] *
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩))
        acc =
      xs.foldl
        (fun acc j =>
          acc +
            projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx])
        acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons j rest ih =>
      simp only [List.foldl_cons]
      have hcomm :
          (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] *
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) =
            projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] := by
        grind
      rw [hcomm]
      exact ih (acc := acc +
        projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
          (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx])

private theorem foldl_projectionCombination_getElem
    (xs : List (Fin k)) (row : Vector Rat m) (basis : Matrix Rat n m)
    (hk : k ≤ n) (idx : Fin m) (acc : Vector Rat m) :
    (xs.foldl
        (fun acc j =>
          acc + projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) •
            basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)
        acc)[idx] =
      xs.foldl
        (fun acc j =>
          acc +
            projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx])
        acc[idx] := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons j rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      have hstart :
          (acc +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) •
                basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] =
            acc[idx] +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
                (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] := by
        change
          (acc +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) •
                basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx.val] =
            acc[idx.val] +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
                (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx.val]
        rw [Vector.getElem_add, Vector.getElem_smul]
        rfl
      rw [hstart]

/-- `prefixSumByRow` is an executable row combination of the first `k` rows of
the basis matrix. -/
private theorem rowCombination_strictPrefixRows_projectionCoeffVector
    (row : Vector Rat m) (basis : Matrix Rat n m) (k : Nat) (hk : k ≤ n) :
    Matrix.rowCombination (strictPrefixRows basis k hk)
        (projectionCoeffVector row basis k hk) =
      prefixSumByRow row basis k hk := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change
    (Matrix.mulVec (Matrix.transpose (strictPrefixRows basis k hk))
        (projectionCoeffVector row basis k hk))[idxFin] =
      (prefixSumByRow row basis k hk)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose (strictPrefixRows basis k hk))
          (projectionCoeffVector row basis k hk))[idxFin] =
        (List.finRange k).foldl
          (fun acc j =>
            acc +
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idxFin] *
                projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩))
          0 by
        unfold Matrix.mulVec Matrix.transpose Matrix.col Matrix.row Vector.dotProduct strictPrefixRows projectionCoeffVector
        simp [Matrix.row]]
  rw [show
      (prefixSumByRow row basis k hk)[idxFin] =
        (List.finRange k).foldl
          (fun acc j =>
            acc +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
                (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idxFin])
          0 by
        unfold prefixSumByRow
        simpa [Vector.getElem_zero] using
          foldl_projectionCombination_getElem
            (xs := List.finRange k) (row := row) (basis := basis) (hk := hk)
            (idx := idxFin) (acc := 0)]
  simpa [Matrix.row] using foldl_projectionCoeff_rowCombination_comm
    (xs := List.finRange k) (row := row) (basis := basis) (hk := hk)
    (idx := idxFin) (acc := 0)

/-- The recursive shape of `prefixSumByRow`: pulling off the last index. -/
private theorem prefixSumByRow_succ
    (row : Vector Rat m) (basis : Matrix Rat n m) (k : Nat) (hk : k + 1 ≤ n) :
    prefixSumByRow row basis (k + 1) hk =
      prefixSumByRow row basis k (Nat.le_of_succ_le hk) +
        projectionCoeff row (basis.row ⟨k, Nat.lt_of_succ_le hk⟩) •
          basis.row ⟨k, Nat.lt_of_succ_le hk⟩ := by
  unfold prefixSumByRow
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  rfl

/-- `prefixCombination` over `coeffMatrix b (basisMatrix b)` agrees with
`prefixSumByRow` taking row `b.row ⟨i, hi⟩`. -/
private theorem prefixCombination_eq_prefixSumByRow
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    prefixCombination (coeffMatrix b (basisMatrix b)) (basisMatrix b) i hi =
      prefixSumByRow (b.row ⟨i, hi⟩) (basisMatrix b) i (Nat.le_of_lt hi) := by
  unfold prefixCombination prefixSumByRow
  congr 1
  funext acc j
  show acc + entry (coeffMatrix b (basisMatrix b)) ⟨i, hi⟩
        ⟨j.val, Nat.lt_trans j.isLt hi⟩ • (basisMatrix b).row ⟨j.val, _⟩ =
      acc + projectionCoeff (b.row ⟨i, hi⟩)
        ((basisMatrix b).row ⟨j.val, _⟩) • (basisMatrix b).row ⟨j.val, _⟩
  have hjlt : j.val < i := j.isLt
  have hentry : entry (coeffMatrix b (basisMatrix b)) ⟨i, hi⟩
        ⟨j.val, Nat.lt_trans j.isLt hi⟩ =
      projectionCoeff (b.row ⟨i, hi⟩)
        ((basisMatrix b).row ⟨j.val, Nat.lt_trans j.isLt hi⟩) := by
    simp [coeffMatrix, entry_ofFn, hjlt, Matrix.row]
  rw [hentry]

/-- `prefixSumByRow` with row free equals `projectionCombination` over the
first `i` rows of `basisRows b.toList`. -/
private theorem prefixSumByRow_eq_projectionCombination
    (b : Matrix Rat n m) (row : Vector Rat m) (i : Nat) (hi : i ≤ n) :
    prefixSumByRow row (basisMatrix b) i hi =
      projectionCombination row ((basisRows b.toList).take i) 0 := by
  have hlen : (basisRows b.toList).length = n := by simp [basisRows_length]
  induction i with
  | zero =>
      simp [prefixSumByRow, projectionCombination]
  | succ k ih =>
      have hk_lt : k < n := Nat.lt_of_succ_le hi
      have hkrows : k < (basisRows b.toList).length := by rw [hlen]; exact hk_lt
      rw [prefixSumByRow_succ, ih (Nat.le_of_succ_le hi)]
      have htake : (basisRows b.toList).take (k + 1) =
          (basisRows b.toList).take k ++ [(basisRows b.toList)[k]!] := by
        rw [List.take_succ_eq_append_getElem hkrows]
        congr 1
        simp [List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem hkrows]
      rw [htake, projectionCombination_append, projectionCombination_singleton]
      have hbasisrow : (basisMatrix b).row ⟨k, hk_lt⟩ = (basisRows b.toList)[k]! := by
        rw [basisMatrix_row_eq_basisRows_get!]
      rw [hbasisrow]

/-- The coefficient-matrix prefix term is an executable row combination of the
earlier generated basis rows. -/
private theorem prefixCombination_eq_strictPrefixRowCombination
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    prefixCombination (coeffMatrix b (basisMatrix b)) (basisMatrix b) i hi =
      Matrix.rowCombination (strictPrefixRows (basisMatrix b) i (Nat.le_of_lt hi))
        (projectionCoeffVector (b.row ⟨i, hi⟩) (basisMatrix b) i (Nat.le_of_lt hi)) := by
  rw [prefixCombination_eq_prefixSumByRow]
  exact (rowCombination_strictPrefixRows_projectionCoeffVector
    (row := b.row ⟨i, hi⟩) (basis := basisMatrix b) (k := i)
    (hk := Nat.le_of_lt hi)).symm

/-- Decomposition invariant: each input row equals its reduced basis row plus
the prefix combination of earlier basis rows weighted by `coeffMatrix`. -/
private theorem basisMatrix_reconstruction_invariant
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    b.row ⟨i, hi⟩ =
      (basisMatrix b).row ⟨i, hi⟩ +
        prefixCombination (coeffMatrix b (basisMatrix b)) (basisMatrix b) i hi := by
  have hilen : i < b.toList.length := by simpa using hi
  have htoList_get : b.toList[i]! = b.row ⟨i, hi⟩ := by
    simp [Matrix.row, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hilen, Vector.getElem_toList]
  have hreduce_forward :=
    basisRows_get!_eq_reduceAgainstBasis_forward
      (rows := b.toList) (k := i) hilen
  rw [htoList_get] at hreduce_forward
  rw [hreduce_forward, ← basisMatrix_row_eq_basisRows_get! b i hi]
  congr 1
  rw [prefixCombination_eq_prefixSumByRow,
    prefixSumByRow_eq_projectionCombination]

end GramSchmidt
end Hex
