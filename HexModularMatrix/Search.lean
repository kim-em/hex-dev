/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Decomp
public import HexDeterminant.Adjugate
import all HexModularMatrix.Decomp

public section

namespace Hex.Matrix.Dixon

variable {p : Nat} [ZMod64.Bounds p]

/-- The completed prefix consists of identity columns. -/
def Canonical (E : Matrix (ZMod64 p) n n) (k : Nat) : Prop :=
  ∀ j : Fin n, j.val < k → ∀ i : Fin n, E[i][j] = if i = j then 1 else 0

theorem pivot_spec {E : Matrix (ZMod64 p) n n} {j i : Fin n} {b : ZMod64 p}
    (h : pivot? E j = some (i, b)) : j ≤ i ∧ E[(i, j)] * b = 1 := by
  unfold pivot? at h
  rw [Fin.foldl_eq_finRange_foldl] at h
  have go (xs : List (Fin n)) (s : Option (Fin n × ZMod64 p))
      (hs : ∀ i b, s = some (i, b) → j ≤ i ∧ E[(i, j)] * b = 1) :
      ∀ i b, xs.foldl (pivotStep E j) s = some (i, b) →
        j ≤ i ∧ E[(i, j)] * b = 1 := by
    induction xs generalizing s with
    | nil => exact hs
    | cons a xs ih =>
      apply ih
      intro i b h
      cases s with
      | some v => exact hs i b h
      | none =>
        dsimp only [pivotStep] at h
        split at h <;> try contradiction
        rename_i hja
        obtain ⟨u, hu, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        exact ⟨hja, ZMod64.inv?_eq_some hu⟩
  exact go (List.finRange n) none (by simp) i b (by simpa only using h)

theorem pivot_none {E : Matrix (ZMod64 p) n n} {j : Fin n}
    (h : pivot? E j = none) (i : Fin n) (hji : j ≤ i) : ZMod64.inv? E[(i, j)] = none := by
  unfold pivot? at h
  rw [Fin.foldl_eq_finRange_foldl] at h
  have go (xs : List (Fin n)) (s : Option (Fin n × ZMod64 p)) :
      xs.foldl (pivotStep E j) s = none →
      s = none ∧ ∀ i ∈ xs, j ≤ i → ZMod64.inv? E[(i, j)] = none := by
    induction xs generalizing s with
    | nil => simp
    | cons a xs ih =>
      intro h
      obtain ⟨ha, hs⟩ := ih _ h
      simp only [pivotStep] at ha
      cases s with
      | some v => contradiction
      | none =>
        refine ⟨rfl, ?_⟩
        intro i hi hji
        rcases List.mem_cons.mp hi with rfl | hi
        · simpa [hji] using ha
        · exact hs i hi hji
  exact (go (List.finRange n) none (by simpa only using h)).2 i (List.mem_finRange i) hji

/-- With a completed prefix, a missing pivot forces the determinant to vanish. -/
theorem no_pivot_det {E : Matrix (ZMod64 p) n n} {j : Fin n}
    (hc : Canonical E j.val) (hz : ∀ i : Fin n, j ≤ i → E[i][j] = 0) : det E = 0 := by
  let coeff (s : Fin n) := if s.val < j.val then E[s][j] else 0
  have hcol (r : Fin n) : (List.finRange n).foldl
      (fun acc s => acc + coeff s * E[r][s]) 0 = E[r][j] := by
    have hterm (s : Fin n) : coeff s * E[r][s] = if s = r then coeff s else 0 := by
      by_cases hs : s.val < j.val
      · dsimp only [coeff]
        rw [ite_eq_left hs, hc s hs]
        by_cases hrs : r = s
        · subst s; simp only [↓reduceIte]; grind only
        · simp only [hrs, Ne.symm hrs, ↓reduceIte]; grind only
      · dsimp only [coeff]
        rw [ite_eq_right hs]
        by_cases hsr : s = r
        · subst s; simp only [↓reduceIte]; grind only
        · simp only [hsr, ↓reduceIte]; grind only
    simp only [hterm]
    rw [List.foldl_add_single (List.finRange n) 0 r coeff (List.mem_finRange r) (List.nodup_finRange n)]
    by_cases hr : r.val < j.val
    · simp [coeff, hr]
    · rw [hz r (by omega)]
      simp [coeff, hr]
  have hE : E = E.setCol j (fun r => (List.finRange n).foldl
      (fun acc s => acc + coeff s * E[r][s]) 0) := by
    simp only [hcol, setCol_self]
  rw [hE, det_setCol_sum_list]
  apply List.foldl_add_eq_self
  intro s _
  by_cases hs : s = j
  · subst s; simp only [coeff, Nat.lt_irrefl, ↓reduceIte]; grind only
  · rw [det_setCol_existing_col_eq_zero E j s hs]
    grind only

theorem pivot_exists (hp : Hex.Nat.Prime p) {E : Matrix (ZMod64 p) n n} {j : Fin n}
    (hc : Canonical E j.val) (hd : det E ≠ 0) : ∃ i b, pivot? E j = some (i, b) := by
  cases h : pivot? E j with
  | some v => exact ⟨v.1, v.2, rfl⟩
  | none =>
    apply False.elim
    apply hd
    apply no_pivot_det hc
    intro i hji
    by_cases hi : E[(i, j)] = 0
    · simpa only [getElem_pair_eq_nested] using hi
    · have hnone := pivot_none h i hji
      have hi' := ZMod64.mul_inv_eq_one_of_prime hp hi
      unfold ZMod64.inv? at hnone
      dsimp only [pivotStep] at hnone
      split at hnone
      · contradiction
      · contradiction

variable {A : Matrix (ZMod64 p) n n}

theorem Canonical.swap {S : Reduction A} {j i : Fin n}
    (hc : Canonical S.echelon j.val) (hji : j ≤ i) :
    Canonical (S.swap j i).echelon j.val := by
  intro c hc' r
  change (S.echelon.rowSwap j i)[r][c] = _
  rw [getElem_rowSwap, hc c hc' j, hc c hc' i, hc c hc' r]
  have hjc : j ≠ c := by intro h; subst c; omega
  have hic : i ≠ c := by intro h; subst c; omega
  by_cases hrj : r = j <;> by_cases hri : r = i <;> simp_all

theorem Canonical.scale {S : Reduction A} {j : Fin n} {a b : ZMod64 p}
    (hc : Canonical S.echelon j.val) (hab : a * b = 1) :
    Canonical (S.scale j a b hab).echelon j.val := by
  intro c hc' r
  change (S.echelon.rowScale j b)[r][c] = _
  rw [getElem_rowScale, hc c hc' j, hc c hc' r]
  have hjc : j ≠ c := by intro h; subst c; omega
  by_cases hrj : r = j <;> simp_all

theorem Canonical.clearRow {S : Reduction A} {j : Fin n}
    (hc : Canonical S.echelon j.val) (i : Fin n) :
    Canonical (S.clearRow j i).echelon j.val := by
  unfold Reduction.clearRow
  split
  · exact hc
  · intro c hc' r
    change (S.echelon.rowAdd j i (-S.echelon[(i, j)]))[r][c] = _
    rw [getElem_rowAdd, hc c hc' j, hc c hc' i, hc c hc' r]
    have hjc : j ≠ c := by intro h; subst c; omega
    by_cases hri : r = i <;> simp_all

theorem clearRow_pivot (S : Reduction A) (j i : Fin n) :
    (S.clearRow j i).echelon[j][j] = S.echelon[j][j] := by
  unfold Reduction.clearRow
  split
  · rfl
  · rename_i h
    change (S.echelon.rowAdd j i _)[j][j] = _
    rw [getElem_rowAdd, ite_eq_right h]

theorem clearRows_column (xs : List (Fin n)) (S : Reduction A) (j : Fin n)
    (hpivot : S.echelon[j][j] = 1) (i : Fin n) :
    (xs.foldl (Reduction.clearRow j) S).echelon[i][j] =
      if i ∈ xs ∧ i ≠ j then 0 else S.echelon[i][j] := by
  induction xs generalizing S with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons, ih _ (by rw [clearRow_pivot]; exact hpivot)]
    by_cases hij : i = j
    · subst i
      simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte]
      exact clearRow_pivot S j a
    · by_cases hi : i ∈ xs
      · simp [hi, hij]
      · simp only [ne_eq, hi, hij, not_false_eq_true, and_true, ↓reduceIte,
          List.mem_cons, or_false]
        unfold Reduction.clearRow
        split
        · rename_i hja
          subst a
          simp [hij]
        · change (S.echelon.rowAdd j a _)[i][j] = _
          rw [getElem_rowAdd]
          by_cases hia : i = a
          · subst a
            simp only [↓reduceIte, getElem_pair_eq_nested, hpivot]
            grind only
          · simp [hia]

theorem clearRows_canonical (xs : List (Fin n)) (S : Reduction A) (j : Fin n)
    (hc : Canonical S.echelon j.val) :
    Canonical (xs.foldl (Reduction.clearRow j) S).echelon j.val := by
  induction xs generalizing S with
  | nil => exact hc
  | cons a xs ih => exact ih _ (hc.clearRow a)


theorem step_complete (hp : Hex.Nat.Prime p) (S : Reduction A) (j : Fin n)
    (hc : Canonical S.echelon j.val) (hd : det A ≠ 0) :
    ∃ T, S.step j = some T ∧ Canonical T.echelon (j.val + 1) := by
  have he : det S.echelon ≠ 0 := by
    intro hz
    apply hd
    rw [S.det_eq, hz]
    simp
  obtain ⟨i, b, hfound⟩ := pivot_exists hp hc he
  obtain ⟨hji, hab⟩ := pivot_spec hfound
  have hpivot : (S.swap j i).echelon[(j, j)] = S.echelon[(i, j)] := by
    simp only [Reduction.swap, getElem_pair_eq_nested, getElem_rowSwap]
    by_cases h : j = i <;> simp_all
  have hinv : (S.swap j i).echelon[(j, j)] * b = 1 := by rw [hpivot]; exact hab
  let U := (S.swap j i).scale j _ b hinv
  have hu : Canonical U.echelon j.val := (hc.swap hji).scale hinv
  have hup : U.echelon[j][j] = 1 := by
    change ((S.swap j i).echelon.rowScale j b)[j][j] = 1
    rw [getElem_rowScale, ite_eq_left rfl]
    rw [getElem_pair_eq_nested] at hinv
    grind only
  refine ⟨Fin.foldl n (Reduction.clearRow j) U, ?_, ?_⟩
  · unfold Reduction.step
    simp only [hfound, Option.bind_eq_bind, Option.bind_some]
    rw [dite_eq_left hinv]
    rfl
  · rw [Fin.foldl_eq_finRange_foldl]
    intro c hc' r
    by_cases hcj : c = j
    · subst c
      rw [clearRows_column _ U j hup r]
      by_cases hrj : r = j
      · subst r; simpa only [ne_eq, not_true_eq_false, and_false, ↓reduceIte] using hup
      · simp [hrj, List.mem_finRange]
    · exact clearRows_canonical _ U j hu c (by
        have hne : c.val ≠ j.val := fun h => hcj (Fin.ext h)
        omega) r


theorem reduceFrom_complete (hp : Hex.Nat.Prime p) (S : Reduction A) (k : Nat)
    (hc : Canonical S.echelon k) (hd : det A ≠ 0) :
    ∃ T, S.reduceFrom k = some T ∧ T.echelon = Matrix.identity n := by
  rw [Reduction.reduceFrom]
  split
  · rename_i hk
    obtain ⟨T, ht, hc'⟩ := step_complete hp S ⟨k, hk⟩ hc hd
    obtain ⟨U, hu, hU⟩ := reduceFrom_complete hp T (k + 1) hc' hd
    refine ⟨U, ?_, hU⟩
    simp only [ht, Option.bind_eq_bind, Option.bind_some, hu]
  · rename_i hk
    refine ⟨S, rfl, ?_⟩
    apply ext_getElem
    intro i j
    rw [hc j (by omega) i, getElem_identity]
termination_by n - k

theorem reduce_complete (hp : Hex.Nat.Prime p) (A : Matrix (ZMod64 p) n n)
    (hd : det A ≠ 0) : ∃ S, reduce? A = some S ∧ S.echelon = Matrix.identity n :=
  reduceFrom_complete hp (.initial A) 0 (by intro j hj; omega) hd

end Hex.Matrix.Dixon

namespace Hex.Matrix

/-- Prime-modulus elimination succeeds whenever the determinant residue is nonzero. -/
theorem decompAt?_isSome {p : Nat} [ZMod64.Bounds p] (hp : Hex.Nat.Prime p)
    (A : Matrix Int n n) (hd : ZMod64.intCast p (det A) ≠ 0) :
    (decompAt? A p hp.one_lt).isSome := by
  have hmap : det (A.mapEntries (ZMod64.intCast p)) = ZMod64.intCast p (det A) :=
    det_mapEntries A (ZMod64.intCast p) (Lean.Grind.Ring.intCast_zero)
      (Lean.Grind.Ring.intCast_one) (Lean.Grind.Ring.intCast_add) (Lean.Grind.Ring.intCast_mul)
  obtain ⟨S, hs, hI⟩ := Dixon.reduce_complete hp (A.mapEntries (ZMod64.intCast p)) (by
    rw [hmap]; exact hd)
  have hf : S.factor ≠ 0 := by
    intro hz
    apply hd
    rw [← hmap, S.det_eq, hz]
    simp
  have hsym : Modular.symMod (S.factor.toNat : Int) p ≠ 0 := by
    intro hz
    have h := Modular.symMod_emod (a := (S.factor.toNat : Int)) (m := p) hp.pos
    rw [hz, Int.zero_emod, Int.emod_eq_of_lt (by omega)
      (by exact_mod_cast S.factor.toNat_lt)] at h
    apply hf
    apply ZMod64.ext_toNat
    change S.factor.toNat = 0
    omega
  have hb : (decompFrom? A p hp.one_lt (Dixon.reduce? (A.mapEntries (ZMod64.intCast p)))).isSome := by
    unfold decompFrom?
    simp only [hs, Option.bind_eq_bind, Option.bind_some]
    rw [dite_eq_left hI, dite_eq_left hsym]
    rfl
  unfold decompAt?
  split
  · rfl
  · exact hb

namespace Dixon

/-- The product of distinct supply primes divides any common multiple. -/
theorem primes_product_dvd (qs : List ZMod64.Prime) (d : Nat)
    (hs : qs.Pairwise (fun a b => b.m < a.m)) (hd : ∀ q ∈ qs, q.m ∣ d) :
    (qs.map (·.m)).prod ∣ d := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨hq, hs⟩ := List.pairwise_cons.mp hs
    have hcop : Nat.Coprime q.m (qs.map (·.m)).prod := by
      have go (xs : List ZMod64.Prime) (hx : ∀ r ∈ xs, r.m < q.m) :
          Nat.Coprime q.m (xs.map (·.m)).prod := by
        induction xs with
        | nil => simp
        | cons r xs ih =>
          simp only [List.map_cons, List.prod_cons]
          apply Nat.Coprime.mul_right
          · exact q.prime.coprime_of_not_dvd (by
              intro hh
              have := Nat.le_of_dvd r.prime.pos hh
              have := hx r (by simp)
              omega)
          · exact ih (by intro a ha; exact hx a (by simp [ha]))
      exact go qs hq
    exact hcop.mul_dvd_of_dvd_of_dvd (hd q (by simp))
      (ih hs (by intro a ha; exact hd a (by simp [ha])))

theorem primes_product_bound (qs : List ZMod64.Prime)
    (hb : ∀ q ∈ qs, 2 ^ 30 < q.m) :
    2 ^ (30 * qs.length) ≤ (qs.map (·.m)).prod := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.pow_add,
      List.map_cons, List.prod_cons]
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul (Nat.le_of_lt (hb q (by simp)))
      (ih (by intro a ha; exact hb a (by simp [ha])))

end Dixon

/-- A bounded prime search finds a decomposition of a nonsingular matrix. -/
theorem decomp?_isSome [LawfulDetBound] {A : Matrix Int n n} {fuel : Nat}
    (hA : det A ≠ 0) (hfuel : (hadamardBound A).log2 / 30 < fuel)
    (hsupply : ∀ q ∈ ZMod64.primesBelow (2 ^ 31 - 1) fuel, 2 ^ 30 < q.m) :
    (decomp? A fuel).isSome := by
  cases h : decomp? A fuel with
  | some D => rfl
  | none =>
    have hcount : (ZMod64.primesBelow (2 ^ 31 - 1) fuel).size = fuel := by
      rcases ZMod64.primesBelow_count (start := 2 ^ 31 - 1) (by decide) fuel with he | ⟨q, hq, he⟩
      · exact he
      · have := hsupply q hq; omega
    have hdiv (q : ZMod64.Prime) (hq : q ∈ ZMod64.primesBelow (2 ^ 31 - 1) fuel) :
        q.m ∣ (det A).natAbs := by
      letI := q.bounds
      have hz : ZMod64.intCast q.m (det A) = 0 := by
        by_cases hz : ZMod64.intCast q.m (det A) = 0
        · exact hz
        · have hi := decompAt?_isSome q.prime A hz
          rw [decomp?_none h q hq] at hi
          contradiction
      have he := congrArg (fun x : ZMod64 q.m => (x.toNat : Int)) hz
      rw [ZMod64.toNat_intCast] at he
      have hd : (q.m : Int) ∣ det A := Int.dvd_of_emod_eq_zero (by exact he)
      simpa using Int.natAbs_dvd_natAbs.mpr hd
    have hd := Dixon.primes_product_dvd
      (ZMod64.primesBelow (2 ^ 31 - 1) fuel).toList (det A).natAbs
      (ZMod64.primesBelow_sorted _ _) (by intro q hq; exact hdiv q (by simpa using hq))
    have hp := Dixon.primes_product_bound (ZMod64.primesBelow (2 ^ 31 - 1) fuel).toList
      (by intro q hq; exact hsupply q (by simpa using hq))
    simp only [Array.length_toList, hcount] at hp
    have hpos : 0 < (det A).natAbs := Int.natAbs_pos.mpr hA
    have hle := Nat.le_trans hp (Nat.le_of_dvd hpos hd)
    have hb := LawfulDetBound.natAbs_det_le A
    have hsmall := Nat.lt_log2_self (n := hadamardBound A)
    have hpower : 2 ^ ((hadamardBound A).log2 + 1) ≤ 2 ^ (30 * fuel) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

end Hex.Matrix
