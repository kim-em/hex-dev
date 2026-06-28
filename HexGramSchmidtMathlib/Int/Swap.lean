/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidtMathlib.Int.Augmented
import all HexGramSchmidtMathlib.Int.Augmented

public section

namespace Hex
namespace GramSchmidt
namespace Int
/-! ### Adjacent-swap pivot Gram-determinant product

Swapping adjacent rows `km1, k` (with `km1 + 1 = k`) of `b` changes only the
leading `k × k` Gram determinant within `0 ≤ t ≤ k + 1`. The new pivot Gram
determinant `gramDet (rowSwap b km1 k) k` satisfies the integer product
identity

    gramDet b' k · gramDet b k = gramDet b (k+1) · gramDet b km1 + B²

where `B = (scaledCoeffs b)[k][km1]`. This is the fraction-free form of the
standard rational adjacent-swap update used by integer LLL. -/

/-- If two integers cast to equal rationals, they are equal. -/
private theorem intCast_rat_injective_int_eq {a b : Int} (h : (a : Rat) = (b : Rat)) :
    a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by
    push_cast
    grind
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega

/-- The rational dot product is additive in its left argument. -/
theorem dot_add_left_rat {m' : Nat} (u v w : Vector Rat m') :
    Vector.dotProduct (u + v) w = Vector.dotProduct u w + Vector.dotProduct v w := by
  rw [dot_comm_rat (u := u + v) (v := w)]
  rw [dot_add_right_rat (u := w) (v := u) (w := v)]
  rw [dot_comm_rat (u := w) (v := u), dot_comm_rat (u := w) (v := v)]

/-- The rational dot product is homogeneous in its left argument: a scalar
factors out. -/
theorem dot_smul_left_rat {m' : Nat} (s : Rat) (u v : Vector Rat m') :
    Vector.dotProduct (s • u) v = s * Vector.dotProduct u v := by
  rw [dot_comm_rat (u := s • u) (v := v)]
  rw [dot_smul_right_rat (s := s) (u := v) (v := u)]
  rw [dot_comm_rat (u := v) (v := u)]

/-- Pythagoras: if `curr ⊥ prev`, then the squared norm of `curr + μ • prev`
splits as `‖curr‖² + μ² · ‖prev‖²`. -/
theorem normSq_add_smul_orthogonal_rat {m' : Nat}
    (curr prev : Vector Rat m') (μ : Rat)
    (horth : Vector.dotProduct curr prev = 0) :
    Vector.normSq (curr + μ • prev) =
      Vector.normSq curr + μ ^ 2 * Vector.normSq prev := by
  show Vector.dotProduct (curr + μ • prev) (curr + μ • prev) =
    Vector.dotProduct curr curr + μ ^ 2 * Vector.dotProduct prev prev
  rw [dot_add_left_rat (u := curr) (v := μ • prev) (w := curr + μ • prev)]
  rw [dot_add_right_rat (u := curr) (v := curr) (w := μ • prev)]
  rw [dot_add_right_rat (u := μ • prev) (v := curr) (w := μ • prev)]
  rw [dot_smul_right_rat (s := μ) (u := curr) (v := prev)]
  rw [dot_smul_left_rat (s := μ) (u := prev) (v := curr)]
  rw [dot_smul_left_rat (s := μ) (u := prev) (v := μ • prev)]
  rw [dot_smul_right_rat (s := μ) (u := prev) (v := prev)]
  have horth_swap : Vector.dotProduct prev curr = 0 := by
    rw [dot_comm_rat]; exact horth
  rw [horth, horth_swap]
  grind

/-- For `j < km1.val`, the Gram-Schmidt basis row is unchanged by the swap
of rows `km1, k`. The norm-square product over indices `< km1.val` therefore
agrees on `b` and `Matrix.rowSwap b km1 k`. -/
theorem gramSchmidtNormProduct_rowSwap_below
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1k : km1.val < k.val) :
    gramSchmidtNormProduct (Matrix.rowSwap b km1 k) km1.val
        (Nat.le_of_lt km1.isLt) =
      gramSchmidtNormProduct b km1.val (Nat.le_of_lt km1.isLt) := by
  unfold gramSchmidtNormProduct
  apply foldl_mul_congr_simple
  intro j _hj
  have hj_lt_km1 : j.val < km1.val := j.isLt
  congr 1
  exact basis_rowSwap_of_before b km1 k
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt km1.isLt)⟩ hkm1k hj_lt_km1

/-- Unconditional version of `gramDet_eq_prod_normSq`: the leading Gram
determinant casts to the rational `gramSchmidtNormProduct` without requiring
linear independence. The `independent` hypothesis in the public theorem is
not actually used by the proof. -/
theorem gramDet_eq_prod_normSq_uncond (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk := by
  rw [gramDet_rat_eq_progressMatrix_zero_det b k hk]
  rw [← progressMatrix_det_invariant b k hk k (Nat.le_refl k)]
  rw [progressMatrix_full_eq_auxMatrix]
  exact auxMatrix_det_eq_prod_normSq b k hk

/-- `gramDet` is independent of the propositional `≤ n` proof, and depends only
on the Nat value `k`. Two `gramDet` calls with equal `Nat` arguments produce
equal values. -/
theorem gramDet_subst_val
    (b : Matrix Int n m) (j₁ j₂ : Nat) (h₁ : j₁ ≤ n) (h₂ : j₂ ≤ n)
    (he : j₁ = j₂) :
    gramDet b j₁ h₁ = gramDet b j₂ h₂ := by
  subst he
  rfl

/-- Same as `gramDet_subst_val` for `gramSchmidtNormProduct`. -/
theorem gramSchmidtNormProduct_subst_val
    (b : Matrix Int n m) (j₁ j₂ : Nat) (h₁ : j₁ ≤ n) (h₂ : j₂ ≤ n)
    (he : j₁ = j₂) :
    gramSchmidtNormProduct b j₁ h₁ = gramSchmidtNormProduct b j₂ h₂ := by
  subst he
  rfl

/-- Integer fraction-free identity for the leading pivot Gram determinant
after swapping adjacent rows `km1, k` with `km1.val + 1 = k.val`:

    gramDet b' k · gramDet b k = gramDet b (k+1) · gramDet b km1 + B²

where `B = (scaledCoeffs b)[k][km1]`. This is the algebraic heart of the
integer LLL adjacent-swap update. -/
theorem gramDet_rowSwap_adjacent_pivot_product
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
    ((gramDet (Matrix.rowSwap b km1 k) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) *
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
        B ^ 2 := by
  intro B
  have hkm1k : km1.val < k.val := by omega
  have hkm1_le_n : km1.val ≤ n := Nat.le_of_lt km1.isLt
  have hk_le_n : k.val ≤ n := Nat.le_of_lt k.isLt
  have hk1_le_n : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
  have hkm1_succ_le : km1.val + 1 ≤ n := Nat.succ_le_of_lt km1.isLt
  -- Local abbreviations on the rational side.
  let μ : Rat := GramSchmidt.entry (coeffs b) k km1
  let prev : Vector Rat m := (basis b).row km1
  let curr : Vector Rat m := (basis b).row k
  let G : Rat := gramSchmidtNormProduct b km1.val hkm1_le_n
  let Nkm1 : Rat := Vector.normSq prev
  let Nk : Rat := Vector.normSq curr
  -- Rational expressions for each Gram determinant we touch.
  have hdkm1_rat : (gramDet b km1.val hkm1_le_n : Rat) = G :=
    gramDet_eq_prod_normSq_uncond b km1.val hkm1_le_n
  -- gramDet b k.val = gramDet b (km1.val + 1) = G * Nkm1.
  have hdk_rat : (gramDet b k.val hk_le_n : Rat) = G * Nkm1 := by
    have h_succ := gramDet_succ_rat b km1.val hkm1_succ_le
    have hgd_eq :
        gramDet b (km1.val + 1) hkm1_succ_le = gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    rw [← hgd_eq, h_succ]
  -- gramDet b (k.val + 1) = G * Nkm1 * Nk.
  have hdkp1_rat : (gramDet b (k.val + 1) hk1_le_n : Rat) = G * Nkm1 * Nk := by
    have h_succ := gramDet_succ_rat b k.val hk1_le_n
    have hgnp_k_eq :
        gramSchmidtNormProduct b k.val hk_le_n =
          gramSchmidtNormProduct b (km1.val + 1) hkm1_succ_le :=
      gramSchmidtNormProduct_subst_val b _ _ _ _ hkm1.symm
    rw [h_succ, hgnp_k_eq,
        gramSchmidtNormProduct_succ b km1.val hkm1_succ_le]
  -- Basis orthogonality between curr and prev.
  have horth : Vector.dotProduct curr prev = 0 :=
    basis_orthogonal b k.val km1.val k.isLt km1.isLt (by omega)
  -- New basis row at km1 of the swapped matrix is `curr + μ • prev`.
  have hbasis_swap :
      (basis (Matrix.rowSwap b km1 k)).row km1 = curr + μ • prev :=
    basis_rowSwap_adjacent_prev b km1 k hkm1
  -- gramDet (rowSwap b km1 k) k.val = G * (Nk + μ^2 * Nkm1).
  have hdprime_rat :
      (gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n : Rat) =
        G * (Nk + μ ^ 2 * Nkm1) := by
    have h_succ :=
      gramDet_succ_rat (Matrix.rowSwap b km1 k) km1.val hkm1_succ_le
    have hgd_eq :
        gramDet (Matrix.rowSwap b km1 k) (km1.val + 1) hkm1_succ_le =
          gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n :=
      gramDet_subst_val (Matrix.rowSwap b km1 k) _ _ _ _ hkm1
    rw [← hgd_eq, h_succ,
        gramSchmidtNormProduct_rowSwap_below b km1 k hkm1k]
    show G * Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row
        ⟨km1.val, km1.isLt⟩) = G * (Nk + μ ^ 2 * Nkm1)
    have hbasis_row :
        (basis (Matrix.rowSwap b km1 k)).row ⟨km1.val, km1.isLt⟩ =
          curr + μ • prev := hbasis_swap
    rw [hbasis_row, normSq_add_smul_orthogonal_rat curr prev μ horth]
  -- Rational expression for B.
  have hB_rat : ((B : Int) : Rat) = G * Nkm1 * μ := by
    show ((GramSchmidt.entry (scaledCoeffs b) k km1 : Int) : Rat) =
        G * Nkm1 * μ
    rw [scaledCoeffs_eq b k.val km1.val k.isLt hkm1k]
    have hgd_eq :
        gramDet b (km1.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hkm1k k.isLt)) =
          gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    show (gramDet b (km1.val + 1) _ : Rat) *
        GramSchmidt.entry (coeffs b) ⟨k.val, k.isLt⟩
          ⟨km1.val, Nat.lt_trans hkm1k k.isLt⟩ = G * Nkm1 * μ
    rw [hgd_eq, hdk_rat]
  -- Promote to Rat and discharge.
  apply intCast_rat_injective_int_eq
  push_cast
  rw [hdprime_rat, hdk_rat, hdkp1_rat, hdkm1_rat, hB_rat]
  grind

/-- All-zero foldl: when every term in the foldl is zero, the result equals
the initial accumulator. -/
private theorem foldl_add_zero_of_all_zero_rat {α : Type}
    (f : α → Rat) (xs : List α) (h : ∀ x ∈ xs, f x = 0) (acc : Rat) :
    xs.foldl (fun acc' x => acc' + f x) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := h x (by simp)
      rw [hx, Rat.add_zero]
      exact ih (fun y hy => h y (by simp [hy])) acc

/-- Foldl isolation: when every term except the `j`-th vanishes, the foldl
over `List.finRange i` collapses to `f ⟨j, hj⟩`. -/
private theorem foldl_finRange_isolate_rat :
    ∀ (i : Nat) (j : Nat) (hj : j < i) (f : Fin i → Rat),
      (∀ q : Fin i, q.val ≠ j → f q = 0) →
      (List.finRange i).foldl (fun acc q => acc + f q) 0 = f ⟨j, hj⟩
  | 0, _, hj, _, _ => absurd hj (Nat.not_lt_zero _)
  | i + 1, j, hj, f, h_zero => by
      rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hj_eq : j = i
      · -- j = i: the `Fin.last i` term contributes `f ⟨j, hj⟩`.
        subst hj_eq
        have hzero_pre : ∀ q : Fin j, f (Fin.castSucc q) = 0 := by
          intro q
          apply h_zero
          have : (Fin.castSucc q).val = q.val := rfl
          rw [this]
          exact Nat.ne_of_lt q.isLt
        have hmem_zero : ∀ q ∈ List.finRange j, f (Fin.castSucc q) = 0 := by
          intro q _
          exact hzero_pre q
        have hfold_zero :
            (List.finRange j).foldl
                (fun (acc : Rat) (q : Fin j) => acc + f (Fin.castSucc q)) 0 = 0 :=
          foldl_add_zero_of_all_zero_rat (fun q => f (Fin.castSucc q))
            (List.finRange j) hmem_zero 0
        rw [hfold_zero, Rat.zero_add]
        rfl
      · -- j < i: recurse on the smaller range.
        have hjlt : j < i := by omega
        have hlast_zero : f (Fin.last i) = 0 := by
          apply h_zero
          have : (Fin.last i).val = i := rfl
          rw [this]
          omega
        rw [hlast_zero, Rat.add_zero]
        have hzero_pre : ∀ q : Fin i, q.val ≠ j → f (Fin.castSucc q) = 0 := by
          intro q hq_ne
          apply h_zero
          have : (Fin.castSucc q).val = q.val := rfl
          rw [this]
          exact hq_ne
        have hih := foldl_finRange_isolate_rat i j hjlt
          (fun q => f (Fin.castSucc q)) hzero_pre
        rw [hih]
        rfl

/-- Dotting the `j`-th Gram-Schmidt basis row with the integer-cast `i`-th
input row picks out the `(i, j)` Gram-Schmidt coefficient weighted by the
squared norm of the basis row. Holds unconditionally: when the basis row is
zero, both sides vanish (orthogonality + the `if`-branch in
`coeffs_lower_projection`). -/
theorem dot_basis_castRow_eq_coeffs_mul_normSq
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    Vector.dotProduct ((basis b).row ⟨j, Nat.lt_trans hj hi⟩)
        (Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i, hi⟩)) =
      GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ *
        Vector.normSq ((basis b).row ⟨j, Nat.lt_trans hj hi⟩) := by
  have hjlt : j < n := Nat.lt_trans hj hi
  -- Expand `castIntRow b i` via `basis_decomposition`.
  have hrow := castIntRow_decomposition b i hi
  show Vector.dotProduct ((basis b).row ⟨j, hjlt⟩) (castIntRow b ⟨i, hi⟩) = _
  rw [hrow]
  rw [dot_add_right_rat]
  -- First term: `dot basis[j] basis[i] = 0` by orthogonality (j ≠ i).
  rw [basis_orthogonal b j i hjlt hi (Nat.ne_of_lt hj)]
  rw [Rat.zero_add]
  -- Second term: linearise the prefixCombination, then isolate the j-th index.
  rw [dot_prefixCombination_right_rat (coeffs := coeffs b) (basisM := basis b)
      (i := i) (hi := hi) (u := (basis b).row ⟨j, hjlt⟩)]
  have h_zero_term : ∀ q : Fin i, q.val ≠ j →
      GramSchmidt.entry (coeffs b) ⟨i, hi⟩
            ⟨q.val, Nat.lt_trans q.isLt hi⟩ *
          Vector.dotProduct ((basis b).row ⟨j, hjlt⟩)
            ((basis b).row ⟨q.val, Nat.lt_trans q.isLt hi⟩) = 0 := by
    intro q hqj
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt hi
    rw [basis_orthogonal b j q.val hjlt hq_lt_n fun h => hqj h.symm]
    grind
  rw [foldl_finRange_isolate_rat i j hj _ h_zero_term]
  -- After isolation: c[i][j] * dot basis[j] basis[j] = c[i][j] * normSq basis[j].
  rfl

/-- Foldl isolation for two indices: when every term except those at `j₁` and `j₂`
vanishes, the foldl over `List.finRange i` collapses to `f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩`. -/
private theorem foldl_finRange_isolate_two_rat :
    ∀ (i : Nat) (j₁ j₂ : Nat) (hj₁ : j₁ < i) (hj₂ : j₂ < i) (_hne : j₁ ≠ j₂)
      (f : Fin i → Rat),
      (∀ q : Fin i, q.val ≠ j₁ → q.val ≠ j₂ → f q = 0) →
      (List.finRange i).foldl (fun acc q => acc + f q) 0 =
        f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
  | 0, _, _, hj₁, _, _, _, _ => absurd hj₁ (Nat.not_lt_zero _)
  | i + 1, j₁, j₂, hj₁, hj₂, hne, f, h_zero => by
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases h1 : j₁ = i
    · -- j₁ = i; then j₂ < i and j₂ ≠ i.
      subst h1
      have hj₂_lt : j₂ < j₁ := by
        have h_le : j₂ ≤ j₁ := Nat.lt_succ_iff.mp hj₂
        exact Nat.lt_of_le_of_ne h_le (fun h => hne h.symm)
      have hzero_pre : ∀ q : Fin j₁, q.val ≠ j₂ → f (Fin.castSucc q) = 0 := by
        intro q hqj₂
        apply h_zero
        · show q.val ≠ j₁
          exact Nat.ne_of_lt q.isLt
        · show q.val ≠ j₂
          exact hqj₂
      have hih := foldl_finRange_isolate_rat j₁ j₂ hj₂_lt
        (fun q => f (Fin.castSucc q)) hzero_pre
      rw [hih]
      have h_cast_j₂ : (Fin.castSucc ⟨j₂, hj₂_lt⟩ : Fin (j₁ + 1)) = ⟨j₂, hj₂⟩ := by
        apply Fin.ext; rfl
      have h_last : (Fin.last j₁ : Fin (j₁ + 1)) = ⟨j₁, hj₁⟩ := by
        apply Fin.ext; rfl
      show f (Fin.castSucc ⟨j₂, hj₂_lt⟩) + f (Fin.last j₁) = f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
      rw [h_cast_j₂, h_last]
      ring
    · by_cases h2 : j₂ = i
      · -- j₂ = i; then j₁ < i.
        subst h2
        have hj₁_lt : j₁ < j₂ := by
          have h_le : j₁ ≤ j₂ := Nat.lt_succ_iff.mp hj₁
          exact Nat.lt_of_le_of_ne h_le h1
        have hzero_pre : ∀ q : Fin j₂, q.val ≠ j₁ → f (Fin.castSucc q) = 0 := by
          intro q hqj₁
          apply h_zero
          · show q.val ≠ j₁
            exact hqj₁
          · show q.val ≠ j₂
            exact Nat.ne_of_lt q.isLt
        have hih := foldl_finRange_isolate_rat j₂ j₁ hj₁_lt
          (fun q => f (Fin.castSucc q)) hzero_pre
        rw [hih]
        have h_cast_j₁ : (Fin.castSucc ⟨j₁, hj₁_lt⟩ : Fin (j₂ + 1)) = ⟨j₁, hj₁⟩ := by
          apply Fin.ext; rfl
        have h_last : (Fin.last j₂ : Fin (j₂ + 1)) = ⟨j₂, hj₂⟩ := by
          apply Fin.ext; rfl
        show f (Fin.castSucc ⟨j₁, hj₁_lt⟩) + f (Fin.last j₂) = f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
        rw [h_cast_j₁, h_last]
      · -- Both j₁ < i, j₂ < i: last term vanishes, recurse.
        have hj₁_lt : j₁ < i := by
          have h_le : j₁ ≤ i := Nat.lt_succ_iff.mp hj₁
          exact Nat.lt_of_le_of_ne h_le h1
        have hj₂_lt : j₂ < i := by
          have h_le : j₂ ≤ i := Nat.lt_succ_iff.mp hj₂
          exact Nat.lt_of_le_of_ne h_le h2
        have hlast_zero : f (Fin.last i) = 0 := by
          apply h_zero
          · show (Fin.last i).val ≠ j₁
            show i ≠ j₁
            exact fun h => h1 h.symm
          · show (Fin.last i).val ≠ j₂
            show i ≠ j₂
            exact fun h => h2 h.symm
        rw [hlast_zero, Rat.add_zero]
        have hzero_pre : ∀ q : Fin i, q.val ≠ j₁ → q.val ≠ j₂ → f (Fin.castSucc q) = 0 := by
          intro q hqj₁ hqj₂
          apply h_zero
          · show q.val ≠ j₁
            exact hqj₁
          · show q.val ≠ j₂
            exact hqj₂
        have hih := foldl_finRange_isolate_two_rat i j₁ j₂ hj₁_lt hj₂_lt hne
          (fun q => f (Fin.castSucc q)) hzero_pre
        rw [hih]
        have h_cast_j₁ : (Fin.castSucc ⟨j₁, hj₁_lt⟩ : Fin (i + 1)) = ⟨j₁, hj₁⟩ := by
          apply Fin.ext; rfl
        have h_cast_j₂ : (Fin.castSucc ⟨j₂, hj₂_lt⟩ : Fin (i + 1)) = ⟨j₂, hj₂⟩ := by
          apply Fin.ext; rfl
        show f (Fin.castSucc ⟨j₁, hj₁_lt⟩) + f (Fin.castSucc ⟨j₂, hj₂_lt⟩) =
          f ⟨j₁, hj₁⟩ + f ⟨j₂, hj₂⟩
        rw [h_cast_j₁, h_cast_j₂]

/-- For an adjacent row swap `b' = rowSwap b km1 k` with `km1.val + 1 = k.val`,
the dot product of the swapped `k`-th basis row with the original `km1`-th basis
row equals the squared norm of the swapped `k`-th basis row. Equivalently,
`dot u_k prev = ||u_k||²`, where `u_k = (basis b').row k` and `prev = (basis b).row km1`.

The proof routes both sides through `dot u_k (cast b.row km1) = dot u_k (cast b'.row k)`
(the cast vectors agree because `b'.row k = b.row km1` from the row swap),
expanding each side via `basis_decomposition`. The prefix combinations vanish on
both sides because `u_k = (basis b').row k` is orthogonal to every `(basis b').row q`
with `q < k`, and the relevant `(basis b).row q` agrees with `(basis b').row q`
for `q < km1`. -/
theorem dot_basis_rowSwap_curr_prev_eq_normSq
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row km1) =
      Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row k) := by
  have hkm1k : km1.val < k.val := by omega
  -- Row equality: (rowSwap b km1 k).row k = b.row km1.
  have hrow_eq : (Matrix.rowSwap b km1 k).row k = b.row km1 := by
    apply Vector.ext
    intro idx hidx
    let c : Fin m := ⟨idx, hidx⟩
    change (Matrix.rowSwap b km1 k)[k][c] = b[km1][c]
    rw [Matrix.rowSwap_getElem]
    simp
  -- prefixCombination of b at km1 vanishes against u_k.
  have hpfx_b_zero :
      Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
          (GramSchmidt.prefixCombination (coeffs b) (basis b) km1.val km1.isLt) = 0 := by
    apply dot_prefixCombination_right_eq_zero
    intro q
    have hq_lt_km1 : q.val < km1.val := q.isLt
    have hq_lt_k : q.val < k.val := by omega
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt km1.isLt
    have hbeq : (basis b).row ⟨q.val, hq_lt_n⟩ =
        (basis (Matrix.rowSwap b km1 k)).row ⟨q.val, hq_lt_n⟩ :=
      (basis_rowSwap_of_before b km1 k ⟨q.val, hq_lt_n⟩ hkm1k hq_lt_km1).symm
    rw [hbeq]
    exact basis_orthogonal (Matrix.rowSwap b km1 k) k.val q.val k.isLt hq_lt_n
      (Nat.ne_of_gt hq_lt_k)
  -- prefixCombination of b' at k vanishes against u_k.
  have hpfx_b'_zero :
      Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
          (GramSchmidt.prefixCombination (coeffs (Matrix.rowSwap b km1 k))
            (basis (Matrix.rowSwap b km1 k)) k.val k.isLt) = 0 := by
    apply dot_prefixCombination_right_eq_zero
    intro q
    have hq_lt_k : q.val < k.val := q.isLt
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt k.isLt
    exact basis_orthogonal (Matrix.rowSwap b km1 k) k.val q.val k.isLt hq_lt_n
      (Nat.ne_of_gt hq_lt_k)
  -- dot u_k (cast b.row km1) = dot u_k (basis b.row km1)
  have hdot_cast_b_km1 :
      Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
          (Vector.map (fun x : Int => (x : Rat)) (b.row km1)) =
      Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row km1) := by
    have hdec := basis_decomposition b km1.val km1.isLt
    show Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
        (Vector.map (fun x : Int => (x : Rat)) (b.row ⟨km1.val, km1.isLt⟩)) = _
    rw [hdec, dot_add_right_rat, hpfx_b_zero, Rat.add_zero]
  -- dot u_k (cast b'.row k) = ||u_k||²
  have hdot_cast_b'_k :
      Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
          (Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row k)) =
      Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row k) := by
    have hdec := basis_decomposition (Matrix.rowSwap b km1 k) k.val k.isLt
    show Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
        (Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row ⟨k.val, k.isLt⟩)) = _
    rw [hdec, dot_add_right_rat, hpfx_b'_zero, Rat.add_zero]
    rfl
  -- cast b.row km1 = cast b'.row k via hrow_eq.
  have hcast_eq :
      Vector.map (fun x : Int => (x : Rat)) ((Matrix.rowSwap b km1 k).row k) =
      Vector.map (fun x : Int => (x : Rat)) (b.row km1) := by
    rw [hrow_eq]
  -- Combine.
  rw [← hdot_cast_b_km1, ← hcast_eq, hdot_cast_b'_k]

/-- For an adjacent row swap `b' = rowSwap b km1 k` with `km1.val + 1 = k.val`,
the dot product of the swapped `k`-th basis row with the integer-cast `i`-th
input row (for `i > k`) decomposes as the dot product of `u_k` with the original
`km1`-th basis row times a linear combination of the original `km1`-th and
`k`-th coefficients of row `i`.

Concretely, with `μ = c[k][km1]`:
  `dot u_k (cast b.row i) = (dot u_k prev) * (c[i][km1] - μ * c[i][k])`

This is the "Cramer-style" dot product expansion that, combined with
`dot_basis_rowSwap_curr_prev_eq_normSq`, lets us extract `c'[i][k]` from the
b'-side Cramer formula `c'[i][k] * ||u_k||² = dot u_k (cast b.row i)`. -/
theorem dot_basis_rowSwap_curr_castRow_eq
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val)
    (i : Fin n) (hki : k.val < i.val) :
    Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
        (Vector.map (fun x : Int => (x : Rat)) (b.row i)) =
      Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row km1) *
        (GramSchmidt.entry (coeffs b) i ⟨km1.val, Nat.lt_trans (Nat.lt_of_succ_le
          (le_of_eq hkm1)) k.isLt⟩ -
         GramSchmidt.entry (coeffs b) k ⟨km1.val, Nat.lt_trans (Nat.lt_of_succ_le
          (le_of_eq hkm1)) k.isLt⟩ *
         GramSchmidt.entry (coeffs b) i k) := by
  have hkm1k : km1.val < k.val := by omega
  have hkm1_lt_i : km1.val < i.val := by omega
  have hkm1_lt_n : km1.val < n := Nat.lt_trans hkm1k k.isLt
  -- The dot product `D = dot u_k prev`.
  set D : Rat := Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row km1) with hD_def
  -- Step A: dot u_k cast b.row i = dot u_k basis b.row i + dot u_k prefixCombination(b, i)
  have hdec_b_i := basis_decomposition b i.val i.isLt
  show Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
      (Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i.val, i.isLt⟩)) = _
  rw [hdec_b_i, dot_add_right_rat]
  -- dot u_k basis b.row i = 0 (basis b.row i = basis b'.row i and orthogonality).
  have hdot_basis_i :
      Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row ⟨i.val, i.isLt⟩) = 0 := by
    have hbasis_eq : (basis b).row ⟨i.val, i.isLt⟩ =
        (basis (Matrix.rowSwap b km1 k)).row ⟨i.val, i.isLt⟩ :=
      (basis_rowSwap_of_after b km1 k ⟨i.val, i.isLt⟩ hkm1 hki).symm
    rw [hbasis_eq]
    exact basis_orthogonal (Matrix.rowSwap b km1 k) k.val i.val k.isLt i.isLt (Nat.ne_of_lt hki)
  rw [hdot_basis_i, Rat.zero_add]
  -- Linearise dot u_k prefixCombination(b, i) into a foldl.
  rw [dot_prefixCombination_right_rat (coeffs := coeffs b) (basisM := basis b)
      (i := i.val) (hi := i.isLt) (u := (basis (Matrix.rowSwap b km1 k)).row k)]
  -- Apply two-isolate at j₁ = km1.val, j₂ = k.val.
  have hkm1_ne_k_val : km1.val ≠ k.val := by omega
  -- Define f
  set f : Fin i.val → Rat := fun q =>
    GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩
        ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩ *
      Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
        ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩) with hf_def
  -- For q ≠ km1, k: f q = 0.
  have h_zero : ∀ q : Fin i.val, q.val ≠ km1.val → q.val ≠ k.val → f q = 0 := by
    intro q hq_km1 hq_k
    have hq_lt_n : q.val < n := Nat.lt_trans q.isLt i.isLt
    -- basis b.row q = basis b'.row q  (either q < km1 or q > k)
    have hbasis_eq_q : (basis b).row ⟨q.val, hq_lt_n⟩ =
        (basis (Matrix.rowSwap b km1 k)).row ⟨q.val, hq_lt_n⟩ := by
      by_cases hcase : q.val < km1.val
      · exact (basis_rowSwap_of_before b km1 k ⟨q.val, hq_lt_n⟩ hkm1k hcase).symm
      · have hge_km1 : km1.val ≤ q.val := Nat.le_of_not_lt hcase
        have h_gt_km1 : km1.val < q.val := Nat.lt_of_le_of_ne hge_km1 (fun h => hq_km1 h.symm)
        have h_gt_k : k.val < q.val := by omega
        exact (basis_rowSwap_of_after b km1 k ⟨q.val, hq_lt_n⟩ hkm1 h_gt_k).symm
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ _ *
        Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
          ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩) = 0
    rw [hbasis_eq_q]
    rw [basis_orthogonal (Matrix.rowSwap b km1 k) k.val q.val k.isLt hq_lt_n
      (fun h => hq_k h.symm)]
    grind
  have hfoldl_eq :
      (List.finRange i.val).foldl (fun (acc : Rat) (q : Fin i.val) => acc + f q) 0 =
      f ⟨km1.val, hkm1_lt_i⟩ + f ⟨k.val, hki⟩ :=
    foldl_finRange_isolate_two_rat i.val km1.val k.val hkm1_lt_i hki hkm1_ne_k_val f h_zero
  -- The foldl on the goal matches our `f`.
  show (List.finRange i.val).foldl
      (fun (acc : Rat) (q : Fin i.val) =>
        acc + GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩
              ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩ *
            Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
              ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩)) 0 = _
  rw [show (fun (acc : Rat) (q : Fin i.val) =>
        acc + GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩
              ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩ *
            Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
              ((basis b).row ⟨q.val, Nat.lt_trans q.isLt i.isLt⟩)) =
       (fun (acc : Rat) (q : Fin i.val) => acc + f q) from rfl]
  rw [hfoldl_eq]
  -- Compute f at km1 and k.
  -- f ⟨km1.val, _⟩ = c[i][km1] * dot u_k (basis b.row km1) = c[i][km1] * D
  -- f ⟨k.val, _⟩ = c[i][k] * dot u_k (basis b.row k) = c[i][k] * dot u_k curr
  -- Use orthogonality: u_k ⊥ basis b'.row km1 = curr + μ * prev.
  --   ⟹ dot u_k curr + μ * D = 0 ⟹ dot u_k curr = -μ * D.
  set μ : Rat := GramSchmidt.entry (coeffs b) k km1 with hμ_def
  have hbasis_swap :
      (basis (Matrix.rowSwap b km1 k)).row km1 = (basis b).row k + μ • (basis b).row km1 :=
    basis_rowSwap_adjacent_prev b km1 k hkm1
  have hdot_swap_zero :
      Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
        ((basis (Matrix.rowSwap b km1 k)).row km1) = 0 :=
    basis_orthogonal (Matrix.rowSwap b km1 k) k.val km1.val k.isLt km1.isLt
      (fun h => Nat.lt_irrefl km1.val (h ▸ hkm1k))
  -- Expand the orthogonality via the basis swap.
  have hdot_curr :
      Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k) ((basis b).row k) = -μ * D := by
    have h := hdot_swap_zero
    rw [hbasis_swap] at h
    rw [dot_add_right_rat, dot_smul_right_rat] at h
    -- h : dot u_k curr + μ * (dot u_k prev) = 0
    -- i.e., dot u_k curr + μ * D = 0
    -- ⟹ dot u_k curr = -μ * D
    have hD_eq : Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
        ((basis b).row km1) = D := rfl
    rw [hD_eq] at h
    linarith
  -- Now evaluate f at km1 and k.
  show f ⟨km1.val, hkm1_lt_i⟩ + f ⟨k.val, hki⟩ = D * _
  have hf_km1 : f ⟨km1.val, hkm1_lt_i⟩ =
      GramSchmidt.entry (coeffs b) i ⟨km1.val, hkm1_lt_n⟩ * D := by
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ ⟨km1.val, _⟩ *
        Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
          ((basis b).row ⟨km1.val, _⟩) = _
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ ⟨km1.val, hkm1_lt_n⟩ *
        Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
          ((basis b).row ⟨km1.val, hkm1_lt_n⟩) =
        GramSchmidt.entry (coeffs b) i ⟨km1.val, hkm1_lt_n⟩ * D
    have hi_eq : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
    have hkm1_eq : (⟨km1.val, hkm1_lt_n⟩ : Fin n) = km1 := Fin.ext rfl
    rw [hi_eq, hkm1_eq]
  have hf_k : f ⟨k.val, hki⟩ =
      GramSchmidt.entry (coeffs b) i k * (-μ * D) := by
    show GramSchmidt.entry (coeffs b) ⟨i.val, i.isLt⟩ ⟨k.val, _⟩ *
        Vector.dotProduct ((basis (Matrix.rowSwap b km1 k)).row k)
          ((basis b).row ⟨k.val, _⟩) = _
    have hi_eq : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
    have hk_eq : (⟨k.val, Nat.lt_trans hki i.isLt⟩ : Fin n) = k := Fin.ext rfl
    rw [hi_eq, hk_eq]
    rw [hdot_curr]
  rw [hf_km1, hf_k]
  ring

/-- Below the diagonal, the executable integral scaled coefficient is exactly
the Cramer determinant encoded by `scaledCoeffMatrix`. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_det
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  rw [scaledCoeffs_eq_scaledCoeffMatrix_bareiss]
  exact
    (HexMatrixMathlib.bareiss_eq_mathlib_det
        (GramSchmidt.scaledCoeffMatrix b i j hji)).trans
      (HexMatrixMathlib.det_eq (GramSchmidt.scaledCoeffMatrix b i j hji)).symm


/-- Conditional form of the leading Gram determinant identity. The remaining
unconditional fact is exactly the nonnegativity of leading Gram determinants:
once `0 ≤ det` is available, the public `Nat`-valued `gramDet` casts back to
the signed determinant. -/
theorem leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n)
    (hdet : 0 ≤ Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht)) :
    Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) =
      Int.ofNat (gramDet b t ht) := by
  rw [gramDet, HexMatrixMathlib.bareiss_eq_mathlib_det, ← HexMatrixMathlib.det_eq]
  exact (Int.toNat_of_nonneg hdet).symm

/-- The public `Nat` Gram determinant casts back to the signed determinant of
the leading integer Gram matrix. -/
theorem leadingGramMatrixInt_det_eq_gramDet_int
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n) :
    Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) =
      Int.ofNat (gramDet b t ht) :=
  leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg b t ht
    (leadingGramMatrixInt_det_nonneg b t ht)

/-- Mathlib-side unconditional diagonal synchronization for the public
scaled-coefficient matrix. The Mathlib-free core exposes the Nat-level version
and the conditional Int lift; the required nonnegativity of the Gram/Bareiss
diagonal slot is supplied here. -/
theorem scaledCoeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi)) := by
  let hk : i + 1 ≤ n := Nat.succ_le_of_lt hi
  rcases scaledCoeffs_diag_eq_zero_or_eq_leadingPrefix_bareiss b (StepWitness.ofGram b)
      i hi with hzero | hbareiss
  · have hnat := scaledCoeffs_diag_toNat (b := b) (StepWitness.ofGram b) i hi
    rw [hzero] at hnat
    simp at hnat
    rw [hzero, ← hnat]
    simp
  · apply scaledCoeffs_diag_of_nonneg b (StepWitness.ofGram b)
    rw [hbareiss]
    have hbareiss_eq :
        Matrix.bareiss
            (Matrix.leadingPrefix (Matrix.gramMatrix b) (i + 1) hk) =
          Matrix.det (GramSchmidt.leadingGramMatrixInt b (i + 1) hk) := by
      rw [← GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram]
      exact HexMatrixMathlib.bareiss_eq_det
        (GramSchmidt.leadingGramMatrixInt b (i + 1) hk)
    rw [hbareiss_eq]
    exact leadingGramMatrixInt_det_nonneg b (i + 1) hk

/-- Stage-B rational closed form for the diagonal of `scaledCoeffs`,
packaged with a no-singular hypothesis for the σ-chain singular-cascade
consumer.

The hypothesis is unused: `scaledCoeffs_diag` already gives the
unconditional integer identification with `gramDet`, and the singular tail
slots are exactly the zero values the public `gramDet` returns once a
leading Gram prefix is singular. -/
theorem scaledCoeffs_diag_eq_gramDet_of_no_singular
    (b : Matrix Int n m) (i : Fin n)
    (_h_nonsing :
      (Matrix.noPivotLoop i.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    ((GramSchmidt.entry (scaledCoeffs b) i i : Int) : Rat) =
      ((gramDet b (i + 1) (Nat.lt_iff_add_one_le.mp i.isLt) : Int) : Rat) := by
  rw [scaledCoeffs_diag b i.val i.isLt]
  push_cast
  rfl

/-- The leading executable Gram determinants of a square upper-triangular
integer matrix with strictly positive diagonal are positive.

This theorem lives in `HexGramSchmidtMathlib`: its proof identifies the
executable `gramDet` with the Leibniz determinant of the leading Gram matrix
via the composition of `HexMatrixMathlib.bareiss_eq_mathlib_det` and
`HexMatrixMathlib.det_eq.symm`. -/
theorem gramDet_pos_of_upperTriangular_pos_diag
    {n : Nat} (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val -> M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i])
    (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet M k hk := by
  cases k with
  | zero =>
      omega
  | succ r =>
      have hrn : r < n := Nat.lt_of_succ_le hk
      have hlead :
          Matrix.gramMatrix (Matrix.leadingRows M (r + 1) hk) =
            Matrix.leadingPrefix (Matrix.gramMatrix M) (r + 1) hk := by
        apply Vector.ext
        intro i hi
        apply Vector.ext
        intro j hj
        let iFin : Fin (r + 1) := ⟨i, hi⟩
        let jFin : Fin (r + 1) := ⟨j, hj⟩
        let ii : Fin n := ⟨i, Nat.lt_of_lt_of_le hi hk⟩
        let jj : Fin n := ⟨j, Nat.lt_of_lt_of_le hj hk⟩
        have hrow_i :
            Matrix.row (Matrix.leadingRows M (r + 1) hk) iFin =
              Matrix.row M ii := by
          apply Vector.ext
          intro c hc
          simp [Matrix.row, Matrix.leadingRows, Matrix.ofFn, iFin, ii]
        have hrow_j :
            Matrix.row (Matrix.leadingRows M (r + 1) hk) jFin =
              Matrix.row M jj := by
          apply Vector.ext
          intro c hc
          simp [Matrix.row, Matrix.leadingRows, Matrix.ofFn, jFin, jj]
        have hdot :
            Vector.dotProduct (Matrix.row (Matrix.leadingRows M (r + 1) hk) iFin)
                (Matrix.row (Matrix.leadingRows M (r + 1) hk) jFin) =
              Vector.dotProduct (Matrix.row M ii) (Matrix.row M jj) := by
          rw [hrow_i, hrow_j]
        simpa [Matrix.gramMatrix, Matrix.leadingPrefix, Matrix.ofFn, iFin, jFin, ii, jj]
          using hdot
      have hdet_pos :
          0 < Matrix.det (GramSchmidt.leadingGramMatrixInt M (r + 1) hk) := by
        have hpos :=
          Matrix.det_gramMatrix_leadingRows_pos_of_upperTriangular_pos_diag M hzero hdiag
            (r + 1) hk
        rwa [hlead, ← GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram] at hpos
      have hdet_nat :
          Matrix.det (GramSchmidt.leadingGramMatrixInt M (r + 1) hk) =
            Int.ofNat (gramDet M (r + 1) hk) :=
        leadingGramMatrixInt_det_eq_gramDet_int M (r + 1) hk
      have hnat_int : 0 < Int.ofNat (gramDet M (r + 1) hk) := by
        simpa [hdet_nat] using hdet_pos
      exact Int.ofNat_lt.mp hnat_int


end Int
end GramSchmidt
end Hex
