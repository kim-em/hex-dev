/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLLMathlib.Interval
public import HexLLL.Basic
public import HexGramSchmidtMathlib.Int
public import HexRowReduceMathlib.RankSpanNullspace
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

public section

/-!
Soundness of the executable reducedness checkers: acceptance of the exact
`lllReducedInt`, the dispatched `lllReducedCheck`, and the bundled
`certCheck` entails the rational `Hex.isLLLReduced` predicate, independence,
and the same-lattice property. The interval branch consumes
`lllReducedInterval_sound`.
-/

namespace HexLLLMathlib

/-! ### Soundness of the integer reducedness checker

`Hex.lllReducedInt b δ η` accepts iff three integer-only inequalities hold over
`Hex.GramSchmidt.Int.data b`. This section bridges those integer inequalities
to the rational predicate `Hex.isLLLReduced b δ η` and to `b.independent`, the
last theorem (`Hex.lllReducedInt_sound`) being the D2 deliverable used by the
combined `certCheck_sound` of `hex-lll` §"Certified external dispatch". -/

/-- Independence from the executable checker's `d`-positivity pass.

The integer `d`-vector `(GramSchmidt.Int.data b).d = gramDetVec b` agrees with
`gramDet b` slot-by-slot (`gramDetVec_eq_gramDet` with `StepWitness.ofGram`),
so each positive `d[k+1]` is exactly the `gramDet`-positivity defining
`b.independent`. -/
private theorem independent_of_dPos
    {n m : Nat} (b : Hex.Matrix Int n m)
    (hdPos : ∀ k : Fin n,
      0 < (Hex.GramSchmidt.Int.data b).d.get
        ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) :
    Hex.Matrix.independent b := by
  intro k
  have h := hdPos k
  have heq :
      (Hex.GramSchmidt.Int.data b).d.get ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ =
        Hex.GramSchmidt.Int.gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) := by
    have hbridge :=
      Hex.GramSchmidt.Int.gramDetVec_eq_gramDet b
        (Hex.GramSchmidt.Int.StepWitness.ofGram b)
        (k.val + 1) (Nat.succ_le_of_lt k.isLt)
    simpa [Hex.GramSchmidt.Int.gramDetVec] using hbridge
  show 0 < Hex.GramSchmidt.Int.gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt)
  rw [← heq]
  exact h

/-- Size-reduced contribution: from one integer `|ν| · η.den ≤ η.num · d[j+1]`
inequality plus `0 < d[j+1]`, derive `μ² ≤ η²` at the same `(i, j)` slot.

The bridge is `scaledCoeffs_eq`, which equates `(ν[i][j] : Rat)` with
`d[j+1] · μ[i][j]`. Once `d[j+1] > 0` and `η.den > 0` are pinned, division by
the positive product `d[j+1] · η.den` turns the integer inequality into
`|μ| ≤ η`, hence (since `η ≥ 0` follows from the same inequality) `μ² ≤ η²`. -/
private theorem sizeSq_of_intCheck
    {n m : Nat} (b : Hex.Matrix Int n m) (_δ η : Rat) {i j : Nat}
    (hi : i < n) (hji : j < i)
    (hd_pos : 0 < (Hex.GramSchmidt.Int.data b).d.get
      ⟨j + 1, Nat.succ_lt_succ (Nat.lt_trans hji hi)⟩)
    (hint :
      ((η.den : Int) *
          ((((Hex.GramSchmidt.Int.data b).ν.getRow ⟨i, hi⟩).get
              ⟨j, Nat.lt_trans hji hi⟩).natAbs : Int)) ≤
        η.num *
          ((Hex.GramSchmidt.Int.data b).d.get
            ⟨j + 1, Nat.succ_lt_succ (Nat.lt_trans hji hi)⟩ : Int)) :
    (((Hex.GramSchmidt.Int.coeffs b).getRow ⟨i, hi⟩).get
        ⟨j, Nat.lt_trans hji hi⟩) *
      (((Hex.GramSchmidt.Int.coeffs b).getRow ⟨i, hi⟩).get
        ⟨j, Nat.lt_trans hji hi⟩) ≤ η * η := by
  -- Names for the integer slots.
  set νij : Int := ((Hex.GramSchmidt.Int.data b).ν.getRow ⟨i, hi⟩).get
      ⟨j, Nat.lt_trans hji hi⟩ with hνij_def
  set dj1 : Nat := (Hex.GramSchmidt.Int.data b).d.get
      ⟨j + 1, Nat.succ_lt_succ (Nat.lt_trans hji hi)⟩ with hdj1_def
  set μ : Rat := ((Hex.GramSchmidt.Int.coeffs b).getRow ⟨i, hi⟩).get
      ⟨j, Nat.lt_trans hji hi⟩ with hμ_def
  -- Bridge ν[i][j] ↔ d[j+1] · μ via scaledCoeffs_eq.
  have hbridge :
      (νij : Rat) = (dj1 : Rat) * μ := by
    have h := Hex.GramSchmidt.Int.scaledCoeffs_eq b i j hi hji
    -- h equates the GS-entry of scaledCoeffs to gramDet·coeffs-entry.
    -- (Hex.GramSchmidt.Int.data b).ν = Hex.GramSchmidt.Int.scaledCoeffs b
    -- (Hex.GramSchmidt.Int.data b).d.get ⟨j+1, _⟩ = gramDet b (j+1).
    have hScaled :
        (Hex.GramSchmidt.entry (Hex.GramSchmidt.Int.scaledCoeffs b)
            ⟨i, hi⟩ ⟨j, Nat.lt_trans hji hi⟩ : Int) = νij := by
      rfl
    have hdEq :
        (dj1 : Nat) = Hex.GramSchmidt.Int.gramDet b (j + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hji hi)) := by
      have hbridge_d :=
        Hex.GramSchmidt.Int.gramDetVec_eq_gramDet b
          (Hex.GramSchmidt.Int.StepWitness.ofGram b)
          (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hji hi))
      simpa [Hex.GramSchmidt.Int.gramDetVec, hdj1_def] using hbridge_d
    have hμEq :
        Hex.GramSchmidt.entry (Hex.GramSchmidt.Int.coeffs b) ⟨i, hi⟩
            ⟨j, Nat.lt_trans hji hi⟩ = μ := by
      rfl
    rw [hScaled] at h
    rw [hμEq] at h
    rw [hdEq]
    exact h
  -- Positivity casts.
  have hdj1_pos : (0 : Rat) < (dj1 : Rat) := by exact_mod_cast hd_pos
  have hdj1_ne : (dj1 : Rat) ≠ 0 := ne_of_gt hdj1_pos
  have hηden_pos : (0 : Rat) < (η.den : Rat) := by exact_mod_cast η.den_pos
  have hηden_ne : (η.den : Rat) ≠ 0 := ne_of_gt hηden_pos
  -- Cast the integer inequality to Rat.
  have hcast : (η.den : Rat) * (νij.natAbs : Rat) ≤ (η.num : Rat) * (dj1 : Rat) := by
    have hint' : (((η.den : Int) * (νij.natAbs : Int) : Int) : Rat) ≤
        ((η.num * (dj1 : Int) : Int) : Rat) := by exact_mod_cast hint
    simpa [Int.cast_mul, Int.cast_natCast] using hint'
  -- η.num ≥ 0 follows: LHS = η.den · |νij| ≥ 0, so η.num · dj1 ≥ 0, then ÷ dj1 > 0.
  have hnumNonneg : (0 : Rat) ≤ (η.num : Rat) := by
    have hLHS_nn : (0 : Rat) ≤ (η.den : Rat) * (νij.natAbs : Rat) := by
      have h1 : (0 : Rat) ≤ (η.den : Rat) := le_of_lt hηden_pos
      have h2 : (0 : Rat) ≤ (νij.natAbs : Rat) := Nat.cast_nonneg _
      exact mul_nonneg h1 h2
    have hRHS_nn : (0 : Rat) ≤ (η.num : Rat) * (dj1 : Rat) :=
      le_trans hLHS_nn hcast
    -- Divide by dj1 > 0.
    have := (mul_nonneg_iff_of_pos_right hdj1_pos).mp hRHS_nn
    exact this
  -- Therefore η ≥ 0.
  have hη_nonneg : (0 : Rat) ≤ η := by
    have hη_eq : η = (η.num : Rat) / (η.den : Rat) := (Rat.num_div_den η).symm
    rw [hη_eq]
    exact div_nonneg hnumNonneg (le_of_lt hηden_pos)
  -- The absolute value of μ.
  -- Rat: |μ| = |νij| / dj1.
  have habsμ_eq : |μ| = (νij.natAbs : Rat) / (dj1 : Rat) := by
    have hμ_val : μ = (νij : Rat) / (dj1 : Rat) := by
      rw [eq_div_iff hdj1_ne, mul_comm]
      exact hbridge.symm
    rw [hμ_val, abs_div]
    have habs_dj1 : |(dj1 : Rat)| = (dj1 : Rat) := abs_of_pos hdj1_pos
    rw [habs_dj1]
    have habs_νij : |(νij : Rat)| = (νij.natAbs : Rat) := by
      rw [Nat.cast_natAbs]
      exact (Int.cast_abs).symm
    rw [habs_νij]
  -- |μ| ≤ η: divide the integer inequality by (η.den · dj1) > 0.
  have habsμ_le_η : |μ| ≤ η := by
    rw [habsμ_eq]
    have hη_eq : η = (η.num : Rat) / (η.den : Rat) := (Rat.num_div_den η).symm
    rw [hη_eq]
    -- We want (|νij| : Rat) / dj1 ≤ η.num / η.den.
    -- Equivalent to: |νij| · η.den ≤ η.num · dj1 (LHS, RHS positive).
    rw [div_le_div_iff₀ hdj1_pos hηden_pos]
    have hswap : (νij.natAbs : Rat) * (η.den : Rat) =
        (η.den : Rat) * (νij.natAbs : Rat) := by ring
    rw [hswap]
    exact hcast
  -- Therefore μ² ≤ η².
  have h0_le_absμ : 0 ≤ |μ| := abs_nonneg μ
  have hsq1 : |μ| * |μ| ≤ η * |μ| := by
    exact mul_le_mul_of_nonneg_right habsμ_le_η h0_le_absμ
  have hsq2 : η * |μ| ≤ η * η := by
    exact mul_le_mul_of_nonneg_left habsμ_le_η hη_nonneg
  have hμsq_eq : |μ| * |μ| = μ * μ := by
    rw [abs_mul_abs_self]
  rw [← hμsq_eq]
  exact le_trans hsq1 hsq2

/-- Lovász contribution: from one integer Lovász inequality at slot `i`
plus positivity of the three involved `d` entries, derive the rational
Lovász condition at the same slot.

Same algebraic identity as `lovasz_check_iff_isLLLReduced_pair`, but stated
directly on `(GramSchmidt.Int.data b).d / ν` rather than going through an
`LLLState`. Bridges: `gramDetVec_eq_gramDet`, `scaledCoeffs_eq`, and
`basis_normSq`. -/
private theorem lovasz_of_intCheck
    {n m : Nat} (b : Hex.Matrix Int n m) (δ _η : Rat) {i : Nat}
    (hi : i + 1 < n) (hindep : Hex.Matrix.independent b)
    (hint :
      (δ.den : Int) *
          (((Hex.GramSchmidt.Int.data b).d.get
              ⟨i + 2, Nat.succ_lt_succ hi⟩ : Int) *
              ((Hex.GramSchmidt.Int.data b).d.get
                ⟨i, Nat.lt_succ_of_lt
                  (Nat.lt_trans (Nat.lt_succ_self i) hi)⟩ : Int) +
            (((Hex.GramSchmidt.Int.data b).ν.getRow ⟨i + 1, hi⟩).get
              ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩) ^ 2) ≥
        δ.num *
          ((Hex.GramSchmidt.Int.data b).d.get
            ⟨i + 1, Nat.succ_lt_succ
              (Nat.lt_trans (Nat.lt_succ_self i) hi)⟩ : Int) ^ 2) :
    δ * Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis b)
        ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ ≤
      Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis b) ⟨i + 1, hi⟩ +
        (((Hex.GramSchmidt.Int.coeffs b).getRow ⟨i + 1, hi⟩).get
            ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩) *
          (((Hex.GramSchmidt.Int.coeffs b).getRow ⟨i + 1, hi⟩).get
            ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩) *
          Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis b)
            ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ := by
  have hi_lt : i < n := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hi1_lt : i + 1 < n := hi
  set iFin : Fin n := ⟨i, hi_lt⟩ with hiFin_def
  set ip1Fin : Fin n := ⟨i + 1, hi⟩ with hip1Fin_def
  have hi0_le : 0 ≤ i := Nat.zero_le _
  -- Bridge `data.d.get ⟨k, ...⟩ = gramDet b k _`.
  have hd_bridge :
      ∀ k (hk : k ≤ n),
        (Hex.GramSchmidt.Int.data b).d.get ⟨k, Nat.lt_succ_of_le hk⟩ =
          Hex.GramSchmidt.Int.gramDet b k hk := by
    intro k hk
    have hbr :=
      Hex.GramSchmidt.Int.gramDetVec_eq_gramDet b
        (Hex.GramSchmidt.Int.StepWitness.ofGram b) k hk
    simpa [Hex.GramSchmidt.Int.gramDetVec] using hbr
  set gd_i : Nat :=
    Hex.GramSchmidt.Int.gramDet b i (Nat.le_of_lt hi_lt) with hgd_i_def
  set gd_i1 : Nat :=
    Hex.GramSchmidt.Int.gramDet b (i + 1)
      (Nat.succ_le_of_lt hi_lt) with hgd_i1_def
  set gd_i2 : Nat :=
    Hex.GramSchmidt.Int.gramDet b (i + 2)
      (Nat.succ_le_of_lt hi1_lt) with hgd_i2_def
  have hdi_eq : (Hex.GramSchmidt.Int.data b).d.get
      ⟨i, Nat.lt_succ_of_lt hi_lt⟩ = gd_i :=
    hd_bridge i (Nat.le_of_lt hi_lt)
  have hdi1_eq : (Hex.GramSchmidt.Int.data b).d.get
      ⟨i + 1, Nat.succ_lt_succ hi_lt⟩ = gd_i1 :=
    hd_bridge (i + 1) (Nat.succ_le_of_lt hi_lt)
  have hdi2_eq : (Hex.GramSchmidt.Int.data b).d.get
      ⟨i + 2, Nat.succ_lt_succ hi⟩ = gd_i2 :=
    hd_bridge (i + 2) (Nat.succ_le_of_lt hi1_lt)
  -- Positivity of the three gd values.
  have hgd_i1_pos : 0 < gd_i1 :=
    Hex.GramSchmidt.Int.gramDet_pos b hindep (i + 1)
      (Nat.succ_le_of_lt hi_lt) (Nat.succ_pos i)
  have hgd_i2_pos : 0 < gd_i2 :=
    Hex.GramSchmidt.Int.gramDet_pos b hindep (i + 2)
      (Nat.succ_le_of_lt hi1_lt) (Nat.succ_pos (i + 1))
  have hgd_i_pos : 0 < gd_i := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · show 0 < Hex.GramSchmidt.Int.gramDet b i _
      rw [Hex.GramSchmidt.Int.gramDet_subst_val b i 0
          (Nat.le_of_lt hi_lt) (Nat.zero_le n) h0,
        Hex.GramSchmidt.Int.gramDet_zero]
      exact Nat.zero_lt_one
    · exact Hex.GramSchmidt.Int.gramDet_pos b hindep i
        (Nat.le_of_lt hi_lt) hpos
  have hgd_i_posR : (0 : Rat) < (gd_i : Rat) := by exact_mod_cast hgd_i_pos
  have hgd_i1_posR : (0 : Rat) < (gd_i1 : Rat) := by exact_mod_cast hgd_i1_pos
  have hgd_i2_posR : (0 : Rat) < (gd_i2 : Rat) := by exact_mod_cast hgd_i2_pos
  have hgd_i_ne : (gd_i : Rat) ≠ 0 := ne_of_gt hgd_i_posR
  have hgd_i1_ne : (gd_i1 : Rat) ≠ 0 := ne_of_gt hgd_i1_posR
  have hδden_pos : (0 : Rat) < (δ.den : Rat) := by exact_mod_cast δ.den_pos
  -- Basis norm identities.
  set Ni : Rat := Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis b) iFin
    with hNi_def
  set Ni1 : Rat := Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis b) ip1Fin
    with hNi1_def
  have hNi_mul : (gd_i : Rat) * Ni = (gd_i1 : Rat) := by
    have hbn := Hex.GramSchmidt.Int.basis_normSq b hindep i hi_lt
    have hNi_val : Ni = (gd_i1 : Rat) / (gd_i : Rat) := by
      show ((Hex.GramSchmidt.Int.basis b).row ⟨i, hi_lt⟩).normSq = _
      exact hbn
    rw [hNi_val, mul_div_cancel₀ _ hgd_i_ne]
  have hNi1_mul : (gd_i1 : Rat) * Ni1 = (gd_i2 : Rat) := by
    have hbn := Hex.GramSchmidt.Int.basis_normSq b hindep (i + 1) hi1_lt
    have hNi1_val : Ni1 = (gd_i2 : Rat) / (gd_i1 : Rat) := by
      show ((Hex.GramSchmidt.Int.basis b).row ⟨i + 1, hi1_lt⟩).normSq = _
      exact hbn
    rw [hNi1_val, mul_div_cancel₀ _ hgd_i1_ne]
  -- ν[i+1][i] = gd_i1 · μ via scaledCoeffs_eq.
  set νB : Int := ((Hex.GramSchmidt.Int.data b).ν.getRow ip1Fin).get ⟨i, hi_lt⟩
    with hνB_def
  set μ : Rat := ((Hex.GramSchmidt.Int.coeffs b).getRow ip1Fin).get ⟨i, hi_lt⟩
    with hμ_def
  have hμ_bridge : (νB : Rat) = (gd_i1 : Rat) * μ := by
    have h := Hex.GramSchmidt.Int.scaledCoeffs_eq b (i + 1) i hi1_lt
      (Nat.lt_succ_self i)
    have hScaled :
        (Hex.GramSchmidt.entry (Hex.GramSchmidt.Int.scaledCoeffs b)
            ip1Fin ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1_lt⟩ : Int) = νB := by
      rfl
    have hμEq :
        Hex.GramSchmidt.entry (Hex.GramSchmidt.Int.coeffs b) ip1Fin
            ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi1_lt⟩ = μ := by
      rfl
    rw [hScaled] at h
    rw [hμEq] at h
    -- Need to rewrite the gd_i1 cast.
    have hgdEq : Hex.GramSchmidt.Int.gramDet b (i + 1)
        (Nat.succ_le_of_lt (Nat.lt_trans (Nat.lt_succ_self i) hi1_lt)) =
        gd_i1 := by rfl
    rw [hgdEq] at h
    exact h
  -- Square form.
  have hνB_sq : ((νB : Int) ^ 2 : Rat) = (gd_i1 : Rat) ^ 2 * μ ^ 2 := by
    have hsq : ((νB : Rat)) ^ 2 = ((gd_i1 : Rat) * μ) ^ 2 := by rw [hμ_bridge]
    rw [show ((νB : Int) ^ 2 : Rat) = ((νB : Rat)) ^ 2 from rfl,
      hsq]; ring
  -- δ.den · δ = δ.num.
  have hδmul : δ * (δ.den : Rat) = (δ.num : Rat) := Rat.mul_den_eq_num δ
  -- Convert the integer hypothesis to a Rat inequality.
  have hcast_iff :
      ((δ.den : Rat) *
          ((gd_i2 : Rat) * (gd_i : Rat) + (gd_i1 : Rat) ^ 2 * μ ^ 2) ≥
        (δ.num : Rat) * (gd_i1 : Rat) ^ 2) := by
    have hcastR : ((δ.den : Int) *
        (((Hex.GramSchmidt.Int.data b).d.get ⟨i + 2, Nat.succ_lt_succ hi⟩ : Int) *
            ((Hex.GramSchmidt.Int.data b).d.get
                ⟨i, Nat.lt_succ_of_lt hi_lt⟩ : Int) +
          (((Hex.GramSchmidt.Int.data b).ν.getRow ip1Fin).get ⟨i, hi_lt⟩) ^ 2) : Rat) ≥
        ((δ.num *
          ((Hex.GramSchmidt.Int.data b).d.get
            ⟨i + 1, Nat.succ_lt_succ hi_lt⟩ : Int) ^ 2 : Int) : Rat) := by
      exact_mod_cast hint
    -- Substitute the d-bridges (Nat-side) on both sides.
    rw [hdi_eq, hdi1_eq, hdi2_eq] at hcastR
    rw [hνB_sq] at hcastR
    push_cast at hcastR
    exact hcastR
  -- The key algebraic identity:
  --   δ.den · (gd_i2 · gd_i + gd_i1² · μ²) - δ.num · gd_i1² =
  --   P · (Ni1 + Ni · μ² - δ · Ni)
  -- where P = δ.den · gd_i · gd_i1.
  set P : Rat := (δ.den : Rat) * (gd_i : Rat) * (gd_i1 : Rat) with hP_def
  have hP_pos : 0 < P := by
    have h1 : 0 < (δ.den : Rat) * (gd_i : Rat) := mul_pos hδden_pos hgd_i_posR
    exact mul_pos h1 hgd_i1_posR
  have hidentity :
      (δ.den : Rat) *
          ((gd_i2 : Rat) * (gd_i : Rat) + (gd_i1 : Rat) ^ 2 * μ ^ 2) -
        (δ.num : Rat) * (gd_i1 : Rat) ^ 2 =
      P * ((Ni1 + Ni * μ * μ) - δ * Ni) := by
    have hμ_sq : μ ^ 2 = μ * μ := sq μ
    rw [hP_def, ← hNi1_mul, ← hNi_mul, ← hδmul, hμ_sq]
    ring
  -- From the cast inequality and the identity, derive the rational Lovász.
  have hLHS_ge :
      0 ≤ (δ.den : Rat) *
              ((gd_i2 : Rat) * (gd_i : Rat) + (gd_i1 : Rat) ^ 2 * μ ^ 2) -
            (δ.num : Rat) * (gd_i1 : Rat) ^ 2 := by linarith
  rw [hidentity] at hLHS_ge
  have hdiff_nn : 0 ≤ (Ni1 + Ni * μ * μ) - δ * Ni :=
    (mul_nonneg_iff_of_pos_left hP_pos).mp hLHS_ge
  linarith

/-- D2 soundness theorem: the executable integer reducedness checker entails
both `b.independent` and the rational `isLLLReduced b δ η` predicate.

This is one of the two soundness ingredients feeding the combined
`certCheck_sound` of `hex-lll` §"Certified external dispatch". The
companion same-lattice piece is `Hex.Matrix.sameLatticeCert_sound`. -/
theorem lllReducedInt_sound (b : Hex.Matrix Int n m) (δ η : Rat) :
    Hex.lllReducedInt b δ η = true →
      Hex.isLLLReduced b δ η ∧ Hex.Matrix.independent b := by
  intro hcheck
  -- Unfold the three pieces of the Bool check.
  unfold Hex.lllReducedInt at hcheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    decide_eq_true_eq, forall_true_left] at hcheck
  obtain ⟨⟨hdPos, hsize⟩, hlovasz_raw⟩ := hcheck
  -- Independence.
  have hindep : Hex.Matrix.independent b := independent_of_dPos b hdPos
  -- Repackage the Lovász raw form (with the leading `if hi : ... then ... else
  -- true = true`) as a clean `∀ i hi → integer Lovász holds at slot i`.
  have hlovasz : ∀ (i : Nat) (hi : i + 1 < n),
      (δ.den : Int) *
          (((Hex.GramSchmidt.Int.data b).d.get
              ⟨i + 2, Nat.succ_lt_succ hi⟩ : Int) *
              ((Hex.GramSchmidt.Int.data b).d.get
                ⟨i, Nat.lt_succ_of_lt
                  (Nat.lt_trans (Nat.lt_succ_self i) hi)⟩ : Int) +
            (((Hex.GramSchmidt.Int.data b).ν.getRow ⟨i + 1, hi⟩).get
              ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩) ^ 2) ≥
        δ.num *
          ((Hex.GramSchmidt.Int.data b).d.get
            ⟨i + 1, Nat.succ_lt_succ
              (Nat.lt_trans (Nat.lt_succ_self i) hi)⟩ : Int) ^ 2 := by
    intro i hi
    have h := hlovasz_raw ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    simp only [hi, dite_true, decide_eq_true_eq] at h
    exact h
  refine ⟨?_, hindep⟩
  refine ⟨?_, ?_⟩
  · -- Size-reduced part of `isLLLReduced`.
    intro i j hi hji
    -- The `hsize` clause, specialized at i (with proof hi) and j (with proof hji).
    have hint := hsize ⟨i, hi⟩ ⟨j, hji⟩
    -- Need positivity of d[j+1] from independence.
    have hd_pos : 0 < (Hex.GramSchmidt.Int.data b).d.get
        ⟨j + 1, Nat.succ_lt_succ (Nat.lt_trans hji hi)⟩ :=
      hdPos ⟨j, Nat.lt_trans hji hi⟩
    -- Apply the size-square bridge.
    exact sizeSq_of_intCheck b δ η hi hji hd_pos hint
  · -- Lovász part.
    intro i hi
    exact lovasz_of_intCheck b δ η hi hindep (hlovasz i hi)

/-- Soundness of the dispatched reducedness clause `Hex.lllReducedCheck`:
whichever side decided — the fixed-precision interval checker
(`HexLLLMathlib.lllReducedInterval_sound`), the exact integer checker
chosen by the size predictor, or the exact fallback after interval
indecision (both via `lllReducedInt_sound` above) — acceptance entails
the rational `isLLLReduced` predicate and independence. The predictor
`Hex.Internal.intervalWins` only selects between sound checkers, so no hypothesis
about it is needed. -/
theorem lllReducedCheck_sound (b : Hex.Matrix Int n m) (δ η : Rat) :
    Hex.lllReducedCheck b δ η = true →
      Hex.isLLLReduced b δ η ∧ Hex.Matrix.independent b := by
  intro hcheck
  unfold Hex.lllReducedCheck at hcheck
  simp only [Hex.Internal.withRecordCheckerOutcome] at hcheck
  by_cases hwin : Hex.Internal.intervalWins b = true
  · rw [if_pos hwin] at hcheck
    by_cases hint : Hex.lllReducedInterval b δ η = true
    · exact HexLLLMathlib.lllReducedInterval_sound b δ η hint
    · rw [if_neg (by simpa using hint)] at hcheck
      exact lllReducedInt_sound b δ η hcheck
  · rw [if_neg (by simpa using hwin)] at hcheck
    exact lllReducedInt_sound b δ η hcheck

/-- Soundness of the certified-dispatch checker `Hex.certCheck`: an accepted
certificate `(B', U, V)` proves that `B` and `B'` generate the same integer row
lattice, that `B'` is independent, and that `B'` is `(δ, η)`-LLL-reduced.

Composes the two soundness ingredients:
* `Hex.Matrix.sameLatticeCert_sound` (Mathlib-free, HexLLL/Basic.lean) for the
  same-lattice clause, and
* `lllReducedCheck_sound` (above) for independence and reducedness, covering
  both the interval decision and the exact integer fallback.

No validity hypothesis on `η`: the `1/2 ≤ η`, `η² < δ` conditions for the LLL
short-vector bound live on `short_vector_bound_of_size_bound`, not on the
checker. This is the single trusted soundness theorem feeding the
certified-dispatch correctness of `lll`. -/
theorem certCheck_sound {B B' : Hex.Matrix Int n m} {U V : Hex.Matrix Int n n}
    {δ η : Rat} :
    Hex.certCheck B B' U V δ η = true →
      (∀ v, B.memLattice v ↔ B'.memLattice v) ∧
        B'.independent ∧ Hex.isLLLReduced B' δ η := by
  intro hcheck
  unfold Hex.certCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨hsame, hred⟩ := hcheck
  refine ⟨Hex.Matrix.sameLatticeCert_sound hsame, ?_, ?_⟩
  · exact (lllReducedCheck_sound B' δ η hred).2
  · exact (lllReducedCheck_sound B' δ η hred).1

end HexLLLMathlib
