/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Basic
public import HexGramSchmidtMathlib.Int
public import HexRowReduceMathlib.RankSpanNullspace
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

public section

/-!
Validity of the executable `LLLState` against its Gram-Schmidt
interpretation: `ofBasis_valid`, the scaled-coefficient identification
`lllState_ν_eq_coeffs`, and the integer Lovász test as the rational
`isLLLReduced` Lovász clause.
-/

namespace HexLLLMathlib

/-- The canonical `LLLState` constructor packages the executable Gram-Schmidt
data. Lives on the Mathlib side because the diagonal Gram-determinant
identification (`gramDetVec_eq_gramDet`) consumes a `StepWitness b`, which is
supplied by `StepWitness.ofGram`. -/
theorem LLLState.ofBasis_valid (b : Hex.Matrix Int n m) (hind : b.independent) :
    (Hex.Internal.LLLState.ofBasis b hind).Valid := by
  let gs := Hex.GramSchmidt.Int.data b
  constructor
  · intro i j hi hj hji
    simp [Hex.Internal.LLLState.ofBasis, Hex.Internal.LLLState.ofBasisUnchecked,
      Hex.GramSchmidt.Int.scaledCoeffs]
  · intro i hi
    simpa [Hex.Internal.LLLState.ofBasis, Hex.Internal.LLLState.ofBasisUnchecked,
      Hex.GramSchmidt.Int.gramDetVec, gs] using
      Hex.GramSchmidt.Int.gramDetVec_eq_gramDet b
        (Hex.GramSchmidt.Int.StepWitness.ofGram b) i (Nat.le_of_lt_succ hi)

/-- Mathlib-side correspondence from the executable LLL state scaled-coefficient
certificate to the rational Gram-Schmidt coefficient relation. -/
theorem lllState_ν_eq_coeffs
    (s : Hex.Internal.LLLState n m) (hvalid : s.Valid)
    (i j : Nat) (hi : i < n) (hj : j < n) (hji : j < i) :
    (((s.ν.getRow ⟨i, hi⟩).get ⟨j, hj⟩ : Int) : Rat) =
      (s.d.get ⟨j + 1, Nat.succ_lt_succ hj⟩ : Rat) *
        (((Hex.GramSchmidt.Int.coeffs s.b).getRow ⟨i, hi⟩).get ⟨j, hj⟩) := by
  have hν := hvalid.ν_eq i j hi hj hji
  have hd :
      s.d.get ⟨j + 1, Nat.succ_lt_succ hj⟩ =
        Hex.GramSchmidt.Int.gramDet s.b (j + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hji hi)) :=
    hvalid.d_eq (j + 1) (Nat.succ_lt_succ hj)
  have hscaled :=
    Hex.GramSchmidt.Int.scaledCoeffs_eq s.b i j hi hji
  rw [hν, hd]
  exact hscaled

/-- Integer Lovász check ↔ rational Lovász condition at pair `(k - 1, k)`.

`Hex.Internal.lllLoop` dispatches on the integer comparison

```
δ.den * (d[k+1] * d[k-1] + ν[k][k-1]²) ≥ δ.num * d[k]²
```

while `Hex.isLLLReduced` quantifies the rational Lovász condition

```
δ * ‖b*[i]‖² ≤ ‖b*[i+1]‖² + μ[i+1][i]² · ‖b*[i]‖²
```

over every adjacent pair `(i, i+1)`. Under `s.Valid` and `s.b.independent`,
the two formulations agree at pair `(k - 1, k)`: the integer scaled
Gram-Schmidt data carried by `s` faithfully encodes the rational Lovász
predicate at that position. This bridges the loop's executable check to the
specification side of `isLLLReduced` so the loop-invariant proof can read off
"the loop advances ⇒ Lovász holds at this pair." -/
theorem lovasz_check_iff_isLLLReduced_pair
    (s : Hex.Internal.LLLState n m) (k : Nat) (hk : k < n) (hk0 : 0 < k)
    (hvalid : s.Valid) (hind : s.b.independent)
    {δ : Rat} (_hδ : (1 : Rat) / 4 < δ) (_hδ' : δ ≤ 1) :
    have hkm1lt : k - 1 < n :=
      Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk
    have hkm1ltN1 : k - 1 < n + 1 :=
      Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le k 1) hk)
    have hkltN1 : k < n + 1 := Nat.lt_succ_of_lt hk
    have hkSuccLt : k + 1 < n + 1 := Nat.succ_lt_succ hk
    Int.ofNat δ.den *
        (Int.ofNat (s.d.get ⟨k + 1, hkSuccLt⟩) *
            Int.ofNat (s.d.get ⟨k - 1, hkm1ltN1⟩) +
          ((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩) ^ 2) ≥
        δ.num * (Int.ofNat (s.d.get ⟨k, hkltN1⟩) ^ 2) ↔
      δ * Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b)
            ⟨k - 1, hkm1lt⟩ ≤
        Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b) ⟨k, hk⟩ +
          (((Hex.GramSchmidt.Int.coeffs s.b).getRow ⟨k, hk⟩).get
              ⟨k - 1, hkm1lt⟩) *
            (((Hex.GramSchmidt.Int.coeffs s.b).getRow ⟨k, hk⟩).get
              ⟨k - 1, hkm1lt⟩) *
            Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b)
              ⟨k - 1, hkm1lt⟩ := by
  intro hkm1lt hkm1ltN1 hkltN1 hkSuccLt
  -- Translate the d-field values to Gram determinants.
  have hdk_eq : s.d.get ⟨k, hkltN1⟩ =
      Hex.GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt_succ hkltN1) :=
    hvalid.d_eq k hkltN1
  have hdkPrev_eq : s.d.get ⟨k - 1, hkm1ltN1⟩ =
      Hex.GramSchmidt.Int.gramDet s.b (k - 1) (Nat.le_of_lt_succ hkm1ltN1) :=
    hvalid.d_eq (k - 1) hkm1ltN1
  have hdkNext_eq : s.d.get ⟨k + 1, hkSuccLt⟩ =
      Hex.GramSchmidt.Int.gramDet s.b (k + 1) (Nat.le_of_lt_succ hkSuccLt) :=
    hvalid.d_eq (k + 1) hkSuccLt
  -- ν → coeffs identity at (k, k - 1), normalised so the carried d-index is k.
  have hkm1ltK : k - 1 < k := Nat.sub_lt hk0 Nat.zero_lt_one
  have hsubAdd : k - 1 + 1 = k := Nat.sub_add_cancel hk0
  have hν :
      (((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int) : Rat) =
        (s.d.get ⟨k, hkltN1⟩ : Rat) *
          (((Hex.GramSchmidt.Int.coeffs s.b).getRow ⟨k, hk⟩).get
            ⟨k - 1, hkm1lt⟩) := by
    have h := lllState_ν_eq_coeffs s hvalid k (k - 1) hk hkm1lt hkm1ltK
    have hidx :
        (⟨k - 1 + 1, Nat.succ_lt_succ hkm1lt⟩ : Fin (n + 1)) =
          ⟨k, hkltN1⟩ :=
      Fin.ext hsubAdd
    rw [hidx] at h
    exact h
  -- Set up the Gram-determinant and basis-norm shorthand.
  set gd_k : Nat :=
    Hex.GramSchmidt.Int.gramDet s.b k (Nat.le_of_lt_succ hkltN1) with hgd_k_def
  set gd_k1 : Nat :=
    Hex.GramSchmidt.Int.gramDet s.b (k + 1) (Nat.le_of_lt_succ hkSuccLt)
      with hgd_k1_def
  set gd_km1 : Nat :=
    Hex.GramSchmidt.Int.gramDet s.b (k - 1) (Nat.le_of_lt_succ hkm1ltN1)
      with hgd_km1_def
  set Nk : Rat :=
    Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b) ⟨k, hk⟩
      with hNk_def
  set Nkm1 : Rat :=
    Hex.Internal.LLLCore.basisNormSq (Hex.GramSchmidt.Int.basis s.b)
        ⟨k - 1, hkm1lt⟩ with hNkm1_def
  set μ : Rat :=
    ((Hex.GramSchmidt.Int.coeffs s.b).getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩
      with hμ_def
  -- Positivity of the Gram determinants.
  have hgd_k_pos_nat : 0 < gd_k :=
    Hex.GramSchmidt.Int.gramDet_pos s.b hind k
      (Nat.le_of_lt_succ hkltN1) hk0
  have hgd_k1_pos_nat : 0 < gd_k1 :=
    Hex.GramSchmidt.Int.gramDet_pos s.b hind (k + 1)
      (Nat.le_of_lt_succ hkSuccLt) (Nat.succ_pos k)
  have hgd_km1_pos_nat : 0 < gd_km1 := by
    rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
    · show 0 < Hex.GramSchmidt.Int.gramDet s.b (k - 1) _
      rw [Hex.GramSchmidt.Int.gramDet_subst_val s.b (k - 1) 0
          (Nat.le_of_lt_succ hkm1ltN1) (Nat.zero_le n) h0,
        Hex.GramSchmidt.Int.gramDet_zero]
      exact Nat.zero_lt_one
    · exact Hex.GramSchmidt.Int.gramDet_pos s.b hind (k - 1)
        (Nat.le_of_lt_succ hkm1ltN1) hpos
  have hgd_k_pos : (0 : Rat) < (gd_k : Rat) := by exact_mod_cast hgd_k_pos_nat
  have hgd_k1_pos : (0 : Rat) < (gd_k1 : Rat) := by exact_mod_cast hgd_k1_pos_nat
  have hgd_km1_pos : (0 : Rat) < (gd_km1 : Rat) := by
    exact_mod_cast hgd_km1_pos_nat
  have hgd_k_ne : (gd_k : Rat) ≠ 0 := ne_of_gt hgd_k_pos
  have hgd_km1_ne : (gd_km1 : Rat) ≠ 0 := ne_of_gt hgd_km1_pos
  have hδden_pos : (0 : Rat) < (δ.den : Rat) := by
    exact_mod_cast δ.den_pos
  have hδden_ne : (δ.den : Rat) ≠ 0 := ne_of_gt hδden_pos
  -- Basis-norm identities.
  have hNk_mul : (gd_k : Rat) * Nk = (gd_k1 : Rat) := by
    have hbn := Hex.GramSchmidt.Int.basis_normSq s.b hind k hk
    have hNk_val : Nk = (gd_k1 : Rat) / (gd_k : Rat) := by
      show ((Hex.GramSchmidt.Int.basis s.b).row ⟨k, hk⟩).normSq = _
      exact hbn
    rw [hNk_val, mul_div_cancel₀ _ hgd_k_ne]
  have hNkm1_mul : (gd_km1 : Rat) * Nkm1 = (gd_k : Rat) := by
    have hbn := Hex.GramSchmidt.Int.basis_normSq s.b hind (k - 1) hkm1lt
    have hNkm1_val :
        Nkm1 = (Hex.GramSchmidt.Int.gramDet s.b (k - 1 + 1)
            (Nat.succ_le_of_lt hkm1lt) : Rat) / (gd_km1 : Rat) := by
      show ((Hex.GramSchmidt.Int.basis s.b).row ⟨k - 1, hkm1lt⟩).normSq = _
      exact hbn
    have hgd_eq :
        Hex.GramSchmidt.Int.gramDet s.b (k - 1 + 1)
            (Nat.succ_le_of_lt hkm1lt) = gd_k :=
      Hex.GramSchmidt.Int.gramDet_subst_val s.b (k - 1 + 1) k
        (Nat.succ_le_of_lt hkm1lt) (Nat.le_of_lt_succ hkltN1) hsubAdd
    rw [hgd_eq] at hNkm1_val
    rw [hNkm1_val, mul_div_cancel₀ _ hgd_km1_ne]
  -- δ * δ.den = δ.num (over Rat).
  have hδmul : δ * (δ.den : Rat) = (δ.num : Rat) := Rat.mul_den_eq_num δ
  -- Cast B = ν[k][k-1] = gd_k * μ (over Rat).
  have hB_cast :
      (((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int) : Rat) =
        (gd_k : Rat) * μ := by
    rw [hν, hdk_eq]
  have hB_sq :
      ((((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int)) ^ 2 : Rat) =
        (gd_k : Rat) ^ 2 * μ ^ 2 := by
    have hsq : (((((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int)) : Rat)) ^ 2 =
        ((gd_k : Rat) * μ) ^ 2 := by rw [hB_cast]
    rw [show ((((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int)) ^ 2 : Rat) =
          (((((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩ : Int)) : Rat)) ^ 2 from by
        rfl, hsq]; ring
  -- Convert the integer inequality to an equivalent Rat inequality with all
  -- `Int.ofNat`/`Int → Rat` casts normalised to direct `Nat → Rat` casts.
  have hcast_iff :
      (Int.ofNat δ.den *
          (Int.ofNat (s.d.get ⟨k + 1, hkSuccLt⟩) *
              Int.ofNat (s.d.get ⟨k - 1, hkm1ltN1⟩) +
            ((s.ν.getRow ⟨k, hk⟩).get ⟨k - 1, hkm1lt⟩) ^ 2) ≥
        δ.num * (Int.ofNat (s.d.get ⟨k, hkltN1⟩) ^ 2)) ↔
      ((δ.den : Rat) *
          ((gd_k1 : Rat) * (gd_km1 : Rat) +
            (gd_k : Rat) ^ 2 * μ ^ 2) ≥
        (δ.num : Rat) * (gd_k : Rat) ^ 2) := by
    rw [ge_iff_le, ge_iff_le, ← @Int.cast_le ℚ, hdk_eq, hdkPrev_eq, hdkNext_eq]
    push_cast
    rw [hB_sq]
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
  rw [hcast_iff]
  -- Define the positive multiplier and the identity.
  set P : Rat := (δ.den : Rat) * (gd_k : Rat) * (gd_km1 : Rat) with hP_def
  have hP_pos : 0 < P := by
    have : 0 < (δ.den : Rat) * (gd_k : Rat) := mul_pos hδden_pos hgd_k_pos
    exact mul_pos this hgd_km1_pos
  -- The key algebraic identity:
  --   δ.den * (gd_k1 * gd_km1 + gd_k^2 * μ^2) - δ.num * gd_k^2
  -- = P * ((Nk + Nkm1 * μ^2) - δ * Nkm1)
  -- proved by substituting gd_k1 = gd_k * Nk, gd_k = gd_km1 * Nkm1, and
  -- δ.num = δ * δ.den, then ring.
  have hidentity :
      (δ.den : Rat) *
          ((gd_k1 : Rat) * (gd_km1 : Rat) + (gd_k : Rat) ^ 2 * μ ^ 2) -
        (δ.num : Rat) * (gd_k : Rat) ^ 2 =
      P * ((Nk + Nkm1 * μ * μ) - δ * Nkm1) := by
    have hμ_sq : μ ^ 2 = μ * μ := sq μ
    rw [hP_def, ← hNk_mul, ← hNkm1_mul, ← hδmul, hμ_sq]
    ring
  -- Convert both sides to "≤ 0" form and use the identity.
  constructor
  · intro hint
    have hLHS_ge :
        0 ≤ (δ.den : Rat) *
              ((gd_k1 : Rat) * (gd_km1 : Rat) + (gd_k : Rat) ^ 2 * μ ^ 2) -
            (δ.num : Rat) * (gd_k : Rat) ^ 2 := by linarith
    rw [hidentity] at hLHS_ge
    have hdiff_nn :
        0 ≤ (Nk + Nkm1 * μ * μ) - δ * Nkm1 :=
      (mul_nonneg_iff_of_pos_left hP_pos).mp hLHS_ge
    linarith
  · intro hrat
    have hdiff_nn : 0 ≤ (Nk + Nkm1 * μ * μ) - δ * Nkm1 := by linarith
    have hLHS_ge :
        0 ≤ (δ.den : Rat) *
              ((gd_k1 : Rat) * (gd_km1 : Rat) + (gd_k : Rat) ^ 2 * μ ^ 2) -
            (δ.num : Rat) * (gd_k : Rat) ^ 2 := by
      rw [hidentity]
      exact mul_nonneg (le_of_lt hP_pos) hdiff_nn
    linarith

end HexLLLMathlib
