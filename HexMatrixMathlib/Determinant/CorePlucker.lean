module

public import HexMatrixMathlib.Determinant.CoreTransport
import all HexMatrixMathlib.Determinant.CoreTransport

public section

namespace HexMatrixMathlib
universe u v
variable {R : Type u} {n : Nat}
theorem ordered_four_det_mul_det_setRow_setRow_eq_cofactorRowPairing_mul_sub
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let M := Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    let r2 : Fin (n + 1) := ⟨p2.val - 1, by have := q.isLt; omega⟩
    let r3 : Fin (n + 1) := ⟨p3.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.det M *
        Hex.Matrix.det (Hex.Matrix.setRow (Hex.Matrix.setRow M r2 B[p1]) r3 B[q]) =
      Hex.Matrix.cofactorRowPairing M r2 B[p1] *
          Hex.Matrix.cofactorRowPairing M r3 B[q] -
        Hex.Matrix.cofactorRowPairing M r3 B[p1] *
          Hex.Matrix.cofactorRowPairing M r2 B[q] := by
  intro M r2 r3
  exact det_mul_det_setRow_setRow_eq_cofactorRowPairing_mul_sub M r2 r3 B[p1] B[q]
    (ordered_four_row_p2_ne_p3 p1 p2 p3 q h12 h23 h3q)

/-- The ordered base minor in the four-row Plucker setup is exactly the
corresponding `nDet`. This theorem gives downstream rewrites a named surface
instead of unfolding `Hex.Matrix.nDet` locally. -/
theorem ordered_four_det_nMatrix_eq_nDet
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let hp1q : p1.val < q.val := Nat.lt_trans h12 (Nat.lt_trans h23 h3q)
    Hex.Matrix.det (Hex.Matrix.nMatrix B p1 q hp1q) =
      Hex.Matrix.nDet B p1 q hp1q := by
  intro hp1q
  rfl

/-- Ordered two-row replacement identity after rewriting each cofactor-row
pairing as the determinant of the corresponding row replacement.

This is the determinant-only form needed before the remaining signed
row-permutation transports to `nDet` minors. -/
theorem ordered_four_det_mul_det_setRow_setRow_eq_det_setRow_mul_sub
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h3q : p3.val < q.val) :
    let M := Hex.Matrix.nMatrix B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q))
    let r2 : Fin (n + 1) := ⟨p2.val - 1, by have := q.isLt; omega⟩
    let r3 : Fin (n + 1) := ⟨p3.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.det M *
        Hex.Matrix.det (Hex.Matrix.setRow (Hex.Matrix.setRow M r2 B[p1]) r3 B[q]) =
      Hex.Matrix.det (Hex.Matrix.setRow M r2 B[p1]) *
          Hex.Matrix.det (Hex.Matrix.setRow M r3 B[q]) -
        Hex.Matrix.det (Hex.Matrix.setRow M r3 B[p1]) *
          Hex.Matrix.det (Hex.Matrix.setRow M r2 B[q]) := by
  intro M r2 r3
  rw [← ordered_four_cofactorRowPairing_p2_p1_eq_det_setRow B p1 p2 p3 q h12 h23 h3q]
  rw [← ordered_four_cofactorRowPairing_p3_q_eq_det_setRow B p1 p2 p3 q h12 h23 h3q]
  rw [← ordered_four_cofactorRowPairing_p3_p1_eq_det_setRow B p1 p2 p3 q h12 h23 h3q]
  rw [← ordered_four_cofactorRowPairing_p2_q_eq_det_setRow B p1 p2 p3 q h12 h23 h3q]
  exact ordered_four_det_mul_det_setRow_setRow_eq_cofactorRowPairing_mul_sub
    B p1 p2 p3 q h12 h23 h3q

/-! ### Double-row replacement transport to `nDet B p2 p3`

The double `setRow` matrix `setRow (setRow M r2 B[p1]) r3 B[q]` (with
`M = nMatrix B p1 q`, `r2 = ⟨p2.val - 1, _⟩`, `r3 = ⟨p3.val - 1, _⟩`)
shares the same row content as `nMatrix B p2 p3`, just permuted: `B[p1]` is
moved up from position `p1.val` to position `p2.val - 1`, and `B[q]` is
moved down from position `q.val - 2` to position `p3.val - 1`. The
resulting permutation is the product of two disjoint cycles
`cycleAhead p1.val (p2.val - p1.val - 1)` and
`cycleBehind (p3.val - 1) (q.val - p3.val - 1)`, with combined sign
`(-1) ^ (p2.val - p1.val - 1 + (q.val - p3.val - 1))`.
-/

private theorem matrixEquiv_double_setRow_eq_submatrix_nMatrix
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) (h3q : p3.val < q.val) :
    let h1q : p1.val < q.val := Nat.lt_trans h12 (Nat.lt_trans h23 h3q)
    let M := Hex.Matrix.nMatrix B p1 q h1q
    let r2 : Fin (n + 1) := ⟨p2.val - 1, by have := q.isLt; omega⟩
    let r3 : Fin (n + 1) := ⟨p3.val - 1, by have := q.isLt; omega⟩
    let m1 : Nat := p2.val - p1.val - 1
    let m2 : Nat := q.val - p3.val - 1
    let hm1 : p1.val + m1 < n + 1 := by have := q.isLt; omega
    let hm2 : (p3.val - 1) + m2 < n + 1 := by have := q.isLt; omega
    let σ : Equiv.Perm (Fin (n + 1)) :=
      OrderedFourShift.cycleAhead (n := n) p1.val m1 hm1 *
        OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2
    matrixEquiv (Hex.Matrix.setRow (Hex.Matrix.setRow M r2 B[p1]) r3 B[q]) =
      (matrixEquiv (Hex.Matrix.nMatrix B p2 p3 h23)).submatrix σ id := by
  intro h1q M r2 r3 m1 m2 hm1 hm2 σ
  ext i j
  show (Hex.Matrix.setRow (Hex.Matrix.setRow M r2 B[p1]) r3 B[q])[i][j] =
    (Hex.Matrix.nMatrix B p2 p3 h23)[σ i][j]
  -- Constants from the four indices.
  have hr2_val : r2.val = p2.val - 1 := rfl
  have hr3_val : r3.val = p3.val - 1 := rfl
  have hm1_val : m1 = p2.val - p1.val - 1 := rfl
  have hm2_val : m2 = q.val - p3.val - 1 := rfl
  have hr2_ne_r3 : r2 ≠ r3 := by
    intro he
    have hv : r2.val = r3.val := congrArg Fin.val he
    rw [hr2_val, hr3_val] at hv
    omega
  -- σ x is cycleAhead applied to (cycleBehind x) under Mathlib's perm-mul.
  have hσ_apply : ∀ x : Fin (n + 1), σ x =
      OrderedFourShift.cycleAhead (n := n) p1.val m1 hm1
        (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 x) := fun _ => rfl
  -- Helper: B-row congruence under matching Fin (n+3) indices.
  have B_entry_congr :
      ∀ (k1 k2 : Fin (n + 3)), k1 = k2 → B[k1][j] = B[k2][j] := fun k1 k2 h =>
    congrArg (fun (x : Fin (n + 3)) => B[x][j]) h
  by_cases h_below_p1 : i.val < p1.val
  · -- Case A: i.val < p1. σ fixes i; both matrices select B[i.val].
    have h_cb_val : (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 i).val =
        i.val :=
      OrderedFourShift.cycleBehind_val_below (p3.val - 1) m2 hm2 i (by omega)
    have h_cb_eq :
        OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 i = i :=
      Fin.ext h_cb_val
    have hσ_val : (σ i).val = i.val := by
      rw [hσ_apply _, h_cb_eq]
      exact OrderedFourShift.cycleAhead_val_below p1.val m1 hm1 i h_below_p1
    have hir2 : i ≠ r2 := by
      intro he
      have hv : i.val = r2.val := congrArg Fin.val he
      rw [hr2_val] at hv; omega
    have hir3 : i ≠ r3 := by
      intro he
      have hv : i.val = r3.val := congrArg Fin.val he
      rw [hr3_val] at hv; omega
    rw [Hex.Matrix.setRow_row_ne _ r3 i B[q] hir3,
        Hex.Matrix.setRow_row_ne _ r2 i B[p1] hir2]
    show (Hex.Matrix.nMatrix B p1 q h1q)[i][j] =
      (Hex.Matrix.nMatrix B p2 p3 h23)[σ i][j]
    rw [Hex.Matrix.nMatrix_entry, Hex.Matrix.nMatrix_entry]
    apply B_entry_congr; apply Fin.ext
    rw [Hex.Matrix.skipIndex2_val_of_lt_p p1 q h1q i h_below_p1,
        Hex.Matrix.skipIndex2_val_of_lt_p p2 p3 h23 (σ i)
          (by show (σ i).val < p2.val; omega)]
    exact hσ_val.symm
  · by_cases h_at_r2 : i.val = p2.val - 1
    · -- Case B: i = r2. D[i] = B[p1]; σ(r2) has val p1.
      have hir2 : i = r2 := Fin.ext (by rw [hr2_val, h_at_r2])
      have hir3 : i ≠ r3 := by rw [hir2]; exact hr2_ne_r3
      rw [Hex.Matrix.setRow_row_ne _ r3 i B[q] hir3, hir2,
          Hex.Matrix.setRow_get_self M r2 B[p1]]
      -- cycleBehind fixes r2 (r2.val = p2-1 < p3-1)
      have h_cb_val :
          (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 r2).val = r2.val :=
        OrderedFourShift.cycleBehind_val_below (p3.val - 1) m2 hm2 r2
          (by rw [hr2_val]; omega)
      have h_cb_eq :
          OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 r2 = r2 :=
        Fin.ext h_cb_val
      -- cycleAhead at r2 = ⟨p1 + m1, _⟩ sends to ⟨p1, _⟩ (top case).
      have h_r2_top : r2.val = p1.val + m1 := by
        rw [hr2_val, hm1_val]; omega
      have hσ_val : (σ r2).val = p1.val := by
        rw [hσ_apply _, h_cb_eq]
        exact OrderedFourShift.cycleAhead_val_top p1.val m1 hm1 r2 h_r2_top
      show B[p1][j] = (Hex.Matrix.nMatrix B p2 p3 h23)[σ r2][j]
      rw [Hex.Matrix.nMatrix_entry]
      apply B_entry_congr; apply Fin.ext
      show p1.val = (Hex.Matrix.skipIndex2 p2 p3 h23 (σ r2)).val
      have h_σ_lt : (σ r2).val < p2.val := by rw [hσ_val]; exact h12
      rw [Hex.Matrix.skipIndex2_val_of_lt_p p2 p3 h23 (σ r2) h_σ_lt]
      exact hσ_val.symm
    · by_cases h_at_r3 : i.val = p3.val - 1
      · -- Case C: i = r3. D[i] = B[q]; σ(r3) has val q-2.
        have hir3 : i = r3 := Fin.ext (by rw [hr3_val, h_at_r3])
        rw [hir3, Hex.Matrix.setRow_get_self _ r3 B[q]]
        -- cycleBehind at r3 = ⟨p3-1, _⟩ = base sends to ⟨p3-1 + m2, _⟩ = ⟨q-2, _⟩.
        have h_cb_val :
            (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 r3).val =
              p3.val - 1 + m2 :=
          OrderedFourShift.cycleBehind_val_base (p3.val - 1) m2 hm2 r3 hr3_val
        have h_cb_q2 :
            (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 r3).val =
              q.val - 2 := by
          rw [h_cb_val, hm2_val]; omega
        -- cycleAhead fixes value q-2 (above p2-1 = p1 + m1).
        have h_above :
            p1.val + m1 < (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 r3).val := by
          rw [h_cb_q2, hm1_val]; omega
        have hσ_val : (σ r3).val = q.val - 2 := by
          rw [hσ_apply _, OrderedFourShift.cycleAhead_val_above p1.val m1 hm1 _ h_above]
          exact h_cb_q2
        show B[q][j] = (Hex.Matrix.nMatrix B p2 p3 h23)[σ r3][j]
        rw [Hex.Matrix.nMatrix_entry]
        apply B_entry_congr; apply Fin.ext
        show q.val = (Hex.Matrix.skipIndex2 p2 p3 h23 (σ r3)).val
        have h_not_lt : ¬ (σ r3).val < p2.val := by rw [hσ_val]; omega
        have h_not_between : ¬ (σ r3).val + 1 < p3.val := by rw [hσ_val]; omega
        rw [Hex.Matrix.skipIndex2_val_of_ge_q p2 p3 h23 (σ r3) h_not_lt h_not_between]
        rw [hσ_val]; omega
      · -- Remaining sub-cases: i is interior, not r2, not r3.
        have hir2 : i ≠ r2 := by
          intro he
          have hv : i.val = r2.val := congrArg Fin.val he
          rw [hr2_val] at hv; exact h_at_r2 hv
        have hir3 : i ≠ r3 := by
          intro he
          have hv : i.val = r3.val := congrArg Fin.val he
          rw [hr3_val] at hv; exact h_at_r3 hv
        rw [Hex.Matrix.setRow_row_ne _ r3 i B[q] hir3,
            Hex.Matrix.setRow_row_ne _ r2 i B[p1] hir2]
        show (Hex.Matrix.nMatrix B p1 q h1q)[i][j] =
          (Hex.Matrix.nMatrix B p2 p3 h23)[σ i][j]
        rw [Hex.Matrix.nMatrix_entry, Hex.Matrix.nMatrix_entry]
        -- Split on where i.val sits relative to the cycle ranges.
        by_cases h_below_p2 : i.val < p2.val
        · -- Case D: p1 ≤ i.val < p2 - 1. cycleA "in", cycleB fixes. σ(i).val = i.val + 1.
          have h_ge_p1 : p1.val ≤ i.val := by omega
          have h_lt_p2m1 : i.val < p2.val - 1 := by omega
          -- cycleBehind fixes (i.val < p2 ≤ p3 - 1, since p2 < p3 means p2 ≤ p3 - 1).
          have h_cb_val :
              (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 i).val = i.val :=
            OrderedFourShift.cycleBehind_val_below (p3.val - 1) m2 hm2 i
              (by omega)
          have h_cb_eq :
              OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 i = i :=
            Fin.ext h_cb_val
          have h_in_ub : i.val < p1.val + m1 := by rw [hm1_val]; omega
          have hσ_val : (σ i).val = i.val + 1 := by
            rw [hσ_apply _, h_cb_eq]
            exact OrderedFourShift.cycleAhead_val_in p1.val m1 hm1 i h_ge_p1 h_in_ub
          apply B_entry_congr; apply Fin.ext
          have h_not_lt_p1 : ¬ i.val < p1.val := by omega
          have h_between_q : i.val + 1 < q.val := by
            have : p2.val < q.val := Nat.lt_trans h23 h3q
            omega
          rw [Hex.Matrix.skipIndex2_val_of_between p1 q h1q i h_not_lt_p1 h_between_q]
          have h_σi_lt_p2 : (σ i).val < p2.val := by rw [hσ_val]; omega
          rw [Hex.Matrix.skipIndex2_val_of_lt_p p2 p3 h23 (σ i) h_σi_lt_p2]
          exact hσ_val.symm
        · by_cases h_below_p3 : i.val < p3.val
          · -- Case E: p2 ≤ i.val ≤ p3 - 2. Both cycles fix. σ(i) = i.
            have h_ge_p2 : p2.val ≤ i.val := by omega
            have h_lt_p3m1 : i.val < p3.val - 1 := by omega
            have h_cb_val :
                (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 i).val = i.val :=
              OrderedFourShift.cycleBehind_val_below (p3.val - 1) m2 hm2 i
                (by omega)
            have h_cb_eq :
                OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 i = i :=
              Fin.ext h_cb_val
            have h_above_a1 : p1.val + m1 < i.val := by rw [hm1_val]; omega
            have hσ_val : (σ i).val = i.val := by
              rw [hσ_apply _, h_cb_eq]
              exact OrderedFourShift.cycleAhead_val_above p1.val m1 hm1 i h_above_a1
            apply B_entry_congr; apply Fin.ext
            have h_not_lt_p1 : ¬ i.val < p1.val := by omega
            have h_between_q : i.val + 1 < q.val := by
              have h3lt : p3.val < q.val := h3q
              omega
            rw [Hex.Matrix.skipIndex2_val_of_between p1 q h1q i h_not_lt_p1 h_between_q]
            have h_σi_ge_p2 : ¬ (σ i).val < p2.val := by rw [hσ_val]; omega
            have h_σi_lt_p3 : (σ i).val + 1 < p3.val := by rw [hσ_val]; omega
            rw [Hex.Matrix.skipIndex2_val_of_between p2 p3 h23 (σ i)
                  h_σi_ge_p2 h_σi_lt_p3]
            rw [hσ_val]
          · by_cases h_below_qm1 : i.val < q.val - 1
            · -- Case F: p3 ≤ i.val ≤ q - 2. cycleA fixes; cycleB "in". σ(i).val = i.val - 1.
              have h_ge_p3 : p3.val ≤ i.val := by omega
              have h_lt_qm1 : i.val ≤ q.val - 2 := by omega
              have h_cb_lb : p3.val - 1 < i.val := by omega
              have h_cb_ub : i.val ≤ p3.val - 1 + m2 := by rw [hm2_val]; omega
              have h_cb_val :
                  (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 i).val =
                    i.val - 1 :=
                OrderedFourShift.cycleBehind_val_in (p3.val - 1) m2 hm2 i h_cb_lb h_cb_ub
              have h_above_a1 :
                  p1.val + m1 <
                    (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 i).val := by
                rw [h_cb_val, hm1_val]; omega
              have hσ_val : (σ i).val = i.val - 1 := by
                rw [hσ_apply _]
                rw [OrderedFourShift.cycleAhead_val_above p1.val m1 hm1 _ h_above_a1]
                exact h_cb_val
              apply B_entry_congr; apply Fin.ext
              have h_not_lt_p1 : ¬ i.val < p1.val := by omega
              have h_between_q : i.val + 1 < q.val := by omega
              rw [Hex.Matrix.skipIndex2_val_of_between p1 q h1q i h_not_lt_p1 h_between_q]
              have h_σi_ge_p2 : ¬ (σ i).val < p2.val := by rw [hσ_val]; omega
              have h_σi_ge_p3 : ¬ (σ i).val + 1 < p3.val := by rw [hσ_val]; omega
              rw [Hex.Matrix.skipIndex2_val_of_ge_q p2 p3 h23 (σ i)
                    h_σi_ge_p2 h_σi_ge_p3]
              rw [hσ_val]; omega
            · -- Case G: i.val ≥ q - 1. Both cycles fix. σ(i) = i.
              have h_ge_qm1 : q.val - 1 ≤ i.val := by omega
              have h_cb_val :
                  (OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 i).val = i.val :=
                OrderedFourShift.cycleBehind_val_above (p3.val - 1) m2 hm2 i
                  (by rw [hm2_val]; omega)
              have h_cb_eq :
                  OrderedFourShift.cycleBehind (n := n) (p3.val - 1) m2 hm2 i = i :=
                Fin.ext h_cb_val
              have h_above_a1 : p1.val + m1 < i.val := by rw [hm1_val]; omega
              have hσ_val : (σ i).val = i.val := by
                rw [hσ_apply _, h_cb_eq]
                exact OrderedFourShift.cycleAhead_val_above p1.val m1 hm1 i h_above_a1
              apply B_entry_congr; apply Fin.ext
              have h_not_lt_p1 : ¬ i.val < p1.val := by omega
              have h_not_between_q : ¬ i.val + 1 < q.val := by omega
              rw [Hex.Matrix.skipIndex2_val_of_ge_q p1 q h1q i h_not_lt_p1 h_not_between_q]
              have h_σi_ge_p2 : ¬ (σ i).val < p2.val := by rw [hσ_val]; omega
              have h_σi_ge_p3 : ¬ (σ i).val + 1 < p3.val := by rw [hσ_val]; omega
              rw [Hex.Matrix.skipIndex2_val_of_ge_q p2 p3 h23 (σ i)
                    h_σi_ge_p2 h_σi_ge_p3]
              rw [hσ_val]

/-- Determinant-level transport for the ordered four-row double `setRow`:
for `p1 < p2 < p3 < q`, replacing rows `r2 := ⟨p2.val - 1, _⟩` and
`r3 := ⟨p3.val - 1, _⟩` of `nMatrix B p1 q` by `B[p1]` and `B[q]` respectively
produces the signed `nDet B p2 p3` minor with combined sign
`(-1) ^ (p2.val - p1.val - 1 + (q.val - p3.val - 1))`. -/
theorem det_double_setRow_eq_pow_mul_nDet
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) (h3q : p3.val < q.val) :
    let h1q : p1.val < q.val := Nat.lt_trans h12 (Nat.lt_trans h23 h3q)
    let M := Hex.Matrix.nMatrix B p1 q h1q
    let r2 : Fin (n + 1) := ⟨p2.val - 1, by have := q.isLt; omega⟩
    let r3 : Fin (n + 1) := ⟨p3.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.det (Hex.Matrix.setRow (Hex.Matrix.setRow M r2 B[p1]) r3 B[q]) =
      (-1 : R) ^ (p2.val - p1.val - 1 + (q.val - p3.val - 1)) *
        Hex.Matrix.nDet B p2 p3 h23 := by
  intro h1q M r2 r3
  have h_sub := matrixEquiv_double_setRow_eq_submatrix_nMatrix B p1 p2 p3 q h12 h23 h3q
  set m1 : Nat := p2.val - p1.val - 1
  set m2 : Nat := q.val - p3.val - 1
  rw [det_eq, h_sub, Matrix.det_permute, Equiv.Perm.sign_mul,
      OrderedFourShift.sign_cycleAhead, OrderedFourShift.sign_cycleBehind,
      ← det_eq]
  show ((((-1 : ℤˣ) ^ m1 * (-1 : ℤˣ) ^ m2 : ℤˣ) : ℤ) : R) *
      Hex.Matrix.det (Hex.Matrix.nMatrix B p2 p3 h23) =
    (-1 : R) ^ (m1 + m2) * Hex.Matrix.nDet B p2 p3 h23
  have h_pow_cast : ∀ k : Nat,
      ((((-1 : ℤˣ)) ^ k : ℤˣ) : R) = (-1 : R) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h_lhs : ((-1 : ℤˣ)) ^ (k + 1) = ((-1 : ℤˣ))^k * (-1 : ℤˣ) := pow_succ _ _
        rw [h_lhs, Units.val_mul, Int.cast_mul, ih, pow_succ]
        simp
  have h_cast :
      ((((-1 : ℤˣ) ^ m1 * (-1 : ℤˣ) ^ m2 : ℤˣ) : ℤ) : R) =
        (-1 : R) ^ (m1 + m2) := by
    rw [Units.val_mul, Int.cast_mul,
        show (((((-1 : ℤˣ)) ^ m1 : ℤˣ) : ℤ) : R) = (-1 : R) ^ m1 from h_pow_cast m1,
        show (((((-1 : ℤˣ)) ^ m2 : ℤˣ) : ℤ) : R) = (-1 : R) ^ m2 from h_pow_cast m2,
        ← pow_add]
  rw [h_cast]
  rfl

/-- Rewrite-ready signed Plucker form: the LHS double-row `setRow` determinant
is identified with the signed `nDet B p2 p3` minor, and the two p1-side
cofactor-row pairings on the RHS are identified with their signed `nDet B p_t q`
minors. The remaining q-side cofactor-row pairings are left in
`cofactorRowPairing` form so the assembly in #6012 can finish them after
the q-row signed transports land. -/
theorem ordered_four_signed_Plucker_p1_side
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) (h3q : p3.val < q.val) :
    let h1q : p1.val < q.val := Nat.lt_trans h12 (Nat.lt_trans h23 h3q)
    let h2q : p2.val < q.val := Nat.lt_trans h23 h3q
    let M := Hex.Matrix.nMatrix B p1 q h1q
    let r2 : Fin (n + 1) := ⟨p2.val - 1, by have := q.isLt; omega⟩
    let r3 : Fin (n + 1) := ⟨p3.val - 1, by have := q.isLt; omega⟩
    Hex.Matrix.nDet B p1 q h1q *
        ((-1 : R) ^ (p2.val - p1.val - 1 + (q.val - p3.val - 1)) *
          Hex.Matrix.nDet B p2 p3 h23) =
      ((-1 : R) ^ (p2.val - p1.val - 1) * Hex.Matrix.nDet B p2 q h2q) *
          Hex.Matrix.cofactorRowPairing M r3 B[q] -
        ((-1 : R) ^ (p3.val - p1.val - 1) * Hex.Matrix.nDet B p3 q h3q) *
          Hex.Matrix.cofactorRowPairing M r2 B[q] := by
  intro h1q h2q M r2 r3
  have h_plucker :=
    ordered_four_det_mul_det_setRow_setRow_eq_cofactorRowPairing_mul_sub
      B p1 p2 p3 q h12 h23 h3q
  dsimp only at h_plucker
  have h_double := det_double_setRow_eq_pow_mul_nDet B p1 p2 p3 q h12 h23 h3q
  dsimp only at h_double
  have h_p2_p1 :=
    ordered_four_cofactorRowPairing_p2_p1_eq_pow_mul_nDet B p1 p2 p3 q h12 h23 h3q
  dsimp only at h_p2_p1
  have h_p3_p1 :=
    ordered_four_cofactorRowPairing_p3_p1_eq_pow_mul_nDet B p1 p2 p3 q h12 h23 h3q
  dsimp only at h_p3_p1
  -- LHS: det M = nDet B p1 q (definitional), and det of the double setRow
  -- is the signed nDet B p2 p3.
  rw [show (Hex.Matrix.det M : R) = Hex.Matrix.nDet B p1 q h1q from rfl,
      h_double, h_p2_p1, h_p3_p1] at h_plucker
  exact h_plucker

/-- Raw ordered four-row `nDet` Plucker kernel. For `p1 < p2 < p3 < q`, the
canonical three-term Grassmann-Plucker identity holds among the six
ordered `nDet` minors of `B`. The proof substitutes the q-side cofactor-row
pairings in `ordered_four_signed_Plucker_p1_side` to obtain a
fully-signed nDet identity, then cancels the common
`(-1) ^ (p2.val - p1.val - 1 + (q.val - p3.val - 1))` factor by squaring it. -/
theorem det_plucker_three_term_nDet_of_ordered_four
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) (h3q : p3.val < q.val) :
    Hex.Matrix.nDet B p2 p3 h23 *
        Hex.Matrix.nDet B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)) -
      Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) *
          Hex.Matrix.nDet B p2 q (Nat.lt_trans h23 h3q) +
      Hex.Matrix.nDet B p1 p2 h12 *
        Hex.Matrix.nDet B p3 q h3q = 0 := by
  have hp1 := ordered_four_signed_Plucker_p1_side B p1 p2 p3 q h12 h23 h3q
  dsimp only at hp1
  have hp2q :=
    ordered_four_cofactorRowPairing_p2_q_eq_pow_mul_nDet B p1 p2 p3 q h12 h23 h3q
  have hp3q :=
    ordered_four_cofactorRowPairing_p3_q_eq_pow_mul_nDet B p1 p2 p3 q h12 h23 h3q
  dsimp only at hp2q hp3q
  rw [hp2q, hp3q] at hp1
  -- After the rewrites, hp1 is
  --   nDet p1 q * (e * nDet p2 p3) =
  --     ((-1)^s12 * nDet p2 q) * ((-1)^s3q * nDet p1 p3) -
  --     ((-1)^s13 * nDet p3 q) * ((-1)^s2q * nDet p1 p2)
  -- with e := (-1)^(s12 + s3q) and s_ij := p_j.val - p_i.val - 1.
  set s12 : Nat := p2.val - p1.val - 1 with hs12_def
  set s13 : Nat := p3.val - p1.val - 1 with hs13_def
  set s2q : Nat := q.val - p2.val - 1 with hs2q_def
  set s3q : Nat := q.val - p3.val - 1 with hs3q_def
  set e : R := (-1 : R) ^ (s12 + s3q) with he_def
  -- Parity equivalence: (s13 + s2q) and (s12 + s3q) differ by 2 * (p3 - p2).
  have hparity_diff : s13 + s2q = (s12 + s3q) + 2 * (p3.val - p2.val) := by
    show (p3.val - p1.val - 1) + (q.val - p2.val - 1) =
        ((p2.val - p1.val - 1) + (q.val - p3.val - 1)) + 2 * (p3.val - p2.val)
    omega
  have hparity_eq : (-1 : R) ^ (s13 + s2q) = e := by
    rw [hparity_diff, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  -- (-1)^k * (-1)^k = 1.
  have h_sq : e * e = 1 := by
    show (-1 : R) ^ (s12 + s3q) * (-1 : R) ^ (s12 + s3q) = 1
    rw [← pow_add, show (s12 + s3q) + (s12 + s3q) = 2 * (s12 + s3q) from
        (Nat.two_mul (s12 + s3q)).symm, pow_mul, neg_one_sq, one_pow]
  -- Repackage hp1 to expose `e` as a common factor on both sides.
  -- LHS: nDet p1 q * (e * nDet p2 p3) = e * (nDet p1 q * nDet p2 p3)
  -- RHS term 1: ((-1)^s12 * nDet p2 q) * ((-1)^s3q * nDet p1 p3)
  --           = e * (nDet p2 q * nDet p1 p3)
  -- RHS term 2: ((-1)^s13 * nDet p3 q) * ((-1)^s2q * nDet p1 p2)
  --           = (-1)^(s13+s2q) * (nDet p3 q * nDet p1 p2)
  --           = e * (nDet p3 q * nDet p1 p2)   (by hparity_eq)
  have hp1' :
      e *
        (Hex.Matrix.nDet B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)) *
          Hex.Matrix.nDet B p2 p3 h23) =
      e *
        (Hex.Matrix.nDet B p2 q (Nat.lt_trans h23 h3q) *
            Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) -
          Hex.Matrix.nDet B p3 q h3q * Hex.Matrix.nDet B p1 p2 h12) := by
    have h_rhs_term1 :
        ((-1 : R) ^ s12 * Hex.Matrix.nDet B p2 q (Nat.lt_trans h23 h3q)) *
            ((-1 : R) ^ s3q *
              Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23)) =
          e *
            (Hex.Matrix.nDet B p2 q (Nat.lt_trans h23 h3q) *
              Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23)) := by
      rw [he_def, pow_add]; ring
    have h_rhs_term2 :
        ((-1 : R) ^ s13 * Hex.Matrix.nDet B p3 q h3q) *
            ((-1 : R) ^ s2q * Hex.Matrix.nDet B p1 p2 h12) =
          e * (Hex.Matrix.nDet B p3 q h3q * Hex.Matrix.nDet B p1 p2 h12) := by
      have : (-1 : R) ^ s13 * (-1 : R) ^ s2q = e := by
        rw [← pow_add]; exact hparity_eq
      calc
        ((-1 : R) ^ s13 * Hex.Matrix.nDet B p3 q h3q) *
            ((-1 : R) ^ s2q * Hex.Matrix.nDet B p1 p2 h12) =
            ((-1 : R) ^ s13 * (-1 : R) ^ s2q) *
              (Hex.Matrix.nDet B p3 q h3q * Hex.Matrix.nDet B p1 p2 h12) := by ring
        _ = e * (Hex.Matrix.nDet B p3 q h3q * Hex.Matrix.nDet B p1 p2 h12) := by
              rw [this]
    have hp1_lhs :
        Hex.Matrix.nDet B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)) *
            (e * Hex.Matrix.nDet B p2 p3 h23) =
          e *
            (Hex.Matrix.nDet B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)) *
              Hex.Matrix.nDet B p2 p3 h23) := by ring
    rw [hp1_lhs, h_rhs_term1, h_rhs_term2, ← mul_sub] at hp1
    exact hp1
  -- Multiply both sides by e and use e * e = 1 to cancel.
  have hp1_cancelled :
      Hex.Matrix.nDet B p1 q (Nat.lt_trans h12 (Nat.lt_trans h23 h3q)) *
          Hex.Matrix.nDet B p2 p3 h23 =
        Hex.Matrix.nDet B p2 q (Nat.lt_trans h23 h3q) *
            Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) -
          Hex.Matrix.nDet B p3 q h3q * Hex.Matrix.nDet B p1 p2 h12 := by
    have hmul := congrArg (e * ·) hp1'
    simp only at hmul
    rw [← mul_assoc e e, ← mul_assoc e e, h_sq, one_mul, one_mul] at hmul
    exact hmul
  -- Rearrange to match the target via commutativity.
  linear_combination hp1_cancelled

private theorem det_plucker_three_term_basisVec_of_lt_p1
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) (hq1 : q.val < p1.val) :
    Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p1 *
        Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p2 *
        Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p3 *
        Hex.Matrix.nDet B p1 p2 h12 = 0 := by
  have hq2 : q.val < p2.val := Nat.lt_trans hq1 h12
  have hq3 : q.val < p3.val := Nat.lt_trans hq2 h23
  have hraw :=
    det_plucker_three_term_nDet_of_ordered_four B q p1 p2 p3 hq1 h12 h23
  rw [Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_gt B p1 q hq1,
      Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_gt B p2 q hq2,
      Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_gt B p3 q hq3]
  linear_combination
    (Hex.Matrix.cofactorSign (R := R)
      (⟨q.val, by have := p1.isLt; omega⟩ : Fin (n + 2)) (Fin.last (n + 1))) *
      hraw

private theorem det_plucker_three_term_basisVec_of_between_p1_p2
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h1q : p1.val < q.val) (hq2 : q.val < p2.val) :
    Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p1 *
        Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p2 *
        Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p3 *
        Hex.Matrix.nDet B p1 p2 h12 = 0 := by
  have hq3 : q.val < p3.val := Nat.lt_trans hq2 h23
  have hraw :=
    det_plucker_three_term_nDet_of_ordered_four B p1 q p2 p3 h1q hq2 h23
  rw [Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_lt B p1 q h1q,
      Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_gt B p2 q hq2,
      Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_gt B p3 q hq3]
  have hrow :
      (⟨q.val, by have := p2.isLt; omega⟩ : Fin (n + 2)) =
        (⟨q.val - 1 + 1, by have := p2.isLt; omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp
    omega
  rw [hrow]
  rw [cofactorSign_consecutive_last_neg (R := R) (n := n + 1) (q.val - 1)
      (by have := p2.isLt; omega)]
  linear_combination
    (Hex.Matrix.cofactorSign (R := R)
      (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 2)) (Fin.last (n + 1))) *
      hraw

private theorem det_plucker_three_term_basisVec_of_between_p2_p3
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (h2q : p2.val < q.val) (hq3 : q.val < p3.val) :
    Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p1 *
        Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p2 *
        Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p3 *
        Hex.Matrix.nDet B p1 p2 h12 = 0 := by
  have h1q : p1.val < q.val := Nat.lt_trans h12 h2q
  have hraw :=
    det_plucker_three_term_nDet_of_ordered_four B p1 p2 q p3 h12 h2q hq3
  rw [Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_lt B p1 q h1q,
      Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_lt B p2 q h2q,
      Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_gt B p3 q hq3]
  have hrow :
      (⟨q.val, by have := p3.isLt; omega⟩ : Fin (n + 2)) =
        (⟨q.val - 1 + 1, by have := p3.isLt; omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp
    omega
  rw [hrow]
  rw [cofactorSign_consecutive_last_neg (R := R) (n := n + 1) (q.val - 1)
      (by have := p3.isLt; omega)]
  linear_combination
    -(Hex.Matrix.cofactorSign (R := R)
      (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 2)) (Fin.last (n + 1))) *
      hraw

private theorem det_plucker_three_term_basisVec_of_gt_p3
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) (h3q : p3.val < q.val) :
    Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p1 *
        Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p2 *
        Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p3 *
        Hex.Matrix.nDet B p1 p2 h12 = 0 := by
  have h1q : p1.val < q.val := Nat.lt_trans h12 (Nat.lt_trans h23 h3q)
  have h2q : p2.val < q.val := Nat.lt_trans h23 h3q
  have hraw :=
    det_plucker_three_term_nDet_of_ordered_four B p1 p2 p3 q h12 h23 h3q
  rw [Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_lt B p1 q h1q,
      Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_lt B p2 q h2q,
      Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_lt B p3 q h3q]
  linear_combination
    (Hex.Matrix.cofactorSign (R := R)
      (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (n + 2)) (Fin.last (n + 1))) *
      hraw

/-- Arbitrary-row basis-vector Plucker coefficient identity for three ordered
rows `p1 < p2 < p3` and a fourth row `q` distinct from them. The proof
transports each order case to the ordered four-row `nDet` kernel and rewrites
the three `mDet` coefficients by basis-vector evaluation. -/
theorem det_plucker_three_term_basisVec_of_ne
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (p1 p2 p3 q : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (hq1 : q ≠ p1) (hq2 : q ≠ p2) (hq3 : q ≠ p3) :
    Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p1 *
        Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p2 *
        Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p3 *
        Hex.Matrix.nDet B p1 p2 h12 = 0 := by
  by_cases hlt1 : q.val < p1.val
  · exact det_plucker_three_term_basisVec_of_lt_p1 B p1 p2 p3 q h12 h23 hlt1
  · have h1q : p1.val < q.val := by
      have hne : q.val ≠ p1.val := by
        intro h
        exact hq1 (Fin.ext h)
      omega
    by_cases hlt2 : q.val < p2.val
    · exact det_plucker_three_term_basisVec_of_between_p1_p2
        B p1 p2 p3 q h12 h23 h1q hlt2
    · have h2q : p2.val < q.val := by
        have hne : q.val ≠ p2.val := by
          intro h
          exact hq2 (Fin.ext h)
        omega
      by_cases hlt3 : q.val < p3.val
      · exact det_plucker_three_term_basisVec_of_between_p2_p3
          B p1 p2 p3 q h12 h23 h2q hlt3
      · have h3q : p3.val < q.val := by
          have hne : q.val ≠ p3.val := by
            intro h
            exact hq3 (Fin.ext h)
          omega
        exact det_plucker_three_term_basisVec_of_gt_p3 B p1 p2 p3 q h12 h23 h3q

private theorem det_plucker_three_term_basisVec_of_eq_p1
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1))
    (p1 p2 p3 : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) p1) p1 *
        Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) p1) p2 *
        Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) p1) p3 *
        Hex.Matrix.nDet B p1 p2 h12 = 0 := by
  rw [Hex.Matrix.mDet_basisVec_eq_zero_of_eq B p1]
  rw [Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_gt B p2 p1 h12]
  rw [Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_gt B p3 p1 (Nat.lt_trans h12 h23)]
  ring

private theorem det_plucker_three_term_basisVec_of_eq_p2
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1))
    (p1 p2 p3 : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) p2) p1 *
        Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) p2) p2 *
        Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) p2) p3 *
        Hex.Matrix.nDet B p1 p2 h12 = 0 := by
  rw [Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_lt B p1 p2 h12]
  rw [Hex.Matrix.mDet_basisVec_eq_zero_of_eq B p2]
  rw [Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_gt B p3 p2 h23]
  have hrow :
      (⟨p2.val, by have := p3.isLt; omega⟩ : Fin (n + 2)) =
        (⟨p2.val - 1 + 1, by have := p3.isLt; omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp
    omega
  rw [hrow]
  rw [cofactorSign_consecutive_last_neg (R := R) (n := n + 1) (p2.val - 1)
      (by have := p3.isLt; omega)]
  ring

private theorem det_plucker_three_term_basisVec_of_eq_p3
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1))
    (p1 p2 p3 : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) p3) p1 *
        Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) p3) p2 *
        Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) p3) p3 *
        Hex.Matrix.nDet B p1 p2 h12 = 0 := by
  rw [Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_lt B p1 p3 (Nat.lt_trans h12 h23)]
  rw [Hex.Matrix.mDet_basisVec_eq_signed_nDet_of_lt B p2 p3 h23]
  rw [Hex.Matrix.mDet_basisVec_eq_zero_of_eq B p3]
  ring

private theorem foldl_det_sum_congr {R : Type u} [Add R] {β : Type v}
    (xs : List β) (f g : β → R) (z : R)
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.foldl (fun acc x => acc + f x) z =
      xs.foldl (fun acc x => acc + g x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      apply ih
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

private theorem foldl_det_sum_mul_left {R : Type u} [CommRing R] {β : Type v}
    (xs : List β) (c : R) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc + c * f x) (c * z) =
      c * xs.foldl (fun acc x => acc + f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← show c * (z + f x) = c * z + c * f x by ring]
      exact ih (z + f x)

private theorem foldl_det_sum_mul_left_zero {R : Type u} [CommRing R]
    {β : Type v} (xs : List β) (c : R) (f : β → R) :
    xs.foldl (fun acc x => acc + c * f x) 0 =
      c * xs.foldl (fun acc x => acc + f x) 0 := by
  have hzero : c * 0 = 0 := by ring
  simpa [hzero] using (foldl_det_sum_mul_left (R := R) xs c f 0)

private theorem foldl_det_sum_mul_right_zero {R : Type u} [CommRing R]
    {β : Type v} (xs : List β) (f : β → R) (c : R) :
    xs.foldl (fun acc x => acc + f x * c) 0 =
      xs.foldl (fun acc x => acc + f x) 0 * c := by
  calc
    xs.foldl (fun acc x => acc + f x * c) 0 =
        xs.foldl (fun acc x => acc + c * f x) 0 := by
          apply foldl_det_sum_congr
          intro x _hmem
          ring
    _ = c * xs.foldl (fun acc x => acc + f x) 0 := by
          exact foldl_det_sum_mul_left_zero xs c f
    _ = xs.foldl (fun acc x => acc + f x) 0 * c := by
          ring

private theorem foldl_det_sum_sub_add_zero_of_body_zero
    {R : Type u} [CommRing R] {β : Type v}
    (xs : List β) (f g h : β → R) (a b c : R)
    (hacc : a - b + c = 0)
    (hall : ∀ x, x ∈ xs → f x - g x + h x = 0) :
    xs.foldl (fun acc x => acc + f x) a -
      xs.foldl (fun acc x => acc + g x) b +
      xs.foldl (fun acc x => acc + h x) c = 0 := by
  induction xs generalizing a b c with
  | nil => exact hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · have hx : f x - g x + h x = 0 := hall x List.mem_cons_self
        linear_combination hacc + hx
      · intro y hy
        exact hall y (List.mem_cons_of_mem x hy)

private theorem det_plucker_three_term_of_basisVec
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (v : Vector R (n + 3))
    (p1 p2 p3 : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val)
    (hbasis : ∀ q : Fin (n + 3),
      Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p1 *
          Hex.Matrix.nDet B p2 p3 h23 -
        Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p2 *
          Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
        Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p3 *
          Hex.Matrix.nDet B p1 p2 h12 = 0) :
    Hex.Matrix.mDet B v p1 * Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B v p2 * Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B v p3 * Hex.Matrix.nDet B p1 p2 h12 = 0 := by
  rw [Hex.Matrix.mDet_eq_sum_basisVec B v p1]
  rw [Hex.Matrix.mDet_eq_sum_basisVec B v p2]
  rw [Hex.Matrix.mDet_eq_sum_basisVec B v p3]
  rw [← foldl_det_sum_mul_right_zero (List.finRange (n + 3))
      (fun q => v[q] * Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p1)
      (Hex.Matrix.nDet B p2 p3 h23)]
  rw [← foldl_det_sum_mul_right_zero (List.finRange (n + 3))
      (fun q => v[q] * Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p2)
      (Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23))]
  rw [← foldl_det_sum_mul_right_zero (List.finRange (n + 3))
      (fun q => v[q] * Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p3)
      (Hex.Matrix.nDet B p1 p2 h12)]
  apply foldl_det_sum_sub_add_zero_of_body_zero
      (List.finRange (n + 3))
      (fun q => v[q] * Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p1 *
        Hex.Matrix.nDet B p2 p3 h23)
      (fun q => v[q] * Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p2 *
        Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23))
      (fun q => v[q] * Hex.Matrix.mDet B (Hex.Matrix.basisVec (R := R) q) p3 *
        Hex.Matrix.nDet B p1 p2 h12)
      0 0 0
  · ring
  · intro q _hqmem
    have hq := hbasis q
    linear_combination v[q] * hq

/-- Universal three-term Plucker identity for one arbitrary row and three
ordered basis rows, assembled from the ordered four-row `nDet` kernel and the
three equal-row basis-vector cases. -/
theorem det_plucker_three_term
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (v : Vector R (n + 3))
    (p1 p2 p3 : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    Hex.Matrix.mDet B v p1 * Hex.Matrix.nDet B p2 p3 h23 -
      Hex.Matrix.mDet B v p2 * Hex.Matrix.nDet B p1 p3 (Nat.lt_trans h12 h23) +
      Hex.Matrix.mDet B v p3 * Hex.Matrix.nDet B p1 p2 h12 = 0 := by
  apply det_plucker_three_term_of_basisVec B v p1 p2 p3 h12 h23
  intro q
  by_cases hq1 : q = p1
  · subst q
    exact det_plucker_three_term_basisVec_of_eq_p1 B p1 p2 p3 h12 h23
  by_cases hq2 : q = p2
  · subst q
    exact det_plucker_three_term_basisVec_of_eq_p2 B p1 p2 p3 h12 h23
  by_cases hq3 : q = p3
  · subst q
    exact det_plucker_three_term_basisVec_of_eq_p3 B p1 p2 p3 h12 h23
  exact det_plucker_three_term_basisVec_of_ne B p1 p2 p3 q h12 h23 hq1 hq2 hq3

/-- Reindex the `(k+2) × (k+2)` bordered minor so Desnanot-Jacobi deletes the
Bareiss pivot row/column first and the trailing row/column last.

The order is `[k, 0, 1, ..., k-1, k+1]` in the original bordered-minor
coordinates. Applying the same permutation to rows and columns preserves the
determinant and makes the Desnanot interior the previous leading pivot. -/
@[expose]
def bareissDesnanotIndex (k : Nat) : Fin (k + 2) ≃ Fin (k + 2) where
  toFun r :=
    if hzero : r.val = 0 then
      ⟨k, by omega⟩
    else if hlast : r.val = k + 1 then
      Fin.last (k + 1)
    else
      ⟨r.val - 1, by omega⟩
  invFun r :=
    if hk : r.val = k then
      0
    else if hlt : r.val < k then
      ⟨r.val + 1, by omega⟩
    else
      Fin.last (k + 1)
  left_inv r := by
    ext
    dsimp
    by_cases hzero : r.val = 0
    · simp [hzero]
    · by_cases hlast : r.val = k + 1
      · simp [hlast]
      · have hlt : r.val - 1 < k := by omega
        have hne : r.val - 1 ≠ k := by omega
        simp [hzero, hlast, hlt, hne]
        omega
  right_inv r := by
    ext
    dsimp
    by_cases hk : r.val = k
    · simp [hk]
    · by_cases hlt : r.val < k
      · have hsucc_ne_last : r.val + 1 ≠ k + 1 := by omega
        simp [hk, hlt]
      · have hlast : r.val = k + 1 := by omega
        simp [hlast]

@[simp, grind =]
theorem bareissDesnanotIndex_zero (k : Nat) :
    bareissDesnanotIndex k 0 = (⟨k, by omega⟩ : Fin (k + 2)) := by
  rfl

@[simp, grind =]
theorem bareissDesnanotIndex_last (k : Nat) :
    bareissDesnanotIndex k (Fin.last (k + 1)) = Fin.last (k + 1) := by
  simp [bareissDesnanotIndex]

/-- Reindexing a bordered minor by `bareissDesnanotIndex` on both axes does not
change its determinant. -/
theorem det_borderedMinor_bareissDesnanotIndex [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n)
    (i j : Fin n) :
    ((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).det =
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) := by
  rw [Matrix.det_submatrix_equiv_self, ← det_eq]

/-- Desnanot-Jacobi specialized to a Bareiss bordered minor after the row/column
reindexing used by `bareissDesnanotIndex`.

This is the Mathlib determinant identity that later proofs rewrite through
`matrixEquiv_borderedMinor`/`det_borderedMinor_eq_submatrix_det` to obtain the
`hdesnanot` hypothesis for `bareissExactDiv_borderedMinor_of_mul_eq`. -/
theorem desnanot_jacobi_borderedMinor_reindex [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n)
    (i j : Fin n) :
    let M : Matrix (Fin (k + 2)) (Fin (k + 2)) R :=
      (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)
    M.det *
        (M.submatrix (Fin.succAbove 0 ∘ (Fin.last k).succAbove)
          (Fin.succAbove 0 ∘ (Fin.last k).succAbove)).det =
      (M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det *
        (M.submatrix (Fin.last (k + 1)).succAbove
          (Fin.last (k + 1)).succAbove).det -
      (M.submatrix (Fin.succAbove 0) (Fin.last (k + 1)).succAbove).det *
        (M.submatrix (Fin.last (k + 1)).succAbove (Fin.succAbove 0)).det := by
  intro M
  exact desnanot_jacobi M

/-- Exact-division equation for one Bareiss bordered-minor update.

The remaining Mathlib-side recurrence proof can supply `hdesnanot` from the
Desnanot-Jacobi identity; this lemma packages the resulting product identity
as the `hexact` premise expected by `Hex.Matrix.stepMatrix_borderedMinor_update`.
-/
theorem bareissExactDiv_borderedMinor_of_mul_eq
    (source : Hex.Matrix Int n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (prevPivot : Int)
    (hprev_ne : prevPivot ≠ 0)
    (hdesnanot :
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) * prevPivot =
        Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i j) -
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j)) :
    Hex.Matrix.exactDiv
        (Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i j) -
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot =
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) := by
  exact Hex.Matrix.bareissExactDiv_borderedMinor_of_mul_eq
    source k hk hnext i j hi hj prevPivot hprev_ne hdesnanot

/-- Cyclic shift on `Fin (k + 1)` mapping `0 ↦ k`, `r ↦ r - 1` for `r ≥ 1`.

This is the row/column rearrangement induced by `bareissDesnanotIndex k` on the
sub-positions selected by `(Fin.last (k + 1)).succAbove`: it carries the Bareiss
pivot row (originally position `k`) from sub-position `0` back to the trailing
sub-position `k`. The same shift compares `bareissDesnanotIndex k` columns with
the natural bordered-minor column order. Defined as the inverse of Mathlib's
`finRotate (k + 1)` so the sign is available immediately. -/
private def bareissCyclicShift (k : Nat) : Fin (k + 1) ≃ Fin (k + 1) :=
  (finRotate (k + 1)).symm

@[simp]
private theorem bareissCyclicShift_apply_zero (k : Nat) :
    bareissCyclicShift k 0 = (Fin.last k : Fin (k + 1)) := by
  show (finRotate (k + 1)).symm 0 = Fin.last k
  rw [Equiv.symm_apply_eq]
  exact finRotate_last.symm

private theorem bareissCyclicShift_apply_of_pos (k : Nat) (r : Fin (k + 1))
    (h : 0 < r.val) :
    bareissCyclicShift k r = (⟨r.val - 1, by omega⟩ : Fin (k + 1)) := by
  have hne : r ≠ 0 := by
    intro h_eq
    rw [h_eq] at h
    exact absurd h (Nat.lt_irrefl _)
  have : NeZero (k + 1) := ⟨Nat.succ_ne_zero _⟩
  ext
  show ((finRotate (k + 1)).symm r : ℕ) = r.val - 1
  exact coe_finRotate_symm_of_ne_zero hne

/-- Sign of the cyclic shift: `(-1)^k`. -/
private theorem sign_bareissCyclicShift (k : Nat) :
    Equiv.Perm.sign (bareissCyclicShift k) = (-1) ^ k := by
  show Equiv.Perm.sign (finRotate (k + 1)).symm = _
  rw [Equiv.Perm.sign_symm]
  exact sign_finRotate k

/-- The entry formula for a Bareiss-reindexed bordered minor: the position
returned by `bareissDesnanotIndex k s.succ` is either an interior source row
(when `s.val < k`) or the trailing row `i` (when `s.val = k`). -/
private theorem bareissDesnanotIndex_succ_lt (k : Nat) (s : Fin (k + 1))
    (hs : s.val < k) :
    bareissDesnanotIndex k s.succ = (⟨s.val, by omega⟩ : Fin (k + 2)) := by
  show (if hzero : s.succ.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.succ.val = k + 1 then Fin.last (k + 1)
        else ⟨s.succ.val - 1, by omega⟩) = _
  have hzero : s.succ.val ≠ 0 := Nat.succ_ne_zero _
  have hne_last : s.succ.val ≠ k + 1 := by
    show s.val + 1 ≠ k + 1; omega
  rw [dif_neg hzero, dif_neg hne_last]
  ext
  show s.succ.val - 1 = s.val
  simp

private theorem bareissDesnanotIndex_succ_top (k : Nat) (s : Fin (k + 1))
    (hs : s.val = k) :
    bareissDesnanotIndex k s.succ = Fin.last (k + 1) := by
  show (if hzero : s.succ.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.succ.val = k + 1 then Fin.last (k + 1)
        else ⟨s.succ.val - 1, by omega⟩) = _
  have hzero : s.succ.val ≠ 0 := Nat.succ_ne_zero _
  have hlast : s.succ.val = k + 1 := by
    show s.val + 1 = k + 1; omega
  rw [dif_neg hzero, dif_pos hlast]

private theorem bareissDesnanotIndex_castSucc_zero (k : Nat) (s : Fin (k + 1))
    (hs : s.val = 0) :
    bareissDesnanotIndex k s.castSucc = (⟨k, by omega⟩ : Fin (k + 2)) := by
  show (if hzero : s.castSucc.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.castSucc.val = k + 1 then Fin.last (k + 1)
        else ⟨s.castSucc.val - 1, by omega⟩) = _
  have hzero' : s.castSucc.val = 0 := hs
  rw [dif_pos hzero']

private theorem bareissDesnanotIndex_castSucc_pos (k : Nat) (s : Fin (k + 1))
    (hs : 0 < s.val) :
    bareissDesnanotIndex k s.castSucc = (⟨s.val - 1, by omega⟩ : Fin (k + 2)) := by
  have hcv : s.castSucc.val = s.val := rfl
  show (if hzero : s.castSucc.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.castSucc.val = k + 1 then Fin.last (k + 1)
        else ⟨s.castSucc.val - 1, by omega⟩) = _
  have hne_zero : s.castSucc.val ≠ 0 := by rw [hcv]; exact Nat.ne_of_gt hs
  have hne_last : s.castSucc.val ≠ k + 1 := by
    rw [hcv]; exact Nat.ne_of_lt (by have := s.isLt; omega)
  rw [dif_neg hne_zero, dif_neg hne_last]
  ext
  show s.castSucc.val - 1 = s.val - 1
  rw [hcv]

/-- Source-row index returned by `bareissDesnanotIndex k r.succ` from `r : Fin (k+1)`:
`r.val` for interior `r.val < k`, `i` when `r.val = k`. -/
private theorem source_row_of_succ [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r : Fin (k + 1)) :
    ∀ (c : Fin (k + 1)),
      matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.succ) (bareissDesnanotIndex k c.succ) =
      (let rr : Fin n := if hr : r.val < k then ⟨r.val, by omega⟩ else i
       let cc : Fin n := if hc : c.val < k then ⟨c.val, by omega⟩ else j
       source[rr][cc]) := by
  intro c
  have hkn : k < n := Nat.lt_of_succ_lt hnext
  by_cases hr : r.val < k <;> by_cases hc : c.val < k
  · rw [bareissDesnanotIndex_succ_lt k r hr, bareissDesnanotIndex_succ_lt k c hc]
    have hri : (⟨r.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show r.val < k + 1; omega
    have hci : (⟨c.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show c.val < k + 1; omega
    rw [show (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
            (⟨r.val, by omega⟩ : Fin (k + 2)) (⟨c.val, by omega⟩ : Fin (k + 2)) : R) =
          (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
            (⟨r.val, by omega⟩ : Fin (k + 2))][(⟨c.val, by omega⟩ : Fin (k + 2))] from rfl]
    rw [Hex.Matrix.borderedMinor_entry_lt_lt source (k + 1) hnext i j _ _ hri hci]
    simp [hr, hc]
  · have hc_eq : c.val = k := by have := c.isLt; omega
    rw [bareissDesnanotIndex_succ_lt k r hr, bareissDesnanotIndex_succ_top k c hc_eq]
    have hri : (⟨r.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show r.val < k + 1; omega
    rw [show (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
            (⟨r.val, by omega⟩ : Fin (k + 2)) (Fin.last (k + 1)) : R) =
          (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
            (⟨r.val, by omega⟩ : Fin (k + 2))][Fin.last (k + 1)] from rfl]
    rw [Hex.Matrix.borderedMinor_entry_lt_last source (k + 1) hnext i j _ hri]
    simp [hr, hc]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    rw [bareissDesnanotIndex_succ_top k r hr_eq, bareissDesnanotIndex_succ_lt k c hc]
    have hci : (⟨c.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show c.val < k + 1; omega
    rw [show (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
            (Fin.last (k + 1)) (⟨c.val, by omega⟩ : Fin (k + 2)) : R) =
          (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
            Fin.last (k + 1)][(⟨c.val, by omega⟩ : Fin (k + 2))] from rfl]
    rw [Hex.Matrix.borderedMinor_entry_last_lt source (k + 1) hnext i j _ hci]
    simp [hr, hc]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    have hc_eq : c.val = k := by have := c.isLt; omega
    rw [bareissDesnanotIndex_succ_top k r hr_eq, bareissDesnanotIndex_succ_top k c hc_eq]
    rw [show (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
            (Fin.last (k + 1)) (Fin.last (k + 1)) : R) =
          (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
            Fin.last (k + 1)][Fin.last (k + 1)] from rfl]
    rw [Hex.Matrix.borderedMinor_entry_last_last]
    simp [hr, hc]

private theorem source_row_of_borderedMinor [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source k hk i j) r c =
      (let rr : Fin n := if hr : r.val < k then ⟨r.val, by omega⟩ else i
       let cc : Fin n := if hc : c.val < k then ⟨c.val, by omega⟩ else j
       source[rr][cc]) := by
  show (Hex.Matrix.borderedMinor source k hk i j)[r][c] = _
  simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn]

/-- For row positions `r.castSucc` (i.e. column `(Fin.last (k + 1)).succAbove r`),
the entry at `bareissDesnanotIndex k r.castSucc` lands in the interior of the
`(k+2)` bordered minor: source row `k` for `r = 0`, source row `r.val - 1` for
`r.val ≥ 1`. Same for columns. -/
private theorem source_row_of_castSucc [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.castSucc) (bareissDesnanotIndex k c.castSucc) =
      (let rr : Fin n := if r.val = 0 then ⟨k, by omega⟩ else ⟨r.val - 1, by omega⟩
       let cc : Fin n := if c.val = 0 then ⟨k, by omega⟩ else ⟨c.val - 1, by omega⟩
       source[rr][cc]) := by
  by_cases hr : r.val = 0 <;> by_cases hc : c.val = 0
  · rw [bareissDesnanotIndex_castSucc_zero k r hr,
        bareissDesnanotIndex_castSucc_zero k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][(⟨k, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]
  · have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [bareissDesnanotIndex_castSucc_zero k r hr,
        bareissDesnanotIndex_castSucc_pos k c hcpos]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    rw [bareissDesnanotIndex_castSucc_pos k r hrpos,
        bareissDesnanotIndex_castSucc_zero k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][(⟨k, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [bareissDesnanotIndex_castSucc_pos k r hrpos,
        bareissDesnanotIndex_castSucc_pos k c hcpos]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]

/-- Mixed `succ`/`castSucc` source-row helper used for `M_1k`. -/
private theorem source_row_of_succ_castSucc [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.succ) (bareissDesnanotIndex k c.castSucc) =
      (let rr : Fin n := if hr : r.val < k then ⟨r.val, by omega⟩ else i
       let cc : Fin n := if c.val = 0 then ⟨k, by omega⟩ else ⟨c.val - 1, by omega⟩
       source[rr][cc]) := by
  by_cases hr : r.val < k <;> by_cases hc : c.val = 0
  · rw [bareissDesnanotIndex_succ_lt k r hr, bareissDesnanotIndex_castSucc_zero k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val, by omega⟩ : Fin (k + 2))][(⟨k, by omega⟩ : Fin (k + 2))] = _
    have hrle : r.val ≤ k := hr.le
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc, hrle]
  · have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [bareissDesnanotIndex_succ_lt k r hr, bareissDesnanotIndex_castSucc_pos k c hcpos]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val, by omega⟩ : Fin (k + 2))][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    have hrle : r.val ≤ k := hr.le
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc, hrle]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    rw [bareissDesnanotIndex_succ_top k r hr_eq, bareissDesnanotIndex_castSucc_zero k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        Fin.last (k + 1)][(⟨k, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [bareissDesnanotIndex_succ_top k r hr_eq, bareissDesnanotIndex_castSucc_pos k c hcpos]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        Fin.last (k + 1)][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]

/-- Mixed `castSucc`/`succ` source-row helper used for `M_k1`. -/
private theorem source_row_of_castSucc_succ [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.castSucc) (bareissDesnanotIndex k c.succ) =
      (let rr : Fin n := if r.val = 0 then ⟨k, by omega⟩ else ⟨r.val - 1, by omega⟩
       let cc : Fin n := if hc : c.val < k then ⟨c.val, by omega⟩ else j
       source[rr][cc]) := by
  by_cases hr : r.val = 0 <;> by_cases hc : c.val < k
  · rw [bareissDesnanotIndex_castSucc_zero k r hr, bareissDesnanotIndex_succ_lt k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][(⟨c.val, by omega⟩ : Fin (k + 2))] = _
    have hcle : c.val ≤ k := hc.le
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc, hcle]
  · have hc_eq : c.val = k := by have := c.isLt; omega
    rw [bareissDesnanotIndex_castSucc_zero k r hr, bareissDesnanotIndex_succ_top k c hc_eq]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][Fin.last (k + 1)] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    rw [bareissDesnanotIndex_castSucc_pos k r hrpos, bareissDesnanotIndex_succ_lt k c hc]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][(⟨c.val, by omega⟩ : Fin (k + 2))] = _
    have hcle : c.val ≤ k := hc.le
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc, hcle]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hc_eq : c.val = k := by have := c.isLt; omega
    rw [bareissDesnanotIndex_castSucc_pos k r hrpos, bareissDesnanotIndex_succ_top k c hc_eq]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][Fin.last (k + 1)] = _
    simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, hr, hc]

/-- The Fin-valued cyclic shift on `Fin (k+1)` agrees with the
position-indexing-by-cases used in `source_row_of_castSucc`. -/
private theorem fin_n_cyclicShift_eq_castSucc_index (k : Nat) (hk : k < n)
    (r : Fin (k + 1)) :
    (if r.val = 0 then (⟨k, hk⟩ : Fin n) else ⟨r.val - 1, by omega⟩) =
    (if h : (bareissCyclicShift k r).val < k then (⟨(bareissCyclicShift k r).val, by omega⟩ : Fin n)
     else ⟨k, hk⟩) := by
  by_cases hr : r.val = 0
  · have hr0 : r = 0 := Fin.ext hr
    have hbs : bareissCyclicShift k r = (Fin.last k : Fin (k + 1)) := by
      rw [hr0]; exact bareissCyclicShift_apply_zero k
    have hge : ¬ (bareissCyclicShift k r).val < k := by
      rw [hbs]; show ¬ k < k; exact Nat.lt_irrefl _
    rw [if_pos hr, dif_neg hge]
  · have hpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hbs : bareissCyclicShift k r = (⟨r.val - 1, by omega⟩ : Fin (k + 1)) :=
      bareissCyclicShift_apply_of_pos k r hpos
    have hbs_val : (bareissCyclicShift k r).val = r.val - 1 := by rw [hbs]
    have hlt : (bareissCyclicShift k r).val < k := by
      rw [hbs_val]; have := r.isLt; omega
    rw [if_neg hr, dif_pos hlt]
    apply Fin.ext
    show r.val - 1 = (bareissCyclicShift k r).val
    rw [hbs_val]

/-- After reindexing by `bareissDesnanotIndex k`, deleting the last row and
column yields the natural `(k+1)` bordered minor of `source` with the original
pivot row/column position `⟨k, _⟩` (i.e. the leading prefix of `source` of size
`k+1`), reindexed by the cyclic shift `bareissCyclicShift k`. -/
private theorem M_kk_eq_matrixEquiv_borderedMinor_submatrix [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (Fin.last (k + 1))) (Fin.succAbove (Fin.last (k + 1)))) =
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk
        (⟨k, hk⟩ : Fin n) (⟨k, hk⟩ : Fin n))).submatrix
        (bareissCyclicShift k) (bareissCyclicShift k) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) r))
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk ⟨k, hk⟩ ⟨k, hk⟩)
        (bareissCyclicShift k r) (bareissCyclicShift k c)
  simp only [Fin.succAbove_last]
  rw [source_row_of_castSucc source k hnext i j r c,
      source_row_of_borderedMinor source k hk ⟨k, hk⟩ ⟨k, hk⟩
        (bareissCyclicShift k r) (bareissCyclicShift k c)]
  dsimp only
  simp only [fin_n_cyclicShift_eq_castSucc_index k hk r,
             fin_n_cyclicShift_eq_castSucc_index k hk c]

/-- After reindexing by `bareissDesnanotIndex k`, deleting row 0 and the last
column yields the natural `(k+1)` bordered minor with trailing row `i` and
trailing column position `⟨k, _⟩`, with columns reindexed by
`bareissCyclicShift k`. -/
private theorem M_1k_eq_matrixEquiv_borderedMinor_submatrix [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (0 : Fin (k + 2))) (Fin.succAbove (Fin.last (k + 1)))) =
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk i (⟨k, hk⟩ : Fin n))).submatrix
        id (bareissCyclicShift k) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) r))
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk i ⟨k, hk⟩)
        r (bareissCyclicShift k c)
  rw [show Fin.succAbove (0 : Fin (k + 2)) r = r.succ from rfl]
  simp only [Fin.succAbove_last]
  rw [source_row_of_succ_castSucc source k hnext i j r c,
      source_row_of_borderedMinor source k hk i ⟨k, hk⟩ r (bareissCyclicShift k c)]
  dsimp only
  simp only [fin_n_cyclicShift_eq_castSucc_index k hk c]

/-- After reindexing by `bareissDesnanotIndex k`, deleting the last row and
column 0 yields the natural `(k+1)` bordered minor with trailing row position
`⟨k, _⟩` and trailing column `j`, with rows reindexed by
`bareissCyclicShift k`. -/
private theorem M_k1_eq_matrixEquiv_borderedMinor_submatrix [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (Fin.last (k + 1))) (Fin.succAbove (0 : Fin (k + 2)))) =
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk (⟨k, hk⟩ : Fin n) j)).submatrix
        (bareissCyclicShift k) id := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) r))
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk ⟨k, hk⟩ j)
        (bareissCyclicShift k r) c
  rw [show Fin.succAbove (0 : Fin (k + 2)) c = c.succ from rfl]
  simp only [Fin.succAbove_last]
  rw [source_row_of_castSucc_succ source k hnext i j r c,
      source_row_of_borderedMinor source k hk ⟨k, hk⟩ j (bareissCyclicShift k r) c]
  dsimp only
  simp only [fin_n_cyclicShift_eq_castSucc_index k hk r]

/-- The interior `(k × k)` submatrix of the reindexed Bareiss bordered minor:
deleting both row 0 and the last row (and similarly columns) leaves exactly
`matrixEquiv (leadingPrefix source k _)`. -/
private theorem M_interior_eq_matrixEquiv_leadingPrefix [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (0 : Fin (k + 2)) ∘ (Fin.last k).succAbove)
        (Fin.succAbove (0 : Fin (k + 2)) ∘ (Fin.last k).succAbove)) =
      matrixEquiv (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk)) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2))
          ((Fin.last k).succAbove r)))
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2))
          ((Fin.last k).succAbove c))) =
      matrixEquiv (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk)) r c
  -- (last k).succAbove r = r.castSucc, then succAbove 0 of r.castSucc = r.castSucc.succ
  simp only [Fin.succAbove_last, Fin.succAbove_zero]
  -- Now use bareissDesnanotIndex_succ_lt with r.castSucc, since (r.castSucc).val = r.val < k
  have hrlt : (r.castSucc : Fin (k + 1)).val < k := r.isLt
  have hclt : (c.castSucc : Fin (k + 1)).val < k := c.isLt
  rw [bareissDesnanotIndex_succ_lt k r.castSucc hrlt,
      bareissDesnanotIndex_succ_lt k c.castSucc hclt]
  show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
      (⟨(r.castSucc : Fin (k + 1)).val, by omega⟩ : Fin (k + 2))][
      (⟨(c.castSucc : Fin (k + 1)).val, by omega⟩ : Fin (k + 2))] = _
  -- Both indices are < k+1, so use borderedMinor_entry_lt_lt
  show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
      (⟨r.val, by omega⟩ : Fin (k + 2))][
      (⟨c.val, by omega⟩ : Fin (k + 2))] = _
  simp [Hex.Matrix.borderedMinor, Hex.Matrix.ofFn, Hex.Matrix.leadingPrefix,
    show r.val ≤ k from r.isLt.le, show c.val ≤ k from c.isLt.le]

/-- After reindexing the `(k+2)` bordered minor by `bareissDesnanotIndex k`,
deleting row 0 and column 0 yields exactly `matrixEquiv` of the natural
`(k+1)` bordered minor with the same trailing row `i` and column `j`. -/
private theorem M11_eq_matrixEquiv_borderedMinor [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (0 : Fin (k + 2))) (Fin.succAbove (0 : Fin (k + 2)))) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk i j) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) r))
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk i j) r c
  rw [show Fin.succAbove (0 : Fin (k + 2)) r = r.succ from rfl,
      show Fin.succAbove (0 : Fin (k + 2)) c = c.succ from rfl,
      source_row_of_succ source k hnext i j r c,
      source_row_of_borderedMinor source k hk i j r c]

/-- Desnanot-Jacobi specialised to a Bareiss bordered minor: the Mathlib
determinant identity from `desnanot_jacobi_borderedMinor_reindex` translated
back into Hex `borderedMinor`/`leadingPrefix` determinants. This produces the
`hdesnanot` premise expected by `bareissExactDiv_borderedMinor_of_mul_eq` with
`prevPivot` instantiated as `det (leadingPrefix source k _)`. -/
theorem desnanot_jacobi_borderedMinor [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) :
    Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) *
        Hex.Matrix.det (Hex.Matrix.leadingPrefix source k (Nat.le_of_lt hk)) =
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
          (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
        Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i j) -
        Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
          i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
        Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j) := by
  -- Mathlib Desnanot-Jacobi on the reindexed bordered minor.
  have hdj := desnanot_jacobi_borderedMinor_reindex source k hnext i j
  -- Unfold the local `let M := ...` binding in hdj so subsequent rewrites match.
  dsimp only at hdj
  -- Identify each Mathlib determinant with a Hex determinant.
  rw [det_borderedMinor_bareissDesnanotIndex source k hnext i j] at hdj
  rw [M_interior_eq_matrixEquiv_leadingPrefix source k hk hnext i j,
      ← det_eq] at hdj
  rw [M11_eq_matrixEquiv_borderedMinor source k hk hnext i j, ← det_eq] at hdj
  rw [M_kk_eq_matrixEquiv_borderedMinor_submatrix source k hk hnext i j,
      Matrix.det_submatrix_equiv_self, ← det_eq] at hdj
  rw [M_1k_eq_matrixEquiv_borderedMinor_submatrix source k hk hnext i j,
      Matrix.det_permute', ← det_eq] at hdj
  rw [M_k1_eq_matrixEquiv_borderedMinor_submatrix source k hk hnext i j,
      Matrix.det_permute, ← det_eq] at hdj
  -- hdj has the form M.det * Mint.det = M11.det * Mkk.det - (sign σ * X) * (sign σ * Y).
  -- Sign² = 1, so the sign factors cancel.
  have hsign_sq : ((Equiv.Perm.sign (bareissCyclicShift k) : ℤ) : R) *
      ((Equiv.Perm.sign (bareissCyclicShift k) : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
        Int.cast_one]
  -- Rearrange hdj using commutativity (M11 * Mkk = Mkk * M11) and the sign²=1
  -- cancellation (M1k * sign * Mk1 * sign = M1k * Mk1).
  linear_combination hdj -
    (Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i
        (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
        (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j)) * hsign_sq

end HexMatrixMathlib
