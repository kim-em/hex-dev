/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmith.Correctness.Invariant

public section

/-! Loop correctness and the public polynomial Smith form theorems. -/

namespace Hex.PolyMatrix

universe u

open Hex

/-- Shape invariant carried by the structurally bounded outer loop. -/
def LoopShape {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) : Prop := PrefixShape s.work s.pivot

def LoopDone {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) : Prop :=
  s.pivot = min n m ∨ trailingMin s.work s.pivot = none

theorem normalizePivot_pivot_monic {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (k : Nat)
    (hkN : k < n) (hkM : k < m)
    (hp : s.work[((⟨k, hkN⟩ : Fin n), (⟨k, hkM⟩ : Fin m))] ≠ 0) :
    (normalizePivot s k hkN hkM).work[
      ((⟨k, hkN⟩ : Fin n), (⟨k, hkM⟩ : Fin m))].Monic := by
  let p := s.work[((⟨k, hkN⟩ : Fin n), (⟨k, hkM⟩ : Fin m))]
  have hpSize : 0 < p.size := by
    apply Nat.pos_of_ne_zero
    intro hs
    exact hp ((DensePoly.size_eq_zero_iff p).mp hs)
  have hlc : p.leadingCoeff ≠ 0 :=
    DensePoly.leadingCoeff_ne_zero_of_pos_size p hpSize
  have hu : (1 / p.leadingCoeff : F) ≠ 0 := by
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.one_mul]
    intro hz
    exact hlc (Lean.Grind.Field.inv_eq_zero_iff.mp hz)
  unfold normalizePivot
  change (s.work.rowScale (⟨k, hkN⟩ : Fin n)
    (DensePoly.C (1 / p.leadingCoeff)))[
      ((⟨k, hkN⟩ : Fin n), (⟨k, hkM⟩ : Fin m))].Monic
  rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale, ite_eq_left rfl]
  rw [← Matrix.getElem_pair_eq_nested]
  change (DensePoly.C (1 / p.leadingCoeff) * p).Monic
  rw [DensePoly.Monic, DensePoly.leadingCoeff_mul]
  · rw [DensePoly.leadingCoeff_C, Lean.Grind.Field.div_eq_mul_inv,
      Lean.Grind.Semiring.one_mul, Lean.Grind.Field.inv_mul_cancel hlc]
  · rw [DensePoly.size_C_of_ne_zero hu]
    omega
  · exact hpSize
  · rw [DensePoly.leadingCoeff_C, Lean.Grind.Field.div_eq_mul_inv,
      Lean.Grind.Semiring.one_mul, Lean.Grind.Field.inv_mul_cancel hlc]
    exact Hex.one_ne_zero_of_nonzero hlc

theorem normalizePivot_pivot_ne {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (k : Nat)
    (hkN : k < n) (hkM : k < m)
    (hp : s.work[((⟨k, hkN⟩ : Fin n), (⟨k, hkM⟩ : Fin m))] ≠ 0) :
    (normalizePivot s k hkN hkM).work[
      ((⟨k, hkN⟩ : Fin n), (⟨k, hkM⟩ : Fin m))] ≠ 0 := by
  intro hz
  have hm := normalizePivot_pivot_monic s k hkN hkM hp
  rw [hz, DensePoly.Monic, DensePoly.leadingCoeff_zero] at hm
  grind

theorem smithStage_shape {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (ik : Fin n) (jk : Fin m)
    (hp : s.work[(ik, jk)] ≠ 0) (hm : s.work[(ik, jk)].Monic) :
    StageShape (smithStage s ik jk hp) ik jk := by
  induction s, hp using smithStage.induct ik jk with
  | case1 s hp col hc ihCol =>
      rw [smithStage]
      change (clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      simp [hc]
      apply ihCol
      exact clearColumnScan_drop_monic ik jk s (List.finRange n) hp hc
  | case2 s hp col hc row hr ihRow =>
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change (clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
        (List.finRange m)).dropped = true at hr
      simp [hc, hr]
      apply ihRow
      exact clearRowScan_drop_monic ik jk col.state (List.finRange m)
        (clearColumnScan_pivot_ne_zero ik jk s (List.finRange n) hp) hr
  | case3 s hp col hc row hr hb =>
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change ¬(clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
        (List.finRange m)).dropped = true at hr
      change badBlock
        (clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
          (List.finRange m)).state.work ik jk = none at hb
      simp [hc, hr]
      split
      · have hc0 : col.dropped = false := bool_eq_false hc
        have hr0 : row.dropped = false := bool_eq_false hr
        have hpCol := clearColumnScan_pivot_ne_zero
          ik jk s (List.finRange n) hp
        have hpRow := clearRowScan_pivot_ne_zero
          ik jk col.state (List.finRange m) hpCol
        have hmCol : col.state.work[(ik, jk)].Monic := by
          rw [clearColumnScan_row ik jk jk s (List.finRange n) hc0]
          exact hm
        have hmRow : row.state.work[(ik, jk)].Monic := by
          rw [clearRowScan_column ik ik jk col.state (List.finRange m) hr0]
          exact hmCol
        refine ⟨hpRow, hmRow, ?_, ?_, ?_⟩
        · intro i hi
          rw [clearRowScan_column ik i jk col.state (List.finRange m) hr0]
          exact clearColumnScan_zero ik i jk s (List.finRange n) hp
            (List.nodup_finRange n) hi (List.mem_finRange i) hc0
        · intro j hj
          exact clearRowScan_zero ik jk j col.state (List.finRange m) hpCol
            (List.nodup_finRange m) hj (List.mem_finRange j) hr0
        · exact badBlock_none_dvd row.state.work ik jk hb
      · simp_all
  | case4 s hp col hc row hr q hb hc0 hr0 hq hki hkj hpCol hcol0 hcol hrow
      hnot hpRow hpBlock ihBlock =>
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change ¬(clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
        (List.finRange m)).dropped = true at hr
      change badBlock
        (clearRowScan ik jk (clearColumnScan ik jk s (List.finRange n)).state
          (List.finRange m)).state.work ik jk = some q at hb
      simp [hc, hr]
      split
      · simp_all
      · rename_i q' hb'
        have hqq : q' = q := by simp_all
        subst q'
        apply ihBlock
        rw [blockStep_pivot row.state ik q.1 jk q.2 hkj hcol hrow]
        rcases pairStep_pivot_shape row.state.work[(ik, jk)] row.state.work[q] with hz | hm'
        · exact False.elim (pairStep_pivot_ne_zero_left hpRow hz)
        · exact hm'

theorem normalizedStage_shape {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (k : Nat)
    (hkN : k < n) (hkM : k < m)
    (hp : s.work[((⟨k, hkN⟩ : Fin n), (⟨k, hkM⟩ : Fin m))] ≠ 0) :
    StageShape
      (smithStageSafe (normalizePivot s k hkN hkM) ⟨k, hkN⟩ ⟨k, hkM⟩)
      ⟨k, hkN⟩ ⟨k, hkM⟩ := by
  have hp' := normalizePivot_pivot_ne s k hkN hkM hp
  have hm' := normalizePivot_pivot_monic s k hkN hkM hp
  unfold smithStageSafe
  split
  · contradiction
  · exact smithStage_shape _ _ _ hp' hm'

theorem transformValid_smithStageSafe {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    (s : LoopState F n m) (ik : Fin n) (jk : Fin m) (h : TransformValid A s) :
    TransformValid A (smithStageSafe s ik jk) := by
  unfold smithStageSafe
  split
  · exact h
  · apply transformValid_smithStage
    exact h

private theorem movedPivot_eq {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m)
    (ik qi : Fin n) (jk qj : Fin m) :
    (swapCols (swapRows s ik qi) jk qj).work[(ik, jk)] = s.work[(qi, qj)] := by
  change ((s.work.rowSwap ik qi).colSwap jk qj)[(ik, jk)] = _
  rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_colSwap]
  by_cases hj : jk = qj
  · rw [ite_eq_left hj]
    subst qj
    rw [Matrix.getElem_rowSwap]
    by_cases hi : ik = qi <;> simp [hi]
  · rw [ite_eq_right hj, ite_eq_left rfl, Matrix.getElem_rowSwap]
    by_cases hi : ik = qi
    · subst qi; simp
    · simp [hi]

theorem loopShape_smithLoopTotal {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (stages : Nat)
    (h : LoopShape s) : LoopShape (smithLoopTotal s stages) := by
  induction stages generalizing s with
  | zero => exact h
  | succ stages ih =>
      rw [smithLoopTotal]
      split
      · rename_i hkN
        split
        · rename_i hkM
          cases ht : trailingMin s.work s.pivot with
          | none => exact h
          | some q =>
              have hq := trailingMin_bounds s.work s.pivot ht
              let ik : Fin n := ⟨s.pivot, hkN⟩
              let jk : Fin m := ⟨s.pivot, hkM⟩
              let moved := swapCols (swapRows s ik q.1) jk q.2
              let normalized := normalizePivot moved ik.val ik.isLt jk.isLt
              let reduced := smithStageSafe normalized ik jk
              have hpMoved : moved.work[(ik, jk)] ≠ 0 := by
                unfold moved
                rw [movedPivot_eq]
                exact trailingMin_nonzero s.work s.pivot ht
              have hMoved : PrefixShape moved.work s.pivot := by
                unfold moved
                apply prefixShape_swapCols
                · apply prefixShape_swapRows h ik q.1
                  · dsimp [ik]
                    exact Nat.le_refl _
                  · exact hq.1
                · dsimp [jk]
                  exact Nat.le_refl _
                · exact hq.2
              have hNorm : PrefixShape normalized.work s.pivot := by
                unfold normalized
                exact prefixShape_normalizePivot ik.isLt jk.isLt hMoved
              have hReduced : PrefixShape reduced.work s.pivot := by
                unfold reduced
                exact prefixShape_smithStageSafe ik jk rfl rfl hNorm
              have hsReduced : StageShape reduced ik jk := by
                unfold reduced normalized
                exact normalizedStage_shape moved ik.val ik.isLt jk.isLt hpMoved
              have hNext : PrefixShape reduced.work (s.pivot + 1) :=
                PrefixShape.extend hReduced ik jk rfl rfl hsReduced
              apply ih
              unfold LoopShape
              exact hNext
        · exact h
      · exact h

theorem loopShape_runSmith {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m)
    (withTransforms : Bool) : LoopShape (runSmith A withTransforms) := by
  unfold runSmith
  apply loopShape_smithLoopTotal
  unfold LoopShape
  exact prefixShape_zero A

theorem loopDone_smithLoopTotal {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (stages : Nat)
    (hle : s.pivot ≤ min n m) (henough : min n m ≤ s.pivot + stages) :
    LoopDone (smithLoopTotal s stages) := by
  induction stages generalizing s with
  | zero =>
      left
      simp only [smithLoopTotal]
      omega
  | succ stages ih =>
      rw [smithLoopTotal]
      split
      · rename_i hkN
        split
        · rename_i hkM
          cases ht : trailingMin s.work s.pivot with
          | none => exact Or.inr ht
          | some q =>
              apply ih
              · change s.pivot + 1 ≤ min n m
                omega
              · change min n m ≤ (s.pivot + 1) + stages
                omega
        · left
          omega
      · left
        omega

theorem loopDone_runSmith {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m)
    (withTransforms : Bool) : LoopDone (runSmith A withTransforms) := by
  unfold runSmith
  apply loopDone_smithLoopTotal
  · change 0 ≤ min n m
    omega
  · change min n m ≤ 0 + min n m
    omega

theorem loopRank_eq_pivot {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (h : LoopShape s) :
    loopRank s = s.pivot := by
  unfold LoopShape at h
  unfold loopRank
  rw [Nat.min_eq_left (Nat.le_min.mpr ⟨h.le_rows, h.le_cols⟩)]

theorem work_eq_diagMatrix {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m)
    (hshape : LoopShape s) (hdone : LoopDone s) :
    s.work = Matrix.diagMatrix (diagonalVector s) n m := by
  have hrank := loopRank_eq_pivot hshape
  unfold LoopShape at hshape
  apply Matrix.ext_getElem
  intro i j
  by_cases hij : i.val = j.val
  · by_cases hik : i.val < s.pivot
    · rw [Matrix.getElem_diagMatrix_of_eq _ i j hij (by omega)]
      simp [diagonalVector, Matrix.getElem_pair_eq_nested, hij]
      have hiEq : i = (⟨j.val, by omega⟩ : Fin n) := Fin.ext hij
      exact congrArg (fun r : Fin n => s.work[r][j]) hiEq
    · have hgei : s.pivot ≤ i.val := by omega
      have hgej : s.pivot ≤ j.val := by omega
      have hz : s.work[(i, j)] = 0 := by
        rcases hdone with hfull | hnone
        · have : False := by
            have hi := i.isLt
            have hj := j.isLt
            omega
          contradiction
        · exact trailingMin_none_zero s.work s.pivot hnone i j hgei hgej
      rw [Matrix.getElem_pair_eq_nested] at hz
      rw [hz, Matrix.getElem_diagMatrix_of_ge _ i j (by omega)]
  · rw [Matrix.getElem_diagMatrix_of_ne _ i j hij]
    have hz : s.work[(i, j)] = 0 := by
      by_cases hik : i.val < s.pivot
      · exact hshape.row_zero i.val hik i.isLt
          (Nat.lt_of_lt_of_le hik hshape.le_cols) j (by omega)
      · by_cases hjk : j.val < s.pivot
        · exact hshape.col_zero j.val hjk
            (Nat.lt_of_lt_of_le hjk hshape.le_rows) j.isLt i (by omega)
        · have hgei : s.pivot ≤ i.val := by omega
          have hgej : s.pivot ≤ j.val := by omega
          rcases hdone with hfull | hnone
          · have : False := by
              have hi := i.isLt
              have hj := j.isLt
              omega
            contradiction
          · exact trailingMin_none_zero s.work s.pivot hnone i j hgei hgej
    simpa only [Matrix.getElem_pair_eq_nested] using hz

theorem runSmith_work_eq_diagMatrix {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m)
    (withTransforms : Bool) :
    (runSmith A withTransforms).work =
      Matrix.diagMatrix (diagonalVector (runSmith A withTransforms)) n m :=
  work_eq_diagMatrix _ (loopShape_runSmith A withTransforms)
    (loopDone_runSmith A withTransforms)

theorem diagonalVector_monic {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (h : LoopShape s)
    (i : Fin (loopRank s)) : (diagonalVector s)[i].Monic := by
  have hrank := loopRank_eq_pivot h
  unfold LoopShape at h
  change ((diagonalVector s)[i.val]'i.isLt).Monic
  unfold diagonalVector
  rw [Vector.getElem_ofFn]
  apply h.monic i.val
  · omega

theorem diagonalVector_chain {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {s : LoopState F n m} (h : LoopShape s)
    (i : Nat) (hi : i + 1 < loopRank s) :
    (diagonalVector s)[i]'(by omega) ∣ (diagonalVector s)[i + 1] := by
  have hrank := loopRank_eq_pivot h
  unfold LoopShape at h
  unfold diagonalVector
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  apply h.future_dvd i
  · omega
  · change i ≤ i + 1
    omega
  · change i ≤ i + 1
    omega

theorem transformValid_meta {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} {A : Matrix (DensePoly F) n m} {s : LoopState F n m}
    (pivot : Nat) (h : TransformValid A s) :
    TransformValid A { s with pivot } := h

theorem transformValid_smithLoopTotal {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    (s : LoopState F n m) (stages : Nat) (h : TransformValid A s) :
    TransformValid A (smithLoopTotal s stages) := by
  induction stages generalizing s with
  | zero => exact h
  | succ stages ih =>
      rw [smithLoopTotal]
      split
      · rename_i hkN
        split
        · rename_i hkM
          cases ht : trailingMin s.work s.pivot
          · exact h
          · rename_i q
            dsimp only
            apply ih
            apply transformValid_meta
            apply transformValid_smithStageSafe
            apply transformValid_normalizePivot
            · rw [movedPivot_eq]
              exact trailingMin_nonzero s.work s.pivot ht
            · apply transformValid_swapCols
              apply transformValid_swapRows
              exact h
        · exact h
      · exact h

theorem transformValid_runSmith_true {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    TransformValid A (runSmith A true) := by
  unfold runSmith
  apply transformValid_smithLoopTotal
  simp only [TransformValid]
  rw [show polyIdentity (F := F) n = Matrix.identity n from polyIdentity_eq_identity n]
  rw [show polyIdentity (F := F) m = Matrix.identity m from polyIdentity_eq_identity m]
  simp

/- Transform erasure

The transform-free and transform-accumulating entry points execute exactly the
same matrix algorithm.  The following commuting lemmas make that fact
explicit, rather than appealing to uniqueness of Smith normal form. -/

@[expose] def eraseTransforms {F : Type u} [Zero F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) : LoopState F n m :=
  { s with transforms := none }

@[simp] theorem eraseTransforms_work {F : Type u} [Zero F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) :
    (eraseTransforms s).work = s.work := rfl

@[simp] theorem eraseTransforms_pivot {F : Type u} [Zero F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) :
    (eraseTransforms s).pivot = s.pivot := rfl

@[simp] theorem eraseTransforms_map {F : Type u} [Zero F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m)
    (f : Transforms F n m → Transforms F n m) :
    eraseTransforms (mapTransforms s f) = eraseTransforms s := by
  cases s
  rfl

@[simp] theorem eraseTransforms_swapRows {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (i j : Fin n) :
    eraseTransforms (swapRows s i j) = swapRows (eraseTransforms s) i j := by
  cases s
  rfl

@[simp] theorem eraseTransforms_swapCols {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (i j : Fin m) :
    eraseTransforms (swapCols s i j) = swapCols (eraseTransforms s) i j := by
  cases s
  rfl

@[simp] theorem eraseTransforms_scaleRow {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (i : Fin n)
    (c cinv : DensePoly F) :
    eraseTransforms (scaleRow s i c cinv) =
      scaleRow (eraseTransforms s) i c cinv := by
  cases s
  rfl

@[simp] theorem eraseTransforms_addRow {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (src dst : Fin n)
    (c : DensePoly F) :
    eraseTransforms (addRow s src dst c) =
      addRow (eraseTransforms s) src dst c := by
  cases s
  rfl

@[simp] theorem eraseTransforms_addCol {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (src dst : Fin m)
    (c : DensePoly F) :
    eraseTransforms (addCol s src dst c) =
      addCol (eraseTransforms s) src dst c := by
  cases s
  rfl

@[simp] theorem eraseTransforms_bezoutRows {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (i j : Fin n)
    (e : PairStep F) :
    eraseTransforms (bezoutRows s i j e) =
      bezoutRows (eraseTransforms s) i j e := by
  cases s
  rfl

@[simp] theorem eraseTransforms_bezoutCols {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (i j : Fin m)
    (e : PairStep F) :
    eraseTransforms (bezoutCols s i j e) =
      bezoutCols (eraseTransforms s) i j e := by
  cases s
  rfl

@[expose] def eraseScan {F : Type u} [Zero F] [DecidableEq F]
    {n m : Nat} (r : ScanResult F n m) : ScanResult F n m :=
  { state := eraseTransforms r.state, dropped := r.dropped }

theorem eraseScan_clearColumnScan {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (ik : Fin n) (jk : Fin m)
    (s : LoopState F n m) (is : List (Fin n)) :
    eraseScan (clearColumnScan ik jk s is) =
      clearColumnScan ik jk (eraseTransforms s) is := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
      rw [clearColumnScan, clearColumnScan]
      split
      · exact ih _
      · dsimp only [eraseTransforms_work]
        split
        · exact ih _
        · split
          · simpa only [eraseTransforms_addRow] using ih (addRow s ik i _)
          · simp only [eraseScan, eraseTransforms_bezoutRows]

theorem eraseScan_clearRowScan {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (ik : Fin n) (jk : Fin m)
    (s : LoopState F n m) (js : List (Fin m)) :
    eraseScan (clearRowScan ik jk s js) =
      clearRowScan ik jk (eraseTransforms s) js := by
  induction js generalizing s with
  | nil => rfl
  | cons j js ih =>
      rw [clearRowScan, clearRowScan]
      split
      · exact ih _
      · dsimp only [eraseTransforms_work]
        split
        · exact ih _
        · split
          · simpa only [eraseTransforms_addCol] using ih (addCol s jk j _)
          · simp only [eraseScan, eraseTransforms_bezoutCols]

@[simp] theorem eraseTransforms_normalizePivot {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (s : LoopState F n m) (k : Nat) (hkN : k < n) (hkM : k < m) :
    eraseTransforms (normalizePivot s k hkN hkM) =
      normalizePivot (eraseTransforms s) k hkN hkM := by
  cases s
  rfl

@[simp] theorem eraseTransforms_blockStep {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (s : LoopState F n m) (ik i : Fin n) (jk j : Fin m) :
    eraseTransforms (blockStep s ik i jk j) =
      blockStep (eraseTransforms s) ik i jk j := by
  simp only [blockStep, eraseTransforms_bezoutCols, eraseTransforms_addRow,
    eraseTransforms_work]

theorem eraseTransforms_smithStage {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m)
    (ik : Fin n) (jk : Fin m) (hp : s.work[(ik, jk)] ≠ 0) :
    eraseTransforms (smithStage s ik jk hp) =
      smithStage (eraseTransforms s) ik jk (by simpa using hp) := by
  induction s, hp using smithStage.induct ik jk with
  | case1 s hp col hc ih =>
      conv =>
        rhs
        rw [smithStage]
      rw [smithStage]
      change (clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      have he := eraseScan_clearColumnScan ik jk s (List.finRange n)
      have hs := congrArg ScanResult.state he
      have hd := congrArg ScanResult.dropped he
      simp only [eraseScan] at hs hd
      have hcE : (clearColumnScan ik jk (eraseTransforms s)
          (List.finRange n)).dropped = true := hd.symm.trans hc
      simp [hc, hcE]
      simpa [col, hs] using ih
  | case2 s hp col hc row hr ih =>
      conv =>
        rhs
        rw [smithStage]
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change (clearRowScan ik jk (clearColumnScan ik jk s
        (List.finRange n)).state (List.finRange m)).dropped = true at hr
      have hec := eraseScan_clearColumnScan ik jk s (List.finRange n)
      have hcs := congrArg ScanResult.state hec
      have hcd := congrArg ScanResult.dropped hec
      simp only [eraseScan] at hcs hcd
      have her := eraseScan_clearRowScan ik jk
        (clearColumnScan ik jk s (List.finRange n)).state (List.finRange m)
      have hrs := congrArg ScanResult.state her
      have hrd := congrArg ScanResult.dropped her
      simp only [eraseScan] at hrs hrd
      have hcE : ¬(clearColumnScan ik jk (eraseTransforms s)
          (List.finRange n)).dropped = true := fun h => hc (hcd.trans h)
      have hrE : (clearRowScan ik jk
          (clearColumnScan ik jk (eraseTransforms s) (List.finRange n)).state
          (List.finRange m)).dropped = true := by
        rw [← hcs]
        exact hrd.symm.trans hr
      have hrsE : eraseTransforms row.state =
          (clearRowScan ik jk
            (clearColumnScan ik jk (eraseTransforms s) (List.finRange n)).state
            (List.finRange m)).state := by
        calc
          eraseTransforms row.state =
              (clearRowScan ik jk (eraseTransforms col.state)
                (List.finRange m)).state := hrs
          _ = _ := by rw [hcs]
      simp [hc, hcE, hr, hrE]
      simpa [row, hrsE] using ih
  | case3 s hp col hc row hr hb =>
      conv =>
        rhs
        rw [smithStage]
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change ¬(clearRowScan ik jk (clearColumnScan ik jk s
        (List.finRange n)).state (List.finRange m)).dropped = true at hr
      change badBlock (clearRowScan ik jk (clearColumnScan ik jk s
        (List.finRange n)).state (List.finRange m)).state.work ik jk = none at hb
      have hec := eraseScan_clearColumnScan ik jk s (List.finRange n)
      have hcs := congrArg ScanResult.state hec
      have hcd := congrArg ScanResult.dropped hec
      simp only [eraseScan] at hcs hcd
      have her := eraseScan_clearRowScan ik jk
        (clearColumnScan ik jk s (List.finRange n)).state (List.finRange m)
      have hrs := congrArg ScanResult.state her
      have hrd := congrArg ScanResult.dropped her
      simp only [eraseScan] at hrs hrd
      have hcE : ¬(clearColumnScan ik jk (eraseTransforms s)
          (List.finRange n)).dropped = true := fun h => hc (hcd.trans h)
      have hrE : ¬(clearRowScan ik jk
          (clearColumnScan ik jk (eraseTransforms s) (List.finRange n)).state
          (List.finRange m)).dropped = true := by
        intro h
        apply hr
        rw [← hcs] at h
        exact hrd.trans h
      have hrsE : eraseTransforms row.state =
          (clearRowScan ik jk
            (clearColumnScan ik jk (eraseTransforms s) (List.finRange n)).state
            (List.finRange m)).state := by
        calc
          eraseTransforms row.state =
              (clearRowScan ik jk (eraseTransforms col.state)
                (List.finRange m)).state := hrs
          _ = _ := by rw [hcs]
      have hbE : badBlock
          (clearRowScan ik jk
            (clearColumnScan ik jk (eraseTransforms s) (List.finRange n)).state
            (List.finRange m)).state.work ik jk = none := by
        rw [← hrsE, eraseTransforms_work]
        exact hb
      simp [hc, hcE, hr, hrE]
      split
      · split
        · simpa [row] using hrsE
        · simp_all
      · simp_all
  | case4 s hp col hc row hr q hb hc0 hr0 hq hki hkj hpCol hcol0 hcol hrow
      hnot hpRow hpBlock ih =>
      conv =>
        rhs
        rw [smithStage]
      rw [smithStage]
      change ¬(clearColumnScan ik jk s (List.finRange n)).dropped = true at hc
      change ¬(clearRowScan ik jk (clearColumnScan ik jk s
        (List.finRange n)).state (List.finRange m)).dropped = true at hr
      change badBlock (clearRowScan ik jk (clearColumnScan ik jk s
        (List.finRange n)).state (List.finRange m)).state.work ik jk = some q at hb
      have hec := eraseScan_clearColumnScan ik jk s (List.finRange n)
      have hcs := congrArg ScanResult.state hec
      have hcd := congrArg ScanResult.dropped hec
      simp only [eraseScan] at hcs hcd
      have her := eraseScan_clearRowScan ik jk
        (clearColumnScan ik jk s (List.finRange n)).state (List.finRange m)
      have hrs := congrArg ScanResult.state her
      have hrd := congrArg ScanResult.dropped her
      simp only [eraseScan] at hrs hrd
      have hcE : ¬(clearColumnScan ik jk (eraseTransforms s)
          (List.finRange n)).dropped = true := fun h => hc (hcd.trans h)
      have hrE : ¬(clearRowScan ik jk
          (clearColumnScan ik jk (eraseTransforms s) (List.finRange n)).state
          (List.finRange m)).dropped = true := by
        intro h
        apply hr
        rw [← hcs] at h
        exact hrd.trans h
      have hrsE : eraseTransforms row.state =
          (clearRowScan ik jk
            (clearColumnScan ik jk (eraseTransforms s) (List.finRange n)).state
            (List.finRange m)).state := by
        calc
          eraseTransforms row.state =
              (clearRowScan ik jk (eraseTransforms col.state)
                (List.finRange m)).state := hrs
          _ = _ := by rw [hcs]
      have hbE : badBlock
          (clearRowScan ik jk
            (clearColumnScan ik jk (eraseTransforms s) (List.finRange n)).state
            (List.finRange m)).state.work ik jk = some q := by
        rw [← hrsE, eraseTransforms_work]
        exact hb
      simp [hc, hcE, hr, hrE]
      split
      · simp_all
      · rename_i q' hb'
        have hqq : q' = q := by simp_all
        subst q'
        split
        · simp_all
        · rename_i q'' hb''
          have hqq : q'' = q := by simp_all
          subst q''
          simpa [row, eraseTransforms_blockStep, hrsE] using ih

@[simp] theorem eraseTransforms_smithStageSafe {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] {n m : Nat}
    (s : LoopState F n m) (ik : Fin n) (jk : Fin m) :
    eraseTransforms (smithStageSafe s ik jk) =
      smithStageSafe (eraseTransforms s) ik jk := by
  conv =>
    rhs
    rw [smithStageSafe]
  rw [smithStageSafe]
  split
  · rename_i hp
    have hpE : (eraseTransforms s).work[(ik, jk)] = 0 := by simpa using hp
    have hpN : (s.work.getRow ik)[jk.val] = 0 := by
      simpa [Matrix.getElem_pair_eq_nested] using hp
    simp [hpN]
  · rename_i hp
    have hpE : ¬(eraseTransforms s).work[(ik, jk)] = 0 := by simpa using hp
    have hpN : ¬(s.work.getRow ik)[jk.val] = 0 := by
      simpa [Matrix.getElem_pair_eq_nested] using hp
    simp [hpN]
    exact eraseTransforms_smithStage s ik jk hp

@[simp] theorem eraseTransforms_meta {F : Type u} [Zero F] [DecidableEq F]
    {n m : Nat} (s : LoopState F n m) (pivot : Nat) :
    eraseTransforms { s with pivot } =
      { eraseTransforms s with pivot } := by
  cases s
  rfl

theorem eraseTransforms_smithLoopTotal {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (s : LoopState F n m) (stages : Nat) :
    eraseTransforms (smithLoopTotal s stages) =
      smithLoopTotal (eraseTransforms s) stages := by
  induction stages generalizing s with
  | zero => rfl
  | succ stages ih =>
      conv =>
        rhs
        rw [smithLoopTotal]
      rw [smithLoopTotal]
      simp only [eraseTransforms_pivot, eraseTransforms_work]
      split
      · rename_i hkN
        simp [hkN]
        split
        · rename_i hkM
          simp [hkM]
          cases ht : trailingMin s.work s.pivot with
          | none => simp
          | some q =>
              simp
              simpa only [eraseTransforms_meta, eraseTransforms_smithStageSafe,
                eraseTransforms_normalizePivot, eraseTransforms_swapCols,
                eraseTransforms_swapRows] using
                ih { smithStageSafe
                  (normalizePivot (swapCols (swapRows s ⟨s.pivot, hkN⟩ q.1)
                    ⟨s.pivot, hkM⟩ q.2) s.pivot hkN hkM)
                    ⟨s.pivot, hkN⟩ ⟨s.pivot, hkM⟩ with
                  pivot := s.pivot + 1 }
        · rename_i hkM
          simp [hkM]
      · rename_i hkN
        simp [hkN]

theorem eraseTransforms_runSmith_true {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    eraseTransforms (runSmith A true) = runSmith A false := by
  unfold runSmith
  rw [eraseTransforms_smithLoopTotal]
  rfl

theorem runSmith_work_false_eq_true {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    (runSmith A false).work = (runSmith A true).work := by
  have h := congrArg LoopState.work (eraseTransforms_runSmith_true A)
  simpa using h.symm

theorem runSmith_pivot_false_eq_true {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    (runSmith A false).pivot = (runSmith A true).pivot := by
  have h := congrArg LoopState.pivot (eraseTransforms_runSmith_true A)
  simpa using h.symm

theorem diagonalVector_false_heq_true {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    HEq (diagonalVector (runSmith A false))
      (diagonalVector (runSmith A true)) := by
  have h := eraseTransforms_runSmith_true A
  rw [← h]
  rfl

/-- The full run returns transforms satisfying the three algebraic clauses of
the Smith contract. -/
theorem snfData_algebra {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) :
    (snfData A).left * A * (snfData A).right = (runSmith A true).work
      ∧ (snfData A).left * (snfData A).leftInv = Matrix.identity n
      ∧ (snfData A).right * (snfData A).rightInv = Matrix.identity m := by
  have hv := transformValid_runSmith_true A
  rcases hasTransforms_runSmith_true A with ⟨t, ht⟩
  unfold TransformValid at hv
  rw [ht] at hv
  rw [snfData_eq_of_transforms A t ht]
  exact hv

theorem snfData_rank_eq_loopRank {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    (snfData A).rank = loopRank (runSmith A true) := by
  rcases hasTransforms_runSmith_true A with ⟨t, ht⟩
  rw [snfData_eq_of_transforms A t ht]

theorem snfData_diag_heq_diagonalVector {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    HEq (snfData A).diag (diagonalVector (runSmith A true)) := by
  rcases hasTransforms_runSmith_true A with ⟨t, ht⟩
  rw [snfData_eq_of_transforms A t ht]

theorem snfData_rank_le_n {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    (snfData A).rank ≤ n := by
  rw [snfData_rank_eq_loopRank]
  unfold loopRank
  omega

theorem snfData_rank_le_m {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    (snfData A).rank ≤ m := by
  rw [snfData_rank_eq_loopRank]
  unfold loopRank
  omega

/-- The general Smith algorithm returns data satisfying the full logical
Smith-normal-form contract. -/
theorem snfData_isSNF {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) : IsSNF A (snfData A) := by
  have hv := transformValid_runSmith_true A
  rcases hasTransforms_runSmith_true A with ⟨t, ht⟩
  unfold TransformValid at hv
  rw [ht] at hv
  have hshape := loopShape_runSmith A true
  have hdone := loopDone_runSmith A true
  have hwork := work_eq_diagMatrix (runSmith A true) hshape hdone
  rw [snfData_eq_of_transforms A t ht]
  refine
    { left_inv := hv.2.1
      right_inv := hv.2.2
      mul_eq := hv.1.trans hwork
      rank_le_n := ?_
      rank_le_m := ?_
      diag_monic := diagonalVector_monic hshape
      chain := diagonalVector_chain hshape }
  · change loopRank (runSmith A true) ≤ n
    unfold loopRank
    omega
  · change loopRank (runSmith A true) ≤ m
    unfold loopRank
    omega

theorem snf_eq {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) :
    snf A = Matrix.diagMatrix (snfData A).diag n m := by
  unfold snf
  rw [runSmith_work_false_eq_true]
  rw [runSmith_work_eq_diagMatrix A true]
  rcases hasTransforms_runSmith_true A with ⟨t, ht⟩
  rw [snfData_eq_of_transforms A t ht]

theorem snfRank_eq {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    {n m : Nat} (A : Matrix (DensePoly F) n m) :
    snfRank A = (snfData A).rank := by
  unfold snfRank loopRank
  rw [runSmith_pivot_false_eq_true]
  symm
  exact snfData_rank_eq_loopRank A

theorem invariantFactors_eq {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    HEq (invariantFactors A) (snfData A).diag := by
  change HEq (diagonalVector (runSmith A false)) (snfData A).diag
  rcases hasTransforms_runSmith_true A with ⟨t, ht⟩
  rw [snfData_eq_of_transforms A t ht]
  exact diagonalVector_false_heq_true A

/-- Entrywise comparison between the transform-free invariant-factor vector
and the diagonal stored with the full transformation data. -/
theorem invariantFactors_get_eq {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m)
    (i : Fin (snfRank A)) :
    (invariantFactors A)[i] =
      (snfData A).diag[Fin.cast (snfRank_eq A) i] := by
  have hrn : snfRank A ≤ n := by
    rw [snfRank_eq A]
    exact (snfData_isSNF A).rank_le_n
  have hrm : snfRank A ≤ m := by
    rw [snfRank_eq A]
    exact (snfData_isSNF A).rank_le_m
  let ii : Fin n := Fin.castLE hrn i
  let jj : Fin m := Fin.castLE hrm i
  have hdiag : Matrix.diagMatrix (invariantFactors A) n m =
      Matrix.diagMatrix (snfData A).diag n m := by
    rw [← snf_eq A]
    exact (runSmith_work_eq_diagMatrix A false).symm
  have he := congrArg (fun M : Matrix (DensePoly F) n m => M[ii][jj]) hdiag
  rw [Matrix.getElem_diagMatrix_of_eq (invariantFactors A) ii jj (by rfl) i.isLt,
    Matrix.getElem_diagMatrix_of_eq (snfData A).diag ii jj (by rfl)
      (by simpa [ii, snfRank_eq A] using i.isLt)] at he
  exact he

/-- Consecutive executable invariant factors form the canonical divisibility
chain. -/
theorem invariantFactors_chain {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) (i : Nat)
    (h : i + 1 < snfRank A) :
    (invariantFactors A)[i]'(by omega) ∣ (invariantFactors A)[i + 1] := by
  exact diagonalVector_chain (loopShape_runSmith A false) i h

private theorem diagonalSolvable_sound {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {S : SmithData F n m}
    {b : Vector (DensePoly F) m} (h : diagonalSolvable S b = true) :
    ∀ j : Fin m,
      if hj : j.val < S.rank then S.diag[j.val]'hj ∣ b[j] else b[j] = 0 := by
  unfold diagonalSolvable at h
  intro j
  have hj := (List.all_eq_true.mp h) j (List.mem_finRange j)
  split
  · rename_i hr
    rw [dite_eq_left hr] at hj
    apply DensePoly.dvd_of_mod_eq_zero
    exact (DensePoly.size_eq_zero_iff _).mp
      ((DensePoly.isZero_eq_true_iff _).mp hj)
  · rename_i hr
    rw [dite_eq_right hr] at hj
    exact (DensePoly.size_eq_zero_iff _).mp
      ((DensePoly.isZero_eq_true_iff _).mp hj)

private theorem diagonalSolvable_complete {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {S : SmithData F n m}
    {b : Vector (DensePoly F) m}
    (h : ∀ j : Fin m,
      if hj : j.val < S.rank then S.diag[j.val]'hj ∣ b[j] else b[j] = 0) :
    diagonalSolvable S b = true := by
  unfold diagonalSolvable
  rw [List.all_eq_true]
  intro j hj
  have hjm : j < m := by simp_all
  let jj : Fin m := ⟨j, hjm⟩
  have hentry := h jj
  split
  · rename_i hr
    rw [dite_eq_left hr] at hentry
    apply (DensePoly.isZero_eq_true_iff _).mpr
    rw [DensePoly.mod_eq_zero_of_dvd _ _ hentry, DensePoly.size_zero]
  · rename_i hr
    rw [dite_eq_right hr] at hentry
    apply (DensePoly.isZero_eq_true_iff _).mpr
    rw [hentry, DensePoly.size_zero]

private theorem diagonalSolution_mul {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {S : SmithData F n m}
    (hSn : S.rank ≤ n) (hSm : S.rank ≤ m)
    (hmonic : ∀ i : Fin S.rank, S.diag[i].Monic)
    {b : Vector (DensePoly F) m} (h : diagonalSolvable S b = true) :
    diagonalSolution S b * Matrix.diagMatrix S.diag n m = b := by
  have hshape := diagonalSolvable_sound h
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  change (diagonalSolution S b * Matrix.diagMatrix S.diag n m)[jj] = b[jj]
  rw [Matrix.getElem_vecMul_diagMatrix S.diag (diagonalSolution S b) hSn jj]
  split
  · rename_i hr
    have hrm : j < m := Nat.lt_of_lt_of_le hr hSm
    have hdvd : S.diag[j]'hr ∣ b[jj] := by
      have hentry := hshape jj
      rw [dite_eq_left hr] at hentry
      exact hentry
    have hdne : S.diag[j]'hr ≠ 0 := by
      intro hz
      have hm := hmonic ⟨j, hr⟩
      change (S.diag[j]'hr).leadingCoeff = 1 at hm
      rw [hz, DensePoly.leadingCoeff_zero] at hm
      exact Lean.Grind.Field.zero_ne_one hm
    rw [diagonalSolution, Vector.getElem_ofFn]
    rw [dite_eq_left hr, dite_eq_left hrm]
    rw [Lean.Grind.CommSemiring.mul_comm]
    change Hex.exactDiv b[j] (S.diag[j]'hr) * S.diag[j]'hr = b[j]
    change S.diag[j]'hr ∣ b[j] at hdvd
    exact DensePoly.exactDiv_mul_eq_of_dvd (b[j]) (S.diag[j]'hr) hdne hdvd
  · rename_i hr
    have hb : b[jj] = 0 := by
      simpa [jj, hr] using hshape jj
    exact hb.symm

private theorem vecMul_cancel_right {R : Type u} [Lean.Grind.CommRing R]
    {n m : Nat} {x y : Vector R n} {V : Matrix R n m}
    {Vinv : Matrix R m n}
    (hV : V * Vinv = Matrix.identity n) (h : x * V = y * V) : x = y := by
  have hc := congrArg (fun z => z * Vinv) h
  change Matrix.vecMul (Matrix.vecMul x V) Vinv =
    Matrix.vecMul (Matrix.vecMul y V) Vinv at hc
  rw [Matrix.vecMul_mul, Matrix.vecMul_mul, hV,
    Matrix.vecMul_identity, Matrix.vecMul_identity] at hc
  exact hc

theorem solve_iff_diagonal {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    {b : Vector (DensePoly F) m} :
    (∃ x : Vector (DensePoly F) n, x * A = b) ↔
      ∃ z : Vector (DensePoly F) n,
        z * Matrix.diagMatrix (snfData A).diag n m = b * (snfData A).right := by
  let S := snfData A
  change (∃ x : Vector (DensePoly F) n, x * A = b) ↔
    ∃ z : Vector (DensePoly F) n,
      z * Matrix.diagMatrix S.diag n m = b * S.right
  have hS : IsSNF A S := snfData_isSNF A
  have hleft : S.leftInv * S.left = Matrix.identity n :=
    Matrix.mul_eq_one_comm hS.left_inv
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x * S.leftInv, ?_⟩
    rw [← hS.mul_eq, Matrix.vecMul_assoc]
    have hmat : S.leftInv * (S.left * A * S.right) = A * S.right := by
      rw [← Matrix.mul_assoc S.leftInv (S.left * A) S.right,
        ← Matrix.mul_assoc S.leftInv S.left A, hleft, Matrix.identity_mul]
    rw [hmat, ← Matrix.vecMul_assoc, hx]
  · rintro ⟨z, hz⟩
    refine ⟨z * S.left, ?_⟩
    apply vecMul_cancel_right hS.right_inv
    calc
      ((z * S.left) * A) * S.right =
          z * (S.left * A * S.right) := by
            rw [Matrix.vecMul_assoc, Matrix.vecMul_assoc, ← Matrix.mul_assoc]
      _ = z * Matrix.diagMatrix S.diag n m := by rw [hS.mul_eq]
      _ = b * S.right := hz

private theorem diagonalSolvable_of_mul {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {S : SmithData F n m}
    (hSn : S.rank ≤ n) {z : Vector (DensePoly F) n}
    {b : Vector (DensePoly F) m}
    (h : z * Matrix.diagMatrix S.diag n m = b) :
    diagonalSolvable S b = true := by
  apply diagonalSolvable_complete
  intro j
  have hj := congrArg (fun v => v[j]) h
  rw [Matrix.getElem_vecMul_diagMatrix S.diag z hSn j] at hj
  split
  · rename_i hr
    rw [dite_eq_left hr] at hj
    refine ⟨z[j.val]'(Nat.lt_of_lt_of_le hr hSn), hj.symm⟩
  · rename_i hr
    rw [dite_eq_right hr] at hj
    exact hj.symm

private theorem mappedSolution_sound {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    {S : SmithData F n m} (hS : IsSNF A S)
    {b : Vector (DensePoly F) m} (h : diagonalSolvable S (b * S.right) = true) :
    (diagonalSolution S (b * S.right) * S.left) * A = b := by
  apply vecMul_cancel_right hS.right_inv
  calc
    ((diagonalSolution S (b * S.right) * S.left) * A) * S.right =
        diagonalSolution S (b * S.right) * (S.left * A * S.right) := by
          rw [Matrix.vecMul_assoc, Matrix.vecMul_assoc, ← Matrix.mul_assoc]
    _ = diagonalSolution S (b * S.right) *
        Matrix.diagMatrix S.diag n m := by rw [hS.mul_eq]
    _ = b * S.right :=
      diagonalSolution_mul hS.rank_le_n hS.rank_le_m hS.diag_monic h

theorem solve_sound {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    {b : Vector (DensePoly F) m} {x : Vector (DensePoly F) n} :
    solve A b = some x → x * A = b := by
  intro h
  unfold solve at h
  dsimp only at h
  split at h
  · rename_i hsol
    simp only [Option.some.injEq] at h
    subst x
    exact mappedSolution_sound (snfData_isSNF A) hsol
  · simp at h

theorem solve_complete {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    {b : Vector (DensePoly F) m} :
    (∃ x : Vector (DensePoly F) n, x * A = b) → (solve A b).isSome := by
  intro h
  rcases solve_iff_diagonal.mp h with ⟨z, hz⟩
  have hsol : diagonalSolvable (snfData A) (b * (snfData A).right) = true :=
    diagonalSolvable_of_mul (snfData_isSNF A).rank_le_n hz
  unfold solve
  dsimp only
  rw [hsol]
  rfl

theorem quotientOrder_eq {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} (A : Matrix (DensePoly F) n m) :
    quotientOrder A =
      if snfRank A = m then
        (invariantFactors A).foldl (fun acc p => acc * p) 1
      else 0 := by
  have hone : polyOne (F := F) = (1 : DensePoly F) := rfl
  have hzero : polyZero (F := F) = (0 : DensePoly F) := rfl
  unfold quotientOrder
  rw [hone, hzero]
  simp only [Vector.foldl_toList]

/-- Diagonal input uses the same certified reduction as the general API. -/
theorem snfDiagonalData_isSNF {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {r : Nat} (d : Vector (DensePoly F) r) :
    IsSNF (Matrix.diagMatrix d r r) (snfDiagonalData d) :=
  snfData_isSNF (Matrix.diagMatrix d r r)

theorem snfDiagonal_eq {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {r : Nat} (d : Vector (DensePoly F) r) :
    snfDiagonal d = Matrix.diagMatrix (snfDiagonalData d).diag r r := by
  exact snf_eq (Matrix.diagMatrix d r r)

private theorem monic_ne_zero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {p : DensePoly F} (hp : p.Monic) : p ≠ 0 := by
  intro h
  change p.leadingCoeff = 1 at hp
  rw [h, DensePoly.leadingCoeff_zero] at hp
  exact Lean.Grind.Field.zero_ne_one hp

private theorem prefixProduct_succ {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {r : Nat} (d : Vector (DensePoly F) r)
    (i : Nat) (hi : i + 1 ≤ r) :
    (d.take (i + 1)).foldl (fun acc p => acc * p) 1 =
      (d.take i).foldl (fun acc p => acc * p) 1 * d[i]'(by omega) := by
  rw [take_foldl_eq_finFoldl d (i + 1) hi,
    take_foldl_eq_finFoldl d i (by omega), Fin.foldl_succ_last]
  congr 1

private theorem poly_mul_left_cancel {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {p a b : DensePoly F} (hp : p ≠ 0)
    (h : p * a = p * b) : a = b := by
  by_cases hab : a = b
  · exact hab
  · exfalso
    have hsub : a - b ≠ 0 := by
      intro hz
      apply hab
      grind
    have hprod : (a - b) * p ≠ 0 := by
      intro hz
      have hs := DensePoly.size_mul_field (a - b) p hsub hp
      rw [hz, DensePoly.size_zero] at hs
      have hsp : 0 < (a - b).size :=
        Nat.pos_of_ne_zero (fun hzero => hsub ((DensePoly.size_eq_zero_iff _).mp hzero))
      have hpp : 0 < p.size :=
        Nat.pos_of_ne_zero (fun hzero => hp ((DensePoly.size_eq_zero_iff _).mp hzero))
      omega
    apply hprod
    rw [DensePoly.sub_mul_poly, DensePoly.mul_comm_poly a p,
      DensePoly.mul_comm_poly b p, h]
    grind

/-- The rank field of Smith data is canonical. -/
theorem IsSNF.rank_eq {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    {S S' : SmithData F n m} (h : IsSNF A S) (h' : IsSNF A S') :
    S.rank = S'.rank := by
  apply Nat.le_antisymm
  · by_cases hle : S.rank ≤ S'.rank
    · exact hle
    · exfalso
      have hlt : S'.rank < S.rank := by omega
      let k := S'.rank + 1
      have heq := (h.detDivisor_eq k).symm.trans (h'.detDivisor_eq k)
      have hkS : k ≤ S.rank := by omega
      have hkS' : ¬ k ≤ S'.rank := by omega
      rw [ite_eq_left hkS, ite_eq_right hkS'] at heq
      have hm := prefixProduct_monic S.diag h.diag_monic k hkS
      exact monic_ne_zero hm heq
  · by_cases hle : S'.rank ≤ S.rank
    · exact hle
    · exfalso
      have hlt : S.rank < S'.rank := by omega
      let k := S.rank + 1
      have heq := (h'.detDivisor_eq k).symm.trans (h.detDivisor_eq k)
      have hkS' : k ≤ S'.rank := by omega
      have hkS : ¬ k ≤ S.rank := by omega
      rw [ite_eq_left hkS', ite_eq_right hkS] at heq
      have hm := prefixProduct_monic S'.diag h'.diag_monic k hkS'
      exact monic_ne_zero hm heq

/-- Every diagonal entry of certified Smith data is canonical. -/
theorem IsSNF.diag_eq {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n m : Nat} {A : Matrix (DensePoly F) n m}
    {S S' : SmithData F n m} (h : IsSNF A S) (h' : IsSNF A S')
    (i : Nat) (hi : i < S.rank) (hi' : i < S'.rank) :
    S.diag[i] = S'.diag[i] := by
  have hrank : S.rank = S'.rank := h.rank_eq h'
  have hp :
      (S.diag.take i).foldl (fun acc p => acc * p) 1 =
        (S'.diag.take i).foldl (fun acc p => acc * p) 1 := by
    have hs := h.detDivisor_eq i
    have hs' := h'.detDivisor_eq i
    rw [ite_eq_left (by omega)] at hs
    rw [ite_eq_left (by omega)] at hs'
    exact hs.symm.trans hs'
  have hpsucc :
      (S.diag.take (i + 1)).foldl (fun acc p => acc * p) 1 =
        (S'.diag.take (i + 1)).foldl (fun acc p => acc * p) 1 := by
    have hs := h.detDivisor_eq (i + 1)
    have hs' := h'.detDivisor_eq (i + 1)
    rw [ite_eq_left (by omega)] at hs
    rw [ite_eq_left (by omega)] at hs'
    exact hs.symm.trans hs'
  rw [prefixProduct_succ S.diag i (by omega),
    prefixProduct_succ S'.diag i (by omega), hp] at hpsucc
  have hprefix := prefixProduct_monic S'.diag h'.diag_monic i (by omega)
  exact poly_mul_left_cancel (monic_ne_zero hprefix) hpsucc

private theorem vector_foldl_eq_finFoldl {α β : Type u} {r : Nat}
    (v : Vector α r) (f : β → α → β) (z : β) :
    v.foldl f z = Fin.foldl r (fun acc i => f acc v[i]) z := by
  rw [← Vector.foldl_toList, Fin.foldl_eq_finRange_foldl]
  have hright :
      (List.finRange r).foldl (fun acc i => f acc v[i]) z =
        ((List.finRange r).map fun i => v[i]).foldl f z := by
    rw [List.foldl_map]
  rw [hright]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [Vector.getElem_toList, List.getElem_map, List.getElem_finRange]
    rfl

private theorem degree_getD_eq_size_sub_one {F : Type u}
    [Lean.Grind.Field F] [DecidableEq F] (p : DensePoly F) :
    p.degree?.getD 0 = p.size - 1 := by
  unfold DensePoly.degree?
  split <;> simp_all

private theorem poly_mul_ne_zero {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {p q : DensePoly F} (hp : p ≠ 0) (hq : q ≠ 0) :
    p * q ≠ 0 := by
  intro hzero
  have hsize := DensePoly.size_mul_field p q hp hq
  rw [hzero, DensePoly.size_zero] at hsize
  have hpSize : 0 < p.size :=
    Nat.pos_of_ne_zero (fun hs => hp ((DensePoly.size_eq_zero_iff p).mp hs))
  have hqSize : 0 < q.size :=
    Nat.pos_of_ne_zero (fun hs => hq ((DensePoly.size_eq_zero_iff q).mp hs))
  omega

private theorem degree_getD_mul {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {p q : DensePoly F} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).degree?.getD 0 = p.degree?.getD 0 + q.degree?.getD 0 := by
  rw [degree_getD_eq_size_sub_one, degree_getD_eq_size_sub_one,
    degree_getD_eq_size_sub_one, DensePoly.size_mul_field p q hp hq]
  have hpSize : 0 < p.size :=
    Nat.pos_of_ne_zero (fun hs => hp ((DensePoly.size_eq_zero_iff p).mp hs))
  have hqSize : 0 < q.size :=
    Nat.pos_of_ne_zero (fun hs => hq ((DensePoly.size_eq_zero_iff q).mp hs))
  omega

private theorem foldl_degree_eq {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] (xs : List (DensePoly F)) (acc : DensePoly F)
    (hacc : acc ≠ 0) (hxs : ∀ p ∈ xs, p ≠ 0) :
    (xs.foldl (fun z p => z * p) acc).degree?.getD 0 =
      acc.degree?.getD 0 +
        xs.foldl (fun z p => z + p.degree?.getD 0) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons p xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc * p) (poly_mul_ne_zero hacc (hxs p (by simp)))
        (fun q hq => hxs q (by simp [hq])), degree_getD_mul hacc (hxs p (by simp))]
      simp only [Nat.zero_add]
      rw [List.foldl_add_eq_add_foldl xs
        (fun q : DensePoly F => q.degree?.getD 0) (p.degree?.getD 0)]
      omega

private theorem vector_degree_foldl {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {r : Nat} (v : Vector (DensePoly F) r)
    (hmonic : ∀ i : Fin r, v[i].Monic) :
    v.foldl (fun z p => z + p.degree?.getD 0) 0 =
      (v.foldl (fun z p => z * p) 1).degree?.getD 0 := by
  rw [← Vector.foldl_toList, ← Vector.foldl_toList]
  symm
  have hone : (1 : DensePoly F) ≠ 0 := by
    intro hone
    have hsize := congrArg DensePoly.size hone
    rw [DensePoly.size_one (Ne.symm Lean.Grind.Field.zero_ne_one),
      DensePoly.size_zero] at hsize
    omega
  have hxs : ∀ p ∈ v.toList, p ≠ 0 := by
    intro p hp
    rcases List.mem_iff_getElem.mp hp with ⟨i, hi, heq⟩
    subst p
    exact monic_ne_zero (hmonic ⟨i, by simpa using hi⟩)
  have hdegree := foldl_degree_eq v.toList (1 : DensePoly F) hone hxs
  have honeDegree : (1 : DensePoly F).degree?.getD 0 = 0 := by
    rw [degree_getD_eq_size_sub_one,
      DensePoly.size_one (Ne.symm Lean.Grind.Field.zero_ne_one)]
  simpa [honeDegree] using hdegree

/-- On a nonsingular square input, the invariant-factor product is the monic
associate of the determinant. -/
theorem prod_invariantFactors {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n : Nat} (A : Matrix (DensePoly F) n n)
    (h : snfRank A = n) :
    (invariantFactors A).foldl (fun acc p => acc * p) 1 =
      DensePoly.monicize (Matrix.det A) := by
  let S := snfData A
  have hS : IsSNF A S := snfData_isSNF A
  have hr : S.rank = n := by
    exact (snfRank_eq A).symm.trans h
  have hfold :
      (invariantFactors A).foldl (fun acc p => acc * p) 1 =
        S.diag.foldl (fun acc p => acc * p) 1 :=
    by
      change (diagonalVector (runSmith A false)).foldl (fun acc p => acc * p) 1 =
        S.diag.foldl (fun acc p => acc * p) 1
      rcases hasTransforms_runSmith_true A with ⟨t, ht⟩
      unfold S
      rw [snfData_eq_of_transforms A t ht]
      have he := eraseTransforms_runSmith_true A
      rw [← he]
      rfl
  have hdiv := hS.detDivisor_eq S.rank
  rw [ite_eq_left (Nat.le_refl S.rank)] at hdiv
  have htake :
      (S.diag.take S.rank).foldl (fun acc p => acc * p) 1 =
        S.diag.foldl (fun acc p => acc * p) 1 := by
    rw [← Vector.foldl_toList, ← Vector.foldl_toList, Vector.toList_take]
    rw [List.take_of_length_le]
    simp
  rw [htake] at hdiv
  have hindex : detDivisor A S.rank = detDivisor A n :=
    congrArg (detDivisor A) hr
  calc
    (invariantFactors A).foldl (fun acc p => acc * p) 1 =
        S.diag.foldl (fun acc p => acc * p) 1 := hfold
    _ = detDivisor A S.rank := hdiv.symm
    _ = detDivisor A n := hindex
    _ = DensePoly.monicize (Matrix.det A) := detDivisor_full A

/-- On a nonsingular square input, the invariant-factor degrees add to the
degree of the determinant. -/
theorem degree_prod_invariantFactors {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] {n : Nat} (A : Matrix (DensePoly F) n n)
    (h : snfRank A = n) :
    (invariantFactors A).foldl
        (fun acc p => acc + p.degree?.getD 0) 0 =
      (Matrix.det A).degree?.getD 0 := by
  let S := snfData A
  have hS : IsSNF A S := snfData_isSNF A
  have hsum :
      (invariantFactors A).foldl
          (fun acc p => acc + p.degree?.getD 0) 0 =
        S.diag.foldl (fun acc p => acc + p.degree?.getD 0) 0 := by
    change (diagonalVector (runSmith A false)).foldl
        (fun acc p => acc + p.degree?.getD 0) 0 =
      S.diag.foldl (fun acc p => acc + p.degree?.getD 0) 0
    rcases hasTransforms_runSmith_true A with ⟨t, ht⟩
    unfold S
    rw [snfData_eq_of_transforms A t ht]
    have he := eraseTransforms_runSmith_true A
    rw [← he]
    rfl
  have hprod :
      S.diag.foldl (fun acc p => acc * p) 1 =
        DensePoly.monicize (Matrix.det A) := by
    have hpublic := prod_invariantFactors A h
    have hfold :
        (invariantFactors A).foldl (fun acc p => acc * p) 1 =
          S.diag.foldl (fun acc p => acc * p) 1 := by
      change (diagonalVector (runSmith A false)).foldl
          (fun acc p => acc * p) 1 =
        S.diag.foldl (fun acc p => acc * p) 1
      rcases hasTransforms_runSmith_true A with ⟨t, ht⟩
      unfold S
      rw [snfData_eq_of_transforms A t ht]
      have he := eraseTransforms_runSmith_true A
      rw [← he]
      rfl
    exact hfold.symm.trans hpublic
  calc
    (invariantFactors A).foldl
        (fun acc p => acc + p.degree?.getD 0) 0 =
        S.diag.foldl (fun acc p => acc + p.degree?.getD 0) 0 := hsum
    _ = (S.diag.foldl (fun acc p => acc * p) 1).degree?.getD 0 :=
      vector_degree_foldl S.diag hS.diag_monic
    _ = (DensePoly.monicize (Matrix.det A)).degree?.getD 0 :=
      congrArg (fun p : DensePoly F => p.degree?.getD 0) hprod
    _ = (Matrix.det A).degree?.getD 0 := by
      rw [degree_getD_eq_size_sub_one, degree_getD_eq_size_sub_one,
        DensePoly.size_monicize]

end Hex.PolyMatrix
