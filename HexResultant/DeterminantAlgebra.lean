/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.SubresultantMinor
public import HexDeterminant.Adjugate
import all HexResultant.SubresultantMinor

public section

/-!
Local determinant algebra for generalized Sylvester minors.

The proof-only determinant in `SubresultantMinor` deliberately avoids a
dependency on `hex-matrix` or `hex-determinant`.  This module develops the
column multilinearity, arbitrary alternation and column-update, permutation,
and block-scaling identities that begin the Brown--Traub proof directly from
its first-row Laplace recursion.
-/

namespace Hex

universe u

namespace SubresultantMinor

/-- Replace one column of a proof-only square coefficient family. -/
@[expose]
def setCol {R : Type u} {n : Nat} (M : Square R n) (dst : Fin n)
    (v : Fin n → R) : Square R n :=
  fun i j => if j = dst then v i else M i j

/-- Entrywise value of a column replacement. -/
@[simp, grind =]
theorem setCol_apply {R : Type u} {n : Nat} (M : Square R n)
    (dst : Fin n) (v : Fin n → R) (i j : Fin n) :
    setCol M dst v i j = if j = dst then v i else M i j := by
  rfl

/-- Replacing a column by itself changes nothing. -/
@[simp, grind =]
theorem setCol_self {R : Type u} {n : Nat} (M : Square R n) (dst : Fin n) :
    setCol M dst (fun i => M i dst) = M := by
  funext i j
  by_cases h : j = dst
  · subst j
    simp [setCol]
  · simp [setCol, h]

/-- Swap two adjacent columns of a proof-only square coefficient family. -/
@[expose]
def swapAdjacent {R : Type u} {n : Nat} (M : Square R (n + 1))
    (left : Fin n) : Square R (n + 1) :=
  fun i j =>
    if j = left.castSucc then M i left.succ
    else if j = left.succ then M i left.castSucc
    else M i j

/-- Entrywise value of an adjacent column swap. -/
@[simp, grind =]
theorem swapAdjacent_apply {R : Type u} {n : Nat}
    (M : Square R (n + 1)) (left : Fin n) (i j : Fin (n + 1)) :
    swapAdjacent M left i j =
      if j = left.castSucc then M i left.succ
      else if j = left.succ then M i left.castSucc
      else M i j := by
  rfl

/-- After an adjacent swap, the left column reads the old right column.
`grind`-only: simp derives this from `swapAdjacent_apply`. -/
@[grind =]
theorem swapAdjacent_left {R : Type u} {n : Nat}
    (M : Square R (n + 1)) (left : Fin n) (i : Fin (n + 1)) :
    swapAdjacent M left i left.castSucc = M i left.succ := by
  simp [swapAdjacent]

/-- After an adjacent swap, the right column reads the old left column.
`grind`-only: simp derives this from `swapAdjacent_apply`. -/
@[grind =]
theorem swapAdjacent_right {R : Type u} {n : Nat}
    (M : Square R (n + 1)) (left : Fin n) (i : Fin (n + 1)) :
    swapAdjacent M left i left.succ = M i left.castSucc := by
  have hne : left.succ ≠ left.castSucc := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  simp [swapAdjacent, hne]

/-- Columns away from the swapped pair are untouched.
`grind`-only: simp derives this from `swapAdjacent_apply`. -/
@[grind =]
theorem swapAdjacent_of_ne {R : Type u} {n : Nat}
    (M : Square R (n + 1)) (left : Fin n) (i j : Fin (n + 1))
    (hl : j ≠ left.castSucc) (hr : j ≠ left.succ) :
    swapAdjacent M left i j = M i j := by
  simp [swapAdjacent, hl, hr]

/-- Adjacent column swaps are involutive. -/
@[simp, grind =]
theorem swapAdjacent_swapAdjacent {R : Type u} {n : Nat}
    (M : Square R (n + 1)) (left : Fin n) :
    swapAdjacent (swapAdjacent M left) left = M := by
  have hne : left.castSucc ≠ left.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  funext i j
  by_cases hl : j = left.castSucc
  · subst j
    simp [swapAdjacent, hne.symm]
  · by_cases hr : j = left.succ
    · subst j
      simp [swapAdjacent, hne.symm]
    · simp [swapAdjacent, hl, hr]

/-- Below the skipped position, the embedding preserves the numeric index. -/
@[simp, grind =]
theorem skipIndex_val_of_lt {n : Nat} (skip : Fin (n + 1)) (i : Fin n)
    (h : i.val < skip.val) :
    (skipIndex skip i).val = i.val := by
  simp [skipIndex, h]

/-- From the skipped position on, the embedding shifts the numeric index up
by one. -/
@[simp, grind =]
theorem skipIndex_val_of_not_lt {n : Nat} (skip : Fin (n + 1)) (i : Fin n)
    (h : ¬i.val < skip.val) :
    (skipIndex skip i).val = i.val + 1 := by
  simp [skipIndex, h]

/-- A skipped-index embedding never returns the deleted position. -/
theorem skipIndex_ne {n : Nat} (skip : Fin (n + 1)) (i : Fin n) :
    skipIndex skip i ≠ skip := by
  intro hsame
  have hval := congrArg Fin.val hsame
  by_cases hlt : i.val < skip.val
  · rw [skipIndex_val_of_lt skip i hlt] at hval
    omega
  · rw [skipIndex_val_of_not_lt skip i hlt] at hval
    omega

/-- The skipped-index embedding is injective. -/
theorem skipIndex_injective {n : Nat} (skip : Fin (n + 1)) :
    Function.Injective (skipIndex skip) := by
  intro i j hsame
  apply Fin.ext
  have hval := congrArg Fin.val hsame
  by_cases hi : i.val < skip.val
  · rw [skipIndex_val_of_lt skip i hi] at hval
    by_cases hj : j.val < skip.val
    · simpa [skipIndex_val_of_lt skip j hj] using hval
    · rw [skipIndex_val_of_not_lt skip j hj] at hval
      omega
  · rw [skipIndex_val_of_not_lt skip i hi] at hval
    by_cases hj : j.val < skip.val
    · rw [skipIndex_val_of_lt skip j hj] at hval
      omega
    · rw [skipIndex_val_of_not_lt skip j hj] at hval
      omega

/-- Contract an index after deleting a distinct position. -/
@[expose]
def eraseIndex {n : Nat} (skip target : Fin (n + 1))
    (h : target ≠ skip) : Fin n :=
  if hlt : target.val < skip.val then
    ⟨target.val, by omega⟩
  else
    ⟨target.val - 1, by
      have hgt : skip.val < target.val := by
        omega
      omega⟩

/-- The skipped-index embedding undoes index contraction. -/
@[simp, grind =]
theorem skipIndex_eraseIndex {n : Nat} (skip target : Fin (n + 1))
    (h : target ≠ skip) :
    skipIndex skip (eraseIndex skip target h) = target := by
  apply Fin.ext
  by_cases hlt : target.val < skip.val
  · simp [eraseIndex, hlt, skipIndex]
  · have hgt : skip.val < target.val := by
      omega
    have hnot : ¬target.val - 1 < skip.val := by
      omega
    simp [eraseIndex, hlt, skipIndex, hnot]
    omega

/-- The left position of an adjacent column pair after deleting a third
column. -/
@[expose]
def eraseAdjacent {n : Nat} (removed : Fin (n + 2)) (left : Fin (n + 1))
    (hleft : removed ≠ left.castSucc) (hright : removed ≠ left.succ) : Fin n :=
  if hlt : removed.val < left.val then
    ⟨left.val - 1, by
      have hpos : 0 < left.val := by
        omega
      omega⟩
  else
    ⟨left.val, by
      have hgt : left.val + 1 < removed.val := by
        have hneLeft : removed.val ≠ left.val := by
          intro h
          exact hleft (Fin.ext h)
        have hneRight : removed.val ≠ left.val + 1 := by
          intro h
          exact hright (Fin.ext h)
        omega
      omega⟩

/-- The contracted left column of an adjacent pair embeds back onto the
original left column. -/
@[simp, grind =]
theorem skipIndex_eraseAdjacent_left {n : Nat} (removed : Fin (n + 2))
    (left : Fin (n + 1)) (hleft : removed ≠ left.castSucc)
    (hright : removed ≠ left.succ) :
    skipIndex removed (eraseAdjacent removed left hleft hright).castSucc =
      left.castSucc := by
  apply Fin.ext
  by_cases hlt : removed.val < left.val
  · have hnot : ¬left.val - 1 < removed.val := by
      omega
    simp [eraseAdjacent, hlt, skipIndex, hnot]
    omega
  · have hneLeft : removed.val ≠ left.val := by
      intro h
      exact hleft (Fin.ext h)
    have hneRight : removed.val ≠ left.val + 1 := by
      intro h
      exact hright (Fin.ext h)
    have hkeep : left.val < removed.val := by
      omega
    simp [eraseAdjacent, hlt, skipIndex, hkeep]

/-- The contracted right column of an adjacent pair embeds back onto the
original right column. -/
@[simp, grind =]
theorem skipIndex_eraseAdjacent_right {n : Nat} (removed : Fin (n + 2))
    (left : Fin (n + 1)) (hleft : removed ≠ left.castSucc)
    (hright : removed ≠ left.succ) :
    skipIndex removed (eraseAdjacent removed left hleft hright).succ =
      left.succ := by
  apply Fin.ext
  by_cases hlt : removed.val < left.val
  · have hpos : 0 < left.val := by
      omega
    have hval : left.val - 1 + 1 = left.val := by
      omega
    have hkeep : ¬left.val < removed.val := by
      omega
    simp [eraseAdjacent, hlt, skipIndex, hkeep, hval]
  · have hneLeft : removed.val ≠ left.val := by
      intro h
      exact hleft (Fin.ext h)
    have hneRight : removed.val ≠ left.val + 1 := by
      intro h
      exact hright (Fin.ext h)
    have hkeep : left.val + 1 < removed.val := by
      omega
    simp [eraseAdjacent, hlt, skipIndex, hkeep]

/-- Deleting the replaced column removes the replacement. -/
theorem deleteFirst_setCol_same {R : Type u} {n : Nat}
    (M : Square R (n + 1)) (dst : Fin (n + 1)) (v : Fin (n + 1) → R) :
    deleteFirst (setCol M dst v) dst = deleteFirst M dst := by
  funext i j
  simp [deleteFirst, setCol, skipIndex_ne]

/-- Deleting another column preserves a replacement at the contracted index. -/
theorem deleteFirst_setCol_ne {R : Type u} {n : Nat}
    (M : Square R (n + 1)) (removed dst : Fin (n + 1))
    (v : Fin (n + 1) → R) (h : dst ≠ removed) :
    deleteFirst (setCol M dst v) removed =
      setCol (deleteFirst M removed) (eraseIndex removed dst h) (fun i => v i.succ) := by
  funext i j
  by_cases hj : j = eraseIndex removed dst h
  · subst j
    simp [deleteFirst, setCol, skipIndex_eraseIndex]
  · have hskip : skipIndex removed j ≠ dst := by
      intro heq
      apply hj
      apply skipIndex_injective removed
      exact heq.trans (skipIndex_eraseIndex removed dst h).symm
    simp [deleteFirst, setCol, hj, hskip]

-- These small fold lemmas stay local deliberately: importing `HexBasic.Fold`
-- would add a released dependency solely for proof infrastructure, while
-- `hex-resultant` is specified to depend only on `hex-poly`.
private theorem foldl_add_add {R : Type u} [Lean.Grind.CommRing R]
    {α : Type v} (xs : List α) (f g : α → R) (a b : R) :
    xs.foldl (fun acc x => acc + (f x + g x)) (a + b) =
      xs.foldl (fun acc x => acc + f x) a +
        xs.foldl (fun acc x => acc + g x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hstart : (a + b) + (f x + g x) =
          (a + f x) + (b + g x) := by
        grind
      rw [hstart]
      exact ih (a + f x) (b + g x)

private theorem foldl_add_mul_left {R : Type u} [Lean.Grind.CommRing R]
    {α : Type v} (xs : List α) (c : R) (f : α → R) (a : R) :
    xs.foldl (fun acc x => acc + c * f x) (c * a) =
      c * xs.foldl (fun acc x => acc + f x) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hstart : c * a + c * f x = c * (a + f x) := by
        grind
      rw [hstart]
      exact ih (a + f x)

private theorem foldl_congr {α : Type u} {β : Type v} (xs : List α)
    (f g : β → α → β) (a b : β) (hab : a = b)
    (hstep : ∀ acc x, x ∈ xs → f acc x = g acc x) :
    xs.foldl f a = xs.foldl g b := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · subst b
        exact hstep a x List.mem_cons_self
      · intro acc y hy
        exact hstep acc y (List.mem_cons_of_mem x hy)

private theorem foldl_add_zero {R : Type u} [Lean.Grind.CommRing R]
    {α : Type v} (xs : List α) (f : α → R) (a : R)
    (hzero : ∀ x, x ∈ xs → f x = 0) :
    xs.foldl (fun acc x => acc + f x) a = a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [hzero x List.mem_cons_self]
      have htail : ∀ y, y ∈ xs → f y = 0 := by
        intro y hy
        exact hzero y (List.mem_cons_of_mem x hy)
      have hrec := ih a htail
      rw [show a + 0 = a by grind]
      exact hrec

private theorem foldl_add_single {R : Type u} [Lean.Grind.CommRing R]
    {α : Type v} [DecidableEq α] (xs : List α) (x : α) (f : α → R)
    (a : R) (hnodup : xs.Nodup) (hmem : x ∈ xs)
    (hzero : ∀ y, y ∈ xs → y ≠ x → f y = 0) :
    xs.foldl (fun acc y => acc + f y) a = a + f x := by
  induction xs generalizing a with
  | nil => simp at hmem
  | cons y ys ih =>
      simp only [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      simp only [List.foldl_cons]
      by_cases hyx : y = x
      · subst y
        have htail : ∀ z, z ∈ ys → f z = 0 := by
          intro z hz
          exact hzero z (List.mem_cons_of_mem x hz) (by
            intro hzx
            exact hnodup.1 (hzx ▸ hz))
        exact foldl_add_zero ys f (a + f x) htail
      · have hxmem : x ∈ ys := by
          exact hmem.resolve_left (fun h => hyx h.symm)
        have hyzero : f y = 0 := hzero y List.mem_cons_self hyx
        rw [hyzero]
        have htail : ∀ z, z ∈ ys → z ≠ x → f z = 0 := by
          intro z hz hzx
          exact hzero z (List.mem_cons_of_mem y hz) hzx
        have hrec := ih a hnodup.2 hxmem htail
        rw [show a + 0 = a by grind]
        exact hrec

private theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.nodup_cons]
      exact ⟨by simp [Fin.ext_iff],
        List.Pairwise.map _ (fun _ _ hne h => hne (Fin.succ_inj.mp h)) ih⟩

/-- If the first row is supported only in its first column, the local
determinant expands to that entry times the remaining first minor. -/
theorem det_firstRow {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R (n + 1))
    (hzero : ∀ j : Fin (n + 1), 0 < j.val →
      M ⟨0, by omega⟩ j = 0) :
    det M = M ⟨0, by omega⟩ ⟨0, by omega⟩ *
      det (deleteFirst M ⟨0, by omega⟩) := by
  let row : Fin (n + 1) := ⟨0, by omega⟩
  let term := fun j : Fin (n + 1) =>
    sign j.val * M row j * det (deleteFirst M j)
  have hterm (j : Fin (n + 1)) (_hjmem : j ∈ List.finRange (n + 1))
      (hj : j ≠ row) : term j = 0 := by
    have hjpos : 0 < j.val := by
      by_cases hjzero : j.val = 0
      · exfalso
        apply hj
        apply Fin.ext
        simp [row, hjzero]
      · omega
    unfold term
    rw [show M row j = 0 by exact hzero j hjpos]
    grind
  simp only [det]
  change (List.finRange (n + 1)).foldl
      (fun acc j => acc + term j) 0 = _
  rw [foldl_add_single (List.finRange (n + 1)) row term 0
    (nodup_finRange (n + 1)) (List.mem_finRange row) hterm]
  simp [term, row, sign]
  grind

private theorem foldl_finRange_adjacent {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (left : Fin (n + 1)) (f : Fin (n + 2) → R)
    (hzero : ∀ j, j ≠ left.castSucc → j ≠ left.succ → f j = 0) :
    (List.finRange (n + 2)).foldl (fun acc j => acc + f j) 0 =
      f left.castSucc + f left.succ := by
  let leftTerm := fun j : Fin (n + 2) => if j = left.castSucc then f j else 0
  let rightTerm := fun j : Fin (n + 2) => if j = left.succ then f j else 0
  have hlr : left.castSucc ≠ left.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  have hrl : left.succ ≠ left.castSucc := fun h => hlr h.symm
  have hsplit (j : Fin (n + 2)) : f j = leftTerm j + rightTerm j := by
    by_cases hjl : j = left.castSucc
    · subst j
      simp [leftTerm, rightTerm, hlr]
      grind
    · by_cases hjr : j = left.succ
      · subst j
        simp [leftTerm, rightTerm, hrl]
        grind
      · simp [leftTerm, rightTerm, hjl, hjr, hzero j hjl hjr]
        grind
  calc
    (List.finRange (n + 2)).foldl (fun acc j => acc + f j) 0 =
        (List.finRange (n + 2)).foldl
          (fun acc j => acc + (leftTerm j + rightTerm j)) (0 + 0) := by
            apply foldl_congr
            · grind
            · intro acc j _hmem
              rw [← hsplit]
    _ =
        (List.finRange (n + 2)).foldl (fun acc j => acc + leftTerm j) 0 +
          (List.finRange (n + 2)).foldl (fun acc j => acc + rightTerm j) 0 :=
      foldl_add_add (List.finRange (n + 2)) leftTerm rightTerm 0 0
    _ = leftTerm left.castSucc + rightTerm left.succ := by
      have hleftSingle :
          (List.finRange (n + 2)).foldl (fun acc j => acc + leftTerm j) 0 =
            0 + leftTerm left.castSucc := by
        apply foldl_add_single (List.finRange (n + 2)) left.castSucc leftTerm 0
          (nodup_finRange (n + 2)) (List.mem_finRange left.castSucc)
        intro j _hj hne
        simp [leftTerm, hne]
      have hrightSingle :
          (List.finRange (n + 2)).foldl (fun acc j => acc + rightTerm j) 0 =
            0 + rightTerm left.succ := by
        apply foldl_add_single (List.finRange (n + 2)) left.succ rightTerm 0
          (nodup_finRange (n + 2)) (List.mem_finRange left.succ)
        intro j _hj hne
        simp [rightTerm, hne]
      rw [hleftSingle, hrightSingle]
      grind
    _ = f left.castSucc + f left.succ := by
      simp [leftTerm, rightTerm]

/-- The local Laplace determinant is additive in any replaced column. -/
theorem det_setCol_add {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R n) (dst : Fin n) (v w : Fin n → R) :
    det (setCol M dst (fun i => v i + w i)) =
      det (setCol M dst v) + det (setCol M dst w) := by
  induction n with
  | zero => exact Fin.elim0 dst
  | succ n ih =>
      let row : Fin (n + 1) := ⟨0, by omega⟩
      let combined := setCol M dst (fun i => v i + w i)
      let left := setCol M dst v
      let right := setCol M dst w
      let term := fun (N : Square R (n + 1)) (j : Fin (n + 1)) =>
        sign j.val * N row j * det (deleteFirst N j)
      have hterm (j : Fin (n + 1)) :
          term combined j = term left j + term right j := by
        by_cases hj : j = dst
        · subst j
          have hc := deleteFirst_setCol_same M dst (fun i => v i + w i)
          have hl := deleteFirst_setCol_same M dst v
          have hr := deleteFirst_setCol_same M dst w
          simp only [term, combined, left, right]
          rw [hc, hl, hr]
          simp [setCol]
          grind
        · have hdst : dst ≠ j := by
            exact fun h => hj h.symm
          have hc := deleteFirst_setCol_ne M j dst (fun i => v i + w i) hdst
          have hl := deleteFirst_setCol_ne M j dst v hdst
          have hr := deleteFirst_setCol_ne M j dst w hdst
          have hminor := ih (deleteFirst M j) (eraseIndex j dst hdst)
            (fun i => v i.succ) (fun i => w i.succ)
          simp only [term, combined, left, right]
          rw [hc, hl, hr]
          have hfun : (fun i : Fin n => v i.succ + w i.succ) =
              fun i => (fun k => v k.succ) i + (fun k => w k.succ) i := rfl
          rw [hfun, hminor]
          simp [setCol, hj]
          grind
      simp only [det]
      change (List.finRange (n + 1)).foldl
          (fun acc j => acc + term combined j) 0 =
        (List.finRange (n + 1)).foldl
            (fun acc j => acc + term left j) 0 +
          (List.finRange (n + 1)).foldl
            (fun acc j => acc + term right j) 0
      calc
        (List.finRange (n + 1)).foldl
            (fun acc j => acc + term combined j) 0 =
          (List.finRange (n + 1)).foldl
            (fun acc j => acc + (term left j + term right j)) (0 + 0) := by
              apply foldl_congr
              · grind
              · intro acc j _hmem
                rw [hterm]
        _ = _ := foldl_add_add (List.finRange (n + 1))
          (fun j => term left j) (fun j => term right j) 0 0

/-- The local Laplace determinant is homogeneous in any replaced column. -/
theorem det_setCol_smul {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R n) (dst : Fin n) (c : R) (v : Fin n → R) :
    det (setCol M dst (fun i => c * v i)) =
      c * det (setCol M dst v) := by
  induction n with
  | zero => exact Fin.elim0 dst
  | succ n ih =>
      let row : Fin (n + 1) := ⟨0, by omega⟩
      let scaled := setCol M dst (fun i => c * v i)
      let base := setCol M dst v
      let term := fun (N : Square R (n + 1)) (j : Fin (n + 1)) =>
        sign j.val * N row j * det (deleteFirst N j)
      have hterm (j : Fin (n + 1)) :
          term scaled j = c * term base j := by
        by_cases hj : j = dst
        · subst j
          have hs := deleteFirst_setCol_same M dst (fun i => c * v i)
          have hb := deleteFirst_setCol_same M dst v
          simp only [term, scaled, base]
          rw [hs, hb]
          simp [setCol]
          grind
        · have hdst : dst ≠ j := by
            exact fun h => hj h.symm
          have hs := deleteFirst_setCol_ne M j dst (fun i => c * v i) hdst
          have hb := deleteFirst_setCol_ne M j dst v hdst
          have hminor := ih (deleteFirst M j) (eraseIndex j dst hdst)
            (fun i => v i.succ)
          simp only [term, scaled, base]
          rw [hs, hb]
          have hfun : (fun i : Fin n => c * v i.succ) =
              fun i => c * (fun k => v k.succ) i := rfl
          rw [hfun, hminor]
          simp [setCol, hj]
          grind
      simp only [det]
      change (List.finRange (n + 1)).foldl
          (fun acc j => acc + term scaled j) 0 =
        c * (List.finRange (n + 1)).foldl
          (fun acc j => acc + term base j) 0
      calc
        (List.finRange (n + 1)).foldl
            (fun acc j => acc + term scaled j) 0 =
          (List.finRange (n + 1)).foldl
            (fun acc j => acc + c * term base j) (c * 0) := by
              apply foldl_congr
              · grind
              · intro acc j _hmem
                rw [hterm]
        _ = _ := foldl_add_mul_left (List.finRange (n + 1)) c
          (fun j => term base j) 0

/-- Replacing a column by zero makes the local determinant vanish. -/
theorem det_setCol_zero {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R n) (dst : Fin n) :
    det (setCol M dst (fun _ => 0)) = 0 := by
  have h := det_setCol_smul M dst (0 : R) (fun _ => 1)
  have hcol : (fun _ : Fin n => (0 : R)) = fun i => 0 * (1 : R) := by
    funext i
    grind
  rw [hcol]
  exact h.trans (by grind)

/-! # Bridge to the reusable matrix determinant

The finite-function determinant remains the definition used by the resultant
development.  This bridge lets later proof-only cofactor arguments reuse the
row and adjugate algebra of `HexDeterminant` without changing that definition.
-/

/-- Regard a proof-only square coefficient family as a `Hex.Matrix`. -/
@[expose]
def toMatrix {R : Type u} {n : Nat} (M : Square R n) : Matrix R n n :=
  Matrix.ofFn M

/-- Entries are unchanged by the matrix view.  Stated in the nested
`M[i][j]` form like `Matrix.getElem_ofFn`, so it is `grind`-only: the
simp-normal form of the left-hand side goes through `Matrix.getRow`. -/
@[grind =]
theorem toMatrix_get {R : Type u} {n : Nat} (M : Square R n)
    (i j : Fin n) : (toMatrix M)[i][j] = M i j := by
  rw [toMatrix, Matrix.getElem_ofFn]

/-- The local first-row Laplace determinant agrees with the reusable Leibniz
matrix determinant. -/
theorem det_toMatrix {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R n) : det M = Matrix.det (toMatrix M) := by
  induction n with
  | zero =>
      rw [det_zero]
      have h := Matrix.det_principalSubmatrix_zero (toMatrix M)
      have hmatrix :
          Matrix.principalSubmatrix (toMatrix M) 0 (Nat.zero_le 0) =
            toMatrix M := by
        apply Matrix.ext_getElem
        intro i
        exact Fin.elim0 i
      rw [hmatrix] at h
      exact h.symm
  | succ n ih =>
      let row : Fin (n + 1) := ⟨0, by omega⟩
      change
        (List.finRange (n + 1)).foldl
            (fun acc j =>
              acc + sign j.val * M row j * det (deleteFirst M j)) 0 =
          Matrix.det (toMatrix M)
      rw [Matrix.det_eq_foldl_laplace_row (toMatrix M) row]
      simp only [toMatrix_get]
      change
        (List.finRange (n + 1)).foldl
            (fun acc j =>
              acc + sign j.val * M row j * det (deleteFirst M j)) 0 =
          (List.finRange (n + 1)).foldl
            (fun acc j =>
              acc + M row j * Matrix.cofactor (toMatrix M) row j) 0
      apply foldl_congr
      · rfl
      · intro acc j _hj
        have hminor :
            Matrix.deleteRowCol (toMatrix M) row j =
              toMatrix (deleteFirst M j) := by
          apply Matrix.ext_getElem
          intro i k
          rw [Matrix.getElem_deleteRowCol, toMatrix_get, toMatrix_get]
          rfl
        have hsign : sign (R := R) j.val =
            Matrix.cofactorSign (R := R) row j := by
          unfold sign Matrix.cofactorSign
          by_cases h : j.val % 2 = 0
          · rw [ite_eq_left h, ite_eq_left (by simpa [row] using h)]
          · rw [ite_eq_right h, ite_eq_right (by simpa [row] using h)]
            grind
        unfold Matrix.cofactor
        rw [hminor, ← ih, ← hsign]
        grind

/-- A local determinant with two equal rows vanishes. -/
theorem det_eq_zero_of_row_eq {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R n) (src dst : Fin n) (h : src ≠ dst)
    (hrow : ∀ j, M src j = M dst j) :
    det M = 0 := by
  rw [det_toMatrix]
  apply Matrix.det_eq_zero_of_row_eq (toMatrix M) src dst h
  apply Vector.ext
  intro j hj
  change (toMatrix M)[src][(⟨j, hj⟩ : Fin n)] =
    (toMatrix M)[dst][(⟨j, hj⟩ : Fin n)]
  rw [toMatrix_get, toMatrix_get]
  exact hrow _

/-- A square matrix with nonzero determinant has trivial right kernel over an
exact-division domain. -/
theorem vector_eq_zero_of_mul_eq_zero {R : Type u}
    [Lean.Grind.CommRing R] [Div R] [ExactDivLaws R] {n : Nat}
    (M : Square R n) (hn : 0 < n) (hdet : det M ≠ 0) (v : Vector R n)
    (hmul : toMatrix M * v = 0) : ∀ j : Fin n, v[j] = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      have hassoc := Matrix.mul_assoc_vec
        (Matrix.adjugate (toMatrix M)) (toMatrix M) v
      have hscale :
          ((Matrix.det (toMatrix M)) • Matrix.identity (R := R) (n + 1)) * v =
            (Matrix.det (toMatrix M)) • v := by
        apply Vector.ext
        intro i hi
        let ii : Fin (n + 1) := ⟨i, hi⟩
        change
          (((Matrix.det (toMatrix M)) • Matrix.identity (R := R) (n + 1)) * v)[ii] =
            ((Matrix.det (toMatrix M)) • v)[ii]
        rw [Matrix.getElem_mulVec, Matrix.row_smul,
          Vector.dotProduct_smul_left]
        have hid := congrArg (fun w : Vector R (n + 1) => w[ii])
          (Matrix.identity_mulVec v)
        rw [Matrix.getElem_mulVec] at hid
        change ((Matrix.identity (R := R) (n + 1)).row ii).dotProduct v =
          v[ii] at hid
        have hentry : ((Matrix.det (toMatrix M)) • v)[ii] =
            Matrix.det (toMatrix M) * v[ii] := by
          simp only [Fin.getElem_fin, Vector.getElem_smul]
          rfl
        rw [hid, hentry]
      rw [Matrix.adjugate_mul, hscale, hmul, Matrix.mulVec_zero] at hassoc
      intro j
      have hj := congrArg (fun w : Vector R (n + 1) => w[j]) hassoc
      have hsmul : ((Matrix.det (toMatrix M)) • v)[j] =
          Matrix.det (toMatrix M) * v[j] := by
        simp only [Fin.getElem_fin, Vector.getElem_smul]
        rfl
      have hzero : (0 : Vector R (n + 1))[j] = 0 := by
        simp only [Fin.getElem_fin, Vector.getElem_zero]
      rw [hsmul, hzero] at hj
      rw [← det_toMatrix] at hj
      apply ExactDivLaws.mul_right_cancel hdet
      grind

/-- The signed cofactor of a column along the final row. -/
@[expose]
def lastCofactor {R : Type u} [Lean.Grind.CommRing R] :
    {n : Nat} → Square R n → Fin n → R
  | 0, _, j => Fin.elim0 j
  | n + 1, M, j => Matrix.cofactor (toMatrix M) (Fin.last n) j

/-- A final-row cofactor is independent of the entries in that final row. -/
theorem lastCofactor_congr {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M N : Square R n) (j : Fin n)
    (h : ∀ i k, i.val < n - 1 → M i k = N i k) :
    lastCofactor M j = lastCofactor N j := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
      simp only [lastCofactor]
      unfold Matrix.cofactor
      congr 1
      apply congrArg Matrix.det
      apply Matrix.ext_getElem
      intro i k
      rw [Matrix.getElem_deleteRowCol, Matrix.getElem_deleteRowCol,
        toMatrix_get, toMatrix_get]
      apply h
      simp [Matrix.skipIndex_last]

/-- Laplace expansion along the final row using `lastCofactor`. -/
theorem det_lastCofactor {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R (n + 1)) :
    det M = (List.finRange (n + 1)).foldl
      (fun acc j => acc + M (Fin.last n) j * lastCofactor M j) 0 := by
  rw [det_toMatrix, Matrix.det_eq_foldl_laplace_row (toMatrix M) (Fin.last n)]
  apply foldl_congr
  · rfl
  · intro acc j _hj
    simp only [toMatrix_get, lastCofactor]

/-- Laplace expansion along the final row, stated for an arbitrary positive
dimension. -/
theorem det_lastCofactor_of_pos {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Square R n) (hn : 0 < n) :
    det M = (List.finRange n).foldl
      (fun acc j => acc + M ⟨n - 1, by omega⟩ j * lastCofactor M j) 0 := by
  cases n with
  | zero => omega
  | succ n =>
      rw [det_lastCofactor M]
      apply foldl_congr
      · rfl
      · intro acc j _hj
        congr 2

/-! # Zero final row

The coefficient row in a generalized Sylvester minor is the last row.  The
local determinant recurses on the first row, so the following lemmas derive
its vanishing on a zero final row directly from that recursion. -/

/-- A square family with zero final row has zero determinant. -/
theorem det_lastRow_zero {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R (n + 1)) (hzero : ∀ j, M (Fin.last n) j = 0) :
    det M = 0 := by
  induction n with
  | zero =>
      change 0 + sign 0 * M 0 0 * 1 = 0
      have hentry : M 0 0 = 0 := by
        apply hzero
      rw [hentry]
      grind
  | succ n ih =>
      have hminor (j : Fin (n + 2)) : det (deleteFirst M j) = 0 := by
        apply ih
        intro k
        change M (Fin.last n).succ (skipIndex j k) = 0
        have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
          apply Fin.ext
          simp
        rw [hlast]
        exact hzero _
      change (List.finRange (n + 2)).foldl
        (fun acc j => acc + sign j.val * M 0 j * det (deleteFirst M j)) 0 = 0
      apply foldl_add_zero
      intro j _hj
      rw [hminor]
      grind

/-- A positive-dimensional square family with zero final row has zero
determinant. -/
theorem det_lastRow_zero_of_pos {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Square R n) (hn : 0 < n)
    (hzero : ∀ j, M ⟨n - 1, by omega⟩ j = 0) :
    det M = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      apply det_lastRow_zero M
      intro j
      have hlast : Fin.last n = ⟨n + 1 - 1, by omega⟩ := by
        apply Fin.ext
        simp
      rw [hlast]
      exact hzero j

/-- Scale a consecutive range of columns. -/
@[expose]
def scaleRange {R : Type u} [Mul R] {n : Nat} (M : Square R n)
    (start count : Nat) (c : R) : Square R n :=
  fun i j => if start ≤ j.val ∧ j.val < start + count then c * M i j else M i j

/-- Scaling `count` consecutive columns scales the determinant by
`c ^ count`. -/
theorem det_scaleRange {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Square R n) (start count : Nat) (c : R)
    (hbound : start + count ≤ n) :
    det (scaleRange M start count c) = c ^ count * det M := by
  induction count with
  | zero =>
      have hmatrix : scaleRange M start 0 c = M := by
        funext i j
        unfold scaleRange
        rw [ite_eq_right (by omega)]
      rw [hmatrix]
      rw [Lean.Grind.Semiring.pow_zero]
      grind
  | succ count ih =>
      have hdst : start + count < n := by
        omega
      let dst : Fin n := ⟨start + count, hdst⟩
      have hmatrix : scaleRange M start (count + 1) c =
          setCol (scaleRange M start count c) dst
            (fun i => c * scaleRange M start count c i dst) := by
        funext i j
        by_cases hj : j = dst
        · subst j
          have hold : ¬(start ≤ dst.val ∧ dst.val < start + count) := by
            simp [dst]
          have hnew : start ≤ dst.val ∧ dst.val < start + (count + 1) := by
            simp [dst]
          simp only [setCol]
          simp only [ite_true]
          unfold scaleRange
          rw [ite_eq_left hnew, ite_eq_right hold]
        · have hvalne : j.val ≠ start + count := by
            intro h
            exact hj (Fin.ext h)
          by_cases hold : start ≤ j.val ∧ j.val < start + count
          · have hnew : start ≤ j.val ∧ j.val < start + (count + 1) := by
              omega
            simp [setCol, scaleRange, hj, hold, hnew]
          · have hnew : ¬(start ≤ j.val ∧ j.val < start + (count + 1)) := by
              omega
            simp [setCol, scaleRange, hj, hold, hnew]
      rw [hmatrix, det_setCol_smul]
      rw [setCol_self]
      rw [ih (by omega)]
      rw [Lean.Grind.Semiring.pow_succ]
      grind

/-- Consecutive Laplace signs are negatives. -/
theorem sign_succ {R : Type u} [Lean.Grind.CommRing R] (j : Nat) :
    sign (R := R) (j + 1) = 0 - sign (R := R) j := by
  unfold sign
  by_cases hj : j % 2 = 0
  · have hnext : (j + 1) % 2 ≠ 0 := by
      omega
    rw [ite_eq_left hj, ite_eq_right hnext]
  · have hjone : j % 2 = 1 := by
      omega
    have hnext : (j + 1) % 2 = 0 := by
      omega
    rw [ite_eq_right hj, ite_eq_left hnext]
    grind

/-- Alternating signs turn addition of exponents into multiplication. -/
theorem sign_add {R : Type u} [Lean.Grind.CommRing R] (a b : Nat) :
    sign (R := R) (a + b) = sign (R := R) a * sign (R := R) b := by
  induction b with
  | zero =>
      simp [sign] <;> grind
  | succ b ih =>
      rw [Nat.add_succ, sign_succ, ih, sign_succ]
      grind

/-- A multiplied sign exponent is repeated multiplication of the sign. -/
theorem sign_mul {R : Type u} [Lean.Grind.CommRing R] (a : Nat) :
    ∀ b : Nat, sign (R := R) (a * b) = sign (R := R) a ^ b
  | 0 => by
      rw [Nat.mul_zero, Lean.Grind.Semiring.pow_zero]
      simp [sign]
  | b + 1 => by
      rw [Nat.mul_succ, sign_add, sign_mul a b,
        Lean.Grind.Semiring.pow_succ]

/-- Every alternating sign is its own multiplicative inverse. -/
theorem sign_mul_self {R : Type u} [Lean.Grind.CommRing R] (n : Nat) :
    sign (R := R) n * sign (R := R) n = 1 := by
  unfold sign
  split <;> grind

/-- Every alternating sign is nonzero in a nontrivial ring. -/
theorem sign_ne_zero {R : Type u} [Lean.Grind.CommRing R]
    (h1 : (1 : R) ≠ 0) (n : Nat) : sign (R := R) n ≠ 0 := by
  intro hzero
  have hself := sign_mul_self (R := R) n
  rw [hzero] at hself
  grind

/-- Deleting either member of an equal adjacent column pair gives the same
minor. -/
theorem deleteFirst_adjacent_eq {R : Type u} {n : Nat}
    (M : Square R (n + 2)) (left : Fin (n + 1))
    (hcol : ∀ i, M i left.castSucc = M i left.succ) :
    deleteFirst M left.castSucc = deleteFirst M left.succ := by
  funext i j
  unfold deleteFirst
  by_cases hlt : j.val < left.val
  · have hltRight : j.val < left.val + 1 := by
      omega
    simp [skipIndex, hlt, hltRight]
  · by_cases heq : j.val = left.val
    · have hj : j = left := Fin.ext heq
      subst j
      have hnotLeft : ¬left.val < left.val := by omega
      have hltRight : left.val < left.val + 1 := by omega
      simp [skipIndex, hnotLeft, hltRight]
      exact (hcol i.succ).symm
    · have hgt : left.val < j.val := by
        omega
      have hnotLeft : ¬j.val < left.val := by omega
      have hnotRight : ¬j.val < left.val + 1 := by omega
      simp [skipIndex, hnotLeft, hnotRight]

/-- The local determinant vanishes when two adjacent columns agree. -/
theorem det_eq_zero_of_adjacent_col_eq {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Square R (n + 1)) (left : Fin n)
    (hcol : ∀ i, M i left.castSucc = M i left.succ) :
    det M = 0 := by
  induction n with
  | zero => exact Fin.elim0 left
  | succ n ih =>
      let row : Fin (n + 2) := ⟨0, by omega⟩
      let term := fun j : Fin (n + 2) =>
        sign j.val * M row j * det (deleteFirst M j)
      have hzero (j : Fin (n + 2)) (hjleft : j ≠ left.castSucc)
          (hjright : j ≠ left.succ) : term j = 0 := by
        let left' := eraseAdjacent j left hjleft hjright
        have hminorCol (i : Fin (n + 1)) :
            deleteFirst M j i left'.castSucc =
              deleteFirst M j i left'.succ := by
          change M i.succ (skipIndex j left'.castSucc) =
            M i.succ (skipIndex j left'.succ)
          rw [skipIndex_eraseAdjacent_left j left hjleft hjright,
            skipIndex_eraseAdjacent_right j left hjleft hjright]
          exact hcol i.succ
        have hminor := ih (deleteFirst M j) left' hminorCol
        simp [term, hminor]
        grind
      have hcancel : term left.castSucc + term left.succ = 0 := by
        have hdelete := deleteFirst_adjacent_eq M left hcol
        have hentry := hcol row
        have hsign := sign_succ (R := R) left.val
        simp only [term]
        rw [hdelete, hentry]
        have hleftVal : left.castSucc.val = left.val := rfl
        have hrightVal : left.succ.val = left.val + 1 := rfl
        rw [hleftVal, hrightVal, hsign]
        grind
      simp only [det]
      change (List.finRange (n + 2)).foldl
        (fun acc j => acc + term j) 0 = 0
      rw [foldl_finRange_adjacent left term hzero]
      exact hcancel

/-- Swapping two adjacent columns negates the local determinant. -/
theorem det_swapAdjacent {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Square R (n + 1)) (left : Fin n) :
    det (swapAdjacent M left) = 0 - det M := by
  let a : Fin (n + 1) := left.castSucc
  let b : Fin (n + 1) := left.succ
  let va : Fin (n + 1) → R := fun i => M i a
  let vb : Fin (n + 1) → R := fun i => M i b
  let vsum : Fin (n + 1) → R := fun i => va i + vb i
  have hab : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    simp [a, b] at hval
  have hboth :
      det (setCol (setCol M a vsum) b vsum) = 0 := by
    apply det_eq_zero_of_adjacent_col_eq (left := left)
    intro i
    simp [setCol, a, b, hab, vsum]
  have hcomm :
      setCol (setCol M a vsum) b va =
        setCol (setCol M b va) a vsum := by
    funext i j
    by_cases hja : j = a
    · subst j
      simp [setCol, hab]
    · by_cases hjb : j = b
      · subst j
        simp [setCol, hja]
      · simp [setCol, hja, hjb]
  have hrestore :
      setCol (setCol M a vsum) b vb = setCol M a vsum := by
    funext i j
    by_cases hjb : j = b
    · subst j
      simp [setCol, vb, hab.symm]
    · simp [setCol, hjb]
  have hswap :
      setCol (setCol M b va) a vb = swapAdjacent M left := by
    funext i j
    by_cases hja : j = a
    · subst j
      simp [setCol, swapAdjacent, a, b, vb]
    · by_cases hjb : j = b
      · subst j
        simp [setCol, swapAdjacent, a, b, va, vb, hja]
      · simp [setCol, swapAdjacent, a, b, va, vb, hja, hjb]
  have hdupA : det (setCol (setCol M b va) a va) = 0 := by
    apply det_eq_zero_of_adjacent_col_eq (left := left)
    intro i
    simp [setCol, a, b, va]
  have hdupB : det (setCol M a vb) = 0 := by
    apply det_eq_zero_of_adjacent_col_eq (left := left)
    intro i
    simp [setCol, a, b, vb]
  have houter := det_setCol_add (setCol M a vsum) b va vb
  have hleft := det_setCol_add (setCol M b va) a va vb
  have hright := det_setCol_add M a va vb
  have hself : setCol M a va = M := setCol_self M a
  rw [show (fun i => va i + vb i) = vsum by rfl] at houter hleft hright
  rw [hboth, hcomm, hrestore, hleft, hright, hdupA, hdupB, hswap,
    hself] at houter
  grind

/-- Apply a sequence of adjacent column transpositions. -/
@[expose]
def applySwaps {R : Type u} {n : Nat} (M : Square R (n + 1))
    (swaps : List (Fin n)) : Square R (n + 1) :=
  swaps.foldl swapAdjacent M

/-- The empty swap sequence acts as the identity. -/
@[simp, grind =]
theorem applySwaps_nil {R : Type u} {n : Nat} (M : Square R (n + 1)) :
    applySwaps M [] = M := by
  rfl

/-- A swap sequence acts head first. -/
@[simp, grind =]
theorem applySwaps_cons {R : Type u} {n : Nat} (M : Square R (n + 1))
    (left : Fin n) (swaps : List (Fin n)) :
    applySwaps M (left :: swaps) = applySwaps (swapAdjacent M left) swaps := by
  rfl

/-- Concatenating swap sequences composes their column actions. -/
@[simp, grind =]
theorem applySwaps_append {R : Type u} {n : Nat} (M : Square R (n + 1))
    (xs ys : List (Fin n)) :
    applySwaps M (xs ++ ys) = applySwaps (applySwaps M xs) ys := by
  simp [applySwaps, List.foldl_append]

/-- A sequence of adjacent column transpositions multiplies the local
determinant by its parity sign. -/
theorem det_applySwaps {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Square R (n + 1)) (swaps : List (Fin n)) :
    det (applySwaps M swaps) = sign (R := R) swaps.length * det M := by
  induction swaps generalizing M with
  | nil =>
      simp [applySwaps, sign]
      grind
  | cons left swaps ih =>
      rw [applySwaps_cons, ih, det_swapAdjacent]
      have hsign := sign_succ (R := R) swaps.length
      simp only [List.length_cons]
      rw [hsign]
      grind

/-- Ordered form of arbitrary duplicate-column vanishing, by descending
recursion on the column gap through one adjacent swap. -/
private theorem det_eq_zero_of_col_eq_of_lt {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (M : Square R (n + 1))
    (a b : Fin (n + 1)) (hab : a.val < b.val)
    (hcol : ∀ i, M i a = M i b) :
    det M = 0 := by
  by_cases hadj : b.val = a.val + 1
  · let left : Fin n := ⟨a.val, by omega⟩
    have ha : left.castSucc = a := by
      apply Fin.ext
      rfl
    have hb : left.succ = b := by
      apply Fin.ext
      simp [left]
      omega
    apply det_eq_zero_of_adjacent_col_eq M left
    intro i
    rw [ha, hb]
    exact hcol i
  · let left : Fin n := ⟨b.val - 1, by omega⟩
    have hbefore : a.val < left.val := by
      simp [left]
      omega
    have haLeft : a ≠ left.castSucc := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
      omega
    have haRight : a ≠ left.succ := by
      intro h
      have hval := congrArg Fin.val h
      simp [left] at hval
      omega
    have hright : left.succ = b := by
      apply Fin.ext
      simp [left]
      omega
    let N := swapAdjacent M left
    have hcolN (i : Fin (n + 1)) :
        N i a = N i left.castSucc := by
      rw [show N i a = M i a by
        exact swapAdjacent_of_ne M left i a haLeft haRight]
      rw [show N i left.castSucc = M i left.succ by
        exact swapAdjacent_left M left i]
      rw [hright]
      exact hcol i
    have hzero := det_eq_zero_of_col_eq_of_lt N a left.castSucc hbefore hcolN
    have hswap := det_swapAdjacent M left
    change det N = 0 at hzero
    change det N = 0 - det M at hswap
    rw [hzero] at hswap
    grind
termination_by b.val - a.val
decreasing_by
  simp_wf
  omega

/-- The local determinant vanishes when any two distinct columns agree. -/
theorem det_eq_zero_of_col_eq {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Square R n) (a b : Fin n)
    (hab : a ≠ b) (hcol : ∀ i, M i a = M i b) :
    det M = 0 := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ n =>
      by_cases hlt : a.val < b.val
      · exact det_eq_zero_of_col_eq_of_lt M a b hlt hcol
      · have hgt : b.val < a.val := by
          have hval : a.val ≠ b.val := by
            intro h
            exact hab (Fin.ext h)
          omega
        exact det_eq_zero_of_col_eq_of_lt M b a hgt (fun i => (hcol i).symm)

/-- Add a scalar multiple of one column to another. -/
@[expose]
def addCol {R : Type u} [Add R] [Mul R] {n : Nat}
    (M : Square R n) (src dst : Fin n) (c : R) : Square R n :=
  setCol M dst (fun i => M i dst + c * M i src)

/-- Entrywise value of a scaled column addition. -/
@[simp, grind =]
theorem addCol_apply {R : Type u} [Add R] [Mul R] {n : Nat}
    (M : Square R n) (src dst : Fin n) (c : R) (i j : Fin n) :
    addCol M src dst c i j =
      if j = dst then M i dst + c * M i src else M i j := by
  rfl

/-- Adding a scalar multiple of one column to a distinct column preserves the
local determinant. -/
theorem det_addCol {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Square R n) (src dst : Fin n)
    (c : R) (h : src ≠ dst) :
    det (addCol M src dst c) = det M := by
  cases n with
  | zero => exact Fin.elim0 src
  | succ n =>
      unfold addCol
      rw [det_setCol_add, det_setCol_smul]
      have hdup : det (setCol M dst (fun i => M i src)) = 0 := by
        apply det_eq_zero_of_col_eq (a := src) (b := dst) (hab := h)
        intro i
        simp [setCol, h]
      rw [hdup, setCol_self]
      grind

end SubresultantMinor

namespace DensePoly
namespace Subresultant

section Scale

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]

/-- Integer-indexed coefficient lookup commutes with scalar multiplication. -/
@[simp]
theorem coeffInt_scale (c : R) (p : DensePoly R) (i : Int) :
    coeffInt (scale c p) i = c * coeffInt p i := by
  unfold coeffInt
  by_cases h : i < 0
  · rw [ite_eq_left h, ite_eq_left h]
    grind
  · rw [ite_eq_right h, ite_eq_right h]
    exact coeff_scale_semiring c p i.toNat

/-- Scaling the left polynomial scales exactly the left Sylvester block. -/
theorem coeffMatrixAt_scale_left (df dg J l : Nat) (c : R)
    (f g : DensePoly R) :
    coeffMatrixAt df dg J l (scale c f) g =
      SubresultantMinor.scaleRange (coeffMatrixAt df dg J l f g)
        0 (dg - J) c := by
  funext i j
  simp only [coeffMatrixAt, SubresultantMinor.scaleRange]
  by_cases hj : j.val < dg - J
  · have hscaled : 0 ≤ j.val ∧ j.val < 0 + (dg - J) := by
      omega
    simp only [ite_eq_left hj, ite_eq_left hscaled]
    by_cases hi : i.val = (df - J) + (dg - J) - 1
    · simp only [ite_eq_left hi, coeffInt_scale]
    · simp only [ite_eq_right hi, coeffInt_scale]
  · have hscaled : ¬(0 ≤ j.val ∧ j.val < 0 + (dg - J)) := by
      omega
    simp only [ite_eq_right hj, ite_eq_right hscaled]

/-- Scaling the right polynomial scales exactly the right Sylvester block. -/
theorem coeffMatrixAt_scale_right (df dg J l : Nat) (c : R)
    (f g : DensePoly R) :
    coeffMatrixAt df dg J l f (scale c g) =
      SubresultantMinor.scaleRange (coeffMatrixAt df dg J l f g)
        (dg - J) (df - J) c := by
  funext i j
  simp only [coeffMatrixAt, SubresultantMinor.scaleRange]
  by_cases hj : j.val < dg - J
  · have hscaled : ¬(dg - J ≤ j.val ∧ j.val < dg - J + (df - J)) := by
      omega
    simp only [ite_eq_left hj, ite_eq_right hscaled]
  · have hlower : dg - J ≤ j.val := by omega
    have hupper : j.val < dg - J + (df - J) := by
      have hjbound := j.isLt
      omega
    have hscaled : dg - J ≤ j.val ∧ j.val < dg - J + (df - J) :=
      ⟨hlower, hupper⟩
    simp only [ite_eq_right hj, ite_eq_left hscaled]
    by_cases hi : i.val = (df - J) + (dg - J) - 1
    · simp only [ite_eq_left hi, coeffInt_scale]
    · simp only [ite_eq_right hi, coeffInt_scale]

/-- Fixed-degree coefficient minors are homogeneous in the left polynomial. -/
theorem coeffMinorAt_scale_left (df dg J l : Nat) (c : R)
    (f g : DensePoly R) :
    coeffMinorAt df dg J l (scale c f) g =
      c ^ (dg - J) * coeffMinorAt df dg J l f g := by
  unfold coeffMinorAt
  rw [coeffMatrixAt_scale_left]
  apply SubresultantMinor.det_scaleRange
  omega

/-- Fixed-degree coefficient minors are homogeneous in the right polynomial. -/
theorem coeffMinorAt_scale_right (df dg J l : Nat) (c : R)
    (f g : DensePoly R) :
    coeffMinorAt df dg J l f (scale c g) =
      c ^ (df - J) * coeffMinorAt df dg J l f g := by
  unfold coeffMinorAt
  rw [coeffMatrixAt_scale_right]
  apply SubresultantMinor.det_scaleRange
  omega

variable [Div R] [ExactDivLaws R]

private theorem formalDegree_scale {c : R} (hc : c ≠ 0) (p : DensePoly R) :
    formalDegree (scale c p) = formalDegree p := by
  unfold formalDegree
  rw [DensePoly.size_scale hc]

/-- Generalized coefficient minors are homogeneous in the left polynomial. -/
theorem coeffMinor_scale_left {c : R} (hc : c ≠ 0) (J l : Nat)
    (f g : DensePoly R) :
    coeffMinor J l (scale c f) g =
      c ^ (formalDegree g - J) * coeffMinor J l f g := by
  unfold coeffMinor
  rw [formalDegree_scale hc]
  exact coeffMinorAt_scale_left (formalDegree f) (formalDegree g) J l c f g

/-- Generalized coefficient minors are homogeneous in the right polynomial. -/
theorem coeffMinor_scale_right {c : R} (hc : c ≠ 0) (J l : Nat)
    (f g : DensePoly R) :
    coeffMinor J l f (scale c g) =
      c ^ (formalDegree f - J) * coeffMinor J l f g := by
  unfold coeffMinor
  rw [formalDegree_scale hc]
  exact coeffMinorAt_scale_right (formalDegree f) (formalDegree g) J l c f g

/-- Generalized subresultants are homogeneous in the left polynomial. -/
theorem poly_scale_left {c : R} (hc : c ≠ 0) (J : Nat)
    (f g : DensePoly R) :
    poly J (scale c f) g =
      scale (c ^ (formalDegree g - J)) (poly J f g) := by
  apply ext_coeff
  intro l
  rw [coeff_scale_semiring]
  simp only [coeff_poly]
  by_cases hl : l < J + 1
  · rw [ite_eq_left hl, ite_eq_left hl, coeffMinor_scale_left hc]
  · rw [ite_eq_right hl, ite_eq_right hl]
    exact (Lean.Grind.Semiring.mul_zero _).symm

/-- Generalized subresultants are homogeneous in the right polynomial. -/
theorem poly_scale_right {c : R} (hc : c ≠ 0) (J : Nat)
    (f g : DensePoly R) :
    poly J f (scale c g) =
      scale (c ^ (formalDegree f - J)) (poly J f g) := by
  apply ext_coeff
  intro l
  rw [coeff_scale_semiring]
  simp only [coeff_poly]
  by_cases hl : l < J + 1
  · rw [ite_eq_left hl, ite_eq_left hl, coeffMinor_scale_right hc]
  · rw [ite_eq_right hl, ite_eq_right hl]
    exact (Lean.Grind.Semiring.mul_zero _).symm

end Scale
end Subresultant
end DensePoly
end Hex
