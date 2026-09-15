/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdeal.Minors
public import HexMatrix.Lists
public import HexMvPoly.Kernel

@[expose] public section

namespace Hex.Matrix

/-- Increasing tuples with entries below both the ambient size and the
current bound, grouped by their final entry. -/
def indexTuplesUpTo (n : Nat) : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | r + 1, bound =>
    ((List.range n).filter (fun i => Nat.blt i bound)).flatMap fun i =>
      (indexTuplesUpTo n r i).map (fun pref => pref ++ [i])

/-- Increasing index tuples in colexicographic order. -/
def indexTuples (r n : Nat) : List (List Nat) := indexTuplesUpTo n r n

/-- Operations on the entry encoding used by a kernel minor computation. -/
structure MinorArithmetic (α : Type u) where
  zero : α
  one : α
  add : α → α → α
  mul : α → α → α
  neg : α → α
  isZero : α → Bool
  beq : α → α → Bool

/-- Integer arithmetic through the kernel's integer primitives. -/
def MinorArithmetic.int : MinorArithmetic Int where
  zero := 0
  one := 1
  add := Int.add
  mul := Int.mul
  neg := Int.neg
  isZero z := decide (z = 0)
  beq a b := decide (a = b)

/-- Reference ring operations for the denotation theorem. -/
def MinorArithmetic.ring (R : Type u) [Lean.Grind.CommRing R] [DecidableEq R] :
    MinorArithmetic R where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := Neg.neg
  isZero z := decide (z = 0)
  beq a b := decide (a = b)

/-- Canonical polynomial term-list arithmetic. -/
def MinorArithmetic.poly [Zero C] [One C] [Add C] [Mul C] [Neg C] [DecidableEq C]
    (k : Nat) : MinorArithmetic (MvPoly.Kernel.PolyList C) where
  zero := []
  one := MvPoly.Kernel.one k
  add := MvPoly.Kernel.add
  mul := MvPoly.Kernel.mul
  neg := MvPoly.Kernel.neg
  isZero := MvPoly.Kernel.isZero
  beq := MvPoly.Kernel.beq

/-- A selected minor by first-row Laplace expansion, structurally recursive
on its row list. Out-of-range entries are padded with zero. -/
def minorList (ops : MinorArithmetic α) : List Nat → List Nat → List (List α) → α
  | [], _, _ => ops.one
  | i :: rows, cols, L =>
    cols.zipIdx.foldl (fun acc (j, pos) =>
      let term := ops.mul (Lists.entry ops.zero (Lists.entry [] L i) j)
        (minorList ops rows (cols.eraseIdx pos) L)
      ops.add acc (if Nat.beq (Nat.mod pos 2) 0 then term else ops.neg term)) ops.zero

/-- All minors, with row selections outermost and column selections innermost. -/
def minorsList (ops : MinorArithmetic α) (r : Nat) (L : List (List α)) : List α :=
  (indexTuples r L.length).flatMap fun rows =>
    (indexTuples r (Lists.entry [] L 0).length).map fun cols => minorList ops rows cols L

/-- Nonzero distinct minors, preserving their first occurrences. -/
def detIdealGensList (ops : MinorArithmetic α) (r : Nat) (L : List (List α)) : List α :=
  ((minorsList ops r L).filter (fun x => !ops.isZero x)).eraseDupsBy ops.beq

private theorem map_finRange (n : Nat) :
    (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

/-- The list encoding preserves the reference enumeration, including order. -/
theorem indexTuplesUpTo_eq (n r bound : Nat) :
    indexTuplesUpTo n r bound =
      (selectedColumnTuplesUpTo n r bound).map (fun t => t.toList.map Fin.val) := by
  induction r generalizing bound with
  | zero => rfl
  | succ r ih =>
    simp only [indexTuplesUpTo, selectedColumnTuplesUpTo, List.map_flatMap]
    rw [← map_finRange, List.filter_map, List.flatMap_map]
    congr 1
    · funext i
      simp only [ih, List.map_map, Function.comp_def, Vector.toList_push, List.map_append,
        List.map_cons, List.map_nil]
    · congr 1
      funext i
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply, Nat.blt_eq, decide_eq_true_eq]

/-- The reference selections read as ordinary natural-number lists. -/
theorem indexTuples_eq_selectedColumnTuples (r n : Nat) :
    indexTuples r n = (selectedColumnTuples r n).map (fun t => t.toList.map Fin.val) :=
  indexTuplesUpTo_eq n r n

/-- There is one list for each choice of a row or column set. -/
theorem length_indexTuples (r n : Nat) : (indexTuples r n).length = Nat.choose n r := by
  rw [indexTuples_eq_selectedColumnTuples, List.length_map, length_selectedColumnTuples]

/-- Enumeration includes every pair of row and column selections. -/
theorem length_minorsList (ops : MinorArithmetic α) (r : Nat) (L : List (List α)) :
    (minorsList ops r L).length =
      Nat.choose L.length r * Nat.choose (Lists.entry [] L 0).length r := by
  have hsum (xs : List (List Nat)) (k : Nat) :
      (xs.map (fun _ => k)).sum = xs.length * k := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]
  simp [minorsList, List.length_flatMap, length_indexTuples, hsum]

/-- The unique empty minor has value one, at every matrix shape. -/
theorem minorsList_zero (ops : MinorArithmetic α) (L : List (List α)) :
    minorsList ops 0 L = [ops.one] := rfl

private theorem erase_map (f : α → β) (xs : List α) (i : Nat) :
    (xs.map f).eraseIdx i = (xs.eraseIdx i).map f := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih => cases i <;> simp [ih]

private theorem split_rows (v : Vector α (r + 1)) :
    v.toList = v[0] :: (v.eraseIdx 0).toList := by
  rw [Vector.toList_eraseIdx]
  have h (xs : List α) (hpos : 0 < xs.length) :
      xs = xs[0] :: xs.eraseIdx 0 := by
    cases xs with
    | nil => simp only [List.length_nil] at hpos; omega
    | cons => rfl
  simpa using h v.toList (by simp)

private theorem zip_indices (v : Vector (Fin n) r) :
    (v.toList.map Fin.val).zipIdx =
      (List.finRange r).map (fun i => (v[i].val, i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getElem_zipIdx]

/-- First-row list Laplace expansion computes the reference selected minor. -/
theorem minorList_eq_det_laplace {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
    {n m r : Nat} (L : List (List R)) (A : Matrix R n m)
    (hL : ∀ (i : Fin n) (j : Fin m), Lists.entry 0 (Lists.entry [] L i.val) j.val = A[i][j])
    (rows : Vector (Fin n) r) (cols : Vector (Fin m) r) :
    minorList (MinorArithmetic.ring R) (rows.toList.map Fin.val) (cols.toList.map Fin.val) L =
      det (selectedSubmatrix A rows cols) := by
  induction r with
  | zero =>
    have hrows : rows.toList = [] := List.eq_nil_of_length_eq_zero (by simp)
    simp [hrows, minorList, MinorArithmetic.ring, det_fin_zero]
  | succ r ih =>
    conv => lhs; rw [split_rows rows, List.map_cons, minorList]
    rw [zip_indices, List.foldl_map, det_eq_foldl_laplace_row _ 0]
    apply List.foldl_congr
    intro acc j hj
    simp only [erase_map]
    rw [← Vector.toList_eraseIdx j.isLt, ih]
    simp only [MinorArithmetic.ring, hL, getElem_selectedSubmatrix,
      cofactor, deleteRowCol_selectedSubmatrix, cofactorSign]
    simp only [Fin.val_zero, Nat.zero_add, Nat.beq_eq]
    have hmod : Nat.mod j.val 2 = j.val % 2 := rfl
    rw [hmod]
    by_cases h : j.val % 2 = 0 <;> simp [h] <;> grind

/-- An interpretation of entry encodings, including the invariant required
for arithmetic and equality to agree with their ring meanings. -/
structure MinorArithmetic.Interpretation (ops : MinorArithmetic α)
    (R : Type u) [Lean.Grind.CommRing R] where
  Valid : α → Prop
  denote : α → R
  valid_zero : Valid ops.zero
  valid_one : Valid ops.one
  valid_add : ∀ {a b}, Valid a → Valid b → Valid (ops.add a b)
  valid_mul : ∀ {a b}, Valid a → Valid b → Valid (ops.mul a b)
  valid_neg : ∀ {a}, Valid a → Valid (ops.neg a)
  denote_zero : denote ops.zero = 0
  denote_one : denote ops.one = 1
  denote_add : ∀ {a b}, Valid a → Valid b → denote (ops.add a b) = denote a + denote b
  denote_mul : ∀ {a b}, Valid a → Valid b → denote (ops.mul a b) = denote a * denote b
  denote_neg : ∀ {a}, Valid a → denote (ops.neg a) = -denote a
  isZero_iff : ∀ {a}, Valid a → (ops.isZero a = true ↔ denote a = 0)
  beq_iff : ∀ {a b}, Valid a → Valid b → (ops.beq a b = true ↔ denote a = denote b)

namespace MinorArithmetic.Interpretation

variable {ops : MinorArithmetic α} {R : Type u} [Lean.Grind.CommRing R]
  (φ : ops.Interpretation R)

/-- List lookup preserves an invariant satisfied by entries and padding. -/
theorem valid_entry (d : α) (hd : φ.Valid d) (xs : List α)
    (hxs : ∀ x ∈ xs, φ.Valid x) (i : Nat) : φ.Valid (Lists.entry d xs i) := by
  induction xs generalizing i with
  | nil => exact hd
  | cons x xs ih =>
    cases i with
    | zero => exact hxs x (by simp)
    | succ i => exact ih (fun y hy => hxs y (by simp [hy])) i

/-- Summation preserves the entry invariant. -/
theorem valid_sum (xs : List β) (f : β → α) (hf : ∀ x ∈ xs, φ.Valid (f x))
    (a : α) (ha : φ.Valid a) : φ.Valid (xs.foldl (fun acc x => ops.add acc (f x)) a) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (fun y hy => hf y (by simp [hy])) _ (φ.valid_add ha (hf x (by simp)))

/-- Interpret a sum using only valid entries and a valid accumulator. -/
theorem denote_sum (xs : List β) (f : β → α) (hf : ∀ x ∈ xs, φ.Valid (f x))
    (a : α) (ha : φ.Valid a) :
    φ.denote (xs.foldl (fun acc x => ops.add acc (f x)) a) =
      xs.foldl (fun acc x => acc + φ.denote (f x)) (φ.denote a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun y hy => hf y (by simp [hy])) _ (φ.valid_add ha (hf x (by simp))),
      φ.denote_add ha (hf x (by simp))]

/-- Matrix lookup preserves the entry invariant, including padded entries. -/
theorem valid_get (L : List (List α))
    (hL : ∀ row ∈ L, ∀ x ∈ row, φ.Valid x) (i j : Nat) :
    φ.Valid (Lists.entry ops.zero (Lists.entry [] L i) j) := by
  apply φ.valid_entry _ φ.valid_zero
  induction L generalizing i with
  | nil => simp [Lists.entry]
  | cons row rest ih =>
    cases i with
    | zero => exact hL row (by simp)
    | succ i => exact ih (fun row hr => hL row (by simp [hr])) i

/-- Every selected minor preserves the entry invariant. -/
theorem valid_minor (L : List (List α))
    (hL : ∀ row ∈ L, ∀ x ∈ row, φ.Valid x) (rows cols : List Nat) :
    φ.Valid (minorList ops rows cols L) := by
  induction rows generalizing cols with
  | nil => exact φ.valid_one
  | cons i rows ih =>
    apply φ.valid_sum _ _ _ _ φ.valid_zero
    intro x hx
    split
    · exact φ.valid_mul (φ.valid_get L hL i x.1) (ih _)
    · exact φ.valid_neg (φ.valid_mul (φ.valid_get L hL i x.1) (ih _))

/-- Interpretation commutes with padded list lookup. -/
theorem entry_map (f : α → β) (d : α) (xs : List α) (i : Nat) :
    f (Lists.entry d xs i) = Lists.entry (f d) (xs.map f) i := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [Lists.entry, ih]

/-- Interpreting entry encodings commutes with selected-minor computation. -/
theorem denote_minor [DecidableEq R] (L : List (List α))
    (hL : ∀ row ∈ L, ∀ x ∈ row, φ.Valid x) (rows cols : List Nat) :
    φ.denote (minorList ops rows cols L) =
      minorList (MinorArithmetic.ring R) rows cols (L.map (List.map φ.denote)) := by
  have hentry (i j : Nat) : φ.denote (Lists.entry ops.zero (Lists.entry [] L i) j) =
      Lists.entry 0 (Lists.entry [] (L.map (List.map φ.denote)) i) j := by
    rw [entry_map φ.denote ops.zero _ j, φ.denote_zero,
      entry_map (List.map φ.denote) [] L i]
    rfl
  induction rows generalizing cols with
  | nil => exact φ.denote_one
  | cons i rows ih =>
    let term (x : Nat × Nat) :=
      let t := ops.mul (Lists.entry ops.zero (Lists.entry [] L i) x.1)
        (minorList ops rows (cols.eraseIdx x.2) L)
      if Nat.beq (Nat.mod x.2 2) 0 then t else ops.neg t
    have ht (x : Nat × Nat) : φ.Valid (term x) := by
      dsimp [term]
      split
      · exact φ.valid_mul (φ.valid_get L hL i _) (φ.valid_minor L hL _ _)
      · exact φ.valid_neg (φ.valid_mul (φ.valid_get L hL i _) (φ.valid_minor L hL _ _))
    change φ.denote (cols.zipIdx.foldl (fun acc x => ops.add acc (term x)) ops.zero) = _
    rw [φ.denote_sum _ _ (fun x _ => ht x) _ φ.valid_zero, φ.denote_zero, minorList]
    apply List.foldl_congr
    intro acc x hx
    dsimp [term, MinorArithmetic.ring]
    split
    · rw [φ.denote_mul (φ.valid_get L hL i _) (φ.valid_minor L hL _ _), ih, hentry]
      rfl
    · rw [φ.denote_neg (φ.valid_mul (φ.valid_get L hL i _) (φ.valid_minor L hL _ _)),
        φ.denote_mul (φ.valid_get L hL i _) (φ.valid_minor L hL _ _), ih, hentry]
      rfl

end MinorArithmetic.Interpretation

/-- Canonical polynomial lists interpret into the executable polynomial ring. -/
def MinorArithmetic.polyInterpretation {k : Nat} {C : Type u}
    [Lean.Grind.CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
    {cmp : Mono k → Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    (MinorArithmetic.poly (C := C) k).Interpretation (MvPoly k C cmp) where
  Valid := MvPoly.Kernel.Canonical k
  denote := MvPoly.Kernel.denote
  valid_zero := by simp [MinorArithmetic.poly, MvPoly.Kernel.Canonical]
  valid_one := MvPoly.Kernel.one_canonical k
  valid_add := MvPoly.Kernel.add_canonical
  valid_mul := MvPoly.Kernel.mul_canonical
  valid_neg := MvPoly.Kernel.neg_canonical
  denote_zero := rfl
  denote_one := MvPoly.Kernel.denote_one
  denote_add _ _ := MvPoly.Kernel.denote_add _ _
  denote_mul ha hb := MvPoly.Kernel.denote_mul _ _ ha.1 hb.1
  denote_neg _ := MvPoly.Kernel.denote_neg _
  isZero_iff := MvPoly.Kernel.isZero_iff
  beq_iff := MvPoly.Kernel.beq_iff

/-- The list enumeration agrees with all reference minors in the same order. -/
theorem minorsList_eq_minors [Lean.Grind.CommRing R] [DecidableEq R]
    (A : Matrix R n m) (r : Nat) :
    minorsList (MinorArithmetic.ring R) r (rowLists A) = minors r A := by
  cases r with
  | zero => rw [minorsList_zero, minors_zero]; rfl
  | succ r =>
    cases n with
    | zero =>
      have hL : rowLists A = [] := List.eq_nil_of_length_eq_zero (length_rowLists A)
      simp [hL, minorsList, indexTuples, indexTuplesUpTo,
        minors, selectedColumnTuples, selectedColumnTuplesUpTo]
    | succ n =>
      have hfirst : (Lists.entry [] (rowLists A) 0).length = m := by
        simpa using congrArg List.length (entry_rowLists A (0 : Fin (n + 1)))
      simp only [minorsList, length_rowLists, hfirst, indexTuples_eq_selectedColumnTuples,
        List.flatMap_map, List.map_map, Function.comp_def, minors]
      congr 1
      funext rows
      congr 1
      funext cols
      exact minorList_eq_det_laplace _ A (get_rowLists A) rows cols

namespace MinorArithmetic.Interpretation

variable {ops : MinorArithmetic α} {R : Type u} [Lean.Grind.CommRing R]
  (φ : ops.Interpretation R)

theorem valid_minors (L : List (List α))
    (hL : ∀ row ∈ L, ∀ x ∈ row, φ.Valid x) (r : Nat) :
    ∀ x ∈ minorsList ops r L, φ.Valid x := by
  intro x hx
  obtain ⟨rows, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨cols, _, rfl⟩ := List.mem_map.mp hx
  exact φ.valid_minor L hL rows cols

theorem denote_minors [DecidableEq R] (L : List (List α))
    (hL : ∀ row ∈ L, ∀ x ∈ row, φ.Valid x) (r : Nat) :
    (minorsList ops r L).map φ.denote =
      minorsList (MinorArithmetic.ring R) r (L.map (List.map φ.denote)) := by
  have hdim : (Lists.entry [] (L.map (List.map φ.denote)) 0).length =
      (Lists.entry [] L 0).length := by
    simpa using (congrArg List.length (entry_map (List.map φ.denote) [] L 0)).symm
  simp only [minorsList, List.length_map, hdim, List.map_flatMap, List.map_map,
    Function.comp_def, φ.denote_minor L hL]

/-- A single checked row and column selection certifies membership without
evaluating the complete enumeration of minor values. -/
theorem minor_mem [DecidableEq R] (L : List (List α))
    (hL : ∀ row ∈ L, ∀ x ∈ row, φ.Valid x) (A : Matrix R n m)
    (hA : L.map (List.map φ.denote) = rowLists A) (r : Nat)
    (rows cols : List Nat) (hr : rows ∈ indexTuples r n) (hc : cols ∈ indexTuples r m) :
    φ.denote (minorList ops rows cols L) ∈ minors r A := by
  rw [indexTuples_eq_selectedColumnTuples] at hr hc
  obtain ⟨rs, hrs, rfl⟩ := List.mem_map.mp hr
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
  rw [φ.denote_minor L hL, hA,
    minorList_eq_det_laplace _ A (get_rowLists A) rs cs]
  exact (mem_minors_iff A r _).mpr ⟨rs, hrs, cs, hcs, rfl⟩

/-- Equality reflection on valid entries transports first-occurrence deduplication. -/
theorem denote_dedup [DecidableEq R] (xs : List α) (hxs : ∀ x ∈ xs, φ.Valid x) :
    (xs.eraseDupsBy ops.beq).map φ.denote = (xs.map φ.denote).eraseDups := by
  have htest (x : α) (hx : φ.Valid x) (ys : List α) (hys : ∀ y ∈ ys, φ.Valid y) :
      (ys.map φ.denote).any (fun y => decide (φ.denote x = y)) = ys.any (ops.beq x) := by
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons, List.any_cons]
      rw [ih (fun z hz => hys z (by simp [hz]))]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact (φ.beq_iff hx (hys y (by simp))).symm
  have hloop (xs : List α) (hxs : ∀ x ∈ xs, φ.Valid x)
      (ys : List α) (hys : ∀ y ∈ ys, φ.Valid y) :
      (List.eraseDupsBy.loop ops.beq xs ys).map φ.denote =
        List.eraseDupsBy.loop (fun x y => decide (x = y)) (xs.map φ.denote) (ys.map φ.denote) := by
    induction xs generalizing ys with
    | nil => simp [List.eraseDupsBy.loop]
    | cons x xs ih =>
      simp only [List.eraseDupsBy.loop, List.map_cons, htest x (hxs x (by simp)) ys hys]
      split
      · exact ih (fun z hz => hxs z (by simp [hz])) ys hys
      · exact ih (fun z hz => hxs z (by simp [hz])) (x :: ys) (by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hxs z (by simp)
          · exact hys z hz)
  exact hloop xs hxs [] (by simp)

/-- Zero recognition on valid entries transports zero removal. -/
theorem denote_filter [DecidableEq R] (xs : List α) (hxs : ∀ x ∈ xs, φ.Valid x) :
    (xs.filter (fun x => !ops.isZero x)).map φ.denote =
      (xs.map φ.denote).filter (fun x => decide (x ≠ 0)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hz : (!ops.isZero x) = decide (φ.denote x ≠ 0) := by
      have hh := φ.isZero_iff (hxs x (by simp))
      cases he : ops.isZero x <;> simp_all
    simp only [List.filter_cons, List.map_cons, hz]
    split <;> simp_all

/-- Canonical minor arithmetic and equality transport the generating list. -/
theorem denote_gens [DecidableEq R] (L : List (List α))
    (hL : ∀ row ∈ L, ∀ x ∈ row, φ.Valid x) (A : Matrix R n m)
    (hA : L.map (List.map φ.denote) = rowLists A) (r : Nat) :
    (detIdealGensList ops r L).map φ.denote = detIdealGens r A := by
  rw [detIdealGensList, φ.denote_dedup _ (fun x hx =>
    φ.valid_minors L hL r x (List.mem_filter.mp hx).1),
    φ.denote_filter _ (φ.valid_minors L hL r), φ.denote_minors L hL r,
    hA, minorsList_eq_minors]
  rfl

end MinorArithmetic.Interpretation

/-- Canonical list minors denote exactly the reference generators. The entry
invariant supplies both zero recognition and equality reflection. -/
theorem detIdealGensList_denote {k : Nat} {C : Type u}
    [Lean.Grind.CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
    {cmp : Mono k → Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (L : List (List (MvPoly.Kernel.PolyList C))) (P : Matrix (MvPoly k C cmp) n m)
    (hL : ∀ row ∈ L, ∀ p ∈ row, MvPoly.Kernel.Canonical k p)
    (hP : L.map (List.map MvPoly.Kernel.denote) = rowLists P) (r : Nat) :
    (detIdealGensList (MinorArithmetic.poly k) r L).map MvPoly.Kernel.denote =
      detIdealGens r P :=
  MinorArithmetic.polyInterpretation.denote_gens L hL P hP r

/-- The membership certificate specialized to canonical polynomial lists. -/
theorem minorList_mem {k : Nat} {C : Type u}
    [Lean.Grind.CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
    {cmp : Mono k → Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (L : List (List (MvPoly.Kernel.PolyList C))) (P : Matrix (MvPoly k C cmp) n m)
    (hL : ∀ row ∈ L, ∀ p ∈ row, MvPoly.Kernel.Canonical k p)
    (hP : L.map (List.map MvPoly.Kernel.denote) = rowLists P) (r : Nat)
    (rows cols : List Nat) (hr : rows ∈ indexTuples r n) (hc : cols ∈ indexTuples r m) :
    MvPoly.Kernel.denote (minorList (MinorArithmetic.poly k) rows cols L) ∈ minors r P :=
  MinorArithmetic.polyInterpretation.minor_mem L hL P hP r rows cols hr hc

end Hex.Matrix
