/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib.Sound
public import HexMvPolyMathlib.Kernel
public import HexMatrixMathlib.Literal

@[expose] public section

namespace HexGenericRankMathlib

open Hex HexMatrixMathlib
open scoped HexMvPolyMathlib BigOperators

/-- A rank certificate quoted as rows of canonical polynomial term lists. -/
structure PolyWitness (C : Type) where
  rank : Nat
  rows : List Nat
  cols : List Nat
  denom : MvPoly.Kernel.PolyList C
  adj : List (List (MvPoly.Kernel.PolyList C))
  deriving Repr, Inhabited

namespace PolyLists

open Hex.Matrix.Lists (entry all)
open Hex.MvPoly.Kernel

variable {C : Type}

/-- The coefficient representation used by the list checker. -/
abbrev Poly (C : Type) := PolyList C

/-- A matrix represented entirely by lists. -/
abbrev Rows (C : Type) := List (List (Poly C))

/-- Padded entry lookup; validation checks dimensions separately. -/
def get (A : Rows C) (i j : Nat) : Poly C := entry [] (entry [] A i) j

/-- Tabulate rows without finite-index objects on the computation path. -/
def table (n m : Nat) (f : Nat → Nat → Poly C) : Rows C :=
  (List.range n).map fun i => (List.range m).map (f i)

/-- Sum a fixed number of polynomial terms. -/
def sum [Zero C] [Add C] [DecidableEq C] (f : Nat → Poly C) : Nat → Poly C
  | 0 => []
  | t + 1 => add (sum f t) (f t)

/-- One entry of a matrix product. -/
def product [Zero C] [Add C] [Mul C] [DecidableEq C] (r : Nat)
    (A B : Nat → Nat → Poly C) (i j : Nat) : Poly C :=
  sum (fun t => mul (A i t) (B t j)) r

/-- The selected pivot block. -/
def block (A : Rows C) (c : PolyWitness C) (i j : Nat) : Poly C :=
  get A (entry 0 c.rows i) (entry 0 c.cols j)

/-- The selected columns. -/
def columns (A : Rows C) (c : PolyWitness C) (i j : Nat) : Poly C :=
  get A i (entry 0 c.cols j)

/-- The selected rows. -/
def rows (A : Rows C) (c : PolyWitness C) (i j : Nat) : Poly C :=
  get A (entry 0 c.rows i) j

/-- Indices quote actual rows and columns of the input matrix. -/
def indices (n m : Nat) (c : PolyWitness C) : Bool :=
  Nat.beq c.rows.length c.rank && Nat.beq c.cols.length c.rank &&
  all (fun i => Nat.blt (entry 0 c.rows i) n && Nat.blt (entry 0 c.cols i) m) c.rank

/-- Exact matrix dimensions and canonical entries. -/
def valid [Zero C] [DecidableEq C] (k n m : Nat) (A : Rows C) : Bool :=
  Nat.beq A.length n && A.all (fun row => Nat.beq row.length m && row.all (isCanonical k))

/-- Verify the pivot-block identity as polynomial arithmetic on lists. -/
def pivotCheck [Zero C] [Add C] [Mul C] [DecidableEq C]
    (A : Rows C) (c : PolyWitness C) : Bool :=
  all (fun i => all (fun j => beq (product c.rank (block A c) (get c.adj) i j)
    (if Nat.beq i j then c.denom else [])) c.rank) c.rank

/-- Verify the all-column identity. The inner product is formed once as a row list. -/
def upperCheck [Zero C] [Add C] [Mul C] [DecidableEq C]
    (n m : Nat) (A : Rows C) (c : PolyWitness C) : Bool :=
  let middle := table c.rank m (product c.rank (get c.adj) (rows A c))
  all (fun i => all (fun j => beq (mul c.denom (get A i j))
    (product c.rank (columns A c) (get middle) i j)) m) n

end PolyLists

/-- Validate shape, canonical data, and the nonzero polynomial denominator. -/
def checkRankPolyHeader {C : Type} [Zero C] [DecidableEq C]
    (k n m : Nat) (A : PolyLists.Rows C) (c : PolyWitness C) : Bool :=
  PolyLists.indices n m c && PolyLists.valid k n m A &&
  PolyLists.valid k c.rank c.rank c.adj && MvPoly.Kernel.isCanonical k c.denom &&
  !MvPoly.Kernel.isZero c.denom

/-- Check the denominator, pivot-block identity, and all-column identity on
canonical term lists. Neither the reference matrix nor the producer is reduced. -/
def checkRankPolyList {C : Type} [Zero C] [Add C] [Mul C] [DecidableEq C]
    (k n m : Nat) (A : PolyLists.Rows C) (c : PolyWitness C) : Bool :=
  checkRankPolyHeader k n m A c && PolyLists.pivotCheck A c && PolyLists.upperCheck n m A c

/-- Combine separately kernel-checked parts without evaluating either identity again. -/
theorem checkRankPolyList_parts {C : Type} [Zero C] [Add C] [Mul C] [DecidableEq C]
    {k n m : Nat} {A : PolyLists.Rows C} {c : PolyWitness C}
    (hh : checkRankPolyHeader k n m A c = true)
    (hp : PolyLists.pivotCheck A c = true) (hu : PolyLists.upperCheck n m A c = true) :
    checkRankPolyList k n m A c = true := by
  simp only [checkRankPolyList, hh, hp, hu, Bool.and_self]

namespace PolyLists

open Hex.Matrix.Lists (entry all all_iff entry_eq_getD)
open Hex.MvPoly.Kernel

variable {C : Type} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C] {k : Nat}

/-- Denotation of one kernel polynomial in the reference polynomial ring. -/
def denote (p : Poly C) : MvPoly k C Mono.grevlex := MvPoly.Kernel.denote p

/-- Denotation of row lists, with the same definitional row constructor as numeric tactics. -/
def matrix (n m : Nat) (A : Rows C) : Hex.Matrix (MvPoly k C Mono.grevlex) n m :=
  matrixEquiv.symm (ofLists n m (A.map (List.map (denote (k := k)))))

theorem denote_nil : denote (k := k) ([] : Poly C) = 0 := rfl

theorem denote_add (p q : Poly C) :
    denote (k := k) (add p q) = denote p + denote q :=
  MvPoly.Kernel.denote_add p q

theorem denote_mul (p q : Poly C) (hp : Canonical k p) (hq : Canonical k q) :
    denote (k := k) (mul p q) = denote p * denote q :=
  MvPoly.Kernel.denote_mul p q hp.1 hq.1

omit [DecidableEq C] [BEq C] [LawfulBEq C] in
theorem canonical_nil : Canonical k ([] : Poly C) := by simp [Canonical]

theorem sum_canonical (f : Nat → Poly C) (r : Nat)
    (hf : ∀ i, i < r → Canonical k (f i)) : Canonical k (sum f r) := by
  induction r with
  | zero => exact canonical_nil
  | succ r ih => exact add_canonical (ih fun i hi => hf i (by omega)) (hf r (by omega))

theorem denote_sum (f : Nat → Poly C) (r : Nat) :
    denote (k := k) (sum f r) = ∑ i : Fin r, denote (f i) := by
  induction r with
  | zero => simp [sum, denote_nil]
  | succ r ih => rw [sum, denote_add, ih, Fin.sum_univ_castSucc]; rfl

theorem product_canonical (r : Nat) (A B : Nat → Nat → Poly C) (i j : Nat)
    (hA : ∀ t, t < r → Canonical k (A i t))
    (hB : ∀ t, t < r → Canonical k (B t j)) : Canonical k (product r A B i j) :=
  sum_canonical _ _ fun t ht => mul_canonical (hA t ht) (hB t ht)

theorem denote_product (r : Nat) (A B : Nat → Nat → Poly C) (i j : Nat)
    (hA : ∀ t, t < r → Canonical k (A i t))
    (hB : ∀ t, t < r → Canonical k (B t j)) :
    denote (k := k) (product r A B i j) =
      ∑ t : Fin r, denote (A i t) * denote (B t j) := by
  rw [product, denote_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact denote_mul _ _ (hA t t.isLt) (hB t t.isLt)

omit [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C] in
theorem get_table (n m : Nat) (f : Nat → Nat → Poly C) (i j : Nat)
    (hi : i < n) (hj : j < m) : get (table n m f) i j = f i j := by
  simp only [get, table, entry_eq_getD]
  rw [getD_eq_getElem' ((List.range n).map fun i => (List.range m).map (f i)) i []
    (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  rw [getD_eq_getElem' _ _ _ (by simpa using hj)]
  simp

theorem canonical_get {n m : Nat} {A : Rows C} (h : valid k n m A = true)
    (i j : Nat) : Canonical k (get A i j) := by
  simp only [valid, Bool.and_eq_true, List.all_eq_true] at h
  rw [get, entry_eq_getD, entry_eq_getD]
  by_cases hi : i < A.length
  · rw [getD_eq_getElem' A i [] hi]
    have hr := (h.2 _ (List.getElem_mem hi)).2
    by_cases hj : j < A[i].length
    · rw [getD_eq_getElem' _ _ _ hj]
      exact isCanonical_iff.mp (hr _ (List.getElem_mem hj))
    · rw [getD_eq_default' _ _ _ (by omega)]
      exact canonical_nil
  · rw [getD_eq_default' A i [] (by omega)]
    exact canonical_nil

theorem entry_map {α β : Type*} (f : α → β) (d : α) (xs : List α) (i : Nat) :
    entry (f d) (xs.map f) i = f (entry d xs i) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [entry, ih]

omit [DecidableEq C] in
theorem matrix_apply (n m : Nat) (A : Rows C) (i : Fin n) (j : Fin m) :
    matrixEquiv (matrix (k := k) n m A) i j = denote (get A i j) := by
  rw [matrix, Equiv.apply_symm_apply, ofLists_apply]
  simp only [← entry_eq_getD]
  change entry (denote [])
    (entry (List.map (denote (k := k)) []) (A.map (List.map (denote (k := k)))) i) j = _
  rw [entry_map, entry_map]
  rfl

theorem pivot_sound {n m : Nat} {A : Rows C} {c : PolyWitness C}
    (hA : valid k n m A = true) (hc : valid k c.rank c.rank c.adj = true)
    (h : pivotCheck A c = true) (i j : Fin c.rank) :
    (∑ t : Fin c.rank, denote (k := k) (block A c i t) * denote (get c.adj t j)) =
      if i = j then denote c.denom else 0 := by
  have h := (all_iff _ _).mp ((all_iff _ _).mp h i i.isLt) j j.isLt
  have he := congrArg (denote (k := k)) (beq_eq_true_iff.mp h)
  rw [denote_product c.rank (block A c) (get c.adj) i j (fun _ _ => canonical_get hA _ _)
    (fun _ _ => canonical_get hc _ _)] at he
  simpa [Nat.beq_eq, Fin.ext_iff, apply_ite, denote_nil] using he

theorem upper_sound {n m : Nat} {A : Rows C} {c : PolyWitness C}
    (hA : valid k n m A = true) (hc : valid k c.rank c.rank c.adj = true)
    (hd : Canonical k c.denom) (h : upperCheck n m A c = true)
    (i : Fin n) (j : Fin m) :
    denote (k := k) c.denom * denote (get A i j) =
      ∑ t : Fin c.rank, denote (columns A c i t) *
        (∑ s : Fin c.rank, denote (get c.adj t s) * denote (rows A c s j)) := by
  let middle := table c.rank m (product c.rank (get c.adj) (rows A c))
  have hm (t : Nat) (ht : t < c.rank) : Canonical k (get middle t j) := by
    rw [get_table _ _ _ _ _ ht j.isLt]
    exact product_canonical _ _ _ _ _ (fun _ _ => canonical_get hc _ _)
      (fun _ _ => canonical_get hA _ _)
  have he := congrArg (denote (k := k)) (beq_eq_true_iff.mp
    ((all_iff _ _).mp ((all_iff _ _).mp h i i.isLt) j j.isLt))
  change denote (mul c.denom (get A i j)) =
    denote (product c.rank (columns A c) (get middle) i j) at he
  rw [denote_mul _ _ hd (canonical_get hA _ _),
    denote_product c.rank (columns A c) (get middle) i j (fun _ _ => canonical_get hA _ _) hm] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro t _
  rw [get_table _ _ _ _ _ t.isLt j.isLt,
    denote_product c.rank (get c.adj) (rows A c) t j (fun _ _ => canonical_get hc _ _)
      (fun _ _ => canonical_get hA _ _)]

end PolyLists

namespace PolyWitness

open PolyLists
open Hex.Matrix.Lists (entry all_iff)

variable {C : Type} {n m : Nat}

theorem get_ofFn {α : Type} {r : Nat} (f : Fin r → α) (i : Fin r) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  exact Vector.getElem_ofFn i.isLt

theorem indices_iff (c : PolyWitness C) : PolyLists.indices n m c = true ↔
    c.rows.length = c.rank ∧ c.cols.length = c.rank ∧
      ∀ i, i < c.rank → entry 0 c.rows i < n ∧ entry 0 c.cols i < m := by
  simp [PolyLists.indices, Bool.and_assoc, all_iff, Nat.blt_eq]

/-- A validated row index, used only in the semantic certificate. -/
def row (c : PolyWitness C) (h : PolyLists.indices n m c = true) (i : Fin c.rank) : Fin n :=
  ⟨entry 0 c.rows i, ((indices_iff c).mp h).2.2 i i.isLt |>.1⟩

/-- A validated column index, used only in the semantic certificate. -/
def col (c : PolyWitness C) (h : PolyLists.indices n m c = true) (i : Fin c.rank) : Fin m :=
  ⟨entry 0 c.cols i, ((indices_iff c).mp h).2.2 i i.isLt |>.2⟩

/-- Read a validated list certificate as the reference rank certificate. -/
abbrev decode [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C] (k : Nat)
    (c : PolyWitness C) (h : PolyLists.indices n m c = true) :
    Hex.Matrix.RankCert (MvPoly k C Mono.grevlex) n m where
  rank := c.rank
  rows := Vector.ofFn (c.row h)
  cols := Vector.ofFn (c.col h)
  denom := PolyLists.denote c.denom
  adj := PolyLists.matrix c.rank c.rank c.adj

end PolyWitness

/-- The list checker identifies a passing list certificate with the
reference check, through the denotation laws of polynomial list arithmetic. -/
theorem checkRankPolyList_sound {C : Type} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
    {k n m : Nat} {A : PolyLists.Rows C} {c : PolyWitness C}
    (h : checkRankPolyList k n m A c = true) :
    Hex.Matrix.checkRank (PolyLists.matrix (k := k) n m A)
      (c.decode k (by
        simp only [checkRankPolyList, checkRankPolyHeader, Bool.and_eq_true] at h
        exact h.1.1.1.1.1.1)) = true := by
  simp only [checkRankPolyList, checkRankPolyHeader, Bool.and_assoc, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨hi, hA, hc, hd, hn, hp, hu⟩
  have hd := MvPoly.Kernel.isCanonical_iff.mp hd
  apply (checkRank_iff_matrixEquiv _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have := (MvPoly.Kernel.isZero_iff (cmp := Mono.grevlex) hd).mpr hz
    simp [hn] at this
  · apply Matrix.ext
    intro i j
    dsimp only [PolyWitness.decode]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, PolyLists.matrix_apply,
      PolyWitness.get_ofFn, PolyWitness.row, PolyWitness.col]
    simpa [PolyLists.block, mul_ite] using
      PolyLists.pivot_sound hA hc hp i j
  · apply Matrix.ext
    intro i j
    dsimp only [PolyWitness.decode]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      smul_eq_mul, PolyLists.matrix_apply, PolyWitness.get_ofFn,
      PolyWitness.row, PolyWitness.col, id_eq]
    simpa [PolyLists.rows, PolyLists.columns] using
      PolyLists.upper_sound hA hc hd hu i j

end HexGenericRankMathlib
