/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDet.Basic
public import HexBareissMathlib.Kernel
public import Mathlib.Data.List.GetD
public import HexMvPolyMathlib.Kernel
public import HexMvPolyMathlib.Aeval
public import HexDeterminantMathlib.CoreTransport
public import HexReflectMathlib.Kernel

public section

namespace Hex.PolyDet

/-- The polynomial producer returns only witnesses accepted by the list checker. -/
theorem check_of_ok {k n : Nat} {C : Type} {cmp : Mono k → Mono k → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing C]
    [DecidableEq C] [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C]
    [IsMonomialOrder cmp] [LawfulGcdOps C]
    (P : Matrix (MvPoly k C cmp) n n) (w : Matrix.DetWitness (MvPoly k C cmp))
    (h : polyDetWitness P = .ok w) : check n (P.rows.toList.map (·.toList)) w = true :=
  Matrix.detWitnessWith_check Hex.exactDiv n (check n) _ w h

/-- A budgeted return has passed the caller's compiled serialization checker. -/
theorem produce_check {k n : Nat} {C : Type} {cmp : Mono k → Mono k → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing C]
    [DecidableEq C] [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C]
    [IsMonomialOrder cmp] [LawfulGcdOps C]
    (budget : Matrix.DetWitness.Budget)
    (check : List (List (MvPoly k C cmp)) → Matrix.DetWitness (MvPoly k C cmp) → Bool)
    (rows : List (List (MvPoly k C cmp))) (w : Matrix.DetWitness (MvPoly k C cmp))
    (h : produce budget n check rows = .ok w) : check rows w = true :=
  Matrix.detWitnessBudgeted_check Hex.exactDiv n MvPoly.termCount budget check rows w h

end Hex.PolyDet

namespace HexMatrixMathlib.DetPoly

open Hex.Matrix (DetOps DetWitness checkDetPolyList)
open Hex.Matrix.DetWitness

variable {R : Type} {S : Type} [CommRing S]

theorem row_eq_getD (A : List (List R)) (i : Nat) : row A i = A.getD i [] := by
  induction A generalizing i with
  | nil => simp [row]
  | cons a as ih =>
    cases i with
    | zero => simp [row]
    | succ i => simp only [row, List.getD_cons_succ, ih]

theorem replace_length (A : List (List R)) (i : Nat) (r : List R) :
    (replace A i r).length = A.length := by
  induction A generalizing i with
  | nil => simp [replace]
  | cons a as ih =>
    cases i with
    | zero => simp [replace]
    | succ i => simp [replace, ih]

theorem replace_getD (A : List (List R)) (i : Nat) (r : List R) (k : Nat) (hi : i < A.length) :
    (replace A i r).getD k [] = if k = i then r else A.getD k [] := by
  induction A generalizing i k with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => cases k <;> simp [replace]
    | succ i =>
      cases k with
      | zero => simp [replace]
      | succ k =>
        simp only [replace, List.getD_cons_succ]
        rw [ih i k (by simpa using hi)]
        simp

theorem swap_length (a b : Nat) (A : List (List R)) :
    (swap a b A).length = A.length := by
  simp [swap, replace_length]

theorem swap_getD (a b : Nat) (A : List (List R)) (ha : a < A.length) (hb : b < A.length)
    (k : Nat) : (swap a b A).getD k [] =
      A.getD (if k = a then b else if k = b then a else k) [] := by
  unfold swap
  rw [replace_getD _ _ _ _ (by rw [replace_length]; exact hb), replace_getD _ _ _ _ ha,
    row_eq_getD, row_eq_getD]
  by_cases hka : k = a
  · subst hka
    by_cases hkb : k = b
    · subst hkb; simp
    · simp [hkb]
  · by_cases hkb : k = b
    · subst hkb; simp [hka]
    · simp [hka, hkb]

theorem permute_length (s : List (Nat × Nat)) (A : List (List R)) :
    (permute s A).length = A.length := by
  induction s generalizing A with
  | nil => rfl
  | cons p s ih => obtain ⟨a, b⟩ := p; simp [permute, ih, swap_length]


/-- Interpretation of serialized arithmetic in a commutative ring. Laws
requiring canonical inputs state that requirement explicitly. -/
structure Decode (ops : DetOps R) (S : Type) [CommRing S] where
  eval : R → S
  zero : eval ops.zero = 0
  one : eval ops.one = 1
  valid_zero : ops.valid ops.zero = true
  valid_one : ops.valid ops.one = true
  valid_add : ∀ a b, ops.valid a = true → ops.valid b = true →
    ops.valid (ops.add a b) = true
  valid_mul : ∀ a b, ops.valid a = true → ops.valid b = true →
    ops.valid (ops.mul a b) = true
  valid_neg : ∀ a, ops.valid a = true → ops.valid (ops.neg a) = true
  add : ∀ a b, ops.valid a = true → ops.valid b = true →
    eval (ops.add a b) = eval a + eval b
  mul : ∀ a b, ops.valid a = true → ops.valid b = true →
    eval (ops.mul a b) = eval a * eval b
  neg : ∀ a, ops.valid a = true → eval (ops.neg a) = -eval a
  beq : ∀ a b, ops.valid a = true → ops.valid b = true →
    (ops.beq a b = true ↔ eval a = eval b)

namespace Decode

variable {ops : DetOps R} (D : Decode ops S)

@[simp] theorem validRow_iff (r : List R) :
    ops.validRow r = true ↔ ∀ x ∈ r, ops.valid x = true := by
  induction r with
  | nil => simp [DetOps.validRow]
  | cons x xs ih => simp [DetOps.validRow, ih]

@[simp] theorem validRows_iff (rs : List (List R)) :
    ops.validRows rs = true ↔ ∀ r ∈ rs, ops.validRow r = true := by
  induction rs with
  | nil => simp [DetOps.validRows]
  | cons r rs ih => simp [DetOps.validRows, ih]

theorem entry_eq_getD (r : List R) (i : Nat) :
    ops.entry r i = r.getD i ops.zero := by
  induction r generalizing i with
  | nil => simp [DetOps.entry]
  | cons x xs ih => cases i <;> simp [DetOps.entry, ih]

include D in
theorem valid_entry (r : List R) (i : Nat) (h : ops.validRow r = true) :
    ops.valid (ops.entry r i) = true := by
  rw [entry_eq_getD]
  by_cases hi : i < r.length
  · rw [getD_eq_getElem' _ _ _ hi]
    exact (validRow_iff r).mp h _ (List.getElem_mem _)
  · rw [getD_eq_default' _ _ _ (by omega)]
    exact D.valid_zero

include D in
theorem valid_dot (a b : List R) (ha : ops.validRow a = true)
    (hb : ops.validRow b = true) : ops.valid (ops.dot a b) = true := by
  induction a generalizing b with
  | nil => exact D.valid_zero
  | cons x xs ih =>
    cases b with
    | nil => exact D.valid_zero
    | cons y ys =>
      simp only [DetOps.validRow, Bool.and_eq_true] at ha hb
      exact D.valid_add _ _ (D.valid_mul _ _ ha.1 hb.1) (ih ys ha.2 hb.2)

theorem eval_entry (r : List R) (i : Nat) :
    D.eval (ops.entry r i) = (r.map D.eval).getD i 0 := by
  induction r generalizing i with
  | nil => simp [DetOps.entry, D.zero]
  | cons x xs ih => cases i <;> simp [DetOps.entry, ih]

theorem eval_dot (a b : List R) (r : Nat) (hlen : a.length ≤ r)
    (ha : ops.validRow a = true) (hb : ops.validRow b = true) :
    D.eval (ops.dot a b) =
      ∑ k : Fin r, D.eval (ops.entry a k) * D.eval (ops.entry b k) := by
  induction a generalizing b r with
  | nil => simp [DetOps.dot, DetOps.entry, D.zero]
  | cons x xs ih =>
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by simp at hlen; omega⟩
    rw [Fin.sum_univ_succ]
    cases b with
    | nil => simp [DetOps.dot, DetOps.entry, D.zero]
    | cons y ys =>
      simp only [DetOps.validRow, Bool.and_eq_true] at ha hb
      simp only [DetOps.dot, Fin.val_zero, Fin.val_succ, DetOps.entry]
      rw [D.add _ _ (D.valid_mul _ _ ha.1 hb.1) (D.valid_dot xs ys ha.2 hb.2),
        D.mul _ _ ha.1 hb.1, ih ys r (by simp at hlen; omega) ha.2 hb.2]

include D in
theorem valid_column (A : List (List R)) (j : Nat) (h : ops.validRows A = true) :
    ops.validRow (ops.column j A) = true := by
  induction A with
  | nil => rfl
  | cons r rs ih =>
    simp only [DetOps.validRows, Bool.and_eq_true] at h
    simp only [DetOps.column, DetOps.validRow, Bool.and_eq_true]
    exact ⟨D.valid_entry r j h.1, ih h.2⟩

theorem column_entry (A : List (List R)) (i j : Nat) :
    ops.entry (ops.column j A) i = ops.entry (A.getD i []) j := by
  induction A generalizing i with
  | nil => simp [DetOps.column, DetOps.entry]
  | cons r rs ih => cases i <;> simp [DetOps.column, DetOps.entry, ih]

@[simp] theorem columns_length (A : List (List R)) (i n : Nat) :
    (ops.columns A i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [DetOps.columns, ih]

theorem columns_getD (A : List (List R)) (i n k : Nat) (hk : k < n) :
    (ops.columns A i n).getD k [] = ops.column (i + k) A := by
  induction n generalizing i k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [DetOps.columns]
    | succ k => simpa [DetOps.columns, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (i + 1) k (by omega)

include D in
theorem valid_columns (A : List (List R)) (i n : Nat) (h : ops.validRows A = true) :
    ops.validRows (ops.columns A i n) = true := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [DetOps.columns, DetOps.validRows, Bool.and_eq_true]
    exact ⟨D.valid_column A i h, ih (i + 1)⟩

include D in
theorem valid_signed (swaps : List (Nat × Nat)) (a : R) (ha : ops.valid a = true) :
    ops.valid (ops.signed swaps a) = true := by
  induction swaps with
  | nil => exact ha
  | cons _ ss ih => exact D.valid_neg _ ih

theorem eval_signed (swaps : List (Nat × Nat)) (a : R) (ha : ops.valid a = true) :
    D.eval (ops.signed swaps a) = (-1 : S) ^ swaps.length * D.eval a := by
  induction swaps with
  | nil => simp [DetOps.signed]
  | cons _ ss ih =>
    rw [DetOps.signed, D.neg _ (D.valid_signed ss a ha), ih]
    simp [pow_succ, mul_assoc]

theorem zeroDots_spec (v : List R) (cs : List (List R))
    (hv : ops.validRow v = true) (hcs : ops.validRows cs = true)
    (h : ops.zeroDots v cs = true) : ∀ c ∈ cs, D.eval (ops.dot v c) = 0 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [DetOps.zeroDots, Bool.and_eq_true] at h
    simp only [DetOps.validRows, Bool.and_eq_true] at hcs
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact ((D.beq _ _ (D.valid_dot v _ hv hcs.1) D.valid_zero).mp h.1).trans D.zero
    · exact ih hcs.2 h.2 c' hc'

/-- The witness identities in the polynomial model. This proposition contains
no Boolean polynomial multiplication or equality test. -/
@[expose] def Triangular (d : R) (swaps : List (Nat × Nat)) :
    List (List R) → Nat → List (List R) → List (List R) → R → Prop
  | _, _, [], [], prev => D.eval d = D.eval (ops.signed swaps prev)
  | done, i, t :: ts, c :: cs, prev =>
      t.length = i + 1 ∧ ops.validRow t = true ∧
      D.eval (ops.entry t i) ≠ 0 ∧ D.eval (ops.entry t i) = D.eval prev ∧
      (∀ c ∈ done, D.eval (ops.dot t c) = 0) ∧
      Triangular d swaps (c :: done) (i + 1) ts cs (ops.dot t c)
  | _, _, _, _, _ => False

/-- Extract the semantic identities from the term-list arithmetic checks. -/
theorem triangular_identities (d : R) (swaps : List (Nat × Nat))
    (hd : ops.valid d = true) :
    ∀ (done : List (List R)) (i : Nat) (ts cs : List (List R)) (prev : R),
      ops.validRows done = true → ops.validRows cs = true → ops.valid prev = true →
      ops.triangular d swaps done i ts cs prev = true →
      D.Triangular d swaps done i ts cs prev := by
  intro done i ts
  induction ts generalizing done i with
  | nil =>
      intro cs prev _ _ hp h
      cases cs with
      | nil => exact (D.beq _ _ hd (D.valid_signed swaps prev hp)).mp h
      | cons c cs => simp [DetOps.triangular] at h
  | cons t ts ih =>
      intro cs prev hdone hcs hp h
      cases cs with
      | nil => simp [DetOps.triangular] at h
      | cons c cs =>
          simp only [DetOps.validRows, Bool.and_eq_true] at hcs
          simp only [DetOps.triangular, Bool.and_eq_true, Nat.beq_eq,
            Bool.not_eq_true'] at h
          obtain ⟨⟨⟨⟨⟨hlen, ht⟩, hnz⟩, hprev⟩, hz⟩, hrest⟩ := h
          have hl := D.valid_entry t i ht
          refine ⟨hlen, ht, ?_, (D.beq _ _ hl hp).mp hprev,
            D.zeroDots_spec t done ht hdone hz, ?_⟩
          · intro he
            have hb := (D.beq _ _ hl D.valid_zero).mpr (he.trans D.zero.symm)
            rw [hb] at hnz
            contradiction
          · exact ih (c :: done) (i + 1) cs (ops.dot t c)
              (by simp only [DetOps.validRows, Bool.and_eq_true]; exact ⟨hcs.1, hdone⟩)
              hcs.2 (D.valid_dot t c ht hcs.1) hrest

/-- The checked adjacent diagonal relations imply the determinant product
identity propositionally, without multiplying pivot polynomials in replay. -/
theorem triangular_spec (d : R) (swaps : List (Nat × Nat))
    (hd : ops.valid d = true) :
    ∀ (done : List (List R)) (i : Nat) (ts cs : List (List R)) (prev : R),
      ops.validRows done = true → ops.validRows cs = true → ops.valid prev = true →
      D.Triangular d swaps done i ts cs prev →
      ts.length = cs.length ∧
      (∀ k, k < ts.length →
        (ts.getD k []).length = i + k + 1 ∧
        ops.validRow (ts.getD k []) = true ∧
        D.eval (ops.entry (ts.getD k []) (i + k)) ≠ 0 ∧
        (∀ c ∈ done, D.eval (ops.dot (ts.getD k []) c) = 0) ∧
        ∀ k', k' < k → D.eval (ops.dot (ts.getD k []) (cs.getD k' [])) = 0) ∧
      (List.ofFn fun k : Fin ts.length => D.eval (ops.entry (ts.getD k []) (i + k))).prod *
          D.eval d =
        (-1 : S) ^ swaps.length * D.eval prev *
          (List.ofFn fun k : Fin ts.length =>
            D.eval (ops.dot (ts.getD k []) (cs.getD k []))).prod := by
  intro done i ts
  induction ts generalizing done i with
  | nil =>
    intro cs prev hdone hcs hp h
    cases cs with
    | nil =>
      have he : D.eval d = D.eval (ops.signed swaps prev) := h
      rw [D.eval_signed swaps prev hp] at he
      simpa using he
    | cons c cs => simp [Triangular] at h
  | cons t ts ih =>
    intro cs prev hdone hcs hp h
    cases cs with
    | nil => simp [Triangular] at h
    | cons c cs =>
      simp only [DetOps.validRows, Bool.and_eq_true] at hcs
      obtain ⟨hlen, ht, hlnz, heq, hz, hrest⟩ := h
      obtain ⟨hcslen, hrows, hprod⟩ := ih (c :: done) (i + 1) cs (ops.dot t c)
        (by simp only [DetOps.validRows, Bool.and_eq_true]; exact ⟨hcs.1, hdone⟩)
        hcs.2 (D.valid_dot t c ht hcs.1) hrest
      refine ⟨by simpa using hcslen, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero =>
          exact ⟨by simpa using hlen, by simpa using ht, by simpa using hlnz,
            fun c' hc' => hz c' hc',
            fun k' hk' => absurd hk' (Nat.not_lt_zero _)⟩
        | succ k =>
          obtain ⟨h1, h2, h3, h4, h5⟩ := hrows k (by simpa using hk)
          refine ⟨?_, by simpa using h2, ?_, ?_, ?_⟩
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h3
          · intro c' hc'
            exact h4 c' (List.mem_cons_of_mem _ hc')
          · intro k' hk'
            cases k' with
            | zero => simpa using h4 c (List.mem_cons_self ..)
            | succ k' => simpa using h5 k' (by omega)
      · rw [List.length_cons, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
        simp only [Fin.val_zero, List.getD_cons_zero, Nat.add_zero, Fin.val_succ,
          List.getD_cons_succ]
        have he : (fun k : Fin ts.length => D.eval (ops.entry (ts.getD k []) (i + (k + 1)))) =
            fun k : Fin ts.length => D.eval (ops.entry (ts.getD k []) (i + 1 + k)) := by
          funext k
          congr 2
          omega
        rw [he, heq]
        linear_combination D.eval prev * hprod

/-- The row-list matrix with its entries interpreted. -/
@[expose] def matrix (n : Nat) (A : List (List R)) : Matrix (Fin n) (Fin n) S :=
  ofLists n n (A.map (List.map D.eval))

theorem matrix_apply (n : Nat) (A : List (List R)) (i j : Fin n) :
    D.matrix n A i j = D.eval (ops.entry (A.getD i []) j) := by
  rw [matrix, ofLists_apply]
  have he : (A.map (List.map D.eval)).getD i [] = (A.getD i []).map D.eval :=
    List.getD_map A [] (List.map D.eval)
  rw [he, ← D.eval_entry]

include D in
theorem valid_row (A : List (List R)) (i : Nat) (h : ops.validRows A = true) :
    ops.validRow (A.getD i []) = true := by
  by_cases hi : i < A.length
  · rw [getD_eq_getElem' _ _ _ hi]
    exact (validRows_iff A).mp h _ (List.getElem_mem _)
  · rw [getD_eq_default' _ _ _ (by omega)]
    rfl

include D in
theorem valid_replace (A : List (List R)) (i : Nat) (r : List R)
    (hA : ops.validRows A = true) (hr : ops.validRow r = true) :
    ops.validRows (replace A i r) = true := by
  induction A generalizing i with
  | nil => rfl
  | cons a as ih =>
    simp only [DetOps.validRows, Bool.and_eq_true] at hA
    cases i <;> simp only [replace, DetOps.validRows, Bool.and_eq_true]
    · exact ⟨hr, hA.2⟩
    · exact ⟨hA.1, ih _ hA.2⟩

include D in
theorem valid_swap (A : List (List R)) (a b : Nat) (h : ops.validRows A = true) :
    ops.validRows (swap a b A) = true := by
  apply D.valid_replace _ _ _
  · apply D.valid_replace _ _ _ h
    simpa [row_eq_getD] using D.valid_row A b h
  · simpa [row_eq_getD] using D.valid_row A a h

include D in
theorem valid_permute (ss : List (Nat × Nat)) (A : List (List R))
    (h : ops.validRows A = true) : ops.validRows (permute ss A) = true := by
  induction ss generalizing A with
  | nil => exact h
  | cons s ss ih => exact ih _ (D.valid_swap A s.1 s.2 h)

theorem matrix_swap (n : Nat) (A : List (List R)) (hA : A.length = n) (a b : Fin n) :
    D.matrix n (swap a b A) = (D.matrix n A).submatrix (Equiv.swap a b) id := by
  ext i j
  rw [Matrix.submatrix_apply, id, D.matrix_apply, D.matrix_apply,
    swap_getD _ _ _ (by omega) (by omega), Equiv.swap_apply_def]
  by_cases hia : (i : Nat) = a
  · have : i = a := Fin.ext hia
    subst this
    simp
  · have hia' : i ≠ a := fun h => hia (congrArg Fin.val h)
    by_cases hib : (i : Nat) = b
    · have : i = b := Fin.ext hib
      subst this
      simp [hia, hia']
    · have hib' : i ≠ b := fun h => hib (congrArg Fin.val h)
      simp [hia, hib, hia', hib']

theorem det_permute (n : Nat) (ss : List (Nat × Nat)) (A : List (List R))
    (hA : A.length = n) (hs : swapsOk n ss = true) :
    (D.matrix n (permute ss A)).det = (-1 : S) ^ ss.length * (D.matrix n A).det := by
  induction ss generalizing A with
  | nil => simp [permute]
  | cons s ss ih =>
    obtain ⟨a, b⟩ := s
    obtain ⟨ha, hb, hab, hs'⟩ := HexMatrixMathlib.swapsOk_cons n a b ss hs
    rw [permute, ih _ (by rw [swap_length]; exact hA) hs',
      D.matrix_swap n A hA ⟨a, ha⟩ ⟨b, hb⟩, Matrix.det_permute,
      Equiv.Perm.sign_swap (by simpa [Fin.ext_iff] using hab)]
    simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- The common semantic contract of the two certificate routes. -/
@[expose] def Identities (n : Nat) (A : List (List R)) : DetWitness R → Prop
  | .triangular swaps T d =>
      A.length = n ∧ rowLengths n A = true ∧ ops.validRows A = true ∧
      swapsOk n swaps = true ∧ ops.valid d = true ∧
      D.Triangular d swaps [] 0 T (ops.columns (permute swaps A) 0 n) ops.one
  | .singular v =>
      A.length = n ∧ rowLengths n A = true ∧ ops.validRows A = true ∧
      v.length = n ∧ ops.validRow v = true ∧ ops.anyNonzero v = true ∧
      ∀ c ∈ ops.columns A 0 n, D.eval (ops.dot v c) = 0

/-- List arithmetic establishes the shared witness contract. -/
theorem identities_of_check (n : Nat) (A : List (List R)) (w : DetWitness R)
    (h : checkDetPolyList ops n A w = true) : D.Identities n A w := by
  cases w with
  | triangular swaps T d =>
      simp only [checkDetPolyList, Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨⟨⟨⟨hl, hr⟩, ha⟩, hs⟩, hd⟩, ht⟩ := h
      exact ⟨hl, hr, ha, hs, hd, D.triangular_identities d swaps hd [] 0 T
        (ops.columns (permute swaps A) 0 n) ops.one rfl
        (D.valid_columns _ 0 n (D.valid_permute swaps A ha)) D.valid_one ht⟩
  | singular v =>
      simp only [checkDetPolyList, Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨hl, hr⟩, ha⟩, hvlen⟩, hv⟩, hnz⟩, hz⟩ := h
      exact ⟨hl, hr, ha, hvlen, hv, hnz,
        D.zeroDots_spec v _ hv (D.valid_columns A 0 n ha) hz⟩

/-- A passing generic polynomial certificate determines the determinant in
any domain interpreting its canonical entry arithmetic. -/
theorem identities_sound [IsDomain S] (n : Nat) (A : List (List R)) (w : DetWitness R)
    (h : D.Identities n A w) :
    (D.matrix n A).det = match w with
      | .triangular _ _ d => D.eval d
      | .singular _ => 0 := by
  cases w with
  | triangular swaps T d =>
    obtain ⟨hAlen, _, hA, hswaps, hd, htri⟩ := h
    set P := permute swaps A with hP
    have hvalidP : ops.validRows P = true := D.valid_permute swaps A hA
    have hdetP : (D.matrix n P).det = (-1 : S) ^ swaps.length * (D.matrix n A).det :=
      D.det_permute n swaps A hAlen hswaps
    obtain ⟨hTlen, hrows, hprod⟩ := D.triangular_spec d swaps hd [] 0 T
      (ops.columns P 0 n) ops.one rfl (D.valid_columns P 0 n hvalidP) D.valid_one htri
    rw [columns_length] at hTlen
    subst hTlen
    let Lm := D.matrix T.length T
    let Pm := D.matrix T.length P
    have hU : ∀ i j : Fin T.length,
        (Lm * Pm) i j = D.eval (ops.dot (T.getD i []) (ops.column j P)) := by
      intro i j
      rw [Matrix.mul_apply, D.eval_dot _ _ T.length
        (by rw [(hrows i i.isLt).1]; omega) (hrows i i.isLt).2.1
        (D.valid_column P j hvalidP)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Lm, Pm, D.matrix_apply, column_entry]
    have hlower : Lm.IsLowerTriangular := by
      intro i j hij
      have hij : (i : Nat) < j := by simpa using hij
      change D.matrix T.length T i j = 0
      rw [D.matrix_apply, entry_eq_getD, getD_eq_default' _ _ _
        (by rw [(hrows i i.isLt).1]; omega), D.zero]
    have hupper : (Lm * Pm).IsUpperTriangular := by
      intro i j hij
      have hij : (j : Nat) < i := by simpa using hij
      rw [hU]
      have hz := (hrows i i.isLt).2.2.2.2 j hij
      simpa only [columns_getD P 0 T.length j j.isLt, Nat.zero_add] using hz
    have hdetL := Matrix.det_of_isLowerTriangular Lm hlower
    have hdetU := Matrix.det_of_isUpperTriangular hupper
    have hl0 : (∏ i, Lm i i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => by
      simpa only [Lm, D.matrix_apply, Nat.zero_add] using (hrows i i.isLt).2.2.1
    have hsign : (-1 : S) ^ swaps.length * (-1 : S) ^ swaps.length = 1 := by
      rw [← mul_pow]
      simp
    have hprodL : (List.ofFn fun k : Fin T.length =>
        D.eval (ops.entry (T.getD k []) (0 + k))).prod = ∏ i, Lm i i := by
      rw [List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => by simp only [Lm, D.matrix_apply, Nat.zero_add]
    have hprodU : (List.ofFn fun k : Fin T.length =>
        D.eval (ops.dot (T.getD k []) ((ops.columns P 0 T.length).getD k []))).prod =
          ∏ i, (Lm * Pm) i i := by
      rw [List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => by
        rw [hU, columns_getD P 0 T.length i i.isLt, Nat.zero_add]
    rw [hprodL, hprodU, D.one, mul_one] at hprod
    have key : (∏ i, Lm i i) * D.eval d = (∏ i, Lm i i) * (D.matrix T.length A).det := by
      rw [hprod, ← hdetU, Matrix.det_mul, hdetL, hdetP]
      linear_combination (∏ i, Lm i i) * (D.matrix T.length A).det * hsign
    exact (mul_left_cancel₀ hl0 key).symm
  | singular v =>
    obtain ⟨_, _, hA, hvlen, hv, hnz, hz⟩ := h
    have hnonzero : ∃ a ∈ v, D.eval a ≠ 0 := by
      have any : ∀ xs : List R, ops.validRow xs = true → ops.anyNonzero xs = true →
          ∃ a ∈ xs, D.eval a ≠ 0 := by
        intro xs
        induction xs with
        | nil => simp [DetOps.anyNonzero]
        | cons x xs ih =>
          intro hxs h
          simp only [DetOps.validRow, Bool.and_eq_true] at hxs
          simp only [DetOps.anyNonzero, Bool.or_eq_true, Bool.not_eq_true'] at h
          rcases h with h | h
          · refine ⟨x, List.mem_cons_self .., ?_⟩
            intro he
            have hb := (D.beq _ _ hxs.1 D.valid_zero).mpr (he.trans D.zero.symm)
            rw [hb] at h
            contradiction
          · obtain ⟨a, ha, hn⟩ := ih hxs.2 h
            exact ⟨a, List.mem_cons_of_mem _ ha, hn⟩
      exact any v hv hnz
    let w : Fin n → S := fun i => D.eval (ops.entry v i)
    have hw : w ≠ 0 := by
      obtain ⟨a, ha, ha0⟩ := hnonzero
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
      intro h0
      have he := congrFun h0 ⟨k, by omega⟩
      simp only [w, Pi.zero_apply, entry_eq_getD] at he
      rw [getD_eq_getElem' _ _ _ hk] at he
      exact ha0 he
    have hmul : Matrix.vecMul w (D.matrix n A) = 0 := by
      funext j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
      have hmem : ops.column j A ∈ ops.columns A 0 n := by
        rw [← Nat.zero_add j, ← columns_getD A 0 n j j.isLt,
          getD_eq_getElem' _ _ _ (by rw [columns_length]; exact j.isLt)]
        exact List.getElem_mem _
      have he := hz _ hmem
      rw [D.eval_dot v (ops.column j A) n (by omega) hv (D.valid_column A j hA)] at he
      simpa only [column_entry, D.matrix_apply, w] using he
    exact Matrix.exists_vecMul_eq_zero_iff.mp ⟨w, hw, hmul⟩

/-- A passing list certificate supplies the shared determinant identities. -/
theorem sound [IsDomain S] (n : Nat) (A : List (List R)) (w : DetWitness R)
    (h : checkDetPolyList ops n A w = true) :
    (D.matrix n A).det = match w with
      | .triangular _ _ d => D.eval d
      | .singular _ => 0 := by
  have hs := D.identities_sound n A w (D.identities_of_check n A w h)
  cases w <;> exact hs

/-- Transport for any canonical serialized coefficient representation, including
modulus-parametrised residue lists once their decoder is supplied. -/
theorem transport [IsDomain S] {F : Type*} [CommRing F] (φ : S →+* F)
    (n : Nat) (rows : List (List R)) (w : DetWitness R)
    (A : Matrix (Fin n) (Fin n) F) (h : checkDetPolyList ops n rows w = true)
    (hA : A = (D.matrix n rows).map φ) :
    A.det = match w with
      | .triangular _ _ d => φ (D.eval d)
      | .singular _ => 0 := by
  rw [hA]
  change (φ.mapMatrix (D.matrix n rows)).det = _
  rw [← RingHom.map_det, D.sound n rows w h]
  cases w <;> simp only [map_zero]

end Decode

open Hex
open scoped HexMvPolyMathlib
attribute [local instance 2000] Ring.toGrindRing

namespace Polynomial


variable {C : Type} [CommRing C] [BEq C] [LawfulBEq C] [DecidableEq C]

@[expose] abbrev ops (k : Nat) := Hex.PolyDet.ops (C := C) k

/-- The generic checker interprets polynomial lists in Mathlib's polynomial
ring, where the coefficient domain supplies the domain instance. -/
@[expose] noncomputable def decode (k : Nat) : Decode (ops (C := C) k) (MvPolynomial (Fin k) C) where
  eval := HexMvPolyMathlib.Kernel.denote (n := k) (cmp := Mono.grevlex)
  zero := by simp [ops, Hex.PolyDet.ops, HexMvPolyMathlib.Kernel.denote, Hex.MvPoly.Kernel.denote]
  one := HexMvPolyMathlib.Kernel.denote_one
  valid_zero := rfl
  valid_one := Hex.MvPoly.Kernel.isCanonical_iff.mpr (Hex.MvPoly.Kernel.one_canonical k)
  valid_add a b ha hb := Hex.MvPoly.Kernel.isCanonical_iff.mpr
    (Hex.MvPoly.Kernel.add_canonical (Hex.MvPoly.Kernel.isCanonical_iff.mp ha) (Hex.MvPoly.Kernel.isCanonical_iff.mp hb))
  valid_mul a b ha hb := Hex.MvPoly.Kernel.isCanonical_iff.mpr
    (Hex.MvPoly.Kernel.mul_canonical (Hex.MvPoly.Kernel.isCanonical_iff.mp ha) (Hex.MvPoly.Kernel.isCanonical_iff.mp hb))
  valid_neg a ha := Hex.MvPoly.Kernel.isCanonical_iff.mpr (Hex.MvPoly.Kernel.neg_canonical (Hex.MvPoly.Kernel.isCanonical_iff.mp ha))
  add a b _ _ := HexMvPolyMathlib.Kernel.denote_add a b
  mul a b ha hb := HexMvPolyMathlib.Kernel.denote_mul a b
    (Hex.MvPoly.Kernel.isCanonical_iff.mp ha).1 (Hex.MvPoly.Kernel.isCanonical_iff.mp hb).1
  neg a _ := HexMvPolyMathlib.Kernel.denote_neg a
  beq a b ha hb := HexMvPolyMathlib.Kernel.beq_iff (Hex.MvPoly.Kernel.isCanonical_iff.mp ha) (Hex.MvPoly.Kernel.isCanonical_iff.mp hb)

/-- The polynomial value carried by a serialized witness. -/
@[expose] def value : DetWitness (Hex.MvPoly.Kernel.PolyList C) → Hex.MvPoly.Kernel.PolyList C
  | .triangular _ _ d => d
  | .singular _ => []

/-- Quote each entry by applying list denotation to its canonical list. -/
def matrix (k n : Nat) (A : List (List (Hex.MvPoly.Kernel.PolyList C))) :
    Hex.Matrix (MvPoly k C Mono.grevlex) n n :=
  HexMatrixMathlib.matrixEquiv.symm
    (ofLists n n (A.map (List.map (Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex)))))

/-- The decoded matrix is the image of the quoted reference matrix under
polynomial correspondence. Neither side is a second quoted tree matrix. -/
theorem decode_matrix (k n : Nat) (A : List (List (Hex.MvPoly.Kernel.PolyList C))) :
    (decode k).matrix n A = (HexMatrixMathlib.matrixEquiv (matrix k n A)).map
      (HexMvPolyMathlib.equiv (n := k) (cmp := Mono.grevlex)) := by
  apply Matrix.ext
  intro i j
  simp only [Decode.matrix, decode, matrix, Equiv.apply_symm_apply,
    Matrix.map_apply, ofLists_apply]
  have hm (r : List (Hex.MvPoly.Kernel.PolyList C)) :
      (r.map (HexMvPolyMathlib.Kernel.denote (n := k) (cmp := Mono.grevlex))).getD j 0 =
        HexMvPolyMathlib.equiv ((r.map (Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex))).getD j 0) := by
    rw [← map_zero (HexMvPolyMathlib.equiv (n := k) (cmp := Mono.grevlex)),
      ← List.getD_map _ _ (HexMvPolyMathlib.equiv (n := k) (cmp := Mono.grevlex))]
    rw [List.map_map]
    rfl
  rw [show (A.map (List.map (HexMvPolyMathlib.Kernel.denote (n := k) (cmp := Mono.grevlex)))).getD i [] =
      (A.getD i []).map (HexMvPolyMathlib.Kernel.denote (n := k) (cmp := Mono.grevlex)) from List.getD_map A [] _,
    show (A.map (List.map (Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex)))).getD i [] =
      (A.getD i []).map (Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex)) from List.getD_map A [] _]
  exact hm _

/-- Polynomial determinant soundness through list denotation and the domain
instance on Mathlib's polynomial ring. No domain instance on `MvPoly` is assumed. -/
theorem checkDetPolyList_sound [IsDomain C] (k n : Nat)
    (A : List (List (Hex.MvPoly.Kernel.PolyList C))) (w : DetWitness (Hex.MvPoly.Kernel.PolyList C))
    (h : checkDetPolyList (ops k) n A w = true) :
    Hex.Matrix.det (matrix k n A) = Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex) (value w) := by
  apply (HexMvPolyMathlib.equiv (n := k) (cmp := Mono.grevlex)).injective
  rw [HexMatrixMathlib.det_eq (matrix k n A), RingEquiv.map_det]
  change ((HexMatrixMathlib.matrixEquiv (matrix k n A)).map
    (HexMvPolyMathlib.equiv (n := k) (cmp := Mono.grevlex))).det = _
  rw [← decode_matrix]
  have hs := (decode k).sound n A w h
  cases w <;> simpa [value, decode, HexMvPolyMathlib.Kernel.denote, Hex.MvPoly.Kernel.denote] using hs

variable {F : Type u} [CommRing F]

/-- Determinants commute unconditionally with evaluation of polynomial entries,
including valuations at which a nonzero pivot polynomial vanishes. -/
theorem transport_det (k n : Nat)
    (rows : List (List (Hex.MvPoly.Kernel.PolyList C)))
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList C))
    (φ : MvPoly k C Mono.grevlex →+* F) (A : Matrix (Fin n) (Fin n) F)
    (hdet : Hex.Matrix.det (matrix k n rows) =
      Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex) (value w))
    (hA : A = (HexMatrixMathlib.matrixEquiv (matrix k n rows)).map φ) :
    A.det = φ (Hex.MvPoly.Kernel.denote (cmp := Mono.grevlex) (value w)) := by
  rw [hA]
  change (φ.mapMatrix (HexMatrixMathlib.matrixEquiv (matrix k n rows))).det = _
  rw [← RingHom.map_det, ← HexMatrixMathlib.det_eq, hdet]

/-- Determinants commute unconditionally with evaluation of polynomial entries,
including valuations at which a nonzero pivot polynomial vanishes. -/
theorem transport [IsDomain C] (k n : Nat)
    (rows : List (List (Hex.MvPoly.Kernel.PolyList C)))
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList C))
    (φ : MvPoly k C Mono.grevlex →+* F) (A : Matrix (Fin n) (Fin n) F)
    (hcheck : checkDetPolyList (ops k) n rows w = true)
    (hA : A = (HexMatrixMathlib.matrixEquiv (matrix k n rows)).map φ) :
    A.det = φ (Hex.MvPoly.Kernel.denote (cmp := Mono.grevlex) (value w)) := by
  rw [hA]
  change (φ.mapMatrix (HexMatrixMathlib.matrixEquiv (matrix k n rows))).det = _
  rw [← RingHom.map_det, ← HexMatrixMathlib.det_eq, checkDetPolyList_sound k n rows w hcheck]

/-- The batch's evaluated entry lists. Identification reduces these direct
list accesses instead of a round trip through the Hex matrix representation. -/
noncomputable abbrev evaluated (k n : Nat)
    (rows : List (List (Hex.MvPoly.Kernel.PolyList Int))) (ctx : Lean.RArray F) :
    Matrix (Fin n) (Fin n) F :=
  (ofLists n n (rows.map (List.map
    (Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex))))).map
      (HexReflectMathlib.Kernel.hom k ctx)

theorem evaluated_eq (k n : Nat)
    (rows : List (List (Hex.MvPoly.Kernel.PolyList Int))) (ctx : Lean.RArray F) :
    evaluated k n rows ctx = (HexMatrixMathlib.matrixEquiv (matrix k n rows)).map
      (HexReflectMathlib.Kernel.hom k ctx) := by
  simp only [evaluated, matrix, Equiv.apply_symm_apply]

/-- Retained public term-list API. Agreement with the target uses the same
batch's canonical list comparison; checker-independent clients use `target_det`. -/
theorem target (k n : Nat) (rows : List (List (Hex.MvPoly.Kernel.PolyList Int)))
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int))
    (ctx : Lean.RArray F) (A : Matrix (Fin n) (Fin n) F)
    (q : Hex.MvPoly.Kernel.PolyList Int) (e : F)
    (hcheck : checkDetPolyList (ops k) n rows w = true)
    (hA : A = evaluated k n rows ctx)
    (he : HexReflectMathlib.Kernel.hom k ctx
      (Hex.MvPoly.Kernel.denote (cmp := Mono.grevlex) q) = e)
    (hq : Hex.MvPoly.Kernel.beq (value w) q = true) : A.det = e := by
  rw [transport k n rows w (HexReflectMathlib.Kernel.hom k ctx) A hcheck (hA.trans (evaluated_eq k n rows ctx)),
    Hex.MvPoly.Kernel.beq_eq_true_iff.mp hq]
  exact he

/-- Retained public term-list API; checker-independent clients use `result_det`.
A generated value is already the witness's value, with no reflexive comparison. -/
theorem result (k n : Nat) (rows : List (List (Hex.MvPoly.Kernel.PolyList Int)))
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int)) (ctx : Lean.RArray F)
    (A : Matrix (Fin n) (Fin n) F) (e : F)
    (hcheck : checkDetPolyList (ops k) n rows w = true)
    (hA : A = evaluated k n rows ctx)
    (he : HexReflectMathlib.Kernel.hom k ctx
      (Hex.MvPoly.Kernel.denote (cmp := Mono.grevlex) (value w)) = e) : A.det = e :=
  (transport k n rows w (HexReflectMathlib.Kernel.hom k ctx) A hcheck
    (hA.trans (evaluated_eq k n rows ctx))).trans he

/-- Retained public term-list scaling API; checker-independent clients use
`scaled_det`. Positivity is used only for the final scalar cancellation. -/
theorem scaled (k n : Nat) (rows : List (List (Hex.MvPoly.Kernel.PolyList Int)))
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int))
    (ctx : Lean.RArray Rat) (A : Matrix (Fin n) (Fin n) Rat) (s : List Nat)
    (hcheck : checkDetPolyList (ops k) n rows w = true)
    (hA : evaluated k n rows ctx =
        Matrix.diagonal (fun i : Fin n => (s.getD i 1 : Rat)) * A)
    (hs : s.length = n) :
    (DetWitness.prodNat s : Rat) * A.det = HexReflectMathlib.Kernel.hom k ctx
      (Hex.MvPoly.Kernel.denote (cmp := Mono.grevlex) (value w)) := by
  have hdet := transport k n rows w (HexReflectMathlib.Kernel.hom k ctx)
    (Matrix.diagonal (fun i : Fin n => (s.getD i 1 : Rat)) * A) hcheck (hA.symm.trans (evaluated_eq k n rows ctx))
  rw [Matrix.det_mul, Matrix.det_diagonal] at hdet
  rw [HexMatrixMathlib.prodNat_cast s n hs]
  exact hdet


/-- Agreement with the target uses the same batch's canonical list comparison. -/
theorem target_det (k n : Nat) (rows : List (List (Hex.MvPoly.Kernel.PolyList Int)))
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int))
    (ctx : Lean.RArray F) (A : Matrix (Fin n) (Fin n) F)
    (q : Hex.MvPoly.Kernel.PolyList Int) (e : F)
    (hcheck : Hex.Matrix.det (matrix k n rows) =
      Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex) (value w))
    (hA : A = evaluated k n rows ctx)
    (he : HexReflectMathlib.Kernel.hom k ctx
      (Hex.MvPoly.Kernel.denote (cmp := Mono.grevlex) q) = e)
    (hq : Hex.MvPoly.Kernel.beq (value w) q = true) : A.det = e := by
  rw [transport_det k n rows w (HexReflectMathlib.Kernel.hom k ctx) A hcheck (hA.trans (evaluated_eq k n rows ctx)),
    Hex.MvPoly.Kernel.beq_eq_true_iff.mp hq]
  exact he

/-- A generated value is already the witness's value; no reflexive list
comparison is needed for the term form or simproc. -/
theorem result_det (k n : Nat) (rows : List (List (Hex.MvPoly.Kernel.PolyList Int)))
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int)) (ctx : Lean.RArray F)
    (A : Matrix (Fin n) (Fin n) F) (e : F)
    (hcheck : Hex.Matrix.det (matrix k n rows) =
      Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex) (value w))
    (hA : A = evaluated k n rows ctx)
    (he : HexReflectMathlib.Kernel.hom k ctx
      (Hex.MvPoly.Kernel.denote (cmp := Mono.grevlex) (value w)) = e) : A.det = e :=
  (transport_det k n rows w (HexReflectMathlib.Kernel.hom k ctx) A hcheck
    (hA.trans (evaluated_eq k n rows ctx))).trans he

/-- Row scaling transports the polynomial certificate to the original rational
matrix. Positivity is used only for the final scalar cancellation. -/
theorem scaled_det (k n : Nat) (rows : List (List (Hex.MvPoly.Kernel.PolyList Int)))
    (w : DetWitness (Hex.MvPoly.Kernel.PolyList Int))
    (ctx : Lean.RArray Rat) (A : Matrix (Fin n) (Fin n) Rat) (s : List Nat)
    (hcheck : Hex.Matrix.det (matrix k n rows) =
      Hex.MvPoly.Kernel.denote (n := k) (cmp := Mono.grevlex) (value w))
    (hA : evaluated k n rows ctx =
        Matrix.diagonal (fun i : Fin n => (s.getD i 1 : Rat)) * A)
    (hs : s.length = n) :
    (DetWitness.prodNat s : Rat) * A.det = HexReflectMathlib.Kernel.hom k ctx
      (Hex.MvPoly.Kernel.denote (cmp := Mono.grevlex) (value w)) := by
  have hdet := transport_det k n rows w (HexReflectMathlib.Kernel.hom k ctx)
    (Matrix.diagonal (fun i : Fin n => (s.getD i 1 : Rat)) * A) hcheck (hA.symm.trans (evaluated_eq k n rows ctx))
  rw [Matrix.det_mul, Matrix.det_diagonal] at hdet
  rw [HexMatrixMathlib.prodNat_cast s n hs]
  exact hdet


/-- A finite universal proposition expressed by nested conjunctions. This is
used only for symbolic literal identification, outside certificate arithmetic. -/
@[expose] def AllFin : (n : Nat) → (Fin n → Prop) → Prop
  | 0, _ => True
  | n + 1, P => P 0 ∧ AllFin n (fun i => P i.succ)

theorem allFin (n : Nat) (P : Fin n → Prop) (h : AllFin n P) : ∀ i, P i := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih => exact Fin.cases h.1 (ih _ h.2)

/-- Symbolic identification requires only the entry proofs, never a decidable
equality instance on the user's carrier. -/
theorem identify {n : Nat} (A B : Matrix (Fin n) (Fin n) F)
    (h : AllFin n (fun i => AllFin n (fun j => A i j = B i j))) : A = B :=
  Matrix.ext fun i j => allFin n _ (allFin n _ h i) j


end Polynomial

end HexMatrixMathlib.DetPoly
