/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdeal.Kernel
public import HexDeterminantalIdealMathlib.Locus
public import HexReflectMathlib
public import HexMatrixMathlib.Literal

@[expose] public section

namespace HexDeterminantalIdealMathlib

open Hex HexMatrixMathlib
open scoped HexMvPolyMathlib

universe u v w

abbrev Poly := MvPoly.Kernel.PolyList
abbrev Rows (C : Type) := List (List (Poly C))

/-- The displayed conjunction omits a redundant final `True`. -/
def AllZero {F : Type u} [Zero F] : List F → Prop
  | [] => True
  | [x] => x = 0
  | x :: y :: xs => x = 0 ∧ AllZero (y :: xs)

theorem allZero_iff {F : Type u} [Zero F] (xs : List F) :
    AllZero xs ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp [AllZero]
  | cons x xs ih => cases xs <;> simp_all [AllZero]

/-- A shape check containing only list lengths and natural comparisons. -/
def shape (n m : Nat) (L : List (List α)) : Bool :=
  Nat.beq L.length n && L.all (fun row => Nat.beq row.length m)

/-- Matrix denotation through the literal layer's row constructor. -/
def listMatrix {R : Type u} [Zero R] (n m : Nat) (L : List (List R)) : Hex.Matrix R n m :=
  matrixEquiv.symm (ofLists n m L)

theorem listMatrix_rows {R : Type u} [Zero R] (n m : Nat) (L : List (List R))
    (h : shape n m L = true) : Hex.Matrix.rowLists (listMatrix n m L) = L := by
  obtain ⟨hn, hm⟩ : L.length = n ∧ ∀ row ∈ L, row.length = m := by
    simpa [shape, Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] using h
  apply List.ext_getElem
  · simpa [Hex.Matrix.length_rowLists] using hn.symm
  · intro i hi hi'
    have hin : i < n := by simpa [Hex.Matrix.length_rowLists] using hi
    have hr : L[i].length = m := hm _ (List.getElem_mem hi')
    have hleft : (Hex.Matrix.rowLists (listMatrix n m L))[i].length = m := by
      simp [Hex.Matrix.rowLists]
    apply List.ext_getElem
    · exact hleft.trans hr.symm
    · intro j hj hj'
      have hjm : j < m := by omega
      have e := Hex.Matrix.get_rowLists (listMatrix n m L) ⟨i, hin⟩ ⟨j, hjm⟩
      simp only [Hex.Matrix.Lists.entry_eq_getD] at e
      rw [getD_eq_getElem' _ _ _ hi, getD_eq_getElem' _ _ _ hj] at e
      rw [e]
      rw [← matrixEquiv_apply]
      rw [listMatrix, Equiv.apply_symm_apply, ofLists_apply,
        getD_eq_getElem' _ _ _ hi', getD_eq_getElem' _ _ _ hj']

/-- Mapping entries preserves rectangular shape. -/
theorem shape_map (f : α → β) (L : List (List α)) (n m : Nat) :
    shape n m (L.map (List.map f)) = shape n m L := by
  simp [shape, List.all_map, Function.comp_def]

variable {C : Type} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
  {k n m : Nat} {F : Type u} [CommRing F]

/-- A quoted polynomial matrix is defined directly from its entry encodings. -/
def polynomial (n m k : Nat) (L : Rows C) : Hex.Matrix (MvPoly k C Mono.grevlex) n m :=
  listMatrix n m (L.map (List.map (MvPoly.Kernel.denote (cmp := Mono.grevlex))))

/-- Denotation with the batch order and coefficient ring instances fixed. -/
def denote (k : Nat) (g : Poly C) : MvPoly k C Mono.grevlex := MvPoly.Kernel.denote g

/-- The evaluation map with the batch monomial order fixed. -/
noncomputable def evaluation (ι : C →+* F) (v : Fin k → F) : MvPoly k C Mono.grevlex →+* F :=
  HexMvPolyMathlib.eval₂MathlibHom ι v

/-- The list view of reflection's polynomial terms. -/
def termLists (f : Int → C) (ts : List (Mono k × Int)) : Poly C :=
  ts.map fun t => (t.1.toList, f t.2)

theorem cons_eq {α : Type*} {a b : α} {as bs : List α} (h : a = b) (hs : as = bs) :
    a :: as = b :: bs := by cases h; cases hs; rfl

theorem fin_ext_nil {α : Type*} (f g : Fin 0 → α) : f = g :=
  funext fun i => Fin.elim0 i

theorem fin_ext_cons {α : Type*} {n : Nat} (f g : Fin (n + 1) → α)
    (h : f 0 = g 0) (hs : (fun i : Fin n => f i.succ) = (fun i : Fin n => g i.succ)) : f = g :=
  funext (Fin.cases h fun i => congrFun hs i)

/-- The batch interpretation transfers to normalized entry encodings. -/
theorem interpret_entry (ι : C →+* F) (v : Fin k → F) (f : Int → C)
    (ts : List (Mono k × Int)) (raw L : Poly C)
    (hraw : termLists f ts = raw) (h : MvPoly.Kernel.normalize raw = L) (a : F)
    (ha : MvPoly.eval₂ ι v (Hex.Reflect.ofIntTerms (cmp := Mono.grevlex) f ts) = a) :
    HexMvPolyMathlib.eval₂MathlibHom ι v (MvPoly.Kernel.denote (cmp := Mono.grevlex) L) = a := by
  have hd : MvPoly.Kernel.denote (cmp := Mono.grevlex) L =
      Hex.Reflect.ofIntTerms f ts := by
    rw [← h, ← hraw, MvPoly.Kernel.denote_normalize, MvPoly.Kernel.denote_eq_ofTerms,
      Hex.Reflect.ofIntTerms, termLists]
    congr 1
    simp [List.map_map, MvPoly.Kernel.mono_toList]
  rw [hd, HexMvPolyMathlib.eval₂MathlibHom_apply]
  exact ha

/-- Interpreting a row-list polynomial matrix commutes with its construction. -/
theorem map_ofLists {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (n m : Nat) (L : List (List R)) :
    (ofLists n m L).map φ = ofLists n m (L.map (List.map φ)) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply, ofLists_apply, ofLists_apply]
  simp only [← Hex.Matrix.Lists.entry_eq_getD]
  have hr := Hex.Matrix.MinorArithmetic.Interpretation.entry_map (List.map φ) [] L i.val
  have he := Hex.Matrix.MinorArithmetic.Interpretation.entry_map φ 0 (Hex.Matrix.Lists.entry [] L i.val) j.val
  simp only [List.map_nil] at hr
  rw [map_zero] at he
  rw [← hr, ← he]

/-- Batch entry equalities identify the matrix without evaluating source atoms. -/
theorem interpret_matrix (ι : C →+* F) (v : Fin k → F) (L : Rows C)
    (source : List (List F)) (A : Matrix (Fin n) (Fin m) F)
    (hL : L.map (List.map (fun p => HexMvPolyMathlib.eval₂MathlibHom ι v
      (MvPoly.Kernel.denote (cmp := Mono.grevlex) p))) = source)
    (hA : A = ofLists n m source) :
    A = (matrixEquiv (polynomial n m k L)).map (HexMvPolyMathlib.eval₂MathlibHom ι v) := by
  rw [hA, ← hL, polynomial, listMatrix, Equiv.apply_symm_apply, map_ofLists]
  simp only [List.map_map, Function.comp_def]

/-- The canonical entry invariant is checked on primitive lists. -/
def canonical (k : Nat) (L : Rows C) : Bool :=
  L.all (fun row => row.all (MvPoly.Kernel.isCanonical k))

omit [BEq C] [LawfulBEq C] in
theorem canonical_iff (L : Rows C) : canonical k L = true ↔
    ∀ row ∈ L, ∀ p ∈ row, MvPoly.Kernel.Canonical k p := by
  simp [canonical, List.all_eq_true, MvPoly.Kernel.isCanonical_iff]

/-- Transport the complete checked generator list to the polynomial matrix. -/
theorem generators (L : Rows C) (hs : shape n m L = true)
    (hc : canonical k L = true) (r : Nat) (G : List (Poly C))
    (hG : Hex.Matrix.detIdealGensList (Hex.Matrix.MinorArithmetic.poly k) r L = G) :
    G.map (MvPoly.Kernel.denote (cmp := Mono.grevlex)) =
      Hex.Matrix.detIdealGens r (polynomial n m k L) := by
  rw [← hG]
  apply Hex.Matrix.detIdealGensList_denote L _ ((canonical_iff L).mp hc)
  exact (listMatrix_rows n m _ (by simpa only [shape_map] using hs)).symm

/-- A displayed list and its equality suffice to state the exact rank locus. -/
theorem locus [IsDomain F] (ι : C →+* F) (v : Fin k → F)
    (P : Hex.Matrix (MvPoly k C Mono.grevlex) n m) (A : Matrix (Fin n) (Fin m) F)
    (hA : A = (matrixEquiv P).map (HexMvPolyMathlib.eval₂MathlibHom ι v))
    (r : Nat) (G : List (MvPoly k C Mono.grevlex))
    (hG : G = Hex.Matrix.detIdealGens r P) (gs : List F)
    (hg : G.map (HexMvPolyMathlib.eval₂MathlibHom ι v) = gs) :
    A.rank < r ↔ AllZero gs := by
  rw [allZero_iff, ← hg, List.forall_mem_map, hG, hA]
  exact (gens_vanish_iff_rank_lt_of_domain ι P v r).symm

/-- A nonzero selected minor gives a lower bound over every source domain. -/
theorem minor_lower [IsDomain F] (ι : C →+* F) (v : Fin k → F)
    (P : Hex.Matrix (MvPoly k C Mono.grevlex) n m) (A : Matrix (Fin n) (Fin m) F)
    (hA : A = (matrixEquiv P).map (HexMvPolyMathlib.eval₂MathlibHom ι v))
    (r : Nat) (g : MvPoly k C Mono.grevlex) (hg : g ∈ Hex.Matrix.minors r P)
    (x : F) (hx : HexMvPolyMathlib.eval₂MathlibHom ι v g = x) (hne : x ≠ 0) :
    r ≤ A.rank := by
  let φ := HexMvPolyMathlib.eval₂MathlibHom (cmp := Mono.grevlex) ι v
  let j := algebraMap F (FractionRing F)
  have hj := IsFractionRing.injective F (FractionRing F)
  have h : r ≤ ((matrixEquiv P).map (j.comp φ)).rank :=
    (le_rank_iff_exists_minor_map_ne_zero (j.comp φ) P r).mpr
      ⟨g, hg, fun he => hne (hx ▸ (hj (he.trans (map_zero j).symm)))⟩
  have hm : (matrixEquiv P).map (j.comp φ) = ((matrixEquiv P).map φ).map j := rfl
  rw [hm, HexMatrixMathlib.rank_map_eq] at h
  simpa only [hA, φ] using h

/-- Certify just one encoded minor. -/
theorem selected (L : Rows C) (hs : shape n m L = true)
    (hc : canonical k L = true) (r : Nat) (rows cols : List Nat)
    (hr : rows ∈ Hex.Matrix.indexTuples r n) (hcol : cols ∈ Hex.Matrix.indexTuples r m)
    (g : Poly C) (hg : Hex.Matrix.minorList (Hex.Matrix.MinorArithmetic.poly k) rows cols L = g) :
    MvPoly.Kernel.denote (cmp := Mono.grevlex) g ∈
      Hex.Matrix.minors r (polynomial n m k L) := by
  rw [← hg]
  have hP : L.map (List.map (MvPoly.Kernel.denote (cmp := Mono.grevlex))) =
      Hex.Matrix.rowLists (polynomial n m k L) :=
    (listMatrix_rows n m _ (by simpa only [shape_map] using hs)).symm
  have ht : MvPoly.Kernel.denote (cmp := Mono.grevlex)
      (Hex.Matrix.minorList (Hex.Matrix.MinorArithmetic.poly k) rows cols L) ∈
      Hex.Matrix.minors r (polynomial n m k L) :=
    Hex.Matrix.minorList_mem L (polynomial n m k L)
      ((canonical_iff L).mp hc) hP r rows cols hr hcol
  exact ht

end HexDeterminantalIdealMathlib
