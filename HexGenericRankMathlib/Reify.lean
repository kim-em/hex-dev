/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib.Kernel
public import HexReflectMathlib

@[expose] public section

namespace HexGenericRankMathlib

open Hex HexMatrixMathlib
open scoped HexMvPolyMathlib

universe u

variable {C : Type} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
  {k n m : Nat} {F : Type u} [CommRing F]

/-- Assemble a row-list equality from entry equalities. -/
theorem cons_eq {α : Type*} {a b : α} {as bs : List α} (h : a = b) (hs : as = bs) :
    a :: as = b :: bs := by cases h; cases hs; rfl

/-- Pointwise equality on an empty finite domain. -/
theorem fin_ext_nil {α : Type*} (f g : Fin 0 → α) : f = g :=
  funext fun i => Fin.elim0 i

/-- Assemble finite function equality from its head and tail. -/
theorem fin_ext_cons {α : Type*} {n : Nat} (f g : Fin (n + 1) → α)
    (h : f 0 = g 0) (hs : (fun i : Fin n => f i.succ) = (fun i : Fin n => g i.succ)) : f = g :=
  funext (Fin.cases h fun i => congrFun hs i)

/-- Transfer nonvanishing from the displayed denominator. -/
theorem nonzero_of_display {R : Type*} [Zero R] {d e : R} (h : d = e) (he : e ≠ 0) :
    d ≠ 0 := h ▸ he

/-- The list view of the terms supplied by one reflection batch. -/
def termLists (f : Int → C) (ts : List (Mono k × Int)) : PolyLists.Poly C :=
  ts.map fun t => (t.1.toList, f t.2)

/-- Normalising reflection's term lists preserves the quoted polynomial. -/
theorem denote_terms (f : Int → C) (ts : List (Mono k × Int))
    (L : PolyLists.Poly C) (h : MvPoly.Kernel.normalize (termLists f ts) = L) :
    PolyLists.denote (k := k) L = Hex.Reflect.ofIntTerms (cmp := Mono.grevlex) f ts := by
  rw [← h, PolyLists.denote, MvPoly.Kernel.denote_normalize,
    MvPoly.Kernel.denote_eq_ofTerms, Hex.Reflect.ofIntTerms, termLists]
  congr 1
  simp [List.map_map, MvPoly.Kernel.mono_toList]

/-- An entry's batch interpretation proof transfers to its canonical term list. -/
theorem interpret_entry (ι : C →+* F) (v : Fin k → F) (f : Int → C)
    (ts : List (Mono k × Int)) (L : PolyLists.Poly C)
    (h : MvPoly.Kernel.normalize (termLists f ts) = L) (a : F)
    (ha : MvPoly.eval₂ ι v (Hex.Reflect.ofIntTerms (cmp := Mono.grevlex) f ts) = a) :
    HexMvPolyMathlib.eval₂MathlibHom ι v (PolyLists.denote L) = a := by
  rw [HexMvPolyMathlib.eval₂MathlibHom_apply, denote_terms f ts L h]
  exact ha

/-- Entrywise evaluation commutes with the row-list matrix constructor. -/
theorem map_matrix (ι : C →+* F) (v : Fin k → F) (L : PolyLists.Rows C) :
    (symbolic (PolyLists.matrix (k := k) n m L)).map (MvPolynomial.eval₂Hom ι v) =
      ofLists n m (L.map (List.map
        (fun p => HexMvPolyMathlib.eval₂MathlibHom ι v (PolyLists.denote p)))) := by
  rw [symbolic_map]
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply, PolyLists.matrix_apply, ofLists_apply]
  simp only [← Hex.Matrix.Lists.entry_eq_getD]
  let f := fun p => HexMvPolyMathlib.eval₂MathlibHom ι v (PolyLists.denote p)
  have hf : f [] = 0 := map_zero _
  change f (PolyLists.get L i j) =
    Hex.Matrix.Lists.entry 0 (Hex.Matrix.Lists.entry [] (L.map (List.map f)) i) j
  rw [← hf]
  change f (PolyLists.get L i j) =
    Hex.Matrix.Lists.entry (f [])
      (Hex.Matrix.Lists.entry (List.map f []) (L.map (List.map f)) i) j
  rw [PolyLists.entry_map, PolyLists.entry_map]
  rfl

/-- Batch interpretation assembled using equality of the two row lists. -/
theorem interpret_matrix (ι : C →+* F) (v : Fin k → F)
    (L : PolyLists.Rows C) (source : List (List F)) (A : Matrix (Fin n) (Fin m) F)
    (hL : L.map (List.map (fun p => HexMvPolyMathlib.eval₂MathlibHom ι v
      (PolyLists.denote p))) = source) (hA : A = ofLists n m source) :
    A = (symbolic (PolyLists.matrix (k := k) n m L)).map (MvPolynomial.eval₂Hom ι v) := by
  rw [map_matrix, hL, hA]

/-- Evaluate one displayed term directly in the source atoms. -/
theorem interpret_cons (ι : C →+* F) (v : Fin k → F)
    (t : List Nat × C) (ts : PolyLists.Poly C) :
    HexMvPolyMathlib.eval₂MathlibHom ι v (PolyLists.denote (t :: ts)) =
      ι t.2 * (∏ i : Fin k, v i ^ t.1.getD i.val 0) +
        HexMvPolyMathlib.eval₂MathlibHom ι v (PolyLists.denote ts) := by
  rw [PolyLists.denote, MvPoly.Kernel.denote, map_add]
  congr 1
  rw [eval₂_comp]
  change MvPolynomial.eval₂ ι v
    (HexMvPolyMathlib.equiv (MvPoly.monomial (MvPoly.Kernel.mono k t.1) t.2)) = _
  rw [HexMvPolyMathlib.equiv_apply, HexMvPolyMathlib.toMvPolynomial_monomial,
    MvPolynomial.eval₂_monomial, Finsupp.prod_pow]
  simp only [HexMvPolyMathlib.monoEquiv_apply, MvPoly.Kernel.get_mono]

/-- Evaluation of the empty term list. -/
theorem interpret_nil (ι : C →+* F) (v : Fin k → F) :
    HexMvPolyMathlib.eval₂MathlibHom ι v (PolyLists.denote []) = 0 := map_zero _

/-- The term-form result distinguishes the polynomial matrix from its
specialisation. Its rank proof is explicitly about the polynomial matrix. -/
structure GenericResult (k : Nat) (C : Type) [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
    {F : Type u} [CommRing F] {n m : Nat} (A : Matrix (Fin n) (Fin m) F) where
  value : Nat
  atoms : Array F
  valuation : Fin k → F
  coefficientMap : C →+* F
  polynomial : Hex.Matrix (MvPoly k C Mono.grevlex) n m
  certificate : Hex.Matrix.RankCert (MvPoly k C Mono.grevlex) n m
  checked : Hex.Matrix.checkRank polynomial certificate = true
  proof : (symbolic polynomial).rank = value
  interpretation : A = (symbolic polynomial).map (MvPolynomial.eval₂Hom coefficientMap valuation)

/-- An unconditional rank value and its proof for the user's matrix. -/
structure RankResult {F : Type u} [CommRing F] {n m : Nat}
    (A : Matrix (Fin n) (Fin m) F) where
  value : Nat
  proof : A.rank = value

end HexGenericRankMathlib
