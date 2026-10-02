/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdeal.Residue
public import HexDeterminantalIdealMathlib.Result

@[expose] public section

namespace HexDeterminantalIdealMathlib.Residue

open Hex HexMatrixMathlib MvPoly.Kernel
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64

/-- Check just the exponent lengths of the raw reflected terms. -/
def exponents (k : Nat) (a : Poly Int) : Bool := a.all (fun t => Nat.beq t.1.length k)

/-- The canonical residue entry check. -/
def canonical (p k : Nat) (L : Rows Nat) : Bool :=
  L.all (fun row => row.all (isCanonicalMod p k))

theorem canonical_iff {p k : Nat} (L : Rows Nat) : canonical p k L = true ↔
    ∀ row ∈ L, ∀ a ∈ row, CanonicalMod p k a := by
  simp [canonical, List.all_eq_true, isCanonicalMod_iff]

variable (p : Nat) [ZMod64.Bounds p] {k n m : Nat} {F : Type*} [CommRing F]

/-- The semantic coefficient conversion is separate from residue arithmetic. -/
def rows (L : Rows Nat) : Rows (ZMod64 p) := L.map (List.map (toResidues p))

theorem denote_eq (k : Nat) (a : Poly Nat) : denoteMod p (n := k) (cmp := Mono.grevlex) a =
    HexDeterminantalIdealMathlib.denote k (toResidues p a) := by
  unfold denoteMod HexDeterminantalIdealMathlib.denote
  generalize toResidues p a = ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [MvPoly.Kernel.denote]
    rw [ih]
    rfl

/-- Transfer a reflected entry through its closed natural-residue reduction. -/
theorem interpret_entry (ι : ZMod64 p →+* F) (v : Fin k → F)
    (ts : List (Mono k × Int)) (raw : Poly Int) (L : Poly Nat)
    (hraw : termLists id ts = raw) (he : exponents k raw = true)
    (h : Hex.Matrix.Residue.reduce p raw = L) (a : F)
    (ha : MvPoly.eval₂ ι v
      (Hex.Reflect.ofIntTerms (cmp := Mono.grevlex) (Int.cast : Int → ZMod64 p) ts) = a) :
    HexMvPolyMathlib.eval₂MathlibHom ι v (HexDeterminantalIdealMathlib.denote k (toResidues p L)) = a := by
  rw [← denote_eq p k L]
  have hlen : ∀ t ∈ raw, t.1.length = k := by
    simpa [exponents, List.all_eq_true, Nat.beq_eq] using he
  have hd : denoteMod p (n := k) (cmp := Mono.grevlex) L =
      Hex.Reflect.ofIntTerms (cmp := Mono.grevlex) (Int.cast : Int → ZMod64 p) ts := by
    rw [← h, Hex.Matrix.Residue.denote_reduce p raw hlen, ← hraw,
      denote_eq_ofTerms, Hex.Reflect.ofIntTerms]
    congr 1
    simp only [CoeffMap.map, termLists, List.map_map, Function.comp_def, mono_toList]
    apply List.map_congr_left
    intro t _
    rfl
  rw [hd, HexMvPolyMathlib.eval₂MathlibHom_apply]
  exact ha

/-- The natural-residue generator check has exactly the reference meaning. -/
theorem generators (L : Rows Nat) (hs : shape n m L = true)
    (hc : canonical p k L = true) (r : Nat) (G : List (Poly Nat))
    (hG : Hex.Matrix.detIdealGensList (Hex.Matrix.MinorArithmetic.residue p k) r L = G) :
    G.map (denoteMod p (n := k) (cmp := Mono.grevlex)) =
      Hex.Matrix.detIdealGens r (polynomial n m k (rows p L)) := by
  rw [← hG]
  apply Hex.Matrix.detIdealGensMod_denote p L _ ((canonical_iff L).mp hc)
  have he : L.map (List.map (denoteMod p (n := k) (cmp := Mono.grevlex))) =
      (rows p L).map (List.map (HexDeterminantalIdealMathlib.denote k)) := by
    simp only [rows, List.map_map, Function.comp_def]
    congr 1
    funext row
    exact List.map_congr_left (fun a _ => denote_eq p k a)
  rw [he]
  have hshape : shape n m ((rows p L).map (List.map
      (HexDeterminantalIdealMathlib.denote k))) = true := by
    rw [shape_map, rows, shape_map]
    exact hs
  exact (listMatrix_rows n m _ hshape).symm

/-- Certify only the selected natural-residue minor. -/
theorem selected (L : Rows Nat) (hs : shape n m L = true)
    (hc : canonical p k L = true) (r : Nat) (rs cs : List Nat)
    (hr : rs ∈ Hex.Matrix.indexTuples r n) (hcol : cs ∈ Hex.Matrix.indexTuples r m)
    (g : Poly Nat) (hg : Hex.Matrix.minorList (Hex.Matrix.MinorArithmetic.residue p k) rs cs L = g) :
    denoteMod p (n := k) (cmp := Mono.grevlex) g ∈
      Hex.Matrix.minors r (polynomial n m k (rows p L)) := by
  rw [← hg]
  have hP : L.map (List.map (denoteMod p (n := k) (cmp := Mono.grevlex))) =
      Hex.Matrix.rowLists (polynomial n m k (rows p L)) := by
    have he : L.map (List.map (denoteMod p (n := k) (cmp := Mono.grevlex))) =
        (rows p L).map (List.map (HexDeterminantalIdealMathlib.denote k)) := by
      simp only [rows, List.map_map, Function.comp_def]
      congr 1
      funext row
      exact List.map_congr_left (fun a _ => denote_eq p k a)
    rw [he]
    have hshape : shape n m ((rows p L).map (List.map
        (HexDeterminantalIdealMathlib.denote k))) = true := by
      rw [shape_map, rows, shape_map]
      exact hs
    exact (listMatrix_rows n m _ hshape).symm
  exact Hex.Matrix.minorMod_mem p L _ ((canonical_iff L).mp hc) hP r rs cs hr hcol

/-- Denotation with the batch monomial order fixed. -/
def denote (k : Nat) (g : Poly Nat) : MvPoly k (ZMod64 p) Mono.grevlex := denoteMod p g

/-- Independent prime-characteristic variables also give the symbolic payload. -/
noncomputable def idealData {D : Type u} [CommRing D] [CharP D p] {σ : Type v}
    (v : Fin k → MvPolynomial σ D) (f : Fin k → σ)
    (hf : Function.Injective f) (hv : v = MvPolynomial.X ∘ f)
    (P : Hex.Matrix (MvPoly k (ZMod64 p) Mono.grevlex) n m) (r : Nat) :
    IdealData.{u, v} (HexReflectMathlib.residueHom p (MvPolynomial σ D)) v P r D σ :=
  HexDeterminantalIdealMathlib.idealData _ v P r (HexReflectMathlib.residueHom p D)
    (HexReflectMathlib.residueHom_injective p D) f hf
    (heq_of_eq (HexReflectMathlib.residueHom_mvPolynomial p σ D)) (heq_of_eq hv)

end HexDeterminantalIdealMathlib.Residue
