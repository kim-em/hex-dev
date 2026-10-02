/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.MatrixEval

public section

namespace Hex.Kronecker

theorem flatten_injective {r : α → α → Prop} {as bs : List (List α)}
    (hr : List.Forall₂ (List.Forall₂ r) as bs) (he : as.flatten = bs.flatten) : as = bs := by
  induction hr with
  | nil => rfl
  | cons h ht ih =>
      have h := List.append_inj he h.length_eq
      rw [List.cons.injEq]
      exact ⟨h.1, ih h.2⟩

theorem checkMulTerms_polynomial {budget : Budget} {mode : MulMode} {k n r m : Nat}
    {a b c : TermMatrix} (h : checkMulTerms budget mode k n r m a b c = true) :
    polyProduct (columnsWith 0 m (matrixPolynomial k b)) (matrixPolynomial k a) = matrixPolynomial k c := by
  by_cases hw : (matrixShape k n r a && matrixShape k r m b && matrixShape k n m c) = true
  swap
  · simp [checkMulTerms, sizeMulTerms, hw] at h
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
  have hc := (Bool.and_eq_true_iff.mp hw).2
  let cap := 2^budget.maxPackedBits
  let ab := matrixBounds cap k a
  let bb := matrixBounds cap k b
  let cb := matrixBounds cap k c
  let products := productBounds cap k (boundColumns k m bb) ab
  let common := commonBounds cap k products.flatten cb.flatten
  let obs := ab.flatten ++ bb.flatten ++ cb.flatten ++ products.flatten
  let s₀ := makeSize budget common obs
  let s := s₀.withMode budget mode r
  have hprod := product_bounded (polyColumns_bounded cap k r m b hb) (matrix_bounded cap k n r a ha)
  have hcb := matrix_bounded cap k n m c hc
  have hpf := List.rel_flatten hprod
  have hcf := List.rel_flatten hcb
  have hlen : common.degrees.length = k := commonBounds_length cap k _ _
    (fun x hx => (bounded_data hpf x hx).1) (fun x hx => (bounded_data hcf x hx).1)
  have hs : s.strides.length = k := by
    cases mode <;> simpa only [s, SizeBound.withMode, s₀, makeSize, length_makeStrides] using hlen
  simp only [checkMulTerms, sizeMulTerms, hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  change (s.accepts budget && checkRows mode s r (Hex.Matrix.Packed.columns m (packMatrix s b))
    (packMatrix s a) (packMatrix s c)) = true at h
  have hacc := withMode_accept s₀ budget mode r rfl (Bool.and_eq_true_iff.mp h).1
  have he := (Bool.and_eq_true_iff.mp h).2
  rw [packMatrix_eval s hs a ha, packMatrix_eval s hs b hb, packMatrix_eval s hs c hc,
    ← columnsWith_int] at he
  let v := fun i : Fin k => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0
  let E := MvPolynomial.eval₂Hom (RingHom.id Int) v
  have hm : columnsWith (0 : Int) m ((matrixPolynomial k b).map (List.map E)) =
      (columnsWith 0 m (matrixPolynomial k b)).map (List.map E) := by
    simpa only [map_zero] using columnsWith_map E 0 m (matrixPolynomial k b)
  change checkRows mode s r (columnsWith 0 m ((matrixPolynomial k b).map (List.map E)))
    ((matrixPolynomial k a).map (List.map E)) ((matrixPolynomial k c).map (List.map E)) = true at he
  rw [hm] at he
  have he := checkRows_polynomial mode s r v _ _ _ he
  apply flatten_injective he
  apply bounded_lists budget obs hpf hcf
    (fun x hx => by simp [obs,products,ab,bb,cb,hx])
    (fun x hx => by simp [obs,products,ab,bb,cb,hx]) hacc
  have hef := List.rel_flatten he
  cases mode <;> simpa only [v, s, SizeBound.withMode, s₀] using hef

end Hex.Kronecker
