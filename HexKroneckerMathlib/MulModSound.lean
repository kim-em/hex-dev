/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.MatrixQuotient

public section

namespace Hex.Kronecker

theorem checkMulTermsMod_polynomial {budget : Budget} {mode : MulMode} {k n r m p : Nat}
    {a b c q : TermMatrix} (h : checkMulTermsMod budget mode k n r m p a b c q = true) :
    List.Forall₂ (fun a b => a.length = b.length)
      (polyProduct (columnsWith 0 m (matrixPolynomial k b)) (matrixPolynomial k a)) (matrixPolynomial k c) ∧
    List.zipWith (List.zipWith (·-·))
      (polyProduct (columnsWith 0 m (matrixPolynomial k b)) (matrixPolynomial k a)) (matrixPolynomial k c) =
      (matrixPolynomial k q).map (List.map (MvPolynomial.C (p:Int)*·)) := by
  by_cases hp : (p == 0) = true
  · simp [checkMulTermsMod, sizeMulTermsMod, hp] at h
  by_cases hw : (matrixShape k n r a && matrixShape k r m b && matrixShape k n m c && matrixShape k n m q) = true
  swap
  · simp [checkMulTermsMod, sizeMulTermsMod, hp, hw] at h
  by_cases hv : (a.all (fun row => row.all (termResidues p)) &&
      b.all (fun row => row.all (termResidues p)) && c.all (fun row => row.all (termResidues p))) = true
  swap
  · simp [checkMulTermsMod, sizeMulTermsMod, hp, hw, hv] at h
  by_cases hq : q.all (fun row => row.all (Hex.MvPoly.Kernel.isCanonical k)) = true
  swap
  · simp [checkMulTermsMod, sizeMulTermsMod, hp, hw, hv, hq] at h
  have hw₁ := (Bool.and_eq_true_iff.mp hw).1
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw₁).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw₁).1).2
  have hc := (Bool.and_eq_true_iff.mp hw₁).2
  have hqs := (Bool.and_eq_true_iff.mp hw).2
  let cap := 2^budget.maxPackedBits
  let ab := matrixBounds cap k a
  let bb := matrixBounds cap k b
  let cb := matrixBounds cap k c
  let qb := matrixBounds cap k q
  let products := productBounds cap k (boundColumns k m bb) ab
  let differences := differenceBounds cap products.flatten cb.flatten
  let scaled := qb.flatten.map ((Bounds.mk (zeroDegrees k) (min p cap)).mul cap)
  let common := commonBounds cap k differences scaled
  let obs := ab.flatten ++ bb.flatten ++ cb.flatten ++ qb.flatten ++ products.flatten ++ differences ++ scaled
  let s₀ := makeSize budget common obs
  let s := s₀.withMode budget mode r
  have hprod := product_bounded (polyColumns_bounded cap k r m b hb) (matrix_bounded cap k n r a ha)
  have hcb := matrix_bounded cap k n m c hc
  have hqb := matrix_bounded cap k n m q hqs
  have hdb := difference_bounded (List.rel_flatten hprod) (List.rel_flatten hcb)
  have hsb := scaled_bounded p (List.rel_flatten hqb)
  have hlen : common.degrees.length = k := commonBounds_length cap k _ _
    (fun x hx => (bounded_data hdb x hx).1) (fun x hx => (bounded_data hsb x hx).1)
  have hs : s.strides.length = k := by
    cases mode <;> simpa only [s, SizeBound.withMode, s₀, makeSize, length_makeStrides] using hlen
  simp only [checkMulTermsMod, sizeMulTermsMod, hp, hw, hv, hq,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  change (s.accepts budget && checkRowsMod mode s r p (Hex.Matrix.Packed.columns m (packMatrix s b))
    (packMatrix s a) (packMatrix s c) (packMatrix s q)) = true at h
  have hacc := withMode_accept s₀ budget mode r rfl (Bool.and_eq_true_iff.mp h).1
  have he := (Bool.and_eq_true_iff.mp h).2
  rw [packMatrix_eval s hs a ha, packMatrix_eval s hs b hb, packMatrix_eval s hs c hc,
    packMatrix_eval s hs q hqs, ← columnsWith_int] at he
  let v := fun i : Fin k => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0
  let E := MvPolynomial.eval₂Hom (RingHom.id Int) v
  have hm : columnsWith (0 : Int) m ((matrixPolynomial k b).map (List.map E)) =
      (columnsWith 0 m (matrixPolynomial k b)).map (List.map E) := by
    simpa only [map_zero] using columnsWith_map E 0 m (matrixPolynomial k b)
  change checkRowsMod mode s r p (columnsWith 0 m ((matrixPolynomial k b).map (List.map E)))
    ((matrixPolynomial k a).map (List.map E)) ((matrixPolynomial k c).map (List.map E))
    ((matrixPolynomial k q).map (List.map E)) = true at he
  rw [hm] at he
  have he := checkRowsMod_polynomial mode s r p v _ _ _ _ he
  refine ⟨he.1, ?_⟩
  apply flatten_injective he.2
  rw [flatten_zipWith _ he.1, ← List.map_flatten]
  apply bounded_lists budget obs hdb hsb
    (fun x hx => by simp [obs,differences,products,ab,bb,cb,qb,hx])
    (fun x hx => by
      have hx : x ∈ scaled := hx
      simp only [obs, List.mem_append]
      tauto) hacc
  have hef := List.rel_flatten he.2
  rw [flatten_zipWith _ he.1, ← List.map_flatten] at hef
  cases mode <;> simpa only [v, s, SizeBound.withMode, s₀] using hef

theorem zipWith_getD (f : α → β → γ) (as : List α) (bs : List β) (da : α) (db : β)
    (hl : as.length = bs.length) (i : Nat) :
    (List.zipWith f as bs).getD i (f da db) = f (as.getD i da) (bs.getD i db) := by
  induction as generalizing bs i with
  | nil =>
      have : bs = [] := List.length_eq_zero_iff.mp hl.symm
      subst bs
      rfl
  | cons a as ih =>
      cases bs with
      | nil => simp at hl
      | cons b bs =>
          cases i with
          | zero => rfl
          | succ i => exact ih bs (by simpa using hl) i

theorem matrixSub_entry {k : Nat} {as bs : List (List (MvPolynomial (Fin k) Int))}
    (hl : List.Forall₂ (fun a b => a.length = b.length) as bs) (i j : Nat) :
    ((List.zipWith (List.zipWith (·-·)) as bs).getD i []).getD j 0 =
      (as.getD i []).getD j 0 - (bs.getD i []).getD j 0 := by
  rw [show ([] : List (MvPolynomial (Fin k) Int)) = List.zipWith (·-·) [] [] from rfl,
    zipWith_getD _ as bs [] [] hl.length_eq i]
  have hrow := rel_getD hl [] [] rfl i
  simp only [List.zipWith_nil_left]
  simpa only [sub_self] using zipWith_getD (·-·) (as.getD i []) (bs.getD i []) 0 0 hrow j

theorem matrixScale_entry {k : Nat} (p : Nat) (qs : List (List (MvPolynomial (Fin k) Int))) (i j : Nat) :
    ((qs.map (List.map (MvPolynomial.C (p:Int)*·))).getD i []).getD j 0 =
      MvPolynomial.C (p:Int)*(qs.getD i []).getD j 0 := by
  rw [show ([] : List (MvPolynomial (Fin k) Int)) = List.map (MvPolynomial.C (p:Int)*·) [] from rfl,
    List.getD_map]
  simp only [List.map_nil]
  have hm := List.getD_map (l := qs.getD i []) (d := (0 : MvPolynomial (Fin k) Int))
    (n := j) (fun x : MvPolynomial (Fin k) Int => MvPolynomial.C (p:Int)*x)
  rw [mul_zero] at hm
  exact hm

/-- Quotient-witness soundness, entrywise in every ring of characteristic `p`. -/
theorem checkMulTermsMod_entry {budget : Budget} {mode : MulMode} {k n r m p : Nat}
    {a b c q : TermMatrix} (h : checkMulTermsMod budget mode k n r m p a b c q = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Fin k → R) (i : Fin n) (j : Fin m),
      (∑ t : Fin r, denoteEntry v a i.val t.val * denoteEntry v b t.val j.val) =
        denoteEntry v c i.val j.val := by
  intro R _ _ v i j
  have hw : (matrixShape k n r a && matrixShape k r m b && matrixShape k n m c && matrixShape k n m q) = true := by
    by_cases hp : (p == 0) = true
    · simp [checkMulTermsMod, sizeMulTermsMod, hp] at h
    by_cases hw : (matrixShape k n r a && matrixShape k r m b && matrixShape k n m c && matrixShape k n m q) = true
    · exact hw
    · simp [checkMulTermsMod, sizeMulTermsMod, hp, hw] at h
  have hw₁ := (Bool.and_eq_true_iff.mp hw).1
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw₁).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw₁).1).2
  obtain ⟨hl,he⟩ := checkMulTermsMod_polynomial h
  have he := congrArg (fun rows => (rows.getD i.val []).getD j.val 0) he
  rw [matrixSub_entry hl, matrixScale_entry, product_entry ha hb, matrixPolynomial_getD,
    matrixPolynomial_getD] at he
  have he := quotient_sound he v
  simpa only [map_sum, map_mul, denoteEntry] using he

/-- An integer quotient matrix certifies the finite product in characteristic `p`. -/
theorem checkMulTermsMod_sound {budget : Budget} {mode : MulMode} {k n r m p : Nat}
    {a b c q : TermMatrix} (h : checkMulTermsMod budget mode k n r m p a b c q = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Fin k → R),
      denoteMatrix n r R v a * denoteMatrix r m R v b = denoteMatrix n m R v c := by
  intro R _ _ v
  funext i j
  simpa only [_root_.Matrix.mul_apply, denoteMatrix] using checkMulTermsMod_entry h v i j

end Hex.Kronecker
