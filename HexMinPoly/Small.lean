/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPoly.MinPoly

public section

/-! Closed forms for degenerate matrix dimensions. -/

namespace Hex.Matrix

universe u

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F]

omit [DecidableEq F] in
private theorem field_smul (x y : F) : x • y = x * y := rfl

omit [DecidableEq F] in
private theorem field_zero : (Zero.zero : F) = 0 := rfl

private theorem eq_zero_of_smul_eq_zero {n : Nat} (c : F) (v : Vector F n)
    (hv : v ≠ 0) (h : c • v = 0) : c = 0 := by
  by_cases hc : c = 0
  · exact hc
  · exact False.elim (hv (by
      apply Vector.ext
      intro i hi
      have hentry := congrArg (fun w : Vector F n => w[i]) h
      simp only [Vector.getElem_smul, Vector.getElem_zero] at hentry
      rw [field_smul] at hentry
      grind))

omit [DecidableEq F] in
private theorem evalVecList_eigen {n : Nat} (coeffs : List F)
    (A : Matrix F n n) (v : Vector F n) (a : F)
    (hA : A * v = a • v) :
    evalVecList coeffs A v = DensePoly.evalCoeffList coeffs a • v := by
  induction coeffs with
  | nil =>
      simp only [evalVecList, List.foldr_nil, DensePoly.evalCoeffList]
      ext i hi
      rw [Vector.getElem_zero, Vector.getElem_smul, field_smul]
      exact (Lean.Grind.Semiring.zero_mul v[i]).symm
  | cons c cs ih =>
      change c • v + A * evalVecList cs A v =
        (DensePoly.evalCoeffList cs a * a + c) • v
      rw [ih, Matrix.mulVec_smul, hA]
      ext i hi
      simp only [Vector.getElem_add, Vector.getElem_smul]
      rw [field_smul, field_smul, field_smul, field_smul]
      grind

/-- Polynomial evaluation on an eigenvector reduces to scalar evaluation at
the corresponding eigenvalue. -/
theorem evalVec_eigen {n : Nat} (p : DensePoly F) (A : Matrix F n n)
    (v : Vector F n) (a : F) (hA : A * v = a • v) :
    evalVec p A v = p.eval a • v := by
  rw [evalVec_eq_list]
  unfold DensePoly.eval
  exact evalVecList_eigen p.toList A v a hA

/-- The zero vector has constant order polynomial `1`. -/
@[simp]
theorem vecMinPoly_zero {n : Nat} (A : Matrix F n n) :
    vecMinPoly A (0 : Vector F n) = 1 := by
  have honeMonic : (1 : DensePoly F).Monic := by
    rw [DensePoly.monic_iff_leadingCoeff_eq_one, DensePoly.leadingCoeff_one]
  apply DensePoly.monic_dvd_antisymm (vecMinPoly_monic A 0) honeMonic
  · apply vecMinPoly_dvd A 0 1
    exact evalVec_zero 1 A
  · refine ⟨vecMinPoly A 0, ?_⟩
    rw [DensePoly.mul_comm_poly, DensePoly.mul_one_right_poly]

/-- The Krylov degree of the zero vector is zero. -/
@[simp]
theorem krylovDeg_zero {n : Nat} (A : Matrix F n n) :
    krylovDeg A (0 : Vector F n) = 0 := by
  have h := degree?_vecMinPoly A (0 : Vector F n)
  rw [vecMinPoly_zero] at h
  have hone : (1 : F) ≠ 0 := fun h => Lean.Grind.Field.zero_ne_one h.symm
  rw [DensePoly.degree?_eq_some_of_pos_size _ (by
      rw [DensePoly.size_one hone]
      omega), DensePoly.size_one hone] at h
  exact Option.some.inj h.symm

private theorem eq_C_of_degree_zero (p : DensePoly F)
    (hdegree : p.degree?.getD 0 = 0) : p = DensePoly.C (p.coeff 0) := by
  by_cases hp : p = 0
  · subst p
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_C]
    by_cases hi : i = 0
    · simp [hi, DensePoly.coeff_zero]
    · rw [ite_eq_right hi]
      exact rfl
  · have hpos : 0 < p.size := by
      by_cases h : 0 < p.size
      · exact h
      · exact False.elim (hp ((DensePoly.size_eq_zero_iff p).mp
          (Nat.eq_zero_of_not_pos h)))
    have hdeg := DensePoly.degree?_eq_some_of_pos_size p hpos
    rw [hdeg, Option.getD_some] at hdegree
    have hsize : p.size ≤ 1 := by omega
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_C]
    by_cases hi : i = 0
    · simp [hi]
    · rw [ite_eq_right hi]
      exact DensePoly.coeff_eq_zero_of_size_le p (by omega)

private theorem linear_size (a : F) : (#p[-a, 1] : DensePoly F).size = 2 := by
  apply Nat.le_antisymm
  · simpa using DensePoly.size_ofCoeffs_le (R := F) #[-a, 1]
  · by_cases h : 2 ≤ (#p[-a, 1] : DensePoly F).size
    · exact h
    · have hz := DensePoly.coeff_eq_zero_of_size_le
        (#p[-a, 1] : DensePoly F) (i := 1) (by omega)
      have hone : (#p[-a, 1] : DensePoly F).coeff 1 = 1 := by
        rw [DensePoly.coeff_ofCoeffs]
        rfl
      rw [hone] at hz
      exact False.elim (Lean.Grind.Field.zero_ne_one hz.symm)

private theorem linear_coeff (a : F) (i : Nat) :
    (#p[-a, 1] : DensePoly F).coeff i =
      if i = 0 then -a else if i = 1 then 1 else 0 := by
  by_cases hi0 : i = 0
  · subst i
    rw [DensePoly.coeff_ofCoeffs, ite_eq_left rfl]
    rfl
  · by_cases hi1 : i = 1
    · subst i
      rw [DensePoly.coeff_ofCoeffs, ite_eq_right (by omega),
        ite_eq_left rfl]
      rfl
    · rw [ite_eq_right hi0, ite_eq_right hi1]
      apply DensePoly.coeff_eq_zero_of_size_le
      rw [linear_size]
      omega

private theorem linear_degree (a : F) :
    (#p[-a, 1] : DensePoly F).degree?.getD 0 = 1 := by
  have hsize := linear_size a
  rw [DensePoly.degree?_eq_some_of_pos_size _ (by omega), Option.getD_some,
    hsize]

private theorem linear_monic (a : F) :
    (#p[-a, 1] : DensePoly F).Monic := by
  rw [DensePoly.monic_iff_leadingCoeff_eq_one,
    DensePoly.leadingCoeff_eq_coeff_last _ (linear_size a ▸ by omega),
    linear_size, DensePoly.coeff_ofCoeffs]
  rfl

private theorem linear_eval (a : F) :
    (#p[-a, 1] : DensePoly F).eval a = 0 := by
  have hpoly : (#p[-a, 1] : DensePoly F) =
      DensePoly.C (-a) + DensePoly.monomial 1 1 := by
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_add_semiring, DensePoly.coeff_C,
      DensePoly.coeff_monomial, linear_coeff]
    by_cases hi0 : i = 0
    · subst i
      simp only [ite_eq_left, ite_eq_right Nat.zero_ne_one]
      simp only [field_zero]
      change -a = -a + (0 : F)
      exact (Lean.Grind.Semiring.add_zero (-a)).symm
    · by_cases hi1 : i = 1
      · subst i
        simp only [ite_eq_right Nat.one_ne_zero, ite_eq_left]
        simp only [field_zero]
        change (1 : F) = 0 + 1
        calc
          (1 : F) = 1 + 0 := (Lean.Grind.Semiring.add_zero 1).symm
          _ = 0 + 1 := Lean.Grind.Semiring.add_comm 1 0
      · simp only [ite_eq_right hi0, ite_eq_right hi1]
        simp only [field_zero]
        change (0 : F) = 0 + 0
        exact (Lean.Grind.Semiring.add_zero 0).symm
  rw [hpoly, DensePoly.eval_add_semiring, DensePoly.eval_C_semiring,
    DensePoly.eval_monomial_semiring]
  grind

private theorem linear_dvd_of_eval_eq_zero (p : DensePoly F) (a : F)
    (heval : p.eval a = 0) : (#p[-a, 1] : DensePoly F) ∣ p := by
  let d : DensePoly F := #p[-a, 1]
  let qr := DensePoly.divMod p d
  have hdDegree : d.degree?.getD 0 = 1 := linear_degree a
  have hdMonic : d.Monic := linear_monic a
  have hcancel : ∀ b : F,
      b - (b / d.leadingCoeff) * d.leadingCoeff = 0 := by
    intro b
    rw [DensePoly.leadingCoeff_eq_one_of_monic hdMonic]
    grind
  have hremDegree :=
    DensePoly.divMod_remainder_degree_lt_of_pos_degree_of_cancel p d (by omega) hcancel
  have hremZero : qr.2.degree?.getD 0 = 0 := by
    change (DensePoly.divMod p d).2.degree?.getD 0 = 0
    omega
  have hremC := eq_C_of_degree_zero qr.2 hremZero
  have hreconstruct : qr.1 * d + qr.2 = p := by
    exact DensePoly.divMod_reconstruction p d hcancel
  have hremEval : qr.2.eval a = 0 := by
    have h := congrArg (fun q : DensePoly F => q.eval a) hreconstruct
    rw [DensePoly.eval_add_semiring, DensePoly.eval_mul_commring,
      linear_eval, heval] at h
    grind
  have hrem : qr.2 = 0 := by
    rw [hremC, DensePoly.eval_C_semiring] at hremEval
    rw [hremC, hremEval]
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_C, DensePoly.coeff_zero]
    split <;> rfl
  refine ⟨qr.1, ?_⟩
  rw [← hreconstruct, hrem, DensePoly.add_zero_poly, DensePoly.mul_comm_poly]

/-- A nonzero eigenvector has the expected linear order polynomial. -/
theorem vecMinPoly_eigen {n : Nat} (A : Matrix F n n) (v : Vector F n)
    (a : F) (hv : v ≠ 0) (hA : A * v = a • v) :
    vecMinPoly A v = #p[-a, 1] := by
  apply DensePoly.monic_dvd_antisymm (vecMinPoly_monic A v) (linear_monic a)
  · apply vecMinPoly_dvd A v
    rw [evalVec_eigen _ A v a hA, linear_eval]
    ext i hi
    simp only [Vector.getElem_smul, Vector.getElem_zero]
    rw [field_smul]
    exact Lean.Grind.Semiring.zero_mul v[i]
  · apply linear_dvd_of_eval_eq_zero
    apply eq_zero_of_smul_eq_zero _ v hv
    rw [← evalVec_eigen (vecMinPoly A v) A v a hA]
    exact evalVec_vecMinPoly A v

/-- The zero matrix of positive dimension has minimal polynomial `x`. -/
@[simp]
theorem minPoly_zero (n : Nat) (hn : 0 < n) :
    minPoly (0 : Matrix F n n) = #p[0, 1] := by
  have hzero : (#p[-(0 : F), 1] : DensePoly F) = #p[0, 1] := by
    apply DensePoly.ext_coeff
    intro i
    rw [linear_coeff]
    by_cases hi0 : i = 0
    · subst i
      rw [DensePoly.coeff_ofCoeffs, ite_eq_left rfl]
      change -(0 : F) = 0
      grind
    · by_cases hi1 : i = 1
      · subst i
        rw [DensePoly.coeff_ofCoeffs, ite_eq_right (by omega),
          ite_eq_left rfl]
        rfl
      · rw [ite_eq_right hi0, ite_eq_right hi1]
        symm
        apply DensePoly.coeff_eq_zero_of_size_le
        have hs : (#p[0, 1] : DensePoly F).size ≤ 2 := by
          simpa using DensePoly.size_ofCoeffs_le (R := F) #[0, 1]
        omega
  rw [← hzero]
  apply DensePoly.monic_dvd_antisymm (minPoly_monic _) (linear_monic 0)
  · apply minPoly_dvd
    intro v
    rw [evalVec_eigen (a := 0)]
    · rw [linear_eval]
      ext i hi
      simp only [Vector.getElem_smul, Vector.getElem_zero]
      rw [field_smul]
      exact Lean.Grind.Semiring.zero_mul v[i]
    · rw [Matrix.zero_mulVec]
      ext i hi
      simp only [Vector.getElem_zero, Vector.getElem_smul]
      rw [field_smul]
      exact (Lean.Grind.Semiring.zero_mul v[i]).symm
  · apply linear_dvd_of_eval_eq_zero
    let i : Fin n := ⟨0, hn⟩
    have h := evalVec_minPoly (0 : Matrix F n n) (basisVec n i)
    rw [evalVec_eigen (a := 0)] at h
    · have hbFin : (basisVec n i)[i] = (1 : F) := by
        unfold basisVec
        rw [Matrix.getElem_row, Matrix.getElem_identity,
          ite_eq_left rfl]
      have hb : (basisVec n i)[i.val] = (1 : F) := by
        exact hbFin
      have hentry := congrArg (fun v : Vector F n => v[i.val]) h
      rw [Vector.getElem_smul, field_smul, hb, Vector.getElem_zero,
        Lean.Grind.Semiring.mul_one] at hentry
      exact hentry
    · rw [Matrix.zero_mulVec]
      ext j hj
      simp only [Vector.getElem_zero, Vector.getElem_smul]
      rw [field_smul]
      exact (Lean.Grind.Semiring.zero_mul (basisVec n i)[j]).symm

/-- A positive-dimensional identity matrix has minimal polynomial `x - 1`. -/
@[simp]
theorem minPoly_identity (n : Nat) (hn : 0 < n) :
    minPoly (Matrix.identity (R := F) n) = #p[-1, 1] := by
  apply DensePoly.monic_dvd_antisymm (minPoly_monic _) (linear_monic 1)
  · apply minPoly_dvd
    intro v
    rw [evalVec_eigen (a := 1)]
    · rw [linear_eval]
      ext i hi
      simp only [Vector.getElem_smul, Vector.getElem_zero]
      rw [field_smul]
      exact Lean.Grind.Semiring.zero_mul v[i]
    · rw [Matrix.identity_mulVec]
      ext i hi
      simp only [Vector.getElem_smul]
      rw [field_smul, Lean.Grind.Semiring.one_mul]
  · apply linear_dvd_of_eval_eq_zero
    let i : Fin n := ⟨0, hn⟩
    have hbFin : (basisVec n i)[i] = (1 : F) := by
      unfold basisVec
      rw [Matrix.getElem_row, Matrix.getElem_identity,
        ite_eq_left rfl]
    have hbNe : basisVec n i ≠ (0 : Vector F n) := by
      intro hzero
      have hentry := congrArg (fun v : Vector F n => v[i.val]) hzero
      rw [show (basisVec n i)[i.val] = (1 : F) from hbFin,
        Vector.getElem_zero] at hentry
      exact Lean.Grind.Field.zero_ne_one hentry.symm
    apply eq_zero_of_smul_eq_zero _ (basisVec n i) hbNe
    rw [← evalVec_eigen (minPoly (Matrix.identity (R := F) n))
      (Matrix.identity (R := F) n) (basisVec n i) 1]
    · exact evalVec_minPoly (Matrix.identity (R := F) n) (basisVec n i)
    · rw [Matrix.identity_mulVec]
      ext j hj
      simp only [Vector.getElem_smul]
      rw [field_smul, Lean.Grind.Semiring.one_mul]

/-- A one-by-one matrix has the expected linear minimal polynomial. -/
@[simp]
theorem minPoly_one_by_one (A : Matrix F 1 1) :
    minPoly A = #p[-A[(0, 0)], 1] := by
  let a := A[(0, 0)]
  have hscalar (v : Vector F 1) : A * v = a • v := by
    ext i hi
    have hi0 : i = 0 := by omega
    subst i
    rw [Vector.getElem_smul, field_smul]
    change (Matrix.mulVec A v)[0] = a * v[0]
    simp [Matrix.mulVec, Matrix.row, Vector.dotProduct, a,
      List.finRange_succ]
    rw [Lean.Grind.Semiring.add_comm, Lean.Grind.Semiring.add_zero]
  apply DensePoly.monic_dvd_antisymm (minPoly_monic _) (linear_monic a)
  · apply minPoly_dvd
    intro v
    rw [evalVec_eigen (a := a) _ _ _ (hscalar v), linear_eval]
    ext i hi
    simp only [Vector.getElem_smul, Vector.getElem_zero]
    rw [field_smul]
    exact Lean.Grind.Semiring.zero_mul v[i]
  · apply linear_dvd_of_eval_eq_zero
    let i : Fin 1 := ⟨0, by omega⟩
    have h := evalVec_minPoly A (basisVec 1 i)
    rw [evalVec_eigen (a := a) _ _ _ (hscalar _)] at h
    have hbFin : (basisVec 1 i)[i] = (1 : F) := by
      unfold basisVec
      rw [Matrix.getElem_row, Matrix.getElem_identity,
        ite_eq_left rfl]
    have hb : (basisVec 1 i)[i.val] = (1 : F) := by
      exact hbFin
    have hentry := congrArg (fun v : Vector F 1 => v[i.val]) h
    rw [Vector.getElem_smul, field_smul, hb, Vector.getElem_zero,
      Lean.Grind.Semiring.mul_one] at hentry
    exact hentry

end Hex.Matrix
