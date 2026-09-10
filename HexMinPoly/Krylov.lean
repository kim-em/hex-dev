/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Data.Vector.Lemmas
public import HexMinPoly.EvalVec

public section

/-! Standard basis vectors and Krylov sequences. -/

namespace Hex.Matrix

universe u

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n : Nat}

/-- The `i`-th standard basis vector of `F^n`. -/
@[expose]
def basisVec (n : Nat) (i : Fin n) : Vector F n :=
  Matrix.row (Matrix.identity (R := F) n) i

/-- `A^j v`, computed using `j` matrix-vector products. -/
@[expose]
def krylovVec (A : Matrix F n n) (v : Vector F n) : Nat → Vector F n
  | 0 => v
  | j + 1 => A * krylovVec A v j

omit [DecidableEq F] in
/-- Krylov iteration is additive in its initial vector. -/
@[simp, grind =]
theorem krylovVec_add (A : Matrix F n n) (u v : Vector F n) (j : Nat) :
    krylovVec A (u + v) j = krylovVec A u j + krylovVec A v j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [krylovVec]
      rw [ih, Matrix.mulVec_add]

omit [DecidableEq F] in
/-- Krylov iteration commutes with scalar multiplication. -/
@[simp, grind =]
theorem krylovVec_smul (A : Matrix F n n) (c : F) (v : Vector F n) (j : Nat) :
    krylovVec A (c • v) j = c • krylovVec A v j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [krylovVec]
      rw [ih, Matrix.mulVec_smul]

omit [DecidableEq F] in
/-- Every iterate of the zero vector is zero. -/
@[simp, grind =]
theorem krylovVec_zero (A : Matrix F n n) (j : Nat) :
    krylovVec A (0 : Vector F n) j = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [krylovVec]
      rw [ih, Matrix.mulVec_zero]

omit [DecidableEq F] in
/-- Starting a Krylov sequence at `A v` shifts its index by one. -/
theorem krylovVec_mulVec (A : Matrix F n n) (v : Vector F n) (j : Nat) :
    krylovVec A (A * v) j = krylovVec A v (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [krylovVec]
      rw [ih]
      change A * krylovVec A v (j + 1) = A * krylovVec A v (j + 1)
      rfl

/-- The first `r` Krylov vectors, sharing every matrix-vector product. -/
@[expose]
def krylovRows (A : Matrix F n n) (v : Vector F n) : (r : Nat) → Vector (Vector F n) r
  | 0 => #v[]
  | 1 => #v[v]
  | r + 2 =>
      let rows := krylovRows A v (r + 1)
      rows.push (A * rows[r])

omit [DecidableEq F] in
/-- Reading the shared Krylov row array agrees with `krylovVec`. -/
@[simp, grind =]
theorem krylovRows_get (A : Matrix F n n) (v : Vector F n) {r : Nat} (i : Fin r) :
    (krylovRows A v r).get i = krylovVec A v i.val := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
      cases r with
      | zero => exact Fin.elim0 i
      | succ r =>
        cases r with
        | zero =>
          have hi : i = ⟨0, by omega⟩ := Fin.eq_of_val_eq (by omega)
          subst i
          rfl
        | succ r =>
          change (krylovRows A v (r + 2))[i.val] = krylovVec A v i.val
          rw [krylovRows]
          by_cases hi : i.val < r + 1
          · rw [Vector.getElem_push_lt]
            exact ih (r + 1) (by omega) ⟨i.val, hi⟩
          · have hieq : i.val = r + 1 := by omega
            have hiFin : i = ⟨r + 1, by omega⟩ := Fin.eq_of_val_eq hieq
            rw [hiFin]
            simp only [Vector.getElem_push, Nat.lt_irrefl]
            change A * (krylovRows A v (r + 1))[r] = krylovVec A v (r + 1)
            rw [show (krylovRows A v (r + 1))[r] = krylovVec A v r by
              exact ih (r + 1) (by omega) ⟨r, by omega⟩]
            rfl

/-- The `r × n` matrix whose rows are `v, A v, …, A^(r-1) v`. -/
@[expose]
def krylovMat (A : Matrix F n n) (v : Vector F n) (r : Nat) : Matrix F r n :=
  Matrix.ofRows (krylovRows A v r)

omit [DecidableEq F] in
/-- Row `i` of the Krylov matrix is `A^i v`. -/
@[simp, grind =]
theorem getRow_krylovMat (A : Matrix F n n) (v : Vector F n) {r : Nat} (i : Fin r) :
    Matrix.getRow (krylovMat A v r) i = krylovVec A v i.val := by
  rw [krylovMat, Matrix.getRow_ofRows]
  exact krylovRows_get A v i

private theorem map_coe_finRange_eq_range (r : Nat) :
    (List.finRange r).map (fun i => i.val) = List.range r := by
  apply List.ext_getElem <;> simp [List.finRange]

private theorem hornerRange (p : DensePoly F) (A : Matrix F n n)
    (v x : Vector F n) (s : Nat) :
    (List.range s).reverse.foldl
        (fun acc i => p.coeff i • v + A * acc) x =
      (List.range s).foldl
          (fun acc i => acc + p.coeff i • krylovVec A v i) 0 +
        krylovVec A x s := by
  induction s generalizing x with
  | zero =>
      simp only [List.range_zero, List.reverse_nil, List.foldl_nil, krylovVec]
      ext i hi
      simp only [Vector.getElem_add, Vector.getElem_zero]
      grind
  | succ s ih =>
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, List.foldl_cons,
        List.foldl_append]
      rw [ih]
      rw [krylovVec_add, krylovVec_smul, krylovVec_mulVec]
      ext i hi
      simp only [Vector.getElem_add, Vector.getElem_smul]
      grind

private theorem coeffKrylovSum_extend (p : DensePoly F) (A : Matrix F n n)
    (v : Vector F n) (r : Nat) (hr : p.size ≤ r) :
    (List.range p.size).foldl
        (fun acc i => acc + p.coeff i • krylovVec A v i) 0 =
      (List.range r).foldl
        (fun acc i => acc + p.coeff i • krylovVec A v i) 0 := by
  have hrEq : r = p.size + (r - p.size) := by omega
  rw [hrEq, List.range_add, List.foldl_append, List.foldl_map]
  symm
  have hterm (i : Nat) : p.coeff (p.size + i) • krylovVec A v (p.size + i) =
      (0 : Vector F n) := by
    have hcoeff : p.coeff (p.size + i) = 0 :=
      p.coeff_eq_zero_of_size_le (Nat.le_add_right p.size i)
    rw [hcoeff]
    ext j hj
    simp only [Vector.getElem_smul, Vector.getElem_zero]
    change (0 : F) * (krylovVec A v (p.size + i))[j] = 0
    grind
  let z :=
    (List.range p.size).foldl
      (fun acc i => acc + p.coeff i • krylovVec A v i) 0
  change (List.range (r - p.size)).foldl
    (fun acc i => acc + p.coeff (p.size + i) • krylovVec A v (p.size + i)) z = z
  generalize List.range (r - p.size) = xs
  induction xs generalizing z with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [hterm]
      have hzero (acc : Vector F n) : acc + 0 = acc := by
        ext j hj
        simp only [Vector.getElem_add, Vector.getElem_zero]
        grind
      rw [hzero]
      exact ih

/-- Horner evaluation is the coefficient row combination of a sufficiently
long Krylov matrix. -/
theorem evalVec_eq_vecMul_krylov (p : DensePoly F) (A : Matrix F n n)
    (v : Vector F n) (r : Nat) (hr : p.size ≤ r) :
    evalVec p A v = vecMul (p.coeffVec r) (krylovMat A v r) := by
  unfold evalVec
  rw [hornerRange p A v 0 p.size, krylovVec_zero]
  have hzero :
      (List.range p.size).foldl
          (fun acc i => acc + p.coeff i • krylovVec A v i) 0 + 0 =
        (List.range p.size).foldl
          (fun acc i => acc + p.coeff i • krylovVec A v i) 0 := by
    ext i hi
    simp only [Vector.getElem_add, Vector.getElem_zero]
    grind
  rw [hzero, coeffKrylovSum_extend p A v r hr]
  rw [krylovMat, Matrix.vecMul_ofRows]
  rw [← map_coe_finRange_eq_range r, List.foldl_map]
  apply List.foldl_add_congr
  intro i hi
  change p.coeff i.val • krylovVec A v i.val =
    (p.coeffVec r).get i • (krylovRows A v r).get i
  rw [DensePoly.coeffVec_get, krylovRows_get]

/-- A polynomial whose coefficients vanish from `r` onward has size at most
`r`. -/
private theorem size_le_of_coeff_eq_zero {p : DensePoly F} {r : Nat}
    (h : ∀ i, r ≤ i → p.coeff i = 0) : p.size ≤ r := by
  by_cases hlt : r < p.size
  · exact absurd (h (p.size - 1) (by omega))
      (DensePoly.coeff_last_ne_zero_of_pos_size p (by omega))
  · omega

/-- Evaluation is additive in its polynomial argument. -/
theorem evalVec_add_poly (p q : DensePoly F) (A : Matrix F n n) (v : Vector F n) :
    evalVec (p + q) A v = evalVec p A v + evalVec q A v := by
  let r := max p.size q.size
  have hp : p.size ≤ r := Nat.le_max_left _ _
  have hq : q.size ≤ r := Nat.le_max_right _ _
  have hpq : (p + q).size ≤ r := by
    apply size_le_of_coeff_eq_zero
    intro i hi
    rw [DensePoly.coeff_add_semiring,
      p.coeff_eq_zero_of_size_le (Nat.le_trans hp hi),
      q.coeff_eq_zero_of_size_le (Nat.le_trans hq hi)]
    change (0 : F) + 0 = 0
    grind
  rw [evalVec_eq_vecMul_krylov (p + q) A v r hpq,
    evalVec_eq_vecMul_krylov p A v r hp,
    evalVec_eq_vecMul_krylov q A v r hq]
  have hcoeff : (p + q).coeffVec r = p.coeffVec r + q.coeffVec r := by
    apply Vector.ext
    intro i hi
    simp [DensePoly.coeffVec, DensePoly.coeff_add_semiring]
  rw [hcoeff, Matrix.vecMul_add]

/-- Evaluation commutes with coefficientwise scaling of a polynomial. -/
theorem evalVec_scale_poly (c : F) (p : DensePoly F)
    (A : Matrix F n n) (v : Vector F n) :
    evalVec (DensePoly.scale c p) A v = c • evalVec p A v := by
  have hscale : (DensePoly.scale c p).size ≤ p.size := by
    apply size_le_of_coeff_eq_zero
    intro i hi
    rw [DensePoly.coeff_scale_semiring, p.coeff_eq_zero_of_size_le hi]
    change c * (0 : F) = 0
    grind
  rw [evalVec_eq_vecMul_krylov (DensePoly.scale c p) A v p.size hscale,
    evalVec_eq_vecMul_krylov p A v p.size (Nat.le_refl _)]
  have hcoeff : (DensePoly.scale c p).coeffVec p.size = c • p.coeffVec p.size := by
    apply Vector.ext
    intro i hi
    simp [DensePoly.coeffVec, DensePoly.coeff_scale_semiring]
    change c * p.coeff i = c * p.coeff i
    rfl
  rw [hcoeff, Matrix.vecMul_smul]

omit [DecidableEq F] in
private theorem evalVecList_zero_prefix (k : Nat) (coeffs : List F)
    (A : Matrix F n n) (v : Vector F n) :
    evalVecList (List.replicate k (Zero.zero : F) ++ coeffs) A v =
      krylovVec A (evalVecList coeffs A v) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [evalVecList, List.foldr_cons]
      change List.foldr (fun c acc => c • v + A * acc) 0
          (List.replicate k (Zero.zero : F) ++ coeffs) =
        krylovVec A (List.foldr (fun c acc => c • v + A * acc) 0 coeffs) k at ih
      rw [ih]
      rw [krylovVec]
      change (0 : F) • v + A * krylovVec A (evalVecList coeffs A v) k =
        A * krylovVec A (evalVecList coeffs A v) k
      ext i hi
      simp only [Vector.getElem_add, Vector.getElem_smul]
      change (0 : F) * v[i] + (A * krylovVec A (evalVecList coeffs A v) k)[i] =
        (A * krylovVec A (evalVecList coeffs A v) k)[i]
      grind

/-- Shifting a polynomial by `x^k` starts its evaluation at the `k`-th
Krylov iterate. -/
theorem evalVec_shift (k : Nat) (p : DensePoly F)
    (A : Matrix F n n) (v : Vector F n) :
    evalVec (DensePoly.shift k p) A v =
      krylovVec A (evalVec p A v) k := by
  unfold DensePoly.shift
  by_cases hz : p.isZero
  · rw [ite_eq_left hz]
    have hp : p = 0 :=
      (DensePoly.size_eq_zero_iff p).mp ((DensePoly.isZero_eq_true_iff p).mp hz)
    rw [evalVec_zero_poly, hp, evalVec_zero_poly, krylovVec_zero]
  · rw [ite_eq_right hz, evalVec_ofList,
      evalVecList_zero_prefix]
    have hlist : evalVecList p.toList A v = evalVec p A v := by
      rw [← evalVec_ofList, DensePoly.ofList_toList]
    rw [hlist]

/-- A monomial selects one Krylov iterate. -/
theorem evalVec_monomial (k : Nat) (c : F) (A : Matrix F n n) (v : Vector F n) :
    evalVec (DensePoly.monomial k c) A v = c • krylovVec A v k := by
  have hmono : DensePoly.monomial k c = DensePoly.shift k (DensePoly.C c) := by
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_monomial, DensePoly.coeff_shift, DensePoly.coeff_C]
    by_cases hi : i = k
    · subst i
      simp
    · by_cases hlt : i < k
      · simp [hi, hlt]
      · have hsub : i - k ≠ 0 := by omega
        simp [hi, hlt, hsub]
  rw [hmono, evalVec_shift, evalVec_C, krylovVec_smul]

private theorem evalVec_monomial_mul (k : Nat) (c : F) (q : DensePoly F)
    (A : Matrix F n n) (v : Vector F n) :
    evalVec (DensePoly.monomial k c * q) A v =
      evalVec (DensePoly.monomial k c) A (evalVec q A v) := by
  have hmono : DensePoly.monomial k c =
      DensePoly.scale c (DensePoly.monomial k 1) := by
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_monomial, DensePoly.coeff_scale_semiring,
      DensePoly.coeff_monomial]
    by_cases hi : i = k
    · simp [hi]
      grind
    · simp [hi]
      change (0 : F) = c * 0
      grind
  calc
    evalVec (DensePoly.monomial k c * q) A v =
        evalVec (DensePoly.scale c (DensePoly.monomial k 1 * q)) A v := by
          rw [hmono, DensePoly.scale_mul]
    _ = c • evalVec (DensePoly.monomial k 1 * q) A v := by
          rw [evalVec_scale_poly]
    _ = c • evalVec (DensePoly.shift k q) A v := by
          rw [DensePoly.monomial_one_mul_poly_eq_shift]
    _ = c • krylovVec A (evalVec q A v) k := by rw [evalVec_shift]
    _ = evalVec (DensePoly.monomial k c) A (evalVec q A v) := by
          rw [evalVec_monomial]

private theorem evalVec_mul_of_size_le :
    ∀ (r : Nat) (p q : DensePoly F) (A : Matrix F n n) (v : Vector F n),
      p.size ≤ r → evalVec (p * q) A v = evalVec p A (evalVec q A v) := by
  intro r
  induction r with
  | zero =>
      intro p q A v hp
      have hp0 : p = 0 := (DensePoly.size_eq_zero_iff p).mp (Nat.le_zero.mp hp)
      subst p
      have hzq : (0 : DensePoly F) * q = 0 := by
        show DensePoly.mul 0 q = 0
        unfold DensePoly.mul
        rw [ite_eq_left (by
          simp [(DensePoly.isZero_eq_true_iff (0 : DensePoly F)).mpr rfl])]
      rw [hzq, evalVec_zero_poly, evalVec_zero_poly]
  | succ r ih =>
      intro p q A v hp
      by_cases hsmall : p.size ≤ r
      · exact ih p q A v hsmall
      · have hsplit : p =
            (p - DensePoly.monomial r (p.coeff r)) +
              DensePoly.monomial r (p.coeff r) := by
          apply DensePoly.ext_coeff
          intro i
          rw [DensePoly.coeff_add_semiring, DensePoly.coeff_sub_ring,
            DensePoly.coeff_monomial]
          grind
        have hsize :
            (p - DensePoly.monomial r (p.coeff r)).size ≤ r := by
          apply size_le_of_coeff_eq_zero
          intro i hi
          rw [DensePoly.coeff_sub_ring, DensePoly.coeff_monomial]
          by_cases hir : i = r
          · subst i
            simp
            grind
          · have hzi : p.coeff i = 0 := p.coeff_eq_zero_of_size_le (by omega)
            simp [hir, hzi]
            change (0 : F) - 0 = 0
            grind
        calc
          evalVec (p * q) A v =
              evalVec (((p - DensePoly.monomial r (p.coeff r)) +
                DensePoly.monomial r (p.coeff r)) * q) A v := by rw [← hsplit]
          _ = evalVec ((p - DensePoly.monomial r (p.coeff r)) * q +
                DensePoly.monomial r (p.coeff r) * q) A v := by
              rw [DensePoly.mul_add_left_poly]
          _ = evalVec ((p - DensePoly.monomial r (p.coeff r)) * q) A v +
                evalVec (DensePoly.monomial r (p.coeff r) * q) A v := by
              rw [evalVec_add_poly]
          _ = evalVec (p - DensePoly.monomial r (p.coeff r)) A (evalVec q A v) +
                evalVec (DensePoly.monomial r (p.coeff r)) A (evalVec q A v) := by
              rw [ih _ q A v hsize, evalVec_monomial_mul]
          _ = evalVec ((p - DensePoly.monomial r (p.coeff r)) +
                DensePoly.monomial r (p.coeff r)) A (evalVec q A v) := by
              rw [evalVec_add_poly]
          _ = evalVec p A (evalVec q A v) := by rw [← hsplit]

/-- Composition: `(p * q)(A) v = p(A) (q(A) v)`. -/
theorem evalVec_mul (p q : DensePoly F) (A : Matrix F n n) (v : Vector F n) :
    evalVec (p * q) A v = evalVec p A (evalVec q A v) :=
  evalVec_mul_of_size_le p.size p q A v (Nat.le_refl _)

end Hex.Matrix
