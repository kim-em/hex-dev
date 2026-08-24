/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix
public import HexPoly

public section

/-! Polynomial evaluation at a matrix, applied directly to a vector. -/

namespace Hex.Matrix

universe u

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n : Nat}

/-- Horner evaluation of `p` at `A`, applied to `v`.  This uses only
matrix-vector products. -/
@[expose]
def evalVec (p : DensePoly F) (A : Matrix F n n) (v : Vector F n) : Vector F n :=
  (List.range p.size).reverse.foldl
    (fun acc i => p.coeff i • v + A * acc) 0

/-- Horner evaluation written directly over a coefficient list. -/
@[expose]
def evalVecList (coeffs : List F) (A : Matrix F n n) (v : Vector F n) :
    Vector F n :=
  coeffs.foldr (fun c acc => c • v + A * acc) 0

/-- The indexed implementation agrees with a fold over the stored coefficient
list. -/
theorem evalVec_eq_list (p : DensePoly F) (A : Matrix F n n) (v : Vector F n) :
    evalVec p A v = evalVecList p.toList A v := by
  unfold evalVec evalVecList
  rw [DensePoly.toList_eq_coeff_range]
  rw [List.foldl_reverse]
  simp only [List.foldr_map]

private theorem evalVecList_trim (coeffs : List F) (A : Matrix F n n)
    (v : Vector F n) :
    evalVecList (DensePoly.trimTrailingZerosList coeffs) A v =
      evalVecList coeffs A v := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
      by_cases htrim : DensePoly.trimTrailingZerosList cs = [] ∧ c = 0
      · have hc : c = (Zero.zero : F) := htrim.2
        have htail : evalVecList cs A v = (0 : Vector F n) := by
          rw [← ih, htrim.1]
          rfl
        rw [show DensePoly.trimTrailingZerosList (c :: cs) = [] by
          simp [DensePoly.trimTrailingZerosList, htrim.1, hc]]
        simp only [evalVecList, List.foldr_nil, List.foldr_cons]
        change List.foldr (fun c acc => c • v + A * acc) 0 cs = 0 at htail
        rw [htail, htrim.2, Matrix.mulVec_zero]
        ext i hi
        simp only [Vector.getElem_add, Vector.getElem_smul, Vector.getElem_zero]
        symm
        change (0 : F) * v[i] + 0 = 0
        grind
      · have htrim' : ¬(DensePoly.trimTrailingZerosList cs = [] ∧
            c = (Zero.zero : F)) := by
          intro h
          exact htrim ⟨h.1, h.2⟩
        rw [show DensePoly.trimTrailingZerosList (c :: cs) =
            c :: DensePoly.trimTrailingZerosList cs by
          simp [DensePoly.trimTrailingZerosList, htrim']]
        simp only [evalVecList, List.foldr_cons] at ih ⊢
        rw [ih]

/-- Evaluating a polynomial built from a coefficient list is the corresponding
list-level Horner fold; normalization does not affect the result. -/
theorem evalVec_ofList (coeffs : List F) (A : Matrix F n n) (v : Vector F n) :
    evalVec (DensePoly.ofList coeffs) A v = evalVecList coeffs A v := by
  rw [evalVec_eq_list]
  unfold DensePoly.ofList DensePoly.toList DensePoly.toArray DensePoly.ofCoeffs
    DensePoly.trimTrailingZeros
  simpa using evalVecList_trim coeffs A v

/-- The zero polynomial evaluates to the zero vector. -/
@[simp, grind =]
theorem evalVec_zero_poly (A : Matrix F n n) (v : Vector F n) :
    evalVec (0 : DensePoly F) A v = 0 := by
  unfold evalVec
  rw [DensePoly.size_zero]
  rfl

/-- A constant polynomial acts by scalar multiplication. -/
theorem evalVec_C (c : F) (A : Matrix F n n) (v : Vector F n) :
    evalVec (DensePoly.C c) A v = c • v := by
  have hC : DensePoly.C c = DensePoly.ofList [c] := by
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_C, DensePoly.coeff_ofList]
    cases i <;> simp
  rw [hC, evalVec_ofList]
  simp only [evalVecList, List.foldr_cons, List.foldr_nil]
  rw [Matrix.mulVec_zero]
  ext i hi
  simp only [Vector.getElem_add, Vector.getElem_smul, Vector.getElem_zero]
  change c * v[i] + 0 = c * v[i]
  grind

private theorem evalFold_add (p : DensePoly F) (A : Matrix F n n)
    (u v xu xv : Vector F n) (indices : List Nat) :
    indices.foldl (fun acc i => p.coeff i • (u + v) + A * acc) (xu + xv) =
      indices.foldl (fun acc i => p.coeff i • u + A * acc) xu +
        indices.foldl (fun acc i => p.coeff i • v + A * acc) xv := by
  induction indices generalizing xu xv with
  | nil => rfl
  | cons i indices ih =>
      simp only [List.foldl_cons]
      have hstep : p.coeff i • (u + v) + A * (xu + xv) =
          (p.coeff i • u + A * xu) + (p.coeff i • v + A * xv) := by
        rw [Matrix.mulVec_add]
        ext j hj
        simp only [Vector.getElem_add, Vector.getElem_smul]
        change p.coeff i * (u[j] + v[j]) + ((A * xu)[j] + (A * xv)[j]) =
          (p.coeff i * u[j] + (A * xu)[j]) +
            (p.coeff i * v[j] + (A * xv)[j])
        grind
      rw [hstep]
      exact ih (p.coeff i • u + A * xu) (p.coeff i • v + A * xv)

private theorem evalFold_smul (p : DensePoly F) (A : Matrix F n n)
    (c : F) (v x : Vector F n) (indices : List Nat) :
    indices.foldl (fun acc i => p.coeff i • (c • v) + A * acc) (c • x) =
      c • indices.foldl (fun acc i => p.coeff i • v + A * acc) x := by
  induction indices generalizing x with
  | nil => rfl
  | cons i indices ih =>
      simp only [List.foldl_cons]
      have hstep : p.coeff i • (c • v) + A * (c • x) =
          c • (p.coeff i • v + A * x) := by
        rw [Matrix.mulVec_smul]
        ext j hj
        simp only [Vector.getElem_add, Vector.getElem_smul]
        change p.coeff i * (c * v[j]) + c * (A * x)[j] =
          c * (p.coeff i * v[j] + (A * x)[j])
        grind
      rw [hstep]
      exact ih (p.coeff i • v + A * x)

/-- Horner evaluation is additive in its vector argument. -/
theorem evalVec_add (p : DensePoly F) (A : Matrix F n n) (u v : Vector F n) :
    evalVec p A (u + v) = evalVec p A u + evalVec p A v := by
  unfold evalVec
  have hzero : (0 : Vector F n) + 0 = 0 := by
    ext i hi
    simp only [Vector.getElem_add, Vector.getElem_zero]
    grind
  simpa only [hzero] using
    evalFold_add p A u v 0 0 (List.range p.size).reverse

/-- Horner evaluation commutes with scalar multiplication of the vector. -/
theorem evalVec_smul (p : DensePoly F) (A : Matrix F n n) (c : F) (v : Vector F n) :
    evalVec p A (c • v) = c • evalVec p A v := by
  unfold evalVec
  have hzero : c • (0 : Vector F n) = 0 := by
    ext i hi
    simp only [Vector.getElem_smul, Vector.getElem_zero]
    change c * 0 = 0
    grind
  simpa only [hzero] using
    evalFold_smul p A c v 0 (List.range p.size).reverse

/-- Evaluating at the zero vector gives the zero vector. -/
@[simp, grind =]
theorem evalVec_zero (p : DensePoly F) (A : Matrix F n n) :
    evalVec p A (0 : Vector F n) = 0 := by
  unfold evalVec
  generalize (List.range p.size).reverse = xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hstep : p.coeff i • (0 : Vector F n) + A * (0 : Vector F n) = 0 := by
        ext j hj
        simp only [Vector.getElem_add, Vector.getElem_smul, Vector.getElem_zero]
        change p.coeff i * 0 + (A * (0 : Vector F n))[j] = 0
        rw [Matrix.mulVec_zero]
        simp only [Vector.getElem_zero]
        grind
      rw [hstep]
      exact ih

/-- Evaluation commutes with a finite fold of vector additions. -/
theorem evalVec_foldl_add (p : DensePoly F) (A : Matrix F n n)
    {I : Type} (xs : List I) (f : I → Vector F n) (acc : Vector F n) :
    evalVec p A (xs.foldl (fun acc i => acc + f i) acc) =
      xs.foldl (fun acc i => acc + evalVec p A (f i)) (evalVec p A acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih, evalVec_add]

end Hex.Matrix
